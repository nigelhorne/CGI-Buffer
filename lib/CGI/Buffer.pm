package CGI::Buffer;

use 5.14.0;	# For IO::Compress::Brotli
use strict;
use warnings;

use Digest::MD5;
use IO::String;
use CGI::Info;
use Carp;
use HTTP::Date;
use Readonly;
use Scalar::Util;

Readonly my $DEFAULT_GENERATE_304 => 1;
Readonly my $DEFAULT_GENERATE_LAST_MODIFIED => 1;
Readonly my $DEFAULT_COMPRESS_CONTENT => 1;
Readonly my $DEFAULT_OPTIMISE_CONTENT => 0;
Readonly my $DEFAULT_LINT_CONTENT => 0;
Readonly my $MIN_GZIP_LEN => 32;

# The longest a client's Cache-Control: max-age may keep a page in the
# server-side cache, since one client's request affects all others
Readonly my $MAX_CLIENT_CACHE_SECONDS => 600;

# The cookie that holds the token protecting forms, different for each client
# but it doesn't change the output
Readonly my $FORM_TOKEN_COOKIE => 'csrf_token';

# Cache-Control directives which, in a request or a response, stop the cache
Readonly my %NO_CACHE_DIRECTIVES => map { $_ => 1 } qw(no-store no-cache private);

# Request methods whose responses may be cached
Readonly my %SAFE_METHODS => map { $_ => 1 } qw(GET HEAD);

# The protocols that understand ETag, If-None-Match and If-Modified-Since
Readonly my $CONDITIONAL_PROTOCOL => qr/^HTTP\/(?:1\.1|[23](?:\.0)?)$/;

# The methods that CGI::Buffer calls on the logger
Readonly my @LOGGER_METHODS => qw(trace debug info warn error);

# An ETag sent with compressed content ends in the name of the encoding
Readonly my $ENCODED_ETAG_SUFFIX => qr/-(?:gzip|br|zstd)"$/;

# Content encodings that we can produce, and the module needed for each
Readonly my %ENCODING_MODULE => (
	'gzip' => 'Compress::Zlib',
	'x-gzip' => 'Compress::Zlib',
	'br' => 'IO::Compress::Brotli',
	'zstd' => 'Compress::Zstd',
);

=head1 NAME

CGI::Buffer - Verify, Cache and Optimise CGI Output

=head1 VERSION

Version 0.88

=cut

our $VERSION = '0.88';

=head1 SYNOPSIS

CGI::Buffer verifies the HTML that you produce by passing it through
C<HTML::Lint>.

CGI::Buffer optimises CGI programs by reducing, filtering and compressing
output to speed up the transmission and by nearly seamlessly making use of
client and server caches.

To make use of client caches, that is to say to reduce needless calls
to your server asking for the same data, all you need to do is to
include the package, and it does the rest.

    use CGI::Buffer;
    # ...

To also make use of server caches, that is to say to save regenerating
output when different clients ask you for the same data, you will need
to create a cache.
But that's simple:

    use CHI;
    use CGI::Buffer;

    # Put this at the top before you output anything
    CGI::Buffer::init(
	cache => CHI->new(driver => 'File')
    );
    if(CGI::Buffer::is_cached()) {
	# Nothing has changed - use the version in the cache
	exit;
    }

    # ...

To temporarily prevent the use of server-side caches, for example whilst
debugging before publishing a code change, set the NO_CACHE environment variable
to any non-zero value.
If you get errors about Wide characters in print it means that you've
forgotten to emit pure HTML on non-ASCII characters.
See L<HTML::Entities>.
As a hack work around you could also remove accents and the like by using
L<Text::Unidecode>,
which works well but isn't really what you want.

=head1 SUBROUTINES/METHODS

=cut

# By default, ETags are generated only for protocols that understand them
our $generate_etag;
our $generate_304 = $DEFAULT_GENERATE_304;
our $generate_last_modified = $DEFAULT_GENERATE_LAST_MODIFIED;
our $compress_content = $DEFAULT_COMPRESS_CONTENT;
our $optimise_content = $DEFAULT_OPTIMISE_CONTENT;
our $lint_content = $DEFAULT_LINT_CONTENT;

our $cache;
our $cache_duration;
our $cache_key;
our $info;
our $logger;
our $lingua;
our $status;
our $script_mtime;
our $cobject;
our($x_cache, $buf, $headers, $header, $body, @content_type, $etag,
	$send_body, @o);

# $raw is what the script printed, which is sent if processing it fails.
# $sent is set once output has started.  $script_encoded is set if the script
# gave its own Content-Encoding.  $content_encoding is the encoding that we've
# applied.  $matched_etag is the client's ETag that If-None-Match matched
our($raw, $sent, $script_encoded, $content_encoding, $matched_etag);

BEGIN {
	# use Exporter();

	$CGI::Buffer::buf = IO::String->new();
	$CGI::Buffer::old_buf = select($CGI::Buffer::buf);
}

END {
	if(defined($^V) && ($^V ge 'v5.14.0')) {
		return if ${^GLOBAL_PHASE} eq 'DESTRUCT';	# >= 5.14.0 only
	}

	# Premise 1: anything from here on can fail, e.g. a logger or a cache
	# Premise 2: until this is done, all that the process prints goes into
	#	the buffer, which is never sent
	# Conclusion: this must be the first thing that is done
	select($CGI::Buffer::old_buf);

	# This can run while an eval is unwinding, and $? is the exit status
	local($@, $!, $?);

	# Premise 1: Perl only gives a warning for an exception in an END block
	# Premise 2: the client would be given an empty response
	# Conclusion: catch it, and send the output as the script printed it
	unless(eval { _send_output(); 1 }) {
		_problem(__PACKAGE__ . ": $@");
		unless($sent) {
			$sent = 1;
			if(defined($raw) && length($raw)) {
				print _to_bytes($raw);
			} else {
				# The script relied upon a cache that has now failed
				print "Status: 500 Internal Server Error\r\n\r\n";
			}
		}
	}

	# This will cause everything to get flushed and prevent
	# outputs to the logger.  We need to do that now since
	# if we leave it to Perl to delete later we may get
	# a message that Log4perl::init() hasn't been called
	$logger = undef;
}

# Everything that the script printed has been buffered, process and send it
sub _send_output {
	my $pos = $CGI::Buffer::buf->getpos;
	$CGI::Buffer::buf->setpos(0);
	read($CGI::Buffer::buf, $buf, $pos);

	# Keep this before anything else that can fail, it's what will be sent if
	# something does
	$raw = $buf;

	# Premise 1: an ETag is only useful if the protocol supports If-None-Match
	# Premise 2: an explicit generate_etag argument is the caller's decision
	# Conclusion: default it from the protocol, but only when it isn't given
	if(!defined($generate_etag)) {
		$generate_etag = _is_conditional_protocol() ? 1 : 0;
	}

	($headers, $body) = split /\r?\n\r?\n/, $buf, 2;

	if($logger) {
		if($ENV{'HTTP_IF_NONE_MATCH'}) {
			$logger->debug("HTTP_IF_NONE_MATCH: $ENV{HTTP_IF_NONE_MATCH}");
		}
		if($ENV{'HTTP_IF_MODIFIED_SINCE'}) {
			$logger->debug("HTTP_IF_MODIFIED_SINCE: $ENV{HTTP_IF_MODIFIED_SINCE}");
		}
		$logger->debug("Generate_etag = $generate_etag, ",
			"Generate_304 = $generate_304, ",
			"Generate_last_modified = $generate_last_modified");
	}

	unless($headers || is_cached()) {
		if($logger) {
			$logger->debug('There was no output');
		}
		if(!defined($headers)) {
			require HTTP::Status;
			HTTP::Status->import();

			if(!defined($status)) {
				if($info) {
					$status = $info->status();
				} else {
					$status = 200;
				}
			}
			$sent = 1;
			print "Status: $status ",
				HTTP::Status::status_message($status),
				"\n\n";
		}
		return;
	}
	$send_body = (defined($ENV{'REQUEST_METHOD'}) && ($ENV{'REQUEST_METHOD'} eq 'HEAD')) ? 0 : 1;

	if($headers) {
		_set_content_type($headers);
	}

	if(defined($body) && ($body eq '')) {
		# E.g. if header of Location is given with no body, for
		#	redirection
		$body = undef;
		if($cache) {
			# Don't try to retrieve it below from the cache
			$send_body = 0;
		}
	} elsif(_is_html() && defined($body) && !$script_encoded) {
		if($optimise_content) {
			# require HTML::Clean;
			require HTML::Packer;	# Overkill using HTML::Clean and HTML::Packer...

			if($logger) {
				$logger->trace('Packer');
			}

			# Whitespace is significant in these, in a <textarea>
			# it's the user's data
			my $preformatted = _protect_preformatted();

			# Level 1 is one pass, higher levels repeat until
			# the body stops shrinking
			my $oldlength = length($body);
			_optimise_content();
			if($optimise_content >= 2) {
				while(length($body) < $oldlength) {
					$oldlength = length($body);
					_optimise_content();
				}
			}

			# If we're on http://www.example.com and have a link
			# to http://www.example.com/foo/bar.htm, change the
			# link to /foo/bar.htm - there's no need to include
			# the site name in the link
			my $href = _info()->host_name();
			my $protocol = $info->protocol() || 'http';

			# The host name must be followed by the end of the
			# link, or the start of its path, query or fragment,
			# otherwise www.example.com.evil.org would become local
			$body =~ s/<a\s+?href="\Q$protocol\E:\/\/\Q$href\E"/<a href="\/"/gi;
			$body =~ s/<a\s+?href="\Q$protocol\E:\/\/\Q$href\E(?=[\/?#])/<a href="/gi;

			# TODO use URI->path_segments to change links in
			# /aa/bb/cc/dd.htm which point to /aa/bb/ff.htm to
			# ../ff.htm

			# TODO: <img border=0 src=...>
			$body =~ s/<img\s+?src="\Q$protocol\E:\/\/\Q$href\E"/<img src="\/"/gi;
			$body =~ s/<img\s+?src="\Q$protocol\E:\/\/\Q$href\E(?=[\/?#])/<img src="/gi;

			# Don't use HTML::Clean because of RT402
			# my $h = new HTML::Clean(\$body);
			# # $h->compat();
			# $h->strip();
			# my $ref = $h->data();

			# Don't always do javascript 'best' since it's confused
			# by the common <!-- HIDE technique.
			# See https://github.com/nevesenin/javascript-packer-perl/issues/1#issuecomment-4356790
			my $options = {
				remove_comments => 1,
				remove_newlines => 0,
				do_stylesheet => 'minify'
			};
			if($optimise_content >= 2) {
				$options->{do_javascript} = 'best';
				# [^>] stops the tag running on into the
				# rest of the page
				$body =~ s/(<script[^>]*+>)\s*+<!--/$1/gi;
				$body =~ s/\/\/-->\s*+<\/script>/<\/script>/gi;
				$body =~ s/(<script[^>]*+>)\s++/$1/gi;
			}
			$body = HTML::Packer->init()->minify(\$body, $options);
			if($optimise_content >= 2) {
				# Change document.write("a"); document.write("b")
				# into document.write("a"+"b");
				# Every substitution shortens the body, so this
				# always terminates.
				# Nothing may cross a </script>, otherwise
				# writes in different scripts get merged
				1 while($body =~ s{
					(<script\s+type\s*=\s*"text/javascript"\s*>)		# $1: opening tag, kept as written
					((?:(?!</script>).)*?)					# $2: code before the writes, within this script
					document\.write\(((?:(?!</script>)[^;])*?)\);\s*+	# $3: first argument
					document\.write\(((?:(?!</script>)[^;])*?)\)		# $4: second argument
				}{$1${2}document.write($3+$4)}gisx);
			}
			_restore_preformatted($preformatted);
		}
		if($lint_content) {
			require HTML::Lint;
			HTML::Lint->import;

			if($logger) {
				$logger->trace('Lint');
			}
			my $lint = HTML::Lint->new();
			$lint->parse($body);
			$lint->eof();

			if($lint->errors) {
				$headers = 'Status: 500 Internal Server Error';
				@o = ('Content-type: text/plain');
				$body = '';
				foreach my $error ($lint->errors) {
					my $errtext = $error->where() . ': ' . $error->errtext() . "\n";
					if($logger) {
						$logger->warn($errtext);
					} else {
						warn($errtext);
					}
					$body .= $errtext;
				}
			}
		}
	}

	if(defined($headers) && ($headers =~ /^Status:\s*(\d+)/mi)) {
		$status = $1;
	} elsif($info) {
		$status = $info->status();
	} else {
		$status = 200;
	}

	if($logger) {
		$logger->debug("Initial status = $status");
	}

	# Range, Content-Length, compression and the ETag all work in bytes.
	# A script which printed bytes is left alone: encoding those would
	# encode any UTF-8 in them a second time
	if(defined($body)) {
		$body = _to_bytes($body);
	}

	my $encoding = _should_gzip();
	my $unzipped_body = $body;

	# Generate the eTag before compressing, since the compressed data
	# includes the mtime field which changes thus causing a different
	# Etag to be generated
	if($generate_etag && defined($body) && _is_conditional_protocol()) {
		_generate_etag();

		if($ENV{'HTTP_IF_NONE_MATCH'} && $generate_304 && ($status == 200)) {
			_check_if_none_match();
		}
	}

	if(defined($unzipped_body)) {
		# Conditions are looked at before Range, and If-Modified-Since
		# isn't looked at if If-None-Match was checked and failed.
		# _check_modified_since() checks generate_304 itself
		if((!$cache) && $info && $ENV{'HTTP_IF_MODIFIED_SINCE'} && ($status == 200) &&
		   !($ENV{'HTTP_IF_NONE_MATCH'} && defined($etag))) {
			_check_modified_since({
				since => $ENV{'HTTP_IF_MODIFIED_SINCE'},
				modified => _my_age()
			});
		}

		my $range = $ENV{'Range'} || $ENV{'HTTP_RANGE'};

		# Only a successful GET can be cut up, and only if the client's
		# copy, if it has given one, is still the current one
		if($range && !$cache && ($status == 200) && _is_get() && _if_range_matches() &&
		   defined(my $partial = _apply_range($body, $range))) {
			# Premise 1: Content-Range counts the bytes of what is sent
			# Premise 2: the offsets the client gave are in the page,
			#	not in a compressed copy
			# Conclusion: a part of a page is never compressed
			$encoding = '';
			_set_status($partial->{status});
			push @o, "Content-Range: $partial->{content_range}";
			if($partial->{status} == 416) {
				# Range Not Satisfiable has no body
				$body = undef;
				$unzipped_body = undef;
				$send_body = 0;
			} else {
				$body = $unzipped_body = $partial->{body};
			}
		}
		# A 304 or 412 has no body to compress, and mustn't say that it has
		if($send_body || ($status == 200)) {
			_compress({ encoding => $encoding });
		}
	}

	if($cache) {
		require Storable;

		my $cache_hash;
		my $key = _generate_key();

		# Cache unzipped version
		if(!defined($body)) {
			# is_cached() has already looked, and it mustn't have
			# expired since then.  A HEAD request needs the headers too
			$cobject ||= _cache_lookup($key);
			if(defined($cobject)) {
				$cache_hash = Storable::thaw($cobject->value());
				$headers = $cache_hash->{'headers'};
				_set_content_type($headers) if(defined($headers));
				@o = ("X-CGI-Buffer-$VERSION: Hit", @{_x_cache_headers('HIT', 'HIT')});
			} elsif($send_body) {
				_problem(__PACKAGE__ . ": error retrieving data for key $key");
			}

			if($send_body && ($status == 200) && defined($cache_hash)) {
				$body = _to_bytes($cache_hash->{'body'});
				if(!defined($body)) {
					# Panic
					$headers = 'Status: 500 Internal Server Error';
					@o = ('Content-type: text/plain');
					$body = "Can't retrieve body for key $key, cache_hash contains:\n";
					foreach my $k (keys %{$cache_hash}) {
						$body .= "\t$k\n";
					}
					_try('removing a bad entry', sub { $cache->remove($key) });
					if($logger) {
						$logger->error("Can't retrieve body for key $key");
						$logger->warn($body);
					} else {
						carp "Can't retrieve body for key $key";
						warn($body);
					}
					$send_body = 0;
					_set_status(500);
				}
			}
			if($send_body && ($status == 200) && $generate_etag && ((!defined($headers)) || ($headers !~ /^ETag:/mi))) {
				_generate_etag();
			}
			unless($etag) {
				# Keep the quotes, they're part of the ETag and
				# If-None-Match includes them
				if(defined($headers) && ($headers =~ /^ETag:\s*("[^"]*")/mi)) {
					$etag = $1;
				} elsif($cache_hash) {
					$etag = $cache_hash->{'etag'};
				}
			}
			# Nothing has been output yet, so we can check if it's OK to
			# send 304 if possible.
			# RFC 9110 13.1.3 says not to look at the date if there's
			# an If-None-Match.
			# _check_modified_since() checks generate_304 itself
			if($status == 200) {
				if($ENV{'HTTP_IF_NONE_MATCH'} && defined($etag)) {
					if($generate_304) {
						_check_if_none_match();
					}
				} elsif($ENV{'HTTP_IF_MODIFIED_SINCE'} && $cobject) {
					_check_modified_since({
						since => $ENV{'HTTP_IF_MODIFIED_SINCE'},
						modified => $cobject->created_at()
					});
				}
			}
			# A 304 has no body to compress, and mustn't say that it has
			if(($status == 200) && $send_body) {
				$encoding = _should_gzip();
				_compress({ encoding => $encoding });
			}
			if($cobject && ($status == 200) && $generate_last_modified) {
				if($logger) {
					$logger->debug('Set Last-Modified to ', HTTP::Date::time2str($cobject->created_at()));
				}
				push @o, 'Last-Modified: ' . HTTP::Date::time2str($cobject->created_at());
			}
		} else {
			# Not in the server side cache
			if($status == 200) {
				unless($cache_duration) {
					# It would be great if CHI::set()
					# allowed the time to be 'lru' for least
					# recently used.
					$cache_duration = '10 minutes';
				}
				my $storable = _is_storable($headers, $unzipped_body);
				if($storable) {
					$cache_hash->{'body'} = $unzipped_body;

					# Remember, we're storing the UNzipped
					# version in the cache, so leave out what's
					# about this response's encoding and length.
					# Blank lines would end the headers
					my @stored = grep {
						length && !/^(?:Content-Encoding|Content-Length|Content-Range):/i &&
						!/^Vary:\s*Accept-Encoding\s*$/i
					} ((defined($headers) ? split(/\r?\n/, $headers) : ()), @o);
					if(scalar(@stored)) {
						$cache_hash->{'headers'} = join("\r\n", @stored);
					}
					if($generate_etag) {
						_generate_etag();
						$cache_hash->{'etag'} = $etag;
					}
					if($logger) {
						$logger->debug("Store $key in the cache, age = $cache_duration ", length($cache_hash->{'body'}), ' bytes');
					}
					_try('storing in the cache', sub {
						$cache->set($key, Storable::freeze($cache_hash), $cache_duration);
					});
				}
				if($generate_last_modified) {
					$cobject = $storable ? _cache_lookup($key) : undef;
					if(defined($cobject)) {
						push @o, 'Last-Modified: ' . HTTP::Date::time2str($cobject->created_at());
					} else {
						push @o, 'Last-Modified: ' . HTTP::Date::time2str(time);
					}
				}
			}
			push @o, @{_x_cache_headers(defined($x_cache) ? $x_cache : 'MISS', 'MISS')}, "X-CGI-Buffer-$VERSION: Miss";
		}
		# We don't need it any more, so give Perl a chance to
		# tidy it up seeing as we're in the destructor
		$cache = undef;
	} else {
		push @o, @{_x_cache_headers('MISS', 'MISS')};
		if($info && $generate_last_modified) {
			if(my $age = _my_age()) {
				push @o, 'Last-Modified: ' . HTTP::Date::time2str($age);
			}
		}
	}

	_add_vary($headers);

	if($generate_etag && defined($etag) && ((!defined($headers)) || ($headers !~ /^ETag:/mi))) {
		# The compressed and the uncompressed versions aren't the same
		# bytes, so can't have the same strong ETag.
		# _check_if_none_match() removes the suffix again, and a 304 is
		# about the copy that the client has so gives back its ETag
		my $e = defined($matched_etag) ? $matched_etag : $etag;
		if($content_encoding && !defined($matched_etag)) {
			$e =~ s/"$/-$content_encoding"/;
		}
		push @o, "ETag: $e";
		if($logger) {
			$logger->debug("Set ETag to $e");
		}
	}

	my $body_length = 0;
	if(defined($body)) {
		$body = _to_bytes($body);
		$body_length = length($body);
	}

	if(defined($headers) && length($headers)) {
		# Put the original headers first, then those generated within
		# CGI::Buffer.  The script is free to end its lines with \n
		unshift @o, grep { length } split(/\r?\n/, $headers);

		# The body may well have changed since the script worked out its
		# length
		if(defined($body)) {
			@o = grep { !/^Content-Length:/i } @o;
		}
		if($body_length && $send_body) {
			push @o, "Content-Length: $body_length";
		}
		_set_status_header();
	} else {
		push @o, "X-CGI-Buffer-$VERSION: No headers";
	}

	if($body_length && $send_body) {
		push @o, ('', $body);
	}

	$sent = 1;
	if(scalar @o) {
		print join("\r\n", @o);
	}

	if((!$send_body) || !defined($body)) {
		print "\r\n\r\n";
	}
}

sub _check_modified_since {
	if($logger) {
		$logger->trace('In _check_modified_since');
	}

	if(!$generate_304) {
		return;
	}
	# RFC 9110 13.1.3: If-Modified-Since is ignored for other methods
	return unless(_is_safe_method());

	my $params = shift;

	if(!defined($$params{since})) {
		return;
	}
	my $s = HTTP::Date::str2time($$params{since});
	if(!defined($s)) {
		# IF_MODIFIED_SINCE isn't a valid data
		return;
	}

	my $age = _my_age();
	if(!defined($age)) {
		return;
	}
	if($age > $s) {
		if($logger) {
			$logger->debug('_check_modified_since: script has been modified');
		}
		# Script has been updated so it may produce different output
		return;
	}

	if($logger) {
		$logger->debug("_check_modified_since: Compare $$params{modified} with $s");
	}
	if($$params{modified} <= $s) {
		push @o, 'Status: 304 Not Modified';
		_set_status(304);
		$send_body = 0;
		if($logger) {
			$logger->debug('Set status to 304');
		}
	}
}

# Reduce output, e.g. remove superfluous white-space.
sub _optimise_content {
	# FIXME: regex bad, HTML parser good
	# Regexp::List - wow!
	# Remove whitespace around newlines.  Possessive quantifiers and only
	# starting at the beginning of a run of whitespace keep it linear.
	# A "+" at the start of a line is JavaScript, so is left alone
	$body =~ s{
		(?<![^\S\n])	# start only at the beginning of a whitespace run
		[^\S\n]*+	# trailing spaces, tabs and \r before the newline
		\n
		\s*+		# blank lines and indentation after it
	}{\n}gx;
	$body =~ s/\<\/div\>\s+\<div/\<\/div\>\<div/gis;
	# In these, (?<!\s) and possessive quantifiers stop each alternation
	# being retried at every position inside a long run of whitespace
	$body =~ s/(?:<div>\s++|(?<!\s)\s++<div>)/<div>/gi;
	$body =~ s/\s+<\/div\>/\<\/div\>/gis;	# Remove spaces before </div>
	$body =~ s/(?:(?<!\s)\s++<p>|<p>\s++)/<p>/i;	# TODO <p class=
	$body =~ s/(?:(?<!\s)\s++<\/p>|<\/p>\s++)/<\/p>/gi;
	$body =~ s/<html>\s+<head>/<html><head>/is;
	$body =~ s/(?<!\s)\s*+<\/head>\s++<body>\s*+/<\/head><body>/i;
	$body =~ s/<html>\s+<body>/<html><body>/is;
	$body =~ s/<body>\s+/<body>/is;
	$body =~ s/\s+\<\/html/\<\/html/is;
	$body =~ s/\s+\<\/body/\<\/body/is;
	# Spaces between tags can be visible, e.g. "Hello <b>world</b>", so
	# they're only removed around the block elements below
	$body =~ s/\<p\>\s/\<p\>/gi;
	$body =~ s/\<\/p\>\s\<p\>/\<\/p\>\<p\>/gi;
	$body =~ s/\<\/tr\>\s\<tr\>/\<\/tr\>\<tr\>/gi;
	$body =~ s/\<\/td\>\s\<\/tr\>/\<\/td\>\<\/tr\>/gi;
	$body =~ s/\<\/td\>\s*\<td\>/\<\/td\>\<td\>/gis;
	$body =~ s/\<\/tr\>\s\<\/table\>/\<\/tr\>\<\/table\>/gi;
	$body =~ s/\<br\s?\/?\>\s?\<p\>/\<p\>/gi;
	$body =~ s/\<br\>\s+/\<br\>/gi;
	$body =~ s/\s+\<br/\<br/gi;
	$body =~ s/\<br\s?\/\>\s/\<br \/\>/gi;
	$body =~ s/[ \t]+/ /gs;	# Remove duplicate space, don't use \s+ it breaks JavaScript
	$body =~ s/\s\<p\>/\<p\>/gi;
	$body =~ s/\s\<script/\<script/gi;
	$body =~ s/(<script>\s|\s<script>)/<script>/gis;
	$body =~ s/(<\/script>\s|\s<\/script>)/<\/script>/gis;
	$body =~ s/\<td\>\s/\<td\>/gi;
	# The link can't leave its quotes, so these can't span tags or
	# backtrack across the rest of the page
	$body =~ s{
		(?<!\s)\s++		# a whole run of whitespace, starting at its first character
		<a\shref="([^"]*+)">	# $1: the link
		\s?
	}{ <a href="$1">}gix;
	$body =~ s{
		\s?
		<a\shref=\s"([^"]*+)">	# $1: the link
	}{ <a href="$1">}gix;
	$body =~ s/\s+<\/a\>\s+/<\/a> /gis;
	$body =~ s/(?:\s?<hr>\s++|(?<!\s)\s++<hr>\s?)/<hr>/gi;
	$body =~ s/<\/li>\s+<li>/<\/li><li>/gis;
	$body =~ s/<\/li>\s+<\/ul>/<\/li><\/ul>/gis;
	$body =~ s/<ul>\s+<li>/<ul><li>/gis;
	$body =~ s/\s+<\/li>/<\/li>/gis;
	$body =~ s/\<\/option\>\s+\<option/\<\/option\>\<option/gis;
	# A title can't contain a tag.  [^<] and the possessive quantifiers stop
	# each unterminated <title> from being searched to the end of the page
	$body =~ s{<title>\s*+([^<]*+)</title>}{
		my $title = $1;
		$title =~ s/(?<!\s)\s++\z//;
		"<title>$title</title>"
	}eix;
	$body =~ s/<\/center>\s+<center>/ /gis;
}

# Create a key for the cache
sub _generate_key {
	if($cache_key) {
		return $cache_key;
	}
	unless(defined($info)) {
		$info = CGI::Info->new({ cache => $cache });
	}

	my $key = __PACKAGE__ . '::' . $info->browser_type() . '::' . $info->domain_name() . '::' . $info->script_name() . '::' . $info->as_string();
	if(defined($ENV{'PATH_INFO'}) && length($ENV{'PATH_INFO'})) {
		# /cgi-bin/foo.cgi/bar and /cgi-bin/foo.cgi/baz are different pages
		$key .= '::PATH_INFO=' . $ENV{'PATH_INFO'};
	}
	if($lingua) {
		$key .= '::' . $lingua->language();
	}
	# Different states of the client are stored in different caches
	foreach my $cookie(_client_cookies()) {
		$key .= "::$cookie";
	}

	# The key is needed before the script has given its headers, so a Vary
	# header can't be part of it.  _is_storable() doesn't store those pages
	$key =~ s/\//::/g;
	$key =~ s/(?:::){2,}/::/g;
	$key =~ s/::$//;
	if(defined($logger)) {
		$logger->trace("Returning $key");
	}
	$cache_key = $key;
	return $key;
}

=head2 init

Set various options and override default values.

    # Put this toward the top of your program before you do anything
    # By default, generate_tag, generate_304 and compress_content are ON,
    # optimise_content and lint_content are OFF.  Set optimise_content to 2 to
    # do aggressive JavaScript optimisations which may fail.
    use CGI::Buffer;
    CGI::Buffer::init(
	generate_etag => 1,	# make good use of client's cache
	generate_last_modified => 1,	# more use of client's cache
	compress_content => 1,	# if gzip the output
	optimise_content => 0,	# optimise your program's HTML, CSS and JavaScript
	cache => CHI->new(driver => 'File'),	# cache requests
	cache_key => 'string',	# key for the cache
	cache_duration => '10 minutes',	# how long to store responses in the cache
	logger => $logger,
	lint_content => 0,	# Pass through HTML::Lint
	generate_304 => 1,	# Generate 304: Not modified
	lingua => CGI::Lingua->new(),
    );

If no cache_key is given, one will be generated which may not be unique.
The cache_key should be a unique value dependent upon the values set by the
browser.

The cache object will be an object that understands get_object(),
set(), remove() and created_at() messages, such as an L<CHI> object. It is
used as a server-side cache to reduce the need to rerun database accesses.

Items stay in the server-side cache by default for 10 minutes.
This can be overridden by the max-age directive of the Cache-Control HTTP header
in the request, if it's a number no larger than 600 seconds, and
the default can be changed by the cache_duration argument to init().

Responses aren't stored in the server-side cache if their headers include
Set-Cookie,
a Cache-Control of no-store, no-cache or private,
or a Vary on anything other than Accept-Encoding
(or Accept-Language when lingua is given),
since they would be given to clients that they weren't meant for.
Neither are HTML pages with no </html>,
which suggests that the script died.
A page that includes the value of the client's C<csrf_token> cookie is never
stored.
The C<csrf_token> and Google Analytics cookies aren't part of the generated
cache key, other cookies and PATH_INFO are.

Logger will be an object that understands debug() such as an L<Log::Log4perl>
object.

To generate a last_modified header, you must give a cache object.

Init allows a reference of the options to be passed. So both of these work:
    use CGI::Buffer;
    #...
    CGI::Buffer::init(generate_etag => 1);
    CGI::Buffer::init({ generate_etag => 1, info => CGI::Info->new() });

Generally speaking, passing by reference is better since it copies less on to
the stack.

Alternatively you can give the options when loading the package:
    use CGI::Buffer { optimise_content => 1 };

=cut

sub init {
	my %params = (ref($_[0]) eq 'HASH') ? %{$_[0]} : @_;

	# Safe options - can be called at any time
	if(defined($params{generate_etag})) {
		$generate_etag = $params{generate_etag};
	}
	if(defined($params{generate_last_modified})) {
		$generate_last_modified = $params{generate_last_modified};
	}
	if(defined($params{compress_content})) {
		$compress_content = $params{compress_content};
	}
	if(defined($params{optimise_content})) {
		$optimise_content = $params{optimise_content};
	}
	if(defined($params{lint_content})) {
		$lint_content = $params{lint_content};
	}
	if(defined($params{logger})) {
		$logger = $params{logger};
		_check_logger();
	}
	if(defined($params{lingua})) {
		$lingua = $params{lingua};
	}
	if(defined($params{generate_304})) {
		$generate_304 = $params{generate_304};
	}
	if(defined($params{info}) && (!defined($info))) {
		$info = $params{info};
	}

	# Unsafe options - must be called before output has been started
	my $pos = $CGI::Buffer::buf->getpos;
	if($pos > 0) {
		if(defined($logger)) {
			my @call_details = caller(0);
			$logger->warn("Too late to call init, $pos characters have been printed, caller line $call_details[2] of $call_details[1]");
		} else {
			# Must do Carp::carp instead of carp for Test::Carp
			Carp::carp "Too late to call init, $pos characters have been printed";
		}
	}
	if(defined($params{cache}) && can_cache()) {
		# There is an argument not to do this since one client will
		# affect others, so it's limited
		my $max_age = _client_max_age();
		if(defined($max_age) && ($max_age <= $MAX_CLIENT_CACHE_SECONDS)) {
			$cache_duration = "$max_age seconds";
			if(defined($logger)) {
				$logger->debug("cache_duration = $cache_duration");
			}
		}
		$cache_duration ||= $params{'cache_duration'};

		if($params{'cache_age'}) {
			# Legacy
			$cache_duration ||= $params{'cache_age'};
		}

		if((!defined($params{cache})) && defined($cache)) {
			if(defined($logger)) {
				if($cache_key) {
					$logger->debug("disabling cache $cache_key");
				} else {
					$logger->debug('disabling cache');
				}
			}
			$cache = undef;
		} else {
			$cache = $params{cache};
		}
		if(defined($params{cache_key})) {
			$cache_key = $params{cache_key};
		}
	}
}

sub import {
	# my $class = shift;
	shift;

	return unless @_;

	init(@_);
}

=head2 set_options

Synonym for init, kept for historical reasons.

=cut

sub set_options {
	my %params = (ref($_[0]) eq 'HASH') ? %{$_[0]} : @_;

	init(\%params);
}

=head2 can_cache

Returns true if the server is allowed to store the results locally.

The cache isn't used if the NO_CACHE or NO_STORE environment variables are set,
if the request method isn't GET or HEAD,
if the client has logged in (the Authorization header or REMOTE_USER is set),
or if the client's Cache-Control header includes any of no-store, no-cache,
private or max-age=0.
The answer is decided on the first call, and doesn't change for the rest of the
request.

=cut

sub can_cache {
	if(defined($x_cache)) {
		return ($x_cache eq 'HIT');
	}
	if(defined($logger) && defined($ENV{'HTTP_CACHE_CONTROL'})) {
		$logger->debug("cache_control = $ENV{HTTP_CACHE_CONTROL}");
	}

	# A request may give several directives, e.g. "no-cache, max-age=0",
	# and any one of them forbids the cache
	my $control = _cache_control();
	my $max_age = _client_max_age();
	my $forbidden = defined($ENV{'NO_CACHE'}) || defined($ENV{'NO_STORE'}) ||
		(!_is_safe_method()) || _is_logged_in() ||
		(grep { $NO_CACHE_DIRECTIVES{$_} } keys %{$control}) ||
		(defined($max_age) && ($max_age == 0));

	$x_cache = $forbidden ? 'MISS' : 'HIT';
	return $forbidden ? 0 : 1;
}

=head2 is_cached

Returns true if the output is cached. If it is then it means that all of the
expensive routines in the CGI script can be by-passed because we already have
the result stored in the cache.

    # Put this toward the top of your program before you do anything

    # Example key generation - use whatever you want as something
    # unique for this call, so that subsequent calls with the same
    # values match something in the cache
    use CGI::Info;
    use CGI::Lingua;
    use CGI::Buffer;

    my $i = CGI::Info->new();
    my $l = CGI::Lingua->new(supported => ['en']);

    # To use server side caching you must give the cache argument, however
    # the cache_key argument is optional - if you don't give one then one will
    # be generated for you
    if(CGI::Buffer::can_cache()) {
        CGI::Buffer::init(
	    cache => CHI->new(driver => 'File'),
	    cache_key => $i->domain_name() . '/' . $i->script_name() . '/' . $i->as_string() . '/' . $l->language()
        );
        if(CGI::Buffer::is_cached()) {
	    # Output will be retrieved from the cache and sent automatically
	    exit;
        }
    }
    # Not in the cache, so now do our expensive computing to generate the
    # results
    print "Content-type: text/html\n";
    # ...

=cut

sub is_cached {
	unless($cache) {
		if($logger) {
			$logger->debug("is_cached: cache hasn't been enabled");
		}
		return 0;
	}

	my $key = _generate_key();

	if($logger) {
		$logger->debug("is_cached: looking for key = $key");
	}
	$cobject = _cache_lookup($key);
	unless($cobject) {
		if($logger) {
			$logger->debug('not found in cache');
		}
		return 0;
	}
	unless($cobject->value($key)) {
		if($logger) {
			$logger->warn('is_cached: object is in the cache but not the data');
		}
		$cobject = undef;
		return 0;
	}

	# If the script has changed, don't use the cache since we may produce
	# different output
	my $age = _my_age();
	unless(defined($age)) {
		if($logger) {
			$logger->debug("Can't determine script's age");
		}
		# Can't determine the age. Play it safe an assume we're not
		# cached
		$cobject = undef;
		return 0;
	}
	if($age > $cobject->created_at()) {
		# Script has been updated so it may produce different output
		if($logger) {
			$logger->debug('Script has been updated');
		}
		$cobject = undef;
		# Nothing will be in date and all new searches would miss
		# anyway, so may as well clear it all
		# FIXME: RT104471
		# $cache->clear();
		return 0;
	}
	if($logger) {
		$logger->debug('Script is in the cache');
	}
	return 1;
}

# Determine the last modification time of the script and cache it for subsequent calls
sub _my_age {
	return $script_mtime if(defined($script_mtime));

	# croak() never returns, so nothing is needed after it
	my $path = _info()->script_path();
	croak 'Failed to retrieve script path' unless(defined($path));

	my @statb = stat($path);
	$script_mtime = $statb[9];	# Set script_mtime to the modification time of the script
	return $script_mtime;
}

# Return the content encoding to use, or '' for none.
# Premise 1: _compress() fails the request with a 406 if it can't load the
#	module for the encoding
# Premise 2: the client is happy with any of the encodings it lists
# Conclusion: choose the first listed encoding that can be loaded, then the 406
#	can't happen
sub _should_gzip
{
	return '' unless($compress_content);
	my $accept = $ENV{'HTTP_ACCEPT_ENCODING'} || $ENV{'HTTP_TE'};
	return '' unless($accept);
	return '' if(defined($content_type[0]) && (lc($content_type[0]) ne 'text'));
	return '' if($script_encoded);	# It would be compressed twice

	foreach my $method(split(/\s*,\s*/, lc($accept))) {
		# e.g. "gzip;q=0.8", where q=0 means "not acceptable"
		my ($name, @params) = split(/\s*;\s*/, $method);
		next unless(defined($name));
		next if(grep { /^q=0(?:\.0*)?$/ } @params);
		return $name if($ENCODING_MODULE{$name} && _can_load($ENCODING_MODULE{$name}));
	}

	return '';
}

# Can the given module be loaded?  The answer is remembered
{
	my %loadable;

	sub _can_load
	{
		my $module = shift;

		if(!exists($loadable{$module})) {
			$loadable{$module} = eval "require $module; 1" ? 1 : 0;
		}
		return $loadable{$module};
	}
}

sub _set_content_type
{
	my $headers = shift;

	foreach my $header (split(/\r?\n/, $headers)) {
		my ($header_name, $header_value) = split /\:\s*/, $header, 2;
		next unless(defined($header_name) && defined($header_value));
		if(lc($header_name) eq 'content-type') {
			@content_type = split /\//, $header_value, 2;
		} elsif((lc($header_name) eq 'content-encoding') && (lc($header_value) !~ /^\s*identity\s*$/)) {
			$script_encoded = 1;
		}
	}
}

# Compress the body with the given encoding, from _should_gzip()
sub _compress {
	my %params = ref $_[0] eq 'HASH' ? %{ $_[0] } : @_;

	my $encoding = $params{encoding};

	# This can be called again, by which time the body is no longer compressed
	$content_encoding = undef;
	@o = grep { !/^Content-Encoding:/ } @o;

	return unless(defined($body) && defined($encoding) && length($encoding));
	return if(length($body) < $MIN_GZIP_LEN);

	# Premise: _should_gzip() only returns encodings whose module loads
	# Conclusion: if one can't be loaded here, the request can't be met
	my $module = $ENCODING_MODULE{$encoding};
	if((!defined($module)) || !_can_load($module)) {
		_set_status(406);
		return;
	}

	# Avoid 'Wide character in memGzip'
	my $bytes = _to_bytes($body);
	my $compressed;
	if($module eq 'Compress::Zlib') {
		$compressed = Compress::Zlib::memGzip(\$bytes);
	} elsif($module eq 'Compress::Zstd') {
		# Facebook
		$compressed = Compress::Zstd::compress(\$bytes);
	} else {
		$compressed = IO::Compress::Brotli::bro($bytes);
	}

	# Don't send it compressed if that makes it larger
	return unless(defined($compressed) && (length($compressed) < length($bytes)));

	$body = $compressed;
	$encoding = 'gzip' if($encoding eq 'x-gzip');
	$content_encoding = $encoding;
	foreach my $header("Content-Encoding: $encoding", 'Vary: Accept-Encoding') {
		push @o, $header unless(grep { $_ eq $header } @o);
	}
}

sub _generate_etag {
	return if(defined($etag));
	return unless(defined($body));

	# bytes to avoid "Wide character in subroutine entry"
	$etag = '"' . Digest::MD5->new->add(_to_bytes($body))->hexdigest() . '"';
	if($logger) {
		$logger->debug("Etag = $etag");
	}
}

sub _check_if_none_match {
	if($ENV{'HTTP_IF_NONE_MATCH'} && defined($etag)) {
		if($logger) {
			$logger->debug("Compare $ENV{HTTP_IF_NONE_MATCH} with $etag");
		}
		# The header is "*" or a list of entity tags, any of which may be
		# weak.  If-None-Match uses the weak comparison (RFC 9110 8.8.3.2),
		# under which the compressed version of a page matches
		my $matched = 0;
		foreach my $tag(split(/\s*,\s*/, $ENV{'HTTP_IF_NONE_MATCH'})) {
			(my $client_etag = $tag) =~ s/^W\///;
			(my $e = $client_etag) =~ s/$ENCODED_ETAG_SUFFIX/"/;
			if($e eq $etag) {
				$matched_etag = $client_etag;
				$matched = 1;
				last;
			}
			$matched = 1 if($e eq '*');
		}
		if($matched) {
			# RFC 9110 13.1.2: 304 is only for GET and HEAD
			my $s = _is_safe_method() ? 304 : 412;
			require HTTP::Status;
			push @o, "Status: $s " . HTTP::Status::status_message($s);
			$send_body = 0;
			_set_status($s);
			if($logger) {
				$logger->debug("Set status to $s");
			}
			return 1;
		}
	}
	if($cache && $logger && $logger->can('is_debug') && $logger->is_debug() && _can_load('Text::Diff')) {
		_try('comparing with the cache', sub {
			my $cached_copy = $cache->get(_generate_key());

			if($cached_copy && $body) {
				require Storable;

				$cached_copy = Storable::thaw($cached_copy)->{body};
				$logger->debug('diffs: ', Text::Diff::diff(\$body, \$cached_copy));
			} else {
				$logger->debug('Nothing to compare');
			}
		});
	}
	return 0;
}

# Run some code which isn't essential to sending the page, e.g. something using
# the cache.  If it fails, give a warning and return undef
sub _try {
	my ($what, $code) = @_;

	my $rc;
	return $rc if(eval { $rc = $code->(); 1 });
	_problem(__PACKAGE__ . ": $what failed: $@");
	return;
}

# Report something which has gone wrong.  This can be called from anywhere, so
# the logger itself may be the thing that's failing
sub _problem {
	my $message = shift;

	if($logger) {
		return if(eval { $logger->warn($message); 1 });
	}
	# Must be Carp::carp instead of carp for Test::Carp
	Carp::carp($message);
}

# Check that the logger can do what will be asked of it, otherwise forget it.
# AUTOLOAD is taken on trust
sub _check_logger {
	foreach my $method(@LOGGER_METHODS) {
		next if(Scalar::Util::blessed($logger) && ($logger->can($method) || $logger->can('AUTOLOAD')));
		$logger = undef;
		_problem(__PACKAGE__ . ": The logger doesn't understand $method()");
		return;
	}
}

# Look for an entry in the cache that can still be used.  A failing cache is the
# same as an empty one.
# CHI's get_object() returns an object even if it has expired
sub _cache_lookup {
	my $key = shift;

	my $object = _try('reading the cache', sub { return $cache->get_object($key) });
	return unless(defined($object));
	if($object->can('is_expired') && $object->is_expired()) {
		if($logger) {
			$logger->debug("$key has expired");
		}
		return;
	}
	return $object;
}

# A string as bytes: a string of characters is encoded, bytes are left alone
sub _to_bytes {
	my $string = shift;

	utf8::encode($string) if(defined($string) && utf8::is_utf8($string));
	return $string;
}

# Is the output an HTML page?
sub _is_html {
	return 0 unless(defined($content_type[0]) && defined($content_type[1]));
	return ((lc($content_type[0]) eq 'text') && (lc($content_type[1]) =~ /^html/)) ? 1 : 0;
}

# Stop the regular expressions from changing the contents of <pre> and <textarea>
# by swapping them for a marker.  Returns what's needed to put them back.
# The end of a tag is only looked for once if it isn't there, so that hostile
# input can't make this quadratic
sub _protect_preformatted {
	my $marker = 'CGIBUFFERPRESERVED' . int(rand(1_000_000_000)) . 'N';
	my (@saved, %no_end);
	my $out = '';
	my $last = 0;

	while($body =~ /<(pre|textarea)\b/gi) {
		my $tag = lc($1);
		my $start = $-[0];
		my $after = pos($body);

		next if($no_end{$tag});
		unless($body =~ /<\/$tag\s*+>/gi) {
			$no_end{$tag} = 1;
			pos($body) = $after;
			next;
		}
		my $end = $+[0];
		push @saved, substr($body, $start, $end - $start);
		$out .= substr($body, $last, $start - $last) . $marker . $#saved . 'X';
		$last = $end;
		pos($body) = $end;
	}
	$body = $out . substr($body, $last);
	return { marker => $marker, saved => \@saved };
}

# Put back what _protect_preformatted() took out
sub _restore_preformatted {
	my $preformatted = shift;

	my $saved = $preformatted->{'saved'};
	$body =~ s/\Q$preformatted->{marker}\E(\d+)X/$saved->[$1]/g if(scalar(@{$saved}));
}

# Tell caches that what's sent depends on what the client accepts.  This is also
# needed when the output isn't compressed, or that's what a cache would then give
# to clients that can take it compressed
sub _add_vary {
	my $headers = shift;

	return unless(defined($headers) && length($headers));
	return unless($compress_content && defined($body) && !$script_encoded);
	return if(defined($content_type[0]) && (lc($content_type[0]) ne 'text'));
	return if($headers =~ /^Vary:.*\baccept-encoding\b/mi);
	return if(grep { /^Vary:.*\baccept-encoding\b/i } @o);
	push @o, 'Vary: Accept-Encoding';
}

# Send one Status header, that of the status we've ended up with, keeping the
# script's one if it's the same since it may have its own wording
sub _set_status_header {
	my $found = 0;
	@o = grep {
		my $keep = 1;
		if(/^Status:\s*(\d+)/i) {
			$keep = (!$found) && ($1 == $status);
			$found ||= $keep;
		}
		$keep
	} @o;

	unless($found) {
		require HTTP::Status;
		HTTP::Status->import();

		push @o, "Status: $status " . HTTP::Status::status_message($status);
		_set_status($status);
	}
}

# If-Range asks for a part only if the client's copy is the current one
# (RFC 9110 14.5), which needs an exact match of a strong validator
sub _if_range_matches {
	my $if_range = $ENV{'HTTP_IF_RANGE'};
	return 1 unless(defined($if_range) && length($if_range));

	if($if_range =~ /^(?:W\/)?"/) {
		_generate_etag();
		return (defined($etag) && ($if_range eq $etag)) ? 1 : 0;
	}
	my $since = HTTP::Date::str2time($if_range);
	return 0 unless(defined($since) && $info);
	my $age = _my_age();
	return (defined($age) && ($age == $since)) ? 1 : 0;
}

# The CGI::Info object, which is created if it wasn't given
sub _info {
	if(!defined($info)) {
		$info = CGI::Info->new($cache ? { cache => $cache } : ())
			or croak(__PACKAGE__, ': Failed to create CGI::Info object');
	}
	return $info;
}

# Set the HTTP status, and tell CGI::Info if we have one
sub _set_status {
	$status = shift;
	if($info) {
		$info->status($status);
	}
}

# Does the protocol support conditional requests (ETag etc.)?
sub _is_conditional_protocol {
	return defined($ENV{'SERVER_PROTOCOL'}) && ($ENV{'SERVER_PROTOCOL'} =~ $CONDITIONAL_PROTOCOL);
}

sub _is_get {
	return (!defined($ENV{'REQUEST_METHOD'})) || ($ENV{'REQUEST_METHOD'} eq 'GET');
}

# The X-Cache and X-Cache-Lookup headers, as an arrayref
sub _x_cache_headers {
	my ($c, $lookup) = @_;

	my $from = $info ? ' from ' . $info->host_name() : '';
	return [ "X-Cache: $c$from", "X-Cache-Lookup: $lookup$from" ];
}

# Work out the response to a Range header, as a hashref of the new status,
# body and Content-Range header, or undef if the range isn't one that we
# support, in which case the header is ignored and the whole body is sent.
# Only a single range of bytes is supported.
#	206: the part of the body asked for
#	416: a valid range which is outside of the body, so has no body
sub _apply_range {
	my ($b, $range) = @_;

	return unless($range =~ /^bytes=(\d*)-(\d*)$/);
	my ($first, $last) = ($1, $2);
	my $length = length($b);

	# "bytes=-" says nothing
	return if(($first eq '') && ($last eq ''));

	# A backwards range is invalid, so is ignored (RFC 7233 2.1)
	return if(($first ne '') && ($last ne '') && ($first > $last));

	if($first eq '') {
		# "bytes=-n" is the last n bytes, all of it if there are
		# fewer than n.  The last 0 bytes can't be satisfied
		$first = ($last >= $length) ? 0 : $length - $last;
		$last = $length - 1;
	} elsif(($last eq '') || ($last >= $length)) {
		# A range past the end stops at the end
		$last = $length - 1;
	}

	# A range starting at or after the end can't be satisfied
	if(($first >= $length) || ($first > $last)) {
		return { status => 416, content_range => "bytes */$length" };
	}

	return {
		status => 206,
		body => substr($b, $first, $last - $first + 1),
		content_range => "bytes $first-$last/$length",
	};
}

# The values of a header in a block of headers
sub _header_values {
	my ($headers, $name) = @_;

	return () unless(defined($headers));
	return map { /^[^:]+:\s*(.*?)\s*$/ ? $1 : () } grep { /^\Q$name\E:/i } split(/\r?\n/, $headers);
}

# May this response be kept and given to other clients?
sub _is_storable {
	my ($headers, $body) = @_;

	# It would log the next client in as this one
	return 0 if(_header_values($headers, 'Set-Cookie') || _header_values($headers, 'Set-Cookie2'));

	# It would give this client's form token to the next one
	return 0 if(_has_form_token($body));

	foreach my $control(_header_values($headers, 'Cache-Control')) {
		foreach my $directive(split(/\s*,\s*/, lc($control))) {
			(my $name = $directive) =~ s/\s*=.*$//;
			return 0 if($NO_CACHE_DIRECTIVES{$name});
		}
	}

	# Accept-Encoding is dealt with here, and lingua is part of the key.
	# Anything else isn't part of the key, so the page would be given to
	# clients that it wasn't meant for
	foreach my $vary(_header_values($headers, 'Vary')) {
		foreach my $name(split(/\s*,\s*/, lc($vary))) {
			next if($name eq 'accept-encoding');
			next if(($name eq 'accept-language') && $lingua);
			return 0;
		}
	}

	# An HTML page with no </html> suggests that the script died part way
	# through, so don't give the partial page to other clients
	if(defined($content_type[0]) && defined($content_type[1]) &&
	   (lc($content_type[0]) eq 'text') && (lc($content_type[1]) =~ /^html/) &&
	   defined($body) && ($body =~ /<html\b/i) && ($body !~ /<\/html\s*+>/i)) {
		if($logger) {
			$logger->debug('Not storing an HTML page with no </html>');
		}
		return 0;
	}
	return 1;
}

sub _is_safe_method {
	return (!defined($ENV{'REQUEST_METHOD'})) || $SAFE_METHODS{$ENV{'REQUEST_METHOD'}};
}

sub _is_logged_in {
	return $ENV{'HTTP_AUTHORIZATION'} || $ENV{'REMOTE_USER'};
}

# The client's cookies, except for Google Analytics ones and the token that
# protects forms, which are different for each client but don't change the output.
# A page with a form is sent that token in a Set-Cookie header, so _is_storable()
# doesn't store it
sub _client_cookies {
	return () unless($ENV{'HTTP_COOKIE'});
	return grep { !/^(?:__utm[abcz]|\Q$FORM_TOKEN_COOKIE\E=)/ } split(/;\s*/, $ENV{'HTTP_COOKIE'});
}

# Does this page include the client's own form token?  _client_cookies() ignores
# the cookie that holds it, on the understanding that it doesn't change the output.
# A script that puts its value into the page has made the page per client
sub _has_form_token {
	my $body = shift;

	return 0 unless($ENV{'HTTP_COOKIE'} && defined($body));

	foreach my $cookie(split(/;\s*/, $ENV{'HTTP_COOKIE'})) {
		next unless($cookie =~ /^\Q$FORM_TOKEN_COOKIE\E=(.+)$/);
		my $token = $1;
		return 1 if(index($body, $token) >= 0);
		# The cookie may be encoded, what's printed may not be
		if($token =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/ge) {
			return 1 if(index($body, $token) >= 0);
		}
	}
	return 0;
}

# The directives in the request's Cache-Control header, as a hashref of
# lower case name to value (undef when there is no value)
sub _cache_control {
	my %directives;

	if(defined(my $control = $ENV{'HTTP_CACHE_CONTROL'})) {
		foreach my $directive(split(/\s*,\s*/, lc($control))) {
			my ($name, $value) = split(/\s*=\s*/, $directive, 2);
			next unless(defined($name) && length($name));
			$value =~ s/^"(.*)"$/$1/ if(defined($value));
			$directives{$name} = $value;
		}
	}
	return \%directives;
}

# The max-age directive in the request, or undef if there isn't a valid one.
# This comes from the client, so it mustn't be trusted to be a number
sub _client_max_age {
	my $max_age = _cache_control()->{'max-age'};

	return (defined($max_age) && ($max_age =~ /^\d+$/)) ? $max_age : undef;
}

=head1 AUTHOR

Nigel Horne, C<< <njh at bandsman.co.uk> >>

=head1 BUGS

CGI::Buffer should be safe even in scripts which produce lots of different
output, e.g. e-commerce situations.
On such pages, however, I strongly urge to setting generate_304 to 0 and
sending the HTTP header "Cache-Control: no-cache".

When using L<Template>, ensure that you don't use it to output to STDOUT,
instead you will need to capture into a variable and print that.
For example:

    my $output;
    $template->process($input, $vars, \$output) || ($output = $template->error());
    print $output;

Can produce buggy JavaScript if you use the <!-- HIDING technique.
This is a bug in L<JavaScript::Packer>, not CGI::Buffer.
See https://github.com/nevesenin/javascript-packer-perl/issues/1#issuecomment-4356790

Mod_deflate can confuse this when compressing output.
Ensure that deflation is off for .pl files:

    SetEnvIfNoCase Request_URI \.(?:gif|jpe?g|png|pl)$ no-gzip dont-vary

If you request compressed output then uncompressed output (or vice
versa) on input that produces the same output, the status will be 304.
The letter of the spec says that's wrong, so I'm noting it here, but
in practice you should not see this happen or have any difficulties
because of it.

CGI::Buffer is not compatible with FastCGI.

I advise adding CGI::Buffer as the last use statement so that it is
cleared up first.  In particular it should be loaded after
L<Log::Log4perl>, if you're using that, so that any messages it
produces are printed after the HTTP headers have been sent by
CGI::Buffer;

CGI::Buffer is not compatible with FCGI, use L<FCGI::Buffer> instead.

Please report any bugs or feature requests to C<bug-cgi-buffer at rt.cpan.org>,
or through the web interface at L<http://rt.cpan.org/NoAuth/ReportBug.html?Queue=CGI-Buffer>.
I will be notified, and then you'll automatically be notified of progress on
your bug as I make changes.

=head1 SEE ALSO

L<HTML::Packer>, L<HTML::Lint>

=head1 SUPPORT

You can find documentation for this module with the perldoc command.

    perldoc CGI::Buffer

You can also look for information at:

=over 4

=item * MetaCPAN

L<https://metacpan.org/release/CGI-Buffer>

=item * RT: CPAN's request tracker

L<https://rt.cpan.org/NoAuth/Bugs.html?Dist=CGI-Buffer>

=item * CPANTS

L<http://cpants.cpanauthors.org/dist/CGI-Buffer>

=item * CPAN Testers' Matrix

L<http://matrix.cpantesters.org/?dist=CGI-Buffer>

=item * CPAN Testers Dependencies

L<http://deps.cpantesters.org/?module=CGI::Buffer>

=back

=head1 ACKNOWLEDGEMENTS

The inspiration and code for some of this is cgi_buffer by Mark
Nottingham: L<https://www.mnot.net/blog/2003/04/24/etags>.

=head1 LICENSE AND COPYRIGHT

The licence for cgi_buffer is:

    "(c) 2000 Copyright Mark Nottingham <mnot@pobox.com>

    This software may be freely distributed, modified and used,
    provided that this copyright notice remain intact.

    This software is provided 'as is' without warranty of any kind."

The rest of the program is Copyright 2011-2026 Nigel Horne,
and is released under the following licence: GPL2

=cut

1; # End of CGI::Buffer
