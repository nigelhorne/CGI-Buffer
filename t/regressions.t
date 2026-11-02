#!perl -w

# Regression tests for bugs fixed in the HTTP handling, compression, the cache
# and optimise_content
# CGI::Buffer does its work in an END block, so each case runs in its own process

use strict;
use warnings;
use Digest::MD5;
use File::Spec;
use Test::Most;
use Test::TempDir::Tiny;

my $lib = File::Spec->rel2abs($ENV{CGI_BUFFER_LIB} || 'lib');
my $have_chi = eval { require CHI; 1 };

# Run a CGI script, returning its headers as an arrayref of lines, and its body.
# preamble is code to run before CGI::Buffer is loaded, init is the arguments to
# init(), cache uses a File cache in the directory
sub run_script {
	my (%args) = @_;

	my $dir = $args{dir} || tempdir();
	my $script = File::Spec->catfile($dir, 'script.pl');
	my $init = $args{init} || '';
	my $cache = '';
	if($args{cache}) {
		$cache = "use CHI;\nCGI::Buffer::init(cache => CHI->new(driver => 'File', root_dir => '$dir/cache'), cache_key => 'k');\nexit if CGI::Buffer::is_cached();\n";
	}
	open(my $fout, '>', $script) or die "$script: $!";
	print $fout "use strict;\nuse warnings;\n", ($args{preamble} || ''),
		"use CGI::Buffer;\n",
		($init ? "CGI::Buffer::init($init);\n" : ''),
		$cache,
		$args{code};
	close $fout;

	local %ENV = (
		PATH => $ENV{'PATH'},
		SERVER_PROTOCOL => 'HTTP/1.1',
		REQUEST_METHOD => 'GET',
		SCRIPT_NAME => '/cgi-bin/script.pl',
		SCRIPT_FILENAME => $script,
		DOCUMENT_ROOT => $dir,
		%{$args{env} || {}}
	);
	my $output = `$^X -I$lib $script 2>&1`;
	my ($headers, $body) = split(/\r?\n\r?\n/, $output, 2);
	return ([ split(/\r?\n/, $headers // '') ], $body // '');
}

# The values of a header
sub header {
	my ($headers, $name) = @_;

	return map { /^\Q$name\E:\s*(.*?)\s*$/i ? $1 : () } @{$headers};
}

my $text = q{print "Content-Type: text/plain\n\nhello world";};

subtest 'Range' => sub {
	my %tests = (
		'bytes=-5' => ['world', 'bytes 6-10/11'],
		'bytes=0-4' => ['hello', 'bytes 0-4/11'],
		'bytes=6-' => ['world', 'bytes 6-10/11'],
		'bytes=6-100' => ['world', 'bytes 6-10/11'],
	);
	foreach my $range(sort keys %tests) {
		my ($headers, $body) = run_script(code => $text, env => { HTTP_RANGE => $range, HTTP_ACCEPT_ENCODING => 'gzip' });
		is($body, $tests{$range}->[0], "$range body");
		is_deeply([header($headers, 'Status')], ['206 Partial Content'], "$range status");
		is_deeply([header($headers, 'Content-Range')], [$tests{$range}->[1]], "$range Content-Range");
		is_deeply([header($headers, 'Content-Encoding')], [], "$range is not compressed");
	}

	my ($headers, $body) = run_script(code => $text, env => { HTTP_RANGE => 'bytes=20-' });
	is_deeply([header($headers, 'Status')], ['416 Range Not Satisfiable'], 'unsatisfiable range gives 416');
	is_deeply([header($headers, 'Content-Range')], ['bytes */11'], '416 Content-Range');
	is($body, '', '416 has no body');

	($headers, $body) = run_script(code => $text, env => { HTTP_RANGE => 'bytes=5-2' });
	is($body, 'hello world', 'backwards range is ignored');

	($headers, $body) = run_script(code => $text, env => { HTTP_RANGE => 'bytes=0-4', REQUEST_METHOD => 'POST' });
	is($body, 'hello world', 'range is ignored for POST');

	($headers, $body) = run_script(
		code => q{print "Status: 200 OK\nContent-Type: text/plain\n\nhello world";},
		env => { HTTP_RANGE => 'bytes=0-4' }
	);
	is($body, 'hello', 'script\'s own Status header');
	is_deeply([header($headers, 'Status')], ['206 Partial Content'], 'only the 206 is sent');

	($headers, $body) = run_script(
		code => q{print "Content-Type: text/plain; charset=utf-8\n\ncaf\xc3\xa9 au lait";},
		env => { HTTP_RANGE => 'bytes=0-4' }
	);
	is($body, "caf\xc3\xa9", 'ranges are in bytes');

	($headers, $body) = run_script(code => $text, env => { HTTP_RANGE => 'bytes=0-4', HTTP_IF_RANGE => '"not-the-etag"' });
	is($body, 'hello world', 'If-Range that does not match gives the whole page');
};

subtest '304 and If-None-Match' => sub {
	my $etag = '"' . Digest::MD5::md5_hex('hello world') . '"';
	my $code = q{print "Status: 200 OK\nContent-Type: text/plain\n\nhello world";};

	foreach my $inm($etag, qq{"aaa", $etag}, "W/$etag", '*') {
		my ($headers, $body) = run_script(code => $code, env => { HTTP_IF_NONE_MATCH => $inm });
		is_deeply([header($headers, 'Status')], ['304 Not Modified'], "If-None-Match: $inm gives one 304");
		is($body, '', 'no body');
		is_deeply([header($headers, 'Content-Encoding')], [], 'no Content-Encoding');
	}

	my ($headers) = run_script(code => $code, env => { HTTP_IF_NONE_MATCH => $etag, REQUEST_METHOD => 'POST' });
	is_deeply([header($headers, 'Status')], ['412 Precondition Failed'], 'matching If-None-Match on POST gives 412');

	($headers) = run_script(
		code => q{print "Status: 404 Not Found\nContent-Type: text/plain\n\nnot here";},
		init => 'info => CGI::Info->new()',
		preamble => "use CGI::Info;\n",
		env => { HTTP_IF_MODIFIED_SINCE => 'Fri, 01 Jan 2100 00:00:00 GMT' },
	);
	is_deeply([header($headers, 'Status')], ['404 Not Found'], 'If-Modified-Since leaves a 404 alone');

	($headers) = run_script(code => $code, env => { SERVER_PROTOCOL => 'HTTP/2' });
	is(scalar(header($headers, 'ETag')), 1, 'ETag for HTTP/2');
	($headers) = run_script(code => $code, env => { SERVER_PROTOCOL => 'HTTP/3' });
	is(scalar(header($headers, 'ETag')), 1, 'ETag for HTTP/3');
};

subtest 'Headers' => sub {
	my ($headers, $body) = run_script(
		code => q{print "Content-Type: text/plain\nContent-Length: 999\n\n", 'x' x 100;},
		env => { HTTP_ACCEPT_ENCODING => 'gzip' }
	);
	is_deeply([header($headers, 'Content-Length')], [length($body)], 'the script\'s Content-Length is replaced');

	($headers, $body) = run_script(
		code => q{print "Content-Type: text/plain\nContent-Encoding: gzip\n\n", 'x' x 100;},
		env => { HTTP_ACCEPT_ENCODING => 'gzip' }
	);
	is($body, 'x' x 100, 'output that the script encoded is not compressed again');
	is_deeply([header($headers, 'Content-Encoding')], ['gzip'], 'one Content-Encoding');

	($headers) = run_script(code => q{print "Content-Type: text/plain\nStatus: 404 Not Found\n\nnot here";});
	is_deeply([header($headers, 'Status')], ['404 Not Found'], 'headers ending in LF give one Status');

	($headers) = run_script(code => $text);
	is_deeply([header($headers, 'Vary')], ['Accept-Encoding'], 'Vary: Accept-Encoding with uncompressed output');
};

subtest 'Compression' => sub {
	my $long = q{print "Content-Type: Text/HTML\n\n<html><body>", 'hello world ' x 20, "</body></html>";};
	my ($headers) = run_script(code => $long, env => { HTTP_ACCEPT_ENCODING => 'gzip' });
	is_deeply([header($headers, 'Content-Encoding')], ['gzip'], 'Text/HTML is compressed');
	my ($etag) = header($headers, 'ETag');
	like($etag, qr/-gzip"$/, 'compressed output has its own ETag');

	($headers) = run_script(code => $long, env => { HTTP_ACCEPT_ENCODING => 'gzip', HTTP_IF_NONE_MATCH => $etag });
	is_deeply([header($headers, 'Status')], ['304 Not Modified'], 'compressed ETag matches');

	my %tests = (
		'gzip;q=0' => [],
		'gzip;q=0.8' => ['gzip'],
		'deflate , gzip' => ['gzip'],
		'identity, x-gzip' => ['gzip'],
		'GZIP' => ['gzip'],
	);
	foreach my $accept(sort keys %tests) {
		($headers) = run_script(code => $long, env => { HTTP_ACCEPT_ENCODING => $accept });
		is_deeply([header($headers, 'Content-Encoding')], $tests{$accept}, "Accept-Encoding: $accept");
	}

	($headers) = run_script(
		preamble => q{BEGIN { unshift @INC, sub { die "No brotli\n" if($_[1] eq 'IO/Compress/Brotli.pm'); return } }} . "\n",
		code => $long, env => { HTTP_ACCEPT_ENCODING => 'br, gzip' }
	);
	is_deeply([header($headers, 'Status')], ['200 OK'], 'no 406 when brotli is not installed');
	is_deeply([header($headers, 'Content-Encoding')], ['gzip'], 'the next encoding is used');

	SKIP: {
		skip 'Compress::Zlib not installed', 2 unless(eval { require Compress::Zlib; 1 });
		my $body;
		($headers, $body) = run_script(
			code => q{print "Content-Type: text/plain; charset=utf-8\n\n", "caf\xc3\xa9 " x 20;},
			env => { HTTP_ACCEPT_ENCODING => 'gzip' }
		);
		is_deeply([header($headers, 'Content-Encoding')], ['gzip'], 'compressed');
		is(Compress::Zlib::memGunzip($body), "caf\xc3\xa9 " x 20, 'UTF-8 printed as bytes is not encoded twice');
	}
};

subtest 'Cache' => sub {
	plan skip_all => 'CHI not installed' unless($have_chi);

	my $html = q{print "Content-Type: text/html\nVary: Accept-Encoding\n\n<html><body>hello</body></html>";};
	my $dir = tempdir();
	my ($headers, $body) = run_script(dir => $dir, cache => 1, code => $html);
	is(scalar(header($headers, 'Status')), 1, 'Vary: Accept-Encoding does not end the headers');
	is($body, '<html><body>hello</body></html>', 'body is intact');
	my ($etag) = header($headers, 'ETag');

	($headers, $body) = run_script(dir => $dir, cache => 1, code => $html);
	like((header($headers, 'X-Cache-Lookup'))[0], qr/^HIT/, 'second request is from the cache');
	is($body, '<html><body>hello</body></html>', 'cached body is intact');

	($headers) = run_script(dir => $dir, cache => 1, code => $html, env => {
		HTTP_IF_NONE_MATCH => '"no-match"',
		HTTP_IF_MODIFIED_SINCE => 'Fri, 01 Jan 2100 00:00:00 GMT'
	});
	is_deeply([header($headers, 'Status')], ['200 OK'], 'If-None-Match is looked at before If-Modified-Since');

	($headers) = run_script(dir => $dir, cache => 1, code => $html, env => { HTTP_IF_NONE_MATCH => $etag });
	is_deeply([header($headers, 'Status')], ['304 Not Modified'], 'ETag of a cached page matches');

	# An ETag that the script gave keeps its quotes in the cache
	my $own = '"0123456789abcdef0123456789abcdef"';
	my $code = q{print "Content-Type: text/html\nETag: \"0123456789abcdef0123456789abcdef\"\n\n<html><body>hello</body></html>";};
	$dir = tempdir();
	run_script(dir => $dir, cache => 1, code => $code);
	($headers) = run_script(dir => $dir, cache => 1, code => $code, env => { HTTP_IF_NONE_MATCH => $own });
	is_deeply([header($headers, 'Status')], ['304 Not Modified'], 'the script\'s own ETag matches from the cache');

	# Expired entries aren't used
	$dir = tempdir();
	($headers, $body) = run_script(dir => $dir, code => q{
		use CHI;
		use Storable;
		my $cache = CHI->new(driver => 'File', root_dir => "$ENV{DOCUMENT_ROOT}/cache");
		$cache->set('k', Storable::freeze({ body => 'stale', headers => 'Content-Type: text/plain' }), { expires_at => time - 60 });
		CGI::Buffer::init(cache => $cache, cache_key => 'k');
		exit if CGI::Buffer::is_cached();
		print "Content-Type: text/plain\n\nfresh";
	});
	is($body, 'fresh', 'an expired entry is not used');

	# A failing cache gives a warning, and the page is still sent
	($headers, $body) = run_script(code => q{
		package BadCache;
		sub new { bless {}, shift }
		sub get_object { die 'broken get' }
		sub set { die 'broken set' }
		sub get { die 'broken get' }
		package main;
		CGI::Buffer::init(cache => BadCache->new(), cache_key => 'k');
		exit if CGI::Buffer::is_cached();
		print "Content-Type: text/plain\n\nstill here";
	});
	like($body, qr/still here/, 'page is sent when the cache fails');
};

subtest 'Logging' => sub {
	my ($headers, $body) = run_script(code => q{
		package MyLogger;
		sub new { bless {}, shift }
		sub AUTOLOAD { our $AUTOLOAD; print STDERR "LOG $AUTOLOAD: @_[1..$#_]\n" unless($AUTOLOAD =~ /DESTROY/) }
		package main;
		CGI::Buffer::init(logger => MyLogger->new());
		print "Content-Type: text/plain\n\nhello";
	});
	like(join("\n", @{$headers}), qr/LOG MyLogger::debug: Initial status = 200/, 'the END block logs');
};

subtest 'optimise_content' => sub {
	my ($headers, $body) = run_script(init => 'optimise_content => 1', env => { NO_CACHE => 1 }, code => q{
		print "Content-Type: text/html\n\n<html><body><pre>a   b\n    c</pre>\n<textarea>x   y</textarea>\n",
			"<p>Hello <b>world</b></p>\n</body></html>";
	});
	like($body, qr{<pre>a   b\n    c</pre>}, '<pre> is left alone');
	like($body, qr{<textarea>x   y</textarea>}, '<textarea> is left alone');

	($headers, $body) = run_script(init => 'optimise_content => 1', env => { NO_CACHE => 1 }, code => q{
		print "Content-Type: text/html\n\n<html><body><p>Hello <b>a</b> <i>b</i></p></body></html>";
	});
	like($body, qr{Hello <b>a</b> <i>b</i>}, 'visible space between tags is kept');

	($headers, $body) = run_script(init => 'optimise_content => 1', env => { NO_CACHE => 1 }, code => q{
		print "Content-Type: text/html\n\n<html><body><script>var a = 1\n+ 2;</script></body></html>";
	});
	like($body, qr{\+ ?2}, '"+" at the start of a line is kept');

	($headers, $body) = run_script(init => 'optimise_content => 2', env => { NO_CACHE => 1 }, code => q{
		print "Content-Type: text/html\n\n<html><body>",
			'<script type="text/javascript">document.write("a");</script>',
			'<p>between</p>',
			'<script type="text/javascript">document.write("b"); document.write("c");</script>',
			"</body></html>";
	});
	like($body, qr{<p>between</p>}, 'text between scripts is kept');
	like($body, qr{document\.write\("a"\)}, 'writes in different scripts are not merged');
	like($body, qr{document\.write\("b"\s*\+\s*"c"\)}, 'writes in the same script are merged');
	unlike($body, qr{text/JavaScript}, 'the script\'s type is not changed');

	my $start = time;
	($headers, $body) = run_script(init => 'optimise_content => 1', env => { NO_CACHE => 1 }, code => q{
		print "Content-Type: text/html\n\n<html><body>", '<title>' x 20000, ' ' x 20000, "</body></html>";
	});
	cmp_ok(time - $start, '<', 20, 'hostile input does not take quadratic time');
};

done_testing();
