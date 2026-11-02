#!perl -w

# Security regressions: responses and requests that mustn't be shared between
# clients through the server-side cache
# CGI::Buffer does its work in an END block, so each case runs in its own process

use strict;
use warnings;
use File::Spec;
use Test::Most;
use Test::Needs 'CHI';
use Test::TempDir::Tiny;

my $lib = File::Spec->rel2abs($ENV{CGI_BUFFER_LIB} || q{lib});

# Run a CGI script that uses a File cache in $dir, returning its output
sub run_script {
	my (%args) = @_;

	my $script = File::Spec->catfile($args{dir}, 'script.pl');
	open(my $fout, '>', $script) or die "$script: $!";
	print $fout <<"EOF";
use strict;
use warnings;
use CHI;
use CGI::Buffer;
CGI::Buffer::init(cache => CHI->new(driver => 'File', root_dir => '$args{dir}/cache'), $args{init});
exit if CGI::Buffer::is_cached();
$args{code}
EOF
	close $fout;

	local %ENV = (
		PATH => $ENV{'PATH'},
		SERVER_PROTOCOL => 'HTTP/1.1',
		REQUEST_METHOD => 'GET',
		SCRIPT_NAME => '/cgi-bin/script.pl',
		SCRIPT_FILENAME => $script,
		DOCUMENT_ROOT => $args{dir},
		%{$args{env} || {}}
	);
	my $output = `$^X -I$lib $script`;
	$output =~ s/\r//g;
	return $output;
}

# Run the same script twice, returning the second output
sub second_request {
	my (%args) = @_;

	run_script(%args, env => { %{$args{env} || {}}, FIRST => 1 });
	return run_script(%args);
}

my $html = '<html><head><title>t</title></head><body>hello</body></html>';

subtest 'Set-Cookie is not replayed to other clients' => sub {
	my $out = second_request(
		dir => tempdir(), init => "cache_key => 'k'",
		code => qq{print "Content-Type: text/html\\n", (\$ENV{FIRST} ? "Set-Cookie: session=SECRET\\n" : ''), "\\n$html";}
	);
	unlike($out, qr/SECRET/, 'cookie not sent to the second client');
	like($out, qr/^X-Cache-Lookup: MISS/m, 'response was not stored');
};

for my $control('no-store', 'no-cache', 'private', 'Private, max-age=60') {
	subtest "Response Cache-Control: $control is not stored" => sub {
		my $out = second_request(
			dir => tempdir(), init => "cache_key => 'k'",
			code => qq{print "Content-Type: text/html\\nCache-Control: $control\\n\\n$html";}
		);
		like($out, qr/^X-Cache-Lookup: MISS/m, 'response was not stored');
	};
}

subtest 'Vary on a request header is not stored' => sub {
	my $out = second_request(
		dir => tempdir(), init => "cache_key => 'k'",
		code => qq{print "Content-Type: text/html\\nVary: User-Agent\\n\\n$html";}
	);
	like($out, qr/^X-Cache-Lookup: MISS/m, 'response was not stored');
};

subtest 'Vary: Accept-Encoding is stored' => sub {
	my $out = second_request(
		dir => tempdir(), init => "cache_key => 'k'",
		code => qq{print "Content-Type: text/html\\nVary: Accept-Encoding\\n\\n$html";}
	);
	like($out, qr/^X-Cache-Lookup: HIT/m, 'response was stored') or diag($out);
};

subtest 'A page containing the client\'s csrf_token is not stored' => sub {
	my $out = second_request(
		dir => tempdir(), init => "cache_key => 'k'",
		env => { HTTP_COOKIE => 'csrf_token=abc%2B123' },
		code => q{print "Content-Type: text/html\n\n<html><body><input value=\"abc+123\"></body></html>";}
	);
	like($out, qr/^X-Cache-Lookup: MISS/m, 'response was not stored');
};

subtest 'A partial HTML page is not stored' => sub {
	my $out = second_request(
		dir => tempdir(), init => "cache_key => 'k'",
		code => q{print "Content-Type: text/html\n\n<html><body>half";}
	);
	like($out, qr/^X-Cache-Lookup: MISS/m, 'response was not stored');
};

for my $env(
	{ REQUEST_METHOD => 'POST' },
	{ HTTP_AUTHORIZATION => 'Basic dXNlcjpwYXNz' },
	{ REMOTE_USER => 'alice' },
	{ HTTP_CACHE_CONTROL => 'max-age=0' },
	{ HTTP_CACHE_CONTROL => 'No-Cache, max-age=10' },
	{ NO_CACHE => 1 },
) {
	my ($name) = keys %{$env};
	subtest "can_cache is false with $name=$env->{$name}" => sub {
		my $out = run_script(
			dir => tempdir(), init => '', env => $env,
			code => q{print "Content-Type: text/plain\n\n", (CGI::Buffer::can_cache() ? 'yes' : 'no');}
		);
		like($out, qr/\nno$/, 'cache not used');
	};
}

subtest 'can_cache is true for a plain GET' => sub {
	my $out = run_script(
		dir => tempdir(), init => '',
		code => q{print "Content-Type: text/plain\n\n", (CGI::Buffer::can_cache() ? 'yes' : 'no');}
	);
	like($out, qr/\nyes$/, 'cache used');
};

subtest 'Client max-age is limited' => sub {
	for my $test(['max-age=60', '60 seconds'], ['max-age=99999999', 'default'], ['max-age=1abc', 'default']) {
		my ($control, $expect) = @{$test};
		my $out = run_script(
			dir => tempdir(), init => '', env => { HTTP_CACHE_CONTROL => $control },
			code => q{print "Content-Type: text/plain\n\n", ($CGI::Buffer::cache_duration // 'default');}
		);
		like($out, qr/\n\Q$expect\E$/, "$control gives $expect");
	}
};

subtest 'Generated cache key' => sub {
	my $out = run_script(
		dir => tempdir(), init => '',
		env => { HTTP_COOKIE => 'a=1; __utma=2; __utmz=3; csrf_token=4; b=5', PATH_INFO => '/foo' },
		code => q{print "Content-Type: text/plain\n\n", CGI::Buffer::_generate_key();}
	);
	like($out, qr/::a=1/, 'first cookie in key');
	like($out, qr/::b=5/, 'later cookie in key');
	unlike($out, qr/__utm/, 'Google Analytics cookies not in key');
	unlike($out, qr/csrf_token/, 'csrf_token not in key');
	like($out, qr/PATH_INFO=::foo/, 'PATH_INFO in key');
};

subtest 'optimise_content does not make other sites local' => sub {
	my $out = run_script(
		dir => tempdir(), init => 'optimise_content => 1',
		env => { HTTP_HOST => 'www.example.com', SERVER_NAME => 'www.example.com', NO_CACHE => 1 },
		code => q{print qq{Content-Type: text/html\n\n<html><body><a href="http://www.example.com.evil.org/x">e</a> <a href="http://www.example.com/y">l</a></body></html>};}
	);
	like($out, qr{href="http://www\.example\.com\.evil\.org/x"}, 'other site left alone');
	like($out, qr{href="/y"}, 'own site made local');
};

done_testing();
