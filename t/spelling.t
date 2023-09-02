#!perl -w

use strict;
use warnings;

use Test::Most;

unless($ENV{RELEASE_TESTING}) {
    plan( skip_all => "Author tests not required for installation" );
}

eval 'use Test::Spelling';
if($@) {
	plan skip_all => 'Test::Spelling required for testing POD spelling';
} else {
	add_stopwords(<DATA>);
	all_pod_files_spelling_ok();
}

__END__
AnnoCPAN
CGI
CPAN
GPL
Init
JavaScript
RT
STDOUT
init
