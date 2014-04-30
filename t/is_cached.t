#!perl -Tw

# Doesn't test anything useful yet

use strict;
use warnings;
use Test::Most tests => 4;
use Storable;
# use Test::NoWarnings;	# HTML::Clean has them

BEGIN {
	use_ok('CGI::Buffer');
}

CACHED: {
	delete $ENV{'REMOTE_ADDR'};
	delete $ENV{'HTTP_USER_AGENT'};

	ok(CGI::Buffer::is_cached() == 0);

	SKIP: {
		eval {
			require CHI;

			CHI->import;
		};

		skip 'CHI not installed', 2 if $@;

		diag("Using CHI $CHI::VERSION");

		my $cache = CHI->new(driver => 'Memory', datastore => {});

		# On some platforms it's failing - find out why
		CGI::Buffer::init({
			cache => $cache,
			cache_key => 'xyzzy',
			logger => MyLogger->new()
		});
		ok(!CGI::Buffer::is_cached());

		my $c;

		$c->{'body'} = '';
		$c->{'etag'} = '';
		$c->{'headers'} = '';

		$cache->set('xyzzy', Storable::freeze($c));
		ok(CGI::Buffer::is_cached());
	}
}

# On some platforms it's failing - find out why
package MyLogger;

sub new {
	my ($proto, %args) = @_;

	my $class = ref($proto) || $proto;

	return bless { }, $class;
}

sub debug {
	my $self = shift;
	my $message = shift;

	# Enable this for debugging
	# ::diag($message);
}
