#!/usr/bin/perl

use warnings;
use strict;

use Modern::Perl;
use Fcntl qw(SEEK_SET SEEK_CUR SEEK_END);

use Compress::Zlib ;
use Compress::Raw::Lzma;

use File::Path qw(make_path );
use File::Basename qw(fileparse);
use File::HomeDir;

use Getopt::Long qw(:config gnu_getopt);

use Term::ProgressBar 2.00;

use Data::Dump;


# Verbosity settings
my $v = 1; # 0 = Quiet, 1 = Normal, 2 = Verbose, 3 = Debug, 4 = Intermediate files

# There are a huge number of possible config variables, more possible with customisation
# We only try to do the common ones
my %config_variables = (
	Home => File::HomeDir->my_home, # Set by tcl function
);

my $prefix = "install_dir";

my $help = <<HELP;
Usage: $0 [OPTIONS] FILE
Extracts installable file from Install Jammer binary installer FILE.

  -v, --verbose          Increase verbosity, more times for more verbose
      --quiet            Suppress all output including warnings
      --prefix PATH      Root of the extracted file directory tree
                         'install_dir' is used if this is not set
  -s, --set NAME=VALUE   Set installer configuration variables
      --help             Display this help and exit
      --version          Display version and licence information and exit

The installer interpolates the variables into the path and file names.
Most of these are hardcoded into the install program and extracted by this
script but some may be set interactively by the user. The script will produce
a warning if any unknown variables are encountered. The --set argument is a
way of providing this missing information, it can be called multiple times.

The script has five verbosity levels:
  0  Quiet,   no output is provided
  1  Normal,  a progress status bar is shown along with warnings
  2  Verbose, detailed progress information provided such as each filename
  3  Debug,   dumps the internal script state at various points
  4  Clutter, intermediate and raw files are dumped to disk
Levels 3 and 4 will only make sense if working through the source code.
HELP

my $version = <<VERSION;
$0 v0.2.0

Copyright (C) 2016 David Tulloh
 
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>.
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
 
Latest version and source code available from
https://github.com/lod/unpack_install_jammer/
VERSION

my $usage = <<USAGE;
Try '$0 --help' for more information.
USAGE

GetOptions(
	'verbose|v+' => \$v,
	'quiet'      => sub { $v= 0 },
	'set|s=s'    => \%config_variables,
	'prefix=s'   => \$prefix,
	'version'    => sub { print $version and exit(0) },
	'help'       => sub { print $help and exit(0) },
) or print STDERR $usage and exit(2);

unless (@ARGV == 1) {
	say STDERR "A FILE must be specified.";
	print STDERR $usage;
	exit(2);
}

my $target = pop(@ARGV);
unless (-f $target) {
	say STDERR "FILE must exist and be readable.";
	print STDERR $usage;
	exit(2);
}

dd (@ARGV, {target => $target, verbose => $v, prefix => $prefix}, \%config_variables) if $v > 2;


sub get_config_var {
	my ($k) = @_;
	say "Using variable $k" if $v > 2;
	unless (exists $config_variables{$k}) {
		# Warn about missing variables but only once
		say "WARNING: Missing variable $k" if $v;
		$config_variables{$k} = $k;
	} else {
		# Interpolate variables
		$config_variables{$k} =~ s/<%(\w+)%>/get_config_var($1)/eg;
	}
	return $config_variables{$k};
}

my $progress = Term::ProgressBar->new({count => 100, silent => $v!=1});

# Open two mmap handles into the target.
# The setup process is fairly slow apparently, so we reuse the handles
# $fh is for sequential access, searching through the file
# $fh2 is for binary access, grabbing chunks identified by the sequential scan

open(my $fh, "<:mmap", $target);
open(my $fh2, "<:mmap", $target);


sub normalize_path {
	# Messing with paths is difficult
	# Goal: Prevent climbing out of the prefix using a path of ../../ etc.
	#
	# To do this properly, handling symlinks, you use Cwd::realpath() or
	# the like. This requires that the path exists though, to chase down
	# the links. Useless for us.
	#
	# The other way is to manually pop the path chucks as you run into a
	# .. element. It doesn't handle symlinks but that shouldn't be an
	# issue for us as any symlinks would have been intentionally placed.
	# This magic script below does the popping, somehow.

	# This subroutine was stolen from Dancer::FileUtils v1.3202
	# Available under GPLv1+
	
    # this is a revised version of what is described in
    # http://www.linuxjournal.com/content/normalizing-path-names-bash
    # by Mitch Frazier
    my $path     = shift or return;
    my $seqregex = qr{
        [^/]*  # anything without a slash
        /\.\./ # that is accompanied by two dots as such
    }x;

    $path =~ s{/\./}{/}g;
    while ( $path =~ s{$seqregex}{} ) {}

    return $path;
}


sub extract_metadata {
	my ($loc) = @_;

	# Each entry is 256 bytes
	seek($fh2, $loc, SEEK_SET);
	read($fh2, my $raw, 256);

	my @vals = unpack("Z4 Z2 Z128 Z12 Z12 Z14 Z84", $raw);

	# Sometimes we match to rubbish, try and filter it out
	return if $vals[2] =~ /[^[:print:]]/;
	my $null_count = () = $raw =~ /\x00/g;
	return if $null_count < 20;

	return {
		encoding => $vals[1],
		id       => $vals[2],
		size     => $vals[3],
		c_size   => $vals[4],
		mtime    => $vals[5],
		c_loc    => $vals[6],
	};
}

sub extract_filelist {
	# Returns a list of files, with attached metadata
	# These files are extracted from the install binary
	# Note that the application files will have been renamed,
	# a second step is required to convert the names back.

	# Unsure where in the binary the file details will be
	# The strings are of a set format we can search for though
	# The install binary seems to have two, identical, blocks of
	# this data for some reason. Just let duplicates overwrite.
	my %files;

	my $buffer = "";
	while(my $buf_len = read($fh, $buffer, 4096)) {
		my $index = -1;
		until(($index = index($buffer, "FILE", $index+1)) == -1) {
			my $meta = extract_metadata(tell($fh)-$buf_len+$index);
			$files{$meta->{id}} = $meta if $meta;
		}
		seek($fh, -4, SEEK_CUR) if $buf_len == 4096; # Wind back, in case the match is on the border
	}

	return %files;
}

sub say_heading {
	my $out = join $,//"", @_;
	say "";
	say $out;
	say "=" x length($out);
}


sub extract_file {
	my ($meta, $out_filename) = @_;

	dd($meta) if $v > 2;

	seek($fh, $meta->{c_loc}, SEEK_SET);
	read($fh, my $raw, $meta->{c_size});

	if ($out_filename and $v > 3) {
		open(my $raw_fh, ">", "$out_filename.raw");
		print $raw_fh $raw;
		close $raw_fh;
	}

	my $output;

	if ($meta->{encoding} eq "ZL") {
		# zlib requires a two byte header, these set the compression method, info, dictionary etc.
		# Out chunks don't have this header, the defaults seem to work though so we add them on
		$raw = pack("CC", 0x78, 0x9C).$raw;

		my ($z, $status) = inflateInit();
		die "inflation init failed\n" unless $status == Z_OK;

		($output, $status) = $z->inflate($raw) ;
		die "zlib inflation failed\n" unless $status == Z_OK;

		if ($v) {
			say sprintf "WARNING: total input doesn't match expected: input = %d, expected = %d", $z->total_in()-2, $meta->{c_size} unless  $z->total_in()-2 == $meta->{c_size}; # 2 offset for header
			say sprintf "WARNING: total output doesn't match expected: output = %d, expected = %d", $z->total_out(), $meta->{size} unless  $z->total_out() == $meta->{size};
		}

	} elsif ($meta->{encoding} eq "LZ") {
		# LZMA format, stream is a modified variant of LZMA 1 or alone
		# We are missing the length portion of the header
		# Splicing in a no-length value makes things work though
		substr($raw, 5, 0, pack("CCCC CCCC", (0xFF) x 8));

		my ($lz, $status) = new Compress::Raw::Lzma::AloneDecoder;
		die "LZMA initialisation failed: $status" if $status;

		$status = $lz->code($raw, $output);
		die "lzma decoding failed: $status" if $status;
	} else {
		say "WARNING: unknown encoding ".$meta->{encoding} if $v;
		$output = $raw;
	}

	if ($out_filename) {
		open(my $out_fh, ">", $out_filename);
		print $out_fh $output;
	} else {
		return $output;
	}
}

sub parse_tcl_data {
	my ($tcl_file, $files) = @_;

	# $tcl_file can be a scalar string or a reference to a scalar string
	# The second is preferred as the string will probably be rather large

	open(my $tcl_fh, '<', ref($tcl_file) ? $tcl_file : \$tcl_file) or die $!;
	my %install_files;

	say_heading "Parsing tcl file" if $v > 2;

	while (<$tcl_fh>) {
		dd($_) if $v > 2;

		next unless /^\s* File \s+ ::/x;

		# Need to do a fancy split for fields like "-alias {License Text}"
		chomp;
		my (undef, $id) = split /\s+/, $_, 3;
		my (%new_elems) = /\s(-\w+) \s+ (.+?) (?:(?=\s+-)|$)/xg;

		# id has a leading double colon, ditch it
		$id =~ s/^:://;

		dd($_, $id, %new_elems) if $v > 2;
		
		# Set every possible elem value rather than what is provided
		# Makes life easier to have a consistent dictionary
		my %elems = (
			type              => $new_elems{"-type"} // "file",
			name              => $new_elems{"-name"},
			size              => $new_elems{"-size"},
			mtime             => $new_elems{"-mtime"},
			srcfile           => $new_elems{"-srcfile"} // $id,
			version           => $new_elems{"-version"},
			location          => $new_elems{"-location"},
			directory         => $new_elems{"-directory"},
			savefiles         => $new_elems{"-savefiles"},
			linktarget        => $new_elems{"-linktarget"},
			filemethod        => $new_elems{"-filemethod"},
			attributes        => $new_elems{"-attributes"},
			permissions       => $new_elems{"-permissions"},
			targetfilename    => $new_elems{"-targetfilename"},
			compressionmethod => $new_elems{"-compressionmethod"},
		);

		dd(%elems) if $v > 2;
		dd($files->{$id}, $files->{$elems{srcfile}}) if $v > 2;

		if ($elems{"type"} eq "file") {
			# We have a file, merge in the install file references
			my $srcfile = $elems{srcfile};
			if ($files->{$srcfile}) {
				$install_files{$srcfile} = {%elems, %{$files->{$srcfile}}};
			} else {
				say "WARNING: Missing file data for $id, $elems{srcfile}" if $v;
			}
		} else {
			# Could be directory, or something else, just store it
			$install_files{$id} = \%elems;
		}
	}
	return %install_files;
}


my $info_blocks_re = qr/array \s+ set \s+ info \s*
	(                   # start of capture group 1
	\{                  # match an opening angle bracket
		(?:
			[^{}]++     # one or more non angle brackets, non backtracking
				|
			(?1)        # found < or >, so recurse to capture group 1
		)*
	\}                  # match a closing angle bracket
	)                   # end of capture group 1
	/x;

sub parse_info_block {
	my ($tcl_file) = @_;

	my @info_blocks;
	if (ref($tcl_file)) {
		@info_blocks = $$tcl_file =~ m/$info_blocks_re/g;
	} else {
		@info_blocks = $tcl_file =~ m/$info_blocks_re/g;
	}

	foreach my $info_block (@info_blocks) {
		$info_block =~ s/^\s*\{\s* | \s*\}\s*$//xg;

		my %info = $info_block =~ /(\w+) \s+ ( \{[^}]*\} | \S+ )/xg;

		foreach (keys %info) {
			# Strip leading and tail {} if present
			$info{$_} =~ s/^\{ (.*) \}$/$1/xg;

			# Add to config variables unless already set
			$config_variables{$_} //= $info{$_};
		}
	}
}

sub install_directories {
	my ($install_files) = @_;

	foreach (keys %$install_files) {
		next unless $install_files->{$_}{type} eq "dir";

		my %meta = %{$install_files->{$_}};
		dd(%meta) if $v >2;
		
		my $path = $meta{directory};
		$path =~ s/<%(\w+)%>/get_config_var($1)/eg;
		my $fullpath = "$prefix/$path";

		# Prevent climbing out of prefix using ../ or the like
		$fullpath = normalize_path($fullpath);
		die "Path climbing out: $fullpath" unless $fullpath =~ m!^$prefix/!;

		say "Path: $fullpath" if $v > 1;
		make_path("$fullpath");


		utime($meta{mtime}, $meta{mtime}, $fullpath) if $meta{mtime};
		
		# The directory permissions are provided as a six digit number: 040755
		# I have no idea what the first three digits do
		# The tcl script just always sets 777, we do our best
		if ($meta{permissions}) {
			my $perms = substr $meta{permissions}, -3;
			chmod(oct($perms), $fullpath);
		}

		$progress->update();
	}
}

sub install_files {
	my ($install_files) = @_;

	foreach (keys %$install_files) {
		next unless $install_files->{$_}{type} eq "file";

		my %meta = %{$install_files->{$_}};
		dd(%meta) if $v >2;

		my $path = $meta{directory} // "/";
		$path =~ s/<%(\w+)%>/get_config_var($1)/eg;

		unless (-d "$prefix/$path") {
			say "WARNING: installing file $_ path $prefix/$path did not exist" if $v;
			make_path("$prefix/$path");
		}

		my $fullname = "$prefix/$path/$meta{name}";
		$fullname =~ s/<%(\w+)%>/get_config_var($1)/eg;

		# Prevent climbing out of prefix using ../ or the like
		$fullname = normalize_path($fullname);
		die "File climbing out: $fullname" unless $fullname =~ m!^$prefix/!;

		say "File: $fullname" if $v > 1;
		extract_file(\%meta, $fullname);

		utime($meta{mtime}, $meta{mtime}, $fullname) if $meta{mtime};
		chmod(oct($meta{permissions}), $fullname) if $meta{permissions};

		$progress->update();
	}
}

sub install_other {
	my ($install_files) = @_;

	# TODO: Other types, links are possible, they could always customise for more :(
	# Links should be created as symlinks, "exec ln -s $link $dest"
	# Need to ensure that the destinations don't violate our prefix "jail"

	foreach (keys %$install_files) {
		my $type = $install_files->{$_}{type};
		if ($type ne "file" and $type ne "dir") {
			say "WARNING: Unsupported type $type for ".$install_files->{$_}{name} if $v;
			$progress->update();
		}

	}

}

sub install {
	my ($install_files) = @_;

	$progress->target(scalar keys %$install_files);

	# Install files
	# Safest way is to do directories first

	install_directories($install_files);
	install_files($install_files);
	install_other($install_files);

	$progress->update(scalar keys %$install_files); # 100%
}

my %files = extract_filelist();


if ($v > 2) {
	say_heading "%files";
	dd(%files);

	say_heading "Encoding Filename";
	foreach (sort keys %files) {
		say $files{$_}->{"encoding"}, " ", $_;
	}
}


if ($v > 3) {
	say_heading "Extracting all files";
	make_path("extracted");
	foreach (sort keys %files) {
		say "Extracting $_";
		my (undef,$path) = fileparse($_);
		make_path("extracted/$path") if $path;
		extract_file($files{$_}, "extracted/$_");
	}
}


# There exists, I hope, a tcl file in the root directory which contains
# the File object creation entries, these tell us how to rename our file blobs
# Various examples of this file have been named main.tcl and main2.tcl
# Rather than fiddle we take the machine gun approach and just hit them all.

my %install_files;
foreach (keys %files) {
	next unless /^\w+\.tcl$/;
	my $tcl_file = extract_file($files{$_});
	%install_files = (%install_files, parse_tcl_data(\$tcl_file, \%files));
	parse_info_block(\$tcl_file);
}

if ($v > 2) {
	say_heading "%config_variables";
	say join " => ", $_, $config_variables{$_} foreach sort keys %config_variables;

	say_heading "%install_files";
	dd(%install_files);
}

install(\%install_files);
