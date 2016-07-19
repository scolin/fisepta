#!/usr/bin/env perl

use strict;

# foreach my $x ("x", "x[i1]", "x.f1", "x[i1].f1", "x.f1[i1]", "x[i1][i2]", "x.f1.f2") {
#   foreach my $y ("y", "y[j1]", "y.g1", "y[j1].g1", "y.g1[j1]", "y[j1][j2]", "y.g1.g2") {
#     print "$x = $y\n";
#   }
# }

my $name = "constraint_pointsto";
my $i = 1;

foreach my $x
    (["  int *x;\n  ", "x"],
     ["  int *x[5];\n  int i1=2;\n  ",  "x[i1]"],
     ["  struct { int *f1; } x;\n  ", "x.f1"],
     ["  struct { int *f1; } x[5];\n  int i1=2;\n  ", "x[i1].f1"],
     ["  struct { int *f1[5]; } x;\n  int i1=2;\n  ", "x.f1[i1]"],
     ["  int *x[5][5];\n  int i1=2;\n  int i2=1;\n  ", "x[i1][i2]"],
     ["  struct { struct { int *f2; } f1; } x;\n  ", "x.f1.f2"]) {
      foreach my $y (
	["int y;\n  ", "&y"],
	["int y[5];\n  int j1=2;\n  ",  "&y[j1]"] ) {
	my $k = sprintf("%03d", $i);
	my $fname = $name."_".$k.".c";
	open (my $fh, ">", $fname) or die "$!";
	print $fh  "\nint main() {\n";
	print $fh  $x->[0].$y->[0].$x->[1]." = ".$y->[1].";\n";
	print $fh  "  return(0);\n}\n\n";
	close($fh) or die "$!";
	$i++;
      }
}

