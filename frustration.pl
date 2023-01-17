#!/usr/bin/perl
# by Jay Coskey

# BIT ROT WARNING: This antique script no longer produces correct results, depite not having been altered in ages.

# This script gets the probability of winning frustration solitaire, using rook polynomials.
# For info on frustration solitaire (and other rank-derangement problems),
# see http://math.dartmouth.edu/~doyle/docs/rank/rank.pdf

# Explanation of the computation.  (Summary of the above PDF.)
#   Imagine a deck of cards laid out in 4 rows, each ordered from Ace to King.
#   Now shuffle the deck, and lay the cards out in the same array.
#   This is a winning game of frustration solitaire if and only if
#       no card ends up in its original column.
#   Total number of ways that no card ends up in its original column
#     = Total # of permutations
#         - total # of ways that one card can be in its original column
#         + total # of ways that two cards can be in their original column
#         - total # of ways that three cards can be in their original column
#         etc.
#     = n! * [1 = 1/1! + 1/2! - ... + (-1)^n/n! ]
#   It can be shown by induction that this same formula applies to the coefficients
#       of certain polynomials being multiplied together.
#   These are called Rook Polynomials.  (See https://en.wikipedia.org/wiki/Rook_polynomial)
#   Rook polynomials are named after their use in determining the number of ways
#       that rooks can be placed on a chessboard so that no two can attack each other.

# In frustration solitaire, where the deck has 4 suits and 13 cards per suit,
# the probability of winning is:
#
#      1309302175551177162931045000259922525308763433362019257020678406144
# p = --------------------------------------------------------------------
#     80658175170943878571660636856403766975289505440883277824000000000000
#
# gcd = 283982221662775934976, so
#
#       4610507544750288132457667562311567997623087869
# p = ------------------------------------------------
#     284025438982318025793544200005777916187500000000
#
# p = 0.0162327274671946, or about 1.62%.

use strict;

use Getopt::Std;
use Math::BigFloat;
use Math::BigInt;

my $verbose;

sub bfact {
    my $num = shift;
    return Math::BigInt->bfac($num);
}

# Compute N(S), as used in the PDF by Doyle, Grinstead, and Snell.
sub getN {
    my ($r, $m, $n) = @_;

    if ($r == 0) {
        return 1;
    }
    if ($r == 1) {
        return $m * $n;
    }
    my $result = 0;
    for (my $j = 1; $j <= $m - $r + 1; $j++) {
        $result += $n * getN($r - 1, $m - $j, $n - 1);
    }
    return $result;
}

# The kth element of the returned array is the coefficient of x^k.
sub getSquareRookPolynomial {
    my $dim  = shift;
    my @poly = ();

    for (my $j = 0; $j <= $dim; $j++) {
        print(".");
        push(@poly, getN($j, $dim, $dim));
    }
    return @poly;
}

# The kth element of a polynomial is the coefficient of x^k.
sub poly_pow {
    my ($power, $ref_poly_base) = @_;
    my @poly_base = @$ref_poly_base;

    if ($power == 0) { return (1); }
    if ($power == 1) { return (@poly_base); }

    my @poly_half = poly_pow(int($power / 2), \@poly_base);
    my @prod = poly_prod(\@poly_half, \@poly_half);
    my $parity = $power % 2;
    if ($parity == 1) {
        @prod = poly_prod(\@prod, \@poly_base);
    }
    return @prod
}

# The kth element of a polynomial is the coefficient of x^k.
sub poly_print {
    my @poly = @_;

    for (my $i = $#poly; $i >= 0; $i--) {
        print "$poly[$i]";
        if ($i > 0) { print " x^$i + "; }
    }
}

# The kth element of a polynomial is the coefficient of x^k.
sub poly_prod {
    my ($ref_poly_a, $ref_poly_b) = @_;
    my @poly_a  = @$ref_poly_a;
    my @poly_b  = @$ref_poly_b;

    my @product = (0) x ($#poly_a + $#poly_b + 1);
    for (my $i = 0; $i <= $#poly_a; $i++) {
        for (my $j = 0; $j <= $#poly_b; $j++) {
            $product[$i + $j] += $poly_a[$i] * $poly_b[$j];
        }
    }
    return @product;
}

sub vprint {
    my @args = @_;
    if ($verbose) { print @args; }
}

########## ########## ########## ##########
# Compute the odds of winning "frustration solitaire",
# given a deck with the specified number of suits and cards per suit.
sub main {
    getopts('v');
    our $opt_v;
    if ($opt_v) { $verbose = 1; } else { $verbose = 0; }
    ($#ARGV == 1)
        || die "\nusage: frustration [-v] num_suits num_cards_per_suit\n\n";
    my $suits = $ARGV[0];
    my $cps = $ARGV[1];
    $| = 1;

    vprint("Settings: $suits suits of $cps cards per suit.\n");
    print "Computing the rook polynomial for a $suits x $suits chessboard";
    my @rook1 = getSquareRookPolynomial($suits);
    print("\n");
    if ($verbose) {
        print "\t";
        poly_print(@rook1);
        print "\n\n";
    }

    print "Now computing that polynomail to the power $cps.\n";
    my $cards = $suits * $cps;
    my @rook2 = poly_pow($cps, \@rook1);
    if ($verbose) {
        print "( ";
        poly_print(@rook1);
        print " )^$cps = ";
        poly_print(@rook2);
        print "\n\n";
    }

    print "Computing the number of winning combinations for frustration solitaire.\n";
    my $allowed = 0;
    for (my $j = 0; $j <= $cards; $j++) {
        $allowed += ((-1) ** $j) * $rook2[$j] * bfact($cards - $j);
    }
    vprint("Done.\n");
    vprint("Allowed = $allowed\n");
    my $fact = bfact($cards + 0);  # "+ 0" works around a Perl bug.
    vprint("$cards! = $fact\n");

    # BUG: $percentage yields NaN for sizes 18x18 and above.
    my $percentage = Math::BigFloat->new(100.0) * $allowed / $fact;
    print "Probability of winning = $percentage%\n";
    if ($verbose) {
        my $limit = exp(-1 * $suits);
        print("Note: (1) Probability of winning approaches e^(#suits)\n");
        print("\twhen cards per suit >> #suits.\n");
        print("Note: (2) e^(-$suits) ~= $limit\n");
    }
}

main();
