#!/usr/bin/perl
# by Jay Coskey

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

# Note: In this implementation, the kth element of a polynomial is the coefficient of x^k.

use strict;

# use Carp::Assert;
use Getopt::Std;
use Math::BigFloat;
use Math::BigInt;

# my $verbose = 1;

sub bfact {
    my $num = shift;
    return Math::BigInt->bfac($num);
}

# Compute N(S), as used in the PDF by Doyle, Grinstead, and Snell.
sub getArrangementCount {
    my ($r, $m, $n) = @_;

    if ($r == 0) {
        return 1;
    }
    if ($r == 1) {
        return $m * $n;
    }
    my $result = Math::BigInt->new(0);
    for (my $j = 1; $j <= $m - $r + 1; $j++) {
        $result->badd($n * getArrangementCount($r - 1, $m - $j, $n - 1));
    }
    return $result;
}

sub getSquareRookPolynomial {
    my $dim  = shift;
    my @poly = ();

    for (my $j = 0; $j <= $dim; $j++) {
        push(@poly, getArrangementCount($j, $dim, $dim));
    }
    return @poly;
}

sub poly_pow {
    my ($ref_poly_base, $power) = @_;
    my @poly_base = @$ref_poly_base;

    if ($power == 0) { return (1); }
    if ($power == 1) { return (@poly_base); }

    my @poly_half = poly_pow(\@poly_base, int($power / 2));
    my @prod = poly_prod(\@poly_half, \@poly_half);
    my $parity = $power % 2;
    if ($parity == 1) {
        @prod = poly_prod(\@prod, \@poly_base);
    }
    return @prod
}

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

sub poly_str {
    my @poly = @_;
    my @result = ();

    for (my $power = $#poly; $power >= 0; $power--) {
        my $term = "";
        if ($poly[$power] != 0) {
            my $is_units = $power == 0;
            if ($poly[$power] != 1 || $is_units) { $term .= "$poly[$power]"; }
            if ($power > 0) {
                $term .= "x^$power";
            }
        }
        push @result, $term;
    }
    return join " + ", @result;
}

# ========================================

sub getFrustrationWinRawOdds {
    my $suits = shift;
    my $cps = shift;
    my $cards = $suits * $cps;

    my @suitPoly = getSquareRookPolynomial($suits);
    my @fullPoly = poly_pow(\@suitPoly, $cps);

    my $winning = Math::BigInt->new(0);
    for (my $k = 0; $k <= $cards; $k++) {
        $winning->badd(((-1) ** $k) * $fullPoly[$k] * bfact($cards - $k));
    }

    my $fact = bfact($cards + 0);  # "+ 0" works around a Perl bug.

    return ($winning, $fact);
}

# ========================================

sub arr_eq {
    my $ref1 = shift;
    my $ref2 = shift;

    my @arr1 = @{$ref1};
    my @arr2 = @{$ref2};

    if (scalar(@arr1) != scalar(@arr2)) {
        return 0;
    }
    foreach my $k (0 .. $#arr1) {
        if ($arr1[$k] != $arr2[$k]) {
            return 0;
        }
    }
    return 1;
}

sub pf_str {
    my $success = shift;
    return $success ? "passed" : "failed";
}

sub test_fact {
    my $tf0 = bfact(0) == 1;
    my $tf1 = bfact(1) == 1;
    my $tf2 = bfact(2) == 2;
    my $tf3 = bfact(3) == 6;
    my $tf4 = bfact(4) == 24;
    my $test_fact = $tf0 && $tf1 && $tf2 && $tf3 && $tf4;
    print("test_fact ", pf_str($test_fact), "\n");
}

sub test_poly {
    my @poly1 = getSquareRookPolynomial(1);
    my @poly2 = getSquareRookPolynomial(2);
    my @poly3 = getSquareRookPolynomial(3);
    my @poly4 = getSquareRookPolynomial(4);

    my @exp_poly1 = (1, 1);
    my @exp_poly2 = (1, 4, 2);
    my @exp_poly3 = (1, 9, 18, 6);
    my @exp_poly4 = (1, 16, 72, 96, 24);

    # print("poly1=", poly_str(@poly1), " - ", join(",", @poly1), "\n");
    # print("poly2=", poly_str(@poly2), " - ", join(",", @poly2), "\n");
    # print("poly3=", poly_str(@poly3), " - ", join(",", @poly3), "\n");
    # print("poly4=", poly_str(@poly4), " - ", join(",", @poly4), "\n");

    my $test_poly1 = arr_eq(\@poly1, \@exp_poly1);
    my $test_poly2 = arr_eq(\@poly2, \@exp_poly2);
    my $test_poly3 = arr_eq(\@poly3, \@exp_poly3);
    my $test_poly4 = arr_eq(\@poly4, \@exp_poly4);

    print("test_poly1 ", pf_str($test_poly1), "\n");
    print("test_poly2 ", pf_str($test_poly2), "\n");
    print("test_poly3 ", pf_str($test_poly3), "\n");
    print("test_poly4 ", pf_str($test_poly4), "\n");
}

# Note: If Math::BigInt is not used throughout, inaccuracy creeps in @ 4 suits, 9 cards per suit.
sub test_frust {
    my @tf_1_2 = getFrustrationWinRawOdds(1, 2);
    my @tf_1_3 = getFrustrationWinRawOdds(1, 3);
    my @tf_2_2 = getFrustrationWinRawOdds(2, 2);
    my @tf_3_3 = getFrustrationWinRawOdds(3, 3);
    my @tf_4_4 = getFrustrationWinRawOdds(4, 4);

    my @exp_1_2 = (1, 2);
    my @exp_1_3 = (2, 6);
    my @exp_2_2 = (4, 24);
    my @exp_3_3 = (12096, 362880);
    my @exp_4_4  = (Math::BigInt->new("248341303296"),
                    Math::BigInt->new("20922789888000"));

    my $test_frust_1_2 = arr_eq(\@tf_1_2, \@exp_1_2);
    my $test_frust_1_3 = arr_eq(\@tf_1_3, \@exp_1_3);
    my $test_frust_2_2 = arr_eq(\@tf_2_2, \@exp_2_2);
    my $test_frust_3_3 = arr_eq(\@tf_3_3, \@exp_3_3);
    my $test_frust_4_4 = arr_eq(\@tf_4_4, \@exp_4_4);

    print("test_frust_1_2 ", pf_str($test_frust_1_2), "\n");
    print("test_frust_1_3 ", pf_str($test_frust_1_3), "\n");
    print("test_frust_2_2 ", pf_str($test_frust_2_2), "\n");
    print("test_frust_3_3 ", pf_str($test_frust_3_3), "\n");
    print("test_frust_4_4 ", pf_str($test_frust_4_4), "\n");
}

sub test {
    $| = 1;
    test_fact();
    print("\n");
    test_poly();
    print("\n");
    test_frust();
}

# ========================================
# Compute the odds of winning "frustration solitaire",
# given a deck with the specified number of suits and cards per suit.
sub main {
    # getopts('v');
    # our $opt_v;
    # if ($opt_v) { $verbose = 1; } else { $verbose = 0; }
    ($#ARGV == 1)
        || die "\nusage: frustration num_suits num_cards_per_suit\n\n";
    my $suits = $ARGV[0];
    my $cps = $ARGV[1];

    $| = 1;
    my ($winning, $fact) = getFrustrationWinRawOdds($suits, $cps);

    # BUG: $percentage yields NaN for sizes 18x18 and above.
    my $percentage = Math::BigFloat->new(100.0) * $winning / $fact;
    print("For a deck with $suits suits and $cps cards per suit:\n");
    print("\tWinning combinations: $winning\n");
    print("\tTotal combinations:   $fact\n");
    print("\tPercentage probability of winning = $percentage\n");

    print("When cards per suit >> #suits, prob of winning --> e^(- #suits),\n");
    my $limit_percent = 100 * exp(-1 * $suits);
    print("\tand e^(-$suits) ~= $limit_percent %\n");
}

test();
print("\n");
main();
