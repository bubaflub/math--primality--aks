#!/usr/bin/perl

use strict;
use warnings;

{
  package polynomial;

  use Math::GMPz;

  sub new {
    my $self = {};
    my $class = shift;
    my $construction_junk = shift;
    if ($construction_junk) {
      if(ref($construction_junk) eq 'ARRAY') {
        $self->{COEF} = $construction_junk;
        $self->{DEGREE} = scalar(@$construction_junk);
      } else {
        $self->{DEGREE} = $construction_junk;
        my @a = [];
        for (my $i = 0; $i < $construction_junk; $i++) {
          push @a, Math::GMPz->new(0);
        }
        $self->{COEF} = @a;
      }
    } else {
      $self->{COEF} = [Math::GMPz->new(0)];
      $self->{DEGREE} = 1;
    }
    bless($self, $class);
    return $self;
  }

  sub coef {
    my $self = shift;
    if (@_) { @{ $self->{COEF} }= @_ }
    return @{ $self->{COEF} };
  }

  sub degree {
    my $self = shift;
    if (@_) { $self->{DEGREE} = shift }
    return $self->{DEGREE};
  }

  sub getCoef {
    my $self = shift;
    my $i = shift;
    if ($i > $self->degree()) {
      return 0;
    }
    return ${ $self->{COEF} }[$i];
  }

  sub isEqual {
    my $self = shift;
    my $other_polynomial = shift;
    if ($self->degree() != $other_polynomial->degree()) {
      return 0;
    }
    for(my $i = 0; $i < $self->degree(); $i++) {
      if($self->getCoef($i) != $other_polynomial->getCoef($i)) {
        return 0;
      }
    }
    return 1;
  }

  sub setCoef {
    my $self = shift;
    my $new_coef = shift;
    my $index = shift;
    if ($index < 0) {
      die "coef is less than 0";
    }

    if ($index > $self->degree()) {
      for( my $j = $self->degree() + 1; $j <= $index; $j++ ) {
        push @{ $self->{COEF} }, Math::GMPz->new(0);
      }
      push @{ $self->{COEF} }, $new_coef;
      $self->degree($index);
    } else {
      ${ $self->{COEF} }[$index] = $new_coef;
    }
  }

  sub compact {
    my $self = shift;
    my $i = 0;
    LOOP: for ($i = $self->degree() - 1; $i > 0; $i--) {
      if (Math::GMPz::Rmpz_cmp_ui($self->getCoef($i), 0) != 0) {
        last LOOP;
      }
      pop @ { $self->{COEF} };
    }
    if ($i != $self->degree()) {
      $self->degree($i + 1);
    }
  }

  sub clear {
    my $self = shift;
    $self->{COEF} = undef;
    $self->{DEGREE} = undef;
    $self->{COEF} = [ Math::GMPz->new(0) ];
    $self->{DEGREE} = 1;
  }

  sub mpz_poly_mod_mult {
    my $self = shift;
    my ($rop, $x, $y, $mod, $polymod) = @_;

    $rop->clear();

    my $xdeg = $x->degree();
    my $ydeg = $y->degree();
    my $maxdeg = $xdeg < $ydeg ? $ydeg : $xdeg;

    LOOP: for(my $i = 0; $i < $polymod; $i++) {
      my $sum = Math::GMPz->new(0);
      my $temp = Math::GMPz->new(0);
      for(my $j = 0; $j <= $i; $j++) {
        Rmpz_add($temp, $y->getCoef($i - $j) + $y->getCoef($i + $polymod - $j));
        Rmpz_mul($temp, $x->getCoef($j), $temp);
        Rmpz_add($sum, $sum, $temp);
      }

      for(my $j = 0; $j < ($i + $polymod); $j++) {
        Rmpz_mul($temp, $x->getCoef($j), $y->getCoef($i + $polymod - $j));
        Rmpz_add($sum, $sum, $temp);
      }

      Rmpz_mod($temp, $sum, $mod);
      $rop->setCoef($temp, $i);

      if ($i > $maxdeg && Rmpz_cmp_ui($sum, 0) == 0) {
        last LOOP;
      }
    }

    $rop->compact();
  }

  sub mpz_poly_mod_power {
    my $self = shift;
    my ($rop, $x, $power, $mult_mod, $poly_mod) = @_;

    $rop->clear();
    $rop->setCoef(Math::GMPz->new(1), 0);

    my $i = Rmpz_sizeinbase($power, 2);

    LOOP: for( ; $i >= 0; $i--) {
      Rmpz_poly_mod_mult($rop, $rop, $rop, $mult_mod, $poly_mod);

      if(Rmpz_tstbit($power, $i)) {
        mpz_poly_mod_mul($rop, $rop, $x, $mult_mod, $poly_mod);
      }

      if($i == 0) {
        last LOOP;
      }
    }

    $rop->compact();
  }
  1
}

package main;

use Math::GMPz qw/:mpz/;
use Data::Dumper;

if (scalar(@ARGV) != 1) {
  print "Usage: aks.pl <number to test>\n";
  exit
}

my $n;
print "Math::GMPz version: $Math::GMPz::VERSION\n";
eval {
  $n = Math::GMPz->new($ARGV[0]);
  1;
} or do {
  print "Error converting ", $ARGV[0], "to a number\n";
  exit;
};
print "Running AKS with number $n\n";

if(Rmpz_perfect_power_p($n)) {
  print "$n is a perfect power.\n";
  exit;
}

my $r = Math::GMPz->new(2);
my $logn = Rmpz_sizeinbase($n, 2);
my $limit = Math::GMPz->new($logn * $logn);
Rmpz_mul_ui($limit, $limit, 4);

# Witness search

OUTERLOOP: while (Rmpz_cmp($r, $n) == -1) {
  if(Rmpz_divisible_p($n, $r)) {
    print "$n is divisible by $r\n";
    exit;
  }

  if(Rmpz_probab_prime_p($n, 5)) {
    my $i = Math::GMPz->new(1);

    INNERLOOP: for ( ; Rmpz_cmp($n, $limit) <= 0; Rmpz_add_ui($i, $i, 1)) {
      my $res = Math::GMPz->new(0);
      Rmpz_powm($res, $n, $i, $r);
      if (Rmpz_cmp_ui($res, 1) == 0) {
        last OUTERLOOP;
      }
    }

  }
  Rmpz_add_ui($r, $r, 1);
}
if (Rmpz_cmp($r, $n) == 0) {
  print "Found $n is prime while checking for r\n";
  exit;
}

# Polynomial check
my $a;
my $sqrtr = Math::GMPz->new(0);

Rmpz_sqrt($sqrtr, $r);
my $polylimit = Math::GMPz->new(0);
Rmpz_add_ui($polylimit, $sqrtr, 1);
Rmpz_mul_ui($polylimit, $polylimit, $logn);
Rmpz_mul_ui($polylimit, $polylimit, 2);

my $intr = Rmpz_get_ui($r);

for($a = 1; Rmpz_cmp_ui($polylimit, $a) <= 0; $a++) {
  print "Checking at $a\n";
  my $final_size = Math::GMPz->new(0);
  Rmpz_mod($final_size, $n, $r);
  my $compare = polynomial->new(Rmpz_get_ui($final_size));
  $compare->setCoef(1, Rmpz_get_ui($final_size));
  $compare->setCoef($a, 0);
  my $res = polynomial->new($intr);
  my $base = polynomial->new(1);
  $base->setCoef($a, 0);
  $base->setCoef(1, 1);

  mpz_poly_mod_power($res, $base, $n, $n, $intr);

  if($res->isEqual($compare)) {
    print "Found not prime at $a\n";
    exit;
  }
}
print "Is prime\n";