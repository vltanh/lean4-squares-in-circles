# A strict central-near occupancy law for actual projection chains

November 3, 2026. Complete elementary hand consequence. This note does
not promote a cone comparison to an actual projection comparison.

Let `0<h<1/2`, and call an actual unit square *near* when it meets the
open disk of radius h about the containing-circle origin. For a unit
direction e, write `x_S=e·c_S` and

`H_S=(|e·u_S|+|e·v_S|)/2>=1/2`.

An actual projection comparison `P<_e S` means

`x_S-x_P>=H_P+H_S`.

Every near square has the strict projection bounds

`-h < x_S+H_S`, and `x_S-H_S < h`.

They follow by projecting an actual point of S inside the open h disk.
The same physical frame supplies both support values.

## 1. Near neighbors force an exact center-side condition

If `P<_e S` and S is near, then

`x_P+H_P <= x_S-H_S < h`,

so `x_P < h-H_P <= h-1/2`.

If `S<_e P` and S is near, then

`x_P-H_P >= x_S+H_S > -h`,

so `x_P > H_P-h >=1/2-h`.

Thus any original P with `|x_P|<=1/2-h` has **no near original that is
actually projection-comparable with P in this direction**. Weak equality
in the actual separator is retained; the strictness comes from meeting
the open central disk.

At `h=23/100`, the threshold is exactly `27/100`. Consequently, for an
actual short chain `E<_e F<_e G` with `|x_F|<=27/100`, both E and G are
non-near. This is stronger than an independent center-radius test in some
original boxes. It uses actual links, so it cannot be transferred to a
weak consecutive link of another mask without a new proof.

## 2. A near set has actual projection height at most two

Suppose `A<_e B<_e C`, with A and C both near. Adding the two actual
comparisons gives

`x_C-H_C >= x_A+H_A+2H_B > -h+1`.

But nearness of C gives `x_C-H_C<h`. These are incompatible because
`1-2h>0`. Therefore the endpoints of an actual three-chain cannot both
be near, regardless of whether its middle original is near.

In any actual projection chain, at most two members can be near, and if
two are near they are consecutive. At `h=23/100`, the contradiction has
the strict interval gap `1-2h=27/50`.

The reviewed all-nine arc theorem supplies at least two near originals
at `Q=1105/256`. Combining that global count with this local law produces
an exact occupancy restriction in any chosen actual projection order.
It does not itself supply a common projection cover or an actual four-chain.

## 3. Short exact terminal for the verified f14 parent

In the complete `negative-f14f5bc4eafdf50d` parent state, the independently
replayed coordinate bound is

`x_F >= -57689/262144`.

The existing mask also supplies the actual F-to-G comparison, and the
physical square width gives `H_F>=1/2`. If G were near, Section 1 would
require `x_F+H_F<h`, but

`x_F+H_F-h >=27/100-57689/262144`

`=327247/6553600 >0`.

This is an exact four-row contradiction. In the existing 54-variable
convention, sum the following inequalities with weights `1,1/2,1,1`:

1. `-x_F <=57689/262144`;
2. `-alpha_F-absbeta_F <=-1`;
3. `x_F-x_G+(alpha_F+absbeta_F+alpha_G+absbeta_G)/2 <=0`;
4. `x_G-(alpha_G+absbeta_G)/2 <=23/100` (necessary under G near).

Every variable cancels, leaving

`0 <= -327247/6553600`.

The stronger exact terminal does not need F itself to be near. In the
full central-cover argument F is separately proved near by its whole
center box, so it excludes the complete `{F,G}` alternative.

The bound `x_F<=17/64` similarly excludes E being near under the actual
E-to-F comparison, since

`27/100-17/64=7/1600>0`.

These exclusions preserve every other central-pair alternative. They do
not close f14: the complete remaining `{F,B}`, `{F,C}`, `{F,H}`, `{F,I}`
cases remain open in the tested relaxation. No original or mask status
is changed by this local occupancy law.
