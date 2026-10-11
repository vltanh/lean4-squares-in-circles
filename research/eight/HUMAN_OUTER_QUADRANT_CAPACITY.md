# No three outer centers in any ninety-degree sector

**Theorem (unconditional geometric restriction at the n=8 ceiling).**
Let three pairwise interior-disjoint unit squares, with arbitrary
orientations, be contained in the disk of squared radius

    q_plus = 9789/2500.

If all three centers have distance at least one from the disk origin,
their center rays cannot lie in a closed angular sector of width
`pi/2`. Thus any such sector contains **at most two outer centers**.

In particular, in a packing of eight squares in this radius range,
if all seven exterior squares have outer centers, every generic
partition of the plane into four quadrants has center populations
`(2,2,2,1)` in some order. A quadrant boundary through a center
can be handled with the closed-sector assertion rather than by
assigning that center to an arbitrary side.

This is a hand proof using the sharp two-square common-point theorem,
with an explicit interior-margin refinement. It does not assume a
contact graph, parallel frames, a sevenfold symmetry, or a numerical
optimality certificate.

## 1. Constants and two previously proved facts

Put

    q0=5/2+sqrt(2),   t=pi/8,
    lambda=(2+sqrt(2))/3,
    eps=7/15000,      eta=1/500.

The prior proofs give two statements for any two disjoint squares
with centers of norm at least one at the stated radius ceiling:

* At `q<=q_plus`, their smaller center-ray separation is
  **strictly greater than `pi/4-eta`**
  (HUMAN_STABLE_OUTER_ANGLE.md).
* At `q<=q0`, every square whose center ray makes angle at most
  `t` with a direction `u` contains `lambda*u`.
  This is the sharp fixed-point theorem
  (HUMAN_SHARP_OUTER_PAIR_SECTOR.md), including the equality cases.

We also need the exact radial perturbation estimate used in the
first proof: for every square of center norm `r>=1` fitting
`D_sqrt(q_plus)`, one can move its center *alone* radially inward
by a vector of norm `<eps` to fit in `D_sqrt(q0)`, retaining
center norm greater than one, center direction and frame.

For completeness, write `L=cos(beta)+sin(beta)` for the sum of
the absolute center-frame direction cosines, `0<=beta<=pi/4`.
The farthest vertex squared norm is `r^2+rL+1/2`. Let
`m>5/4` solve `m^2+mL+1/2=q0`. If `r>m`,
the required inward translation is

    r-m <= (q_plus-q0)/(r+m+L)
        < (7/5000)/3 = eps.

If `r<=m`, no translation is necessary. The inequalities
`m>5/4` and `0<q_plus-q0<7/5000` were proved with
rational square comparisons in the sharp pair notes.

## 2. A uniform two-point depth lemma for the middle square

**Lemma.** Let a unit square S with center `(r,0)`, `r>=1`,
be contained in `D_sqrt(q0)`. Put

    w_minus=lambda*(cos(t),-sin(t)),
    w_plus =lambda*(cos(t),+sin(t)).

At least one of the two open disks

    D(w_minus,1/100),  D(w_plus,1/100)

lies entirely in the *open interior* of S. More precisely,
when its relative square-frame angle `alpha` lies in
`[0,pi/4]`, the first disk does; when
`alpha in [-pi/4,0]`, the second disk does.

**Proof.** Reflection makes it enough to treat
`0<=alpha<=pi/4`. Write

    c=cos(alpha),   s=sin(alpha),
    L=c+s,         m=m(alpha),

where `m` solves `m^2+mL+1/2=q0`, so `1<=r<=m`.
Relative to the square's orthonormal frame
`e=(c,s),f=(-s,c)`, the coordinates of
`w_minus-(r,0)` are

    A=lambda*cos(t+alpha)-r*c,
    B=-lambda*sin(t+alpha)+r*s.                       (1)

It suffices to prove

    |A|<49/100,   |B|<49/100.                          (2)

Then every displacement of norm at most `1/100`
has projection at most `1/100` on either frame
axis, so its sum with `w_minus-(r,0)` remains
strictly within `(-1/2,1/2)` in each coordinate.

Here are all the needed elementary constant bounds:

    lambda<23/20,         lambda*sin(t)>43/100,
    lambda*cos(t)>21/20,  1/sqrt(2)>7/10,
    1/sqrt(2)<5/7.                                    (3)

Each follows by substituting `sin(t)^2=(2-sqrt(2))/4`,
`cos(t)^2=(2+sqrt(2))/4` and squaring positive
rationals. For example,
`sqrt(2)>707/500` and `cos(t)>923/1000`
give `lambda*cos(t)>(1707/1500)*(923/1000)
=1575561/1500000>21/20`.
The remaining bounds, including `lambda*sin(t)>43/100`,
are established in HUMAN_SHARP_OUTER_PAIR_SECTOR.md.

For A above, use `r>=1` and `c>=1/sqrt(2)`:

    A <= lambda*cos(t)-c
      < 23/20-7/10=9/20<49/100.                      (4)

For A below, let

    H(alpha)=m(alpha)*c-lambda*cos(t+alpha).

The derivative calculation in section 2 of the sharp pair note
proves `H'(alpha)>0` throughout the full interval, without
sampled extrema. We sharpen its last endpoint estimate here.
The defining equation for m gives

    m(pi/4)<32/25,                                    (5)

since substituting `32/25` into
`m^2+sqrt(2)*m+1/2-q0` gives
`-226/625+(7/25)*sqrt(2)>19/625>0`.
Consequently, using (3),

    -A<=H(alpha)<=H(pi/4)
       =m(pi/4)/sqrt(2)-lambda*sin(t)
       <32/35-43/100
       =339/700<49/100.                              (6)

For B above, (1), `r<=m<=sqrt(2)`,
and `sin(t+alpha)=sin(t)c+cos(t)s` give

    B <= (sqrt(2)-lambda*cos(t))*s
       < (3/2-21/20)*s
       <=9/20<49/100.                                 (7)

For B below, use `r>=1`:

    B >= (1-lambda*cos(t))*s-lambda*sin(t)*c.

Cauchy--Schwarz bounds its negative by

    [ (lambda*cos(t)-1)^2
       +(lambda*sin(t))^2 ]^(1/2)
      = [lambda^2+1-2*lambda*cos(t)]^(1/2)
      < [ (23/20)^2+1-2*(21/20) ]^(1/2)
      =sqrt(89)/20<49/100.                            (8)

The final comparison is `89*25<49^2`, namely
`2225<2401`. This proves (2) and the closed
disk margin. Reflection handles `alpha<=0`. QED.

## 3. No three center directions fit in a quadrant

Suppose three such squares have center-ray arguments
`theta1<theta2<theta3` inside one angular sector
of width at most `pi/2`. These strict inequalities
hold because the already proved pair gap is positive.

Put `delta1=theta2-theta1` and
`delta2=theta3-theta2`. The stable pair theorem gives

    delta1,delta2 > pi/4-eta,
    delta1+delta2 <= pi/2.

Therefore each lies strictly below `pi/4+eta` too:

    |delta_i-pi/4|<eta.                                (9)

Rotate to make the middle center ray horizontal,
so `theta2=0`.

Perform the individual inward perturbations of
section 1 to copies `S1^0,S2^0,S3^0` in
`D_sqrt(q0)`. These copies are **not** asserted
pairwise disjoint; we only use individual containment
and their known translation vectors of norm `<eps`.

By the depth lemma, the middle copy `S2^0`
contains a full open disk of radius `1/100`
around one of the two points `w_minus,w_plus`.
Thus the original middle square `S2` contains
the open disk around that point of radius
`1/100-eps`.

If the selected point is `w_minus`, use the
first square `S1^0`. The fixed-point theorem
applies at the direction `theta1+t`, exactly
angle `t` from its center ray, and gives

    z=lambda*(cos(theta1+t),sin(theta1+t)) in S1^0.

By (9), `theta1+t` differs from `-t` by less
than eta. Chord length does not exceed arc
length, so

    |z-w_minus|<lambda*eta.

Translating `S1^0` back to its original position
produces a point `z'` in the original closed
square S1 with

    |z'-w_minus| < lambda*eta+eps
                < 1/100-eps.                           (10)

Indeed `lambda<23/20`, so the necessary comparison is

    lambda/500+2*eps
      <23/10000+14/15000
      <1/100.

Thus `z'` belongs to the *open interior* of the
middle square S2, while also belonging to S1.
Any open neighborhood of a closed-square point
meets that square's open interior; hence S1 and
S2 have overlapping interiors, a contradiction.

If the selected point is `w_plus`, use the
third square `S3^0`, applying the fixed-point
theorem at direction `theta3-t`. By (9) that
direction is within eta of `+t`; the same
estimate (10) produces an interior overlap
of S2 and S3.

Both cases contradict disjointness. Therefore
a closed sector of width pi/2 cannot contain
three outer center rays. QED.

## 4. What this does and does not classify

The theorem applies to squares with center norm
at least one. An exterior square with center norm
less than one is **not** covered; the known
tilted candidate contains such a square.

For all seven exterior centers outer, this gives
a clean center-ray `2,2,2,1` quadrant occupancy
(up to permutation) for any generic rotation,
without relying on a numerical marker-ring
certificate. It does not assign whole squares
to the four central side caps, does not force
parallel frames, and does not prove the five
projected inequalities of the sharp candidate.

The unrestricted lower bound `R8>=Rhat`
remains open; the theorem removes triple-outer
quadrant clusters but does not eliminate
seven-outer cycles or inner-attached outer paths.
