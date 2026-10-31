# A unit gap between boundary squares forces an obtuse center angle

**Date:** October 30, 2026 UTC. **Status:** complete proposed hand
derivation, awaiting independent full review. All earlier frozen
angular and diagonal sources remain unchanged.

This gives a force-free boundary-pair theorem and a whole-cycle
consequence: the remaining alternating eight-body four-load family
is impossible in the compatible physical scope. Together with the
existing long-run angular theorem, every compatible eight-body cycle
with exactly four marked physical boundary bodies is excluded. No
torque equation or discrete transmitter orientation is used.

## 1. Geometric statements

Work in the full radius window

    79/40<=R<=sqrt(Q), Q=1105/256.

All squares below are actual unit squares contained in the disk
centered at O of radius R. A boundary square physically touches
the containing circle, whether or not it carries a selected load.

Put

    K=1/sqrt(2), B=13/32, A=K+B.

For a boundary square with center C, write e=C/|C| and let Je be
either consistently chosen perpendicular unit direction.

**Lemma 1 (two fixed interior points).** Both points

    P_+=A*e+B*Je,
    P_-=A*e-B*Je                                         (1)

belong to the square's open interior. The points are specified in
disk-centered coordinates, not relative to C.

**Theorem 2 (unit-gap angle).** If two physical boundary squares
S,T satisfy

    dist(S,T)>=1,

then their minor center angle is strictly greater than pi/2.
Equivalently, two boundary squares whose center directions make
a nonobtuse angle have set distance strictly less than one.

Their own frames may differ arbitrarily. Neither theorem uses
contact forces, actual application means, a graph, or a plane
embedding. The strict conclusion includes the right-angle endpoint.

## 2. Boundary-center bounds in the square's own frame

Let r=|C|. Every actual square center satisfies

    r<M=91/60,                                           (2)

because the farthest squared corner norm is at least
`r^2+r+1/2`, whose value at M exceeds Q by `31/57600`.
For a physical boundary square,

    r>=R-1/sqrt(2)>5/4.                                 (3)

The first inequality follows from its actual boundary corner, at
distance 1/sqrt(2) from its center. The second uses R>=79/40 and
`1/sqrt(2)<29/40`.

Reflect and exchange the actual square axes so that its radial
direction has own-coordinate components c,s, with

    c>=s>=0, c^2+s^2=1, 0<=s<=1/sqrt(2).

The physical boundary condition and farthest-corner formula give

    r^2+r(s+c)+1/2=R^2.

Completing the square, and using `(s+c)^2<=2`, yields

    r<=R-(s+c)/2<133/64-(s+c)/2.                         (4)

The last strict inequality follows from
`Q=17680/4096<(133/64)^2=17689/4096`.

Two elementary comparisons needed below are

    K>70/99,
    K+13/16>M,

because `(70/99)^2<1/2` and

    70/99+13/16-M=23/7920>0.                            (5)

Also `A<3/4+13/32=37/32<5/4<r`, since K<3/4. Thus the
radial inward displacement r-A is positive.

## 3. Exact proof that both fixed points are interior

Relative to C, the two points (1) have radial/transverse coordinates

    (-(r-A), +B), (-(r-A), -B).

Their two absolute own-coordinate deviations are at most

    F_1=(r-A)*s+B*c,
    F_2=(r-A)*c+B*s.

By (2),(5),

    F_1-F_2=(c-s)*(A+B-r)>=0.                           (6)

It therefore suffices to prove F_1<1/2. Equations (4),(5) imply

    F_1 <= G(s,c)
         :=(6113/6336)*s+(13/32)*c-(s^2+s*c)/2.          (7)

Here

    6113/6336=133/64-13/32-70/99.

The non-strict symbol in (7) is valid also at s=0; no endpoint
strictness needs to be extracted from that estimate. We prove
G<1/2 uniformly by two elementary cubic inequalities.

Throughout the interval,

    c<=1-s^2/2.                                         (8)

For any positive k with nonnegative `1-k*s^2`, squaring gives
`c>=1-k*s^2` whenever

    s^2 <= (2*k-1)/k^2.

In particular,

    c>=1-(5/9)*s^2  if 0<=s<=3/5,
    c>=1-(3/5)*s^2  if 0<=s<=1/sqrt(2).                 (9)

The relevant squared thresholds are 9/25 and 5/9, respectively.
All quantities squared are nonnegative.

### 3.1 The interval 0<=s<=3/5

Use the first lower bound of (9) in the positive term s*c and
the upper bound (8) in the negative term `-(13/16)*c`. From (7),

    1-2*G
      =1+s^2+s*c-(6113/3168)*s-(13/16)*c
      >=P(s):=3/16-(2945/3168)*s+(45/32)*s^2-(5/9)*s^3.
                                                               (10)

Set z=s-9/20. Exact expansion gives

    P(s)=467/140800-(47/31680)*z
          +(21/32-(5/9)*z)*z^2.                        (11)

Here `-9/20<=z<=3/20`, so the quadratic coefficient is at least
`55/96>0`, and |z|<=9/20. Therefore

    P(s)>=467/140800-(47/31680)*(9/20)
         =373/140800>0.                                 (12)

### 3.2 The interval 3/5<=s<=1/sqrt(2)

Use the second lower bound of (9) instead. The same calculation gives

    1-2*G>=H(s):=3/16-(2945/3168)*s+(45/32)*s^2-(3/5)*s^3.

This cubic is increasing on the whole interval. Indeed

    H''(s)=45/16-(18/5)*s
           >45/16-(18/5)*(3/4)=9/80>0,

since `1/sqrt(2)<3/4`, and the exact initial values are

    H'(3/5)=43517/396000>0,
    H(3/5)=2107/330000>0.                               (13)

Consequently H(s)>0 throughout this interval. Equations (10)--(13)
prove `G<1/2`. Together with (6),(7), this puts both own-coordinate
deviations of both points strictly below one half. They lie in the
actual square's open interior, proving Lemma 1. No square has been
reoriented; the own-frame reduction was only for this calculation.

## 4. The right-angle distance comparison

Let the two boundary center directions have minor angle theta in
[0,pi/2]. Rotate and, if necessary, reflect the disk frame so that
their angles are -theta/2 and theta/2. Choose the interior point
from each pair (1) that turns toward the other center direction:

    P=A*e_S+B*Je_S,
    Q=A*e_T-B*Je_T.

Their horizontal coordinates are equal. Their distance is exactly

    |P-Q|=2*|A*sin(theta/2)-B*cos(theta/2)|.               (14)

For t in [0,pi/4], the function

    f(t)=A*sin(t)-B*cos(t)

is strictly increasing, because `f'(t)=A*cos(t)+B*sin(t)>0`.
Its endpoint values are

    f(0)=-B=-13/32,
    f(pi/4)=(A-B)/sqrt(2)=1/2.

Thus `|P-Q|<=1` in (14), including theta=pi/2. Both points are
in open square interiors. If they are different, move P a sufficiently
small positive distance toward Q while remaining in S; this strictly
reduces the point distance. If they coincide, the set distance is
already zero. In either case

    dist(S,T)<1.                                        (15)

This proves Theorem 2 by contraposition. The proof includes arbitrary
independent square orientations and either actual boundary-corner mask.

## 5. Every nonempty common-normal run consumes more than a quarter turn

For an actual common-normal supported run from endpoint square S to
endpoint square T, with j internal unit squares, tight support
equalities give

    n.(c_T-c_S)=h_S(n)+h_T(n)+sum_internal 2*h_i(n).

For every actual x in S and y in T, this implies

    n.(y-x)>=sum_internal 2*h_i(n)>=j.

Hence

    dist(S,T)>=j.                                       (16)

If j>=1 and both endpoints physically touch the containing circle,
Theorem 2 applies: their minor center angle is strictly greater than
pi/2. This uses only the positive support widths; internal orientations
are completely free, and actual contact applications need not lie on
one line.

## 6. Complete compatible marked-cycle consequences

Use the same compatible physical marked-cycle scope as

`UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md`,

frozen SHA256
`b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.

Specifically, there is a simple cycle of actual bodies, at least two
marked physical circle-touching vertices, a common signed supporting
normal along each marked-to-marked run, and a compatible physical
embedding of that same actual graph. Its exact annular-order argument
preserves the marked boundary spokes and identifies marked cycle order
with actual center angular order, up to reversal. The successive
positive center angular gaps therefore sum to 2*pi, and each is at
least its endpoint minor angle.

**Corollary 3 (at most three nonempty runs).** At most three of the
marked-to-marked runs can have an internal body.

Otherwise four of the successive gaps would each exceed pi/2 by
(16) and Theorem 2, contradicting their total 2*pi. Any other gaps
are positive and do not weaken the contradiction.

**Corollary 4 (whole alternating four-mark family).** A compatible
marked cycle with four marked physical boundary vertices and one
or more internal bodies on each of its four runs is impossible.
In particular the entire eight-body alternating pattern

    (1,1,1,1)

is excluded. The result permits every internal orientation, both
side and diagonal transmitters, all actual endpoint means, and
arbitrary extra positive contacts at marked bodies.

**Corollary 5 (all eight-body four-mark cycles).** Every compatible
eight-body cycle with exactly four such marked vertices is impossible.
The frozen base theorem gives `m+ell<=8`, where ell counts runs
with two internal bodies, so an eight-body cycle has no such run.
All runs have at most two internal bodies by the center-span bound.
With four marks and four internal bodies, the absence of a two-body
run forces every run to have exactly one internal body. Corollary 4
then excludes it.

More generally, every compatible eight-body marked cycle requires at
least five marked boundary bodies. If it had at most three, the base
theorem's absence of long runs would give at most twice the mark
count, hence at most six bodies. Four marks are excluded above.

## 7. Full translational-stress caller and retained frontier

For a physical force-balanced stress, require every unmarked cycle
body to be unloaded and to have true positive degree two in the
whole same retained graph. Its full two-force equation makes the
incident forces equal and opposite, which propagates one common
signed support normal through each run. This supplies the premise
of (16) without a torque equation.

Marked bodies may have arbitrary true degrees, extra positive chords
or attachments, and arbitrary circle weights including zero. Their
physical boundary contact is required. The compatible drawing, true
degrees, unloaded predicates, normals and actual means all belong
to that same retained certificate. No external force is dropped to
manufacture a two-force internal body.

For an entire simple positive component with four positively
circle-loaded bodies, mark those four. The other bodies are unloaded
and have full degree two. In either the compatible translational
certificate or a compatible full force-and-torque certificate, the
base theorem excludes nine or more bodies, and Corollary 5 excludes
eight. Thus such an entire four-load simple component has at most
seven bodies.

The seven-body record orbit `(2,0,1,0)` has only two nonempty runs
and is retained. This source does not exclude every eight-body
cycle with five or more marks, arbitrary chorded blocks whose
circle-clear vertices have additional forces, or the remaining
seven-body side-short record family. It assigns no automatic
original coarse-row credit.

## 8. Verification boundary

Lemma 1 and Theorem 2 are self-contained geometric arguments. The
cycle corollaries use the frozen base's already stated compatible
annular-order join and true-degree caller. No hypothesis is moved
between different stress selections.

The exact cubic expansions, derivative values, radical comparisons
and rational margins were recomputed directly. This is a continuous
proof with no pose grid or numerical search premise. No Lean
compilation, CI run, original ledger mutation, metadata edit or
remote publication is asserted here.
