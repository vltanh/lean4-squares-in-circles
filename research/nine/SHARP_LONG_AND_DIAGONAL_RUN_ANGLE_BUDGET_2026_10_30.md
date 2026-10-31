# Long and diagonal runs sharpen the marked-cycle angular budget

**Date:** October 30, 2026 UTC. **Status:** complete proposed hand
derivation, awaiting separate full independent review. The frozen base
angular theorem is unchanged. No original case flag is changed here.

A support gap of two forces an endpoint angle greater than 175 degrees,
using the coupled endpoint-height estimate already proved for the
expanded-square cover. A single diagonal-width transmitter forces an
endpoint angle greater than 105 degrees. These two estimates exclude
both seven-body four-boundary cyclic placements of one long run and
one diagonal short run. They also allow at most one diagonal short run
in any eight-body cycle within the same compatible physical scope.

## 1. Geometric setting and literal inputs

Let actual unit squares have pairwise disjoint open interiors and lie
in a disk centered at O with squared radius at most

    Q=1105/256.

Put `M=91/60` and `L=89/60`. Every actual center has norm strictly
less than M, since its farthest squared corner norm is at least
`|c|^2+|c|+1/2`, and the latter expression at M exceeds Q by
`31/57600`.

For a unit square S with orthonormal side axes u,v, its support
halfwidth in a unit direction n is

    h_S(n)=(|n.u|+|n.v|)/2.

Two earlier complete sources are used at the following literal versions:

| Input | SHA256 |
| --- | --- |
| `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md` | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` |
| `UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md` | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` |

The first input supplies its complete coupled-height estimate, retaining
all endpoint tilts. The second supplies actual marked-center cyclic
order, the forty-degree boundary separation, and the eighty-degree
one-internal-body angle bound. The stronger angular estimates below do
not alter either input.

## 2. Any support gap of two gives more than 175 degrees

Suppose actual endpoint squares A,B have a signed unit direction n with

    n.(c_B-c_A)>=2+h_A(n)+h_B(n).                         (1)

Use the n-horizontal disk frame and write

    c_A=(-X_A,y_A), c_B=(X_B,y_B).

Sections 2--3 of the expanded-square source give

    X_A,X_B>L,
    |y_A|+|y_B|<=1/8.                                    (2)

This is a force-free implication of (1) and actual disk containment;
the endpoints need not touch the containing circle.

**Lemma 1 (long-gap angle).** The minor angle theta between c_A and
c_B satisfies

    theta>35*pi/36 =175 degrees.                         (3)

**Proof.** The two endpoint directions deviate from their respective
opposite horizontal axes by absolute angles

    alpha_A=atan(|y_A|/X_A),
    alpha_B=atan(|y_B|/X_B).

The deficit of the minor endpoint angle from pi is at most
`alpha_A+alpha_B`. By `atan(t)<=t` for t>=0 and (2),

    alpha_A+alpha_B < (1/8)/L=15/178.                     (4)

The inequality is strict when at least one transverse coordinate is
nonzero because both X values are strictly greater than L. If both
coordinates vanish, the left side is zero and the same strict bound
holds.

For an entirely exact comparison with five degrees, use

    pi>12*sin(pi/12)=3*(sqrt(6)-sqrt(2))
       >3*(22/9-10/7)=64/21.

Here `sin(x)<x` for x>0 gives the first inequality; the radical
comparisons follow from `6>(22/9)^2` and `2<(10/7)^2`.
Consequently

    pi/36>16/189>15/178,
    16/189-15/178=13/33642>0.                            (5)

Combining (4),(5) gives the strict conclusion (3). This includes
both transverse sign patterns and the exactly antipodal case. QED.

An actual common-normal run with two internal squares satisfies (1)
by support telescoping, since their widths are each at least one.
No torque equation or discrete width classification is needed for
this long-angle bound.

## 3. A diagonal-width short run gives more than 105 degrees

Suppose actual endpoint squares A,B have a signed unit support direction
n with

    n.(c_B-c_A)>=sqrt(2)+h_A(n)+h_B(n).                   (6)

Then their center distance is at least `1+sqrt(2)`.

**Lemma 2 (diagonal-gap angle).** Their minor center angle theta obeys

    theta>7*pi/12 =105 degrees.                          (7)

**Proof.** Both centers are nonzero: if one were zero their distance
would be less than M, contradicting (6). Suppose theta<=7*pi/12.
The exact trigonometric value and elementary radical bounds give

    cos(theta)>=cos(7*pi/12)=-(sqrt(6)-sqrt(2))/4
              >-13/50.                                 (8)

Indeed `sqrt(6)<49/20` and `sqrt(2)>141/100`, so their difference
is less than `49/20-141/100=26/25`. Both radical comparisons follow
by positive squaring.

Writing r,s for the endpoint center radii, with 0<r,s<M, yields

    |c_B-c_A|^2=r^2+s^2-2*r*s*cos(theta)
               <r^2+s^2+(13/25)*r*s
               <(63/25)*M^2
               =57967/10000
               =29/5-33/10000
               <29/5<3+2*sqrt(2)=(1+sqrt(2))^2.          (9)

The final radical comparison uses `sqrt(2)>7/5`. This contradicts
(6) and proves (7). QED.

A common-normal run with one internal square of actual width sqrt(2)
satisfies (6). The geometric implication uses its actual width; it
does not infer that width from translational balance alone.

## 4. The strengthened marked-cycle inequality

Adopt exactly the compatible physical marked-cycle hypotheses of the
frozen base angular theorem, including its radius window

    79/40<=R<=sqrt(Q).

There is a simple cycle of m distinct actual bodies. At least two
marked bodies physically touch the containing circle. Each marked-
to-marked run has a common signed actual support normal. The graph's
compatible physical embedding preserves the geometric sector order
of its actual center-to-contact drawing and the marked boundary
spokes. Marked bodies may have arbitrary additional edges.

As the base theorem proves, every run has zero, one or two internal
bodies. Let

* k_0 count direct runs;
* d count one-internal-body runs whose actual support width is sqrt(2);
* k_s count the other one-internal-body runs;
* ell count two-internal-body runs.

Thus

    m=k_0+2*k_s+2*d+3*ell.                              (10)

The k_s runs may have arbitrary smaller actual widths in the geometric
theorem. The notation does not assert a side-normal orientation.

The full actual annular-order join in the base source identifies
marked cycle order with actual center angular order. Its consecutive
positive angular gaps therefore sum to 360 degrees. The gaps for
the four run classes above are strictly larger than, respectively,

    40, 80, 105, 175 degrees.                            (11)

The first two entries are the unchanged base estimates; the last two
are Lemmas 2 and 1. A directed consecutive gap is at least its
minor endpoint angle, even when that directed gap exceeds pi.

**Theorem 3 (refined cycle budget).** The whole family satisfies

    40*m+25*d+55*ell <360,

or, equivalently as an integer bound,

    8*m+5*d+11*ell <=71.                                (12)

**Proof.** Sum (11), use the full-turn angular sum and (10), and
divide the strict integer inequality by five. QED.

The theorem includes actual boundary marks of zero selected circle
weight and every actual endpoint degree allowed by the compatible
cycle premise. It uses no new stress selection or force polygon.

## 5. Explicit full force-and-torque transmitter caller

For applying the diagonal count to a physical stress, keep one retained
physical force-and-torque certificate with its actual shared contact
means. Every unmarked internal body is unloaded and has true positive
degree two in that same full graph. This condition includes all its
positive contacts, rather than just the two displayed cycle edges.
The compatible physical embedding is for this same certificate.

Translational balance gives equal opposite pair forces and the common
signed normal along each run, as in the base theorem. At a one-body
run with internal square U, let p_-,p_+ be its two original physical
application means. Its zero moment equation then gives

    (p_+-p_-) cross n=0.

Opposite support equalities and positive width imply

    p_+-p_-=2*h_U(n)*n.                                  (13)

If one component of n in U's own orthonormal frame is zero, the
opposite support sets are parallel sides. Equation (13) equates the
transverse coordinates of the actual means, and the width is one.
If both components are nonzero, the opposite support sets consist
of uniquely exposed opposite vertices. Their difference has own-
coordinate magnitudes one and one. Parallelism with n forces
`|n.u|=|n.v|=1/sqrt(2)`, so the width is sqrt(2).

Thus the one-body runs of this full physical caller are exactly
side-normal width-one runs or diagonal-normal width-sqrt(2) runs.
Every latter run is counted by d in (12). The argument retains
arbitrary shared-side endpoint means and every physical circle mask.
No force or moment is removed from an endpoint with other incident
edges. A merely translational caller can still use the geometric
theorem whenever it directly establishes the actual width, but may
not infer this two-value classification without the moment equation.

## 6. Whole-family consequences and retained record

### 6.1 Both seven-body four-boundary cyclic orbits lose every diagonal short run

Consider a compatible seven-body cycle with four marked physical
boundary vertices and run-count multiset `{2,1,0,0}`. Up to rotation
and reversal, its two cyclic orders are represented by

    (2,1,0,0) and (2,0,1,0).

If the one-internal-body run has actual width sqrt(2), then m=7,
ell=1 and d=1. Equation (12) would require

    8*7+5+11=72<=71,

which is impossible. Equivalently its four consecutive angular
gaps would sum to more than `175+105+40+40=360` degrees.

This excludes both full diagonal-short cyclic placements
simultaneously, over all original physical means, load masks,
endpoint degrees and completing squares. In particular it applies
to an entire simple seven-body component with four positively
loaded bodies when that same retained force-and-torque certificate
has the compatible physical embedding.

The side-normal one-internal-body subfamilies remain beyond this
argument. The record-compatible opposite orbit `(2,0,1,0)` has
side width one, so d=0 and `8*m+11*ell=67<=71`; it is retained.

### 6.2 Every compatible eight-body cycle has at most one diagonal short run

The base theorem already rules out ell>=1 when m=8. Equation (12)
then gives

    64+5*d<=71,
    d<=1.                                               (14)

Thus any compatible eight-body marked cycle with two or more
diagonal-width one-body runs is impossible, independently of the
number of marks and the placement of those runs. For the remaining
eight-body four-load family `(1,1,1,1)`, at most one of its four
single transmitters may be diagonal in the full physical caller.
All endpoint means and other physical squares remain in scope.

### 6.3 General seven-body implication

Whenever m=7 and ell=1 in the compatible marked-cycle scope,
equation (12) forces d=0. Thus the diagonal exclusion is not limited
to four marks or to an isolated simple component. Additional
positive chords or attachments at physically boundary marked
vertices are allowed, as long as every unmarked caller body is
genuinely unloaded of full degree two.

## 7. Boundaries and verification

The long-angle lemma and diagonal-gap lemma are force-free geometric
implications. The cycle sum additionally requires the same actual
compatible embedding and marked-boundary order used in the frozen
base theorem. The discrete side/diagonal interpretation requires
the explicit full moment caller in Section 5. These roles are not
interchanged between independently selected certificates.

This source does not exclude the side-short seven-body record orbit,
all eight-body cycles, or arbitrary chorded nine-body blocks. It
does not declare an original coarse parent closed. All rational and
radical comparisons above were checked by exact arithmetic. No pose
sample, Lean compilation, CI run, finite search certificate, original
ledger edit, or remote publication is asserted.
