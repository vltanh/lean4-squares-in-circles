# Independent review of the long and diagonal marked-cycle angle refinement

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete frozen source below. No repair requested.**
This is a mathematical hand review, not a Lean or CI result and not an
original case-ledger mutation.

## 1. Literal source and reviewer scope

Reviewed the entire current file:

`SHARP_LONG_AND_DIAGONAL_RUN_ANGLE_BUDGET_2026_10_30.md`

- Size: 12,298 bytes.
- SHA256: `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc`.
- Git blob: `8b0138d3101318ec8dfe27c724b9bf3fbeb95beb`.

The reviewer authored the earlier base marked-cycle angular manuscript.
This is an independent reconstruction of the new refinement and its
callers, not a claim of independent authorship of that imported base.
The base itself has separate full root and axial reviews. The reviewer
also previously read and independently reviewed the complete expanded
endpoint-cover source, including its coupled-height lemma.

The two imported source versions are exactly:

| Input | SHA256 |
| --- | --- |
| Expanded endpoint cover | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` |
| Uniform marked-cycle budget | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` |

The review below follows the full proof and scopes, rather than treating
those earlier review summaries as proof substitutes.

## 2. Long-gap angle: all signs and exact five-degree comparison

The support-gap hypothesis supplies the unchanged origin-centered frame
with endpoint horizontal coordinates of magnitude greater than 89/60
and transverse absolute sum at most 1/8. These are literal conclusions
of the coupled endpoint-height source; endpoint circle contact and
torque are unnecessary.

For either transverse sign, the deficit of the minor endpoint angle
from pi is at most the sum of the two absolute deviations from opposite
horizontal axes. Each deviation is atan(|y|/X). Hence their sum is
strictly less than 15/178. When both y coordinates vanish the left side
is zero, so strictness still holds. No assumption that both endpoint
centers are above or below the channel has entered.

The displayed exact pi bound is sound:

    pi>12*sin(pi/12)=3*(sqrt(6)-sqrt(2))
       >3*(22/9-10/7)=64/21.

The first inequality is sin(x)<x at x=pi/12. The radical comparisons
have respective squared reserves 2/81 and 2/49. Dividing by 36 gives

    pi/36>16/189>15/178,
    16/189-15/178=13/33642>0.

Thus the endpoint minor angle is strictly greater than 175 degrees,
including the exactly antipodal configuration. A two-internal common-
normal run supplies the support-gap hypothesis using full actual widths
at least one. This part remains entirely geometric.

## 3. Diagonal-gap angle: complete radial and trigonometric bound

The diagonal-reserve premise gives endpoint center distance at least
1+sqrt(2). Neither endpoint can have zero center because M=91/60 is
smaller than that distance.

If the minor angle were at most 105 degrees, then

    cos(theta)>=-(sqrt(6)-sqrt(2))/4>-13/50,

using sqrt(6)<49/20 and sqrt(2)>141/100. Both comparisons follow by
squaring positive numbers. The center bound then gives

    distance^2<(63/25)*M^2
              =57967/10000
              =29/5-33/10000
              <29/5<3+2*sqrt(2).

The final step uses sqrt(2)>7/5. This contradicts the actual reserve.
The inequality uses arbitrary endpoint radii below M; it imposes no
equal-radius, aligned-frame, or radial-mask condition.

## 4. The complete marked-cycle sum and integer conversion

The source retains the full compatible physical marked-cycle premises
of the base theorem: physical boundary marks, actual signed normals,
the same true unmarked vertices, and the spoke-preserving embedding.
Its imported center-order proof gives one full turn, even with arbitrary
marked endpoint degrees, extra marked chords, or only two marks.

For direct, other one-body, diagonal one-body and long runs, the
respective strict angle costs are 40,80,105,175 degrees. With the
source's counts,

    m=k_0+2*k_s+2*d+3*ell,

their sum is exactly

    40*k_0+80*k_s+105*d+175*ell
      =40*m+25*d+55*ell<360.

Dividing by five gives an integer strictly below 72, equivalently

    8*m+5*d+11*ell<=71.

No angular gap was replaced by its minor angle with an incorrect
equality: each directed consecutive gap is at least its minor endpoint
angle, which is sufficient. The other one-body widths may be arbitrary
values smaller than sqrt(2) in the geometric scope.

## 5. Full force-and-torque caller

The diagonal interpretation is separated correctly from the force-free
geometric lemmas. For a genuinely unloaded true-positive-degree-two
body, full force balance makes its forces equal and opposite. Full
moment balance at the actual two contact means makes their difference
parallel to the common normal. Actual opposite support faces give the
positive width identity.

If the normal has one zero own-frame component, the supports are
opposite sides and the transverse means agree; the width is one. If
both components are nonzero, the supports are unique opposite vertices.
Their difference has own-coordinate magnitudes one and one, so
parallelism forces diagonal direction and width sqrt(2). The cases
are exhaustive, including all corner endpoints of side means.

The source does not transfer this classification to a merely
translational certificate. Extra forces on marked endpoints remain;
they are not used in the internal degree-two equations. All means and
all physical masks stay in the same retained certificate.

## 6. Family consequences and remaining scope

For m=7, ell=1 and d=1 the integer expression is 72, so the family is
excluded. The two dihedral cyclic placements of the count multiset
{2,1,0,0} are correctly represented by (2,1,0,0) and (2,0,1,0).
Thus every diagonal-short instance of both placements is covered,
without a side-contact-owner or fixed-mean exception.

For m=8, the base theorem first gives ell=0. The refined inequality
then gives 64+5*d<=71, hence d<=1. This is uniform in the marked load
count and cyclic placement, and includes the remaining four-load
alternating family (1,1,1,1).

The general m=7, ell=1 consequence also forces d=0 for any allowed
number of marks and any permitted marked attachments. The side-short
record orbit has d=0 and gives 67<=71, so it is preserved.

No whole seven-body block, all eight-body cycles, arbitrary chorded
nine-body component, or unrestricted nine-square lower bound is
claimed. The complete radius-window and compatible-selection premises
remain in place. No numerical pose search, compilation, new finite
certificate, remote write, or original ledger mutation was used in
this review.
