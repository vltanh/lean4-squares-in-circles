# Independent full review of both aligned-endpoint return-wrapper proofs

Date: October 30, 2026 UTC. Reviewer: axial_chain continuation.

**Result: PASS for both complete frozen sources, no repair identified.**

| Source | Bytes | SHA256 |
| --- | ---: | --- |
| `ALIGNED_ENDPOINT_CORNER_WRAPPERS_OBEY_THE_UNEQUAL_FLOOR_SECTION_BOUND_2026_10_30.md` | 10936 | `55607f2ab5a25c056fcc12e893b3d4c7e60814c6d2e607c21b806277d29de5bc` |
| `OBLIQUE_ALIGNED_ENDPOINT_RETURN_SECTION_BOUND_BY_ACTUAL_UPPER_CORNER_TANGENT_2026_10_30.md` | 15777 | `a43df2c0bdf368d43c5858829e9a5594b8ac202fcfcf5b59e10d9282f8572bea` |

I read both entire sources and reconstructed every local geometry,
contact-type, section-existence and endpoint-inequality argument.
The two proofs use different final corner estimates and are not merely
two checks of the same displayed polynomial. I independently derived
the common wrapper parametrization and its two section candidates before
reading the frozen sources. This review then checks their exact final
statements and bytes, including their different physical hypotheses.

## 1. Literal actual scope and nonempty sections

The right aligned endpoint is
B=[x,x+1] times [f-1,f], with x in (59/60,61/60) and
f in [3/8,1/2]. Its actual outer-lower corner supplies
(x+1)^2+(1-f)^2<=q; equality holds when B is physically boundary.
It follows directly that q>15061/3600>4, so neither proof needs
an inherited lower-radius window for its local result.

For an inward return own axis n=(-alpha,beta), perpendicular axis
u=(beta,alpha), and actual supporting-side point p=(x,f), the
closed-side chart is p+[0,1]n+[r-1,r]u. The alternative slider
in the block source is exactly its change of variable r to1-r.
Every original side endpoint is retained in the annular statement;
the block statement uses a genuine side-interior r in (0,1) only
after proving the complementary vertex-contact alternative.

The annular proof of section existence is valid even without a whole
positive-height premise on C. If its top were at most5/4, then
beta<=7/8, alpha>=sqrt(15)/8>7/16, and the rightward reach is
less than7/16. Its whole horizontal extent lies strictly between
-1/2 and3/2, and its heights lie between-5/8 and5/4. Every corner
then has squared norm below61/16<4<q, contradicting actual
physical circle contact. Its bottom is already below5/4.

The block proof uses its stronger declared whole-C premise y>0 to
improve the rightward reach to2/5, hence x<17/12. Its resulting
corner bound257/72 is below the actual q by at least the displayed
strict reserve737/1200. The comparison
49/(32sqrt(15))<2/5 is exactly60025<61440. Both existence
arguments are complete on the whole slider and angle domains. They
do not treat a formal edge formula as proof that a section exists.

## 2. Annular source: both candidates and exact square expansion

Solving the actual own-coordinate inequalities gives exactly

    ell_1=x+(r-1-alpha*k)/beta,
    ell_2=x+(beta*k-1)/alpha,
    k=5/4-f,

with the actual left endpoint their maximum. The contained corner
P=p+r*u+n gives beta*ell_1=u.P-1-alpha*(5/4) and
n.P=1-alpha*x+beta*f. I checked the exact identity

    [1+alpha*z+beta*d]^2+[1-alpha*x+beta*f]^2-Q
       =alpha*{2(z-x)+2(zd-xf)beta
          +alpha[z^2+x^2-d^2-f^2-2(d+f)/(1+beta)]},

where d=g(f+1)-1. It follows directly from
beta-1=-alpha^2/(1+beta) and (d+1)^2+(f+1)^2=Q.
The first term exceeds7/15, the mixed coefficient is at least37/960,
and the remaining bracket exceeds-3/16. Thus the braces exceed
67/240. The stated reserve1471/57600 in the bracket is exact.
The comparison square root is defined by the original corner; its
other side is positive. The resulting strict ell_1 bound is valid
without any sign assumption on n.P.

For ell_2, the actual endpoint corner supplies
x+1<=g(1-f). The sum g(1-f)+g(1+f) decreases throughout the
floor interval and exceeds55/16>24/7. Therefore

    0<x+1-g(1+f)<7f/6.

The convex quadratic (7f/6)^2+(5/4-f)^2 has exact endpoint
values245/256 and65/72. Cauchy's inequality with the original
unit pair (alpha,beta) now gives the strict ell_2 bound. This
closes both candidates over the entire angular domain, including
their shared active-edge endpoint and both closed support-side limits.

## 3. Block source: independent opposite-edge and tangent arguments

The block source derives the same two possible left endpoints by
maximizing the inward normal coordinate. Its opposite-face bound
ell<=x-sqrt(1-k^2) follows from the exact nonnegative square
(beta-k)^2, with both quantities before squaring positive.

The function
g(h+1)+sqrt(1-(5/4-h)^2) increases on [3/8,1/2], because its
derivative sign reduces by positive squaring to
Q(5/4-h)^2>(h+1)^2. Its lower endpoint exceeds 163/80,
while x+1<121/60. The resulting strict margin is 1/48, as stated.

For the other edge, the contradictory section inequality gives the
unchanged slider bound r<=r0=beta*d-alpha*k. It consequently
forces alpha/beta<4/5 and beta>3/4 on the whole hypothetical
failure domain. The actual upper corner Z remains unchanged when
the auxiliary comparison point Z0 is introduced.

I expanded the full tangent identity independently. With
z0=(A0,B0), K=x+1, d=K-A0, k=9/4-B0, it is exactly

    (z0.Z0-Q)/alpha
       =(B0-A0)+(9A0/4-B0*K)beta
        +alpha[A0*K+9B0/4-Q-(A0+B0)/(1+beta)].

The beta coefficient is at least67/320. The entire first term
is greater than281/1280, using the negative B0 coefficient with
its upper bound. The concave one-variable function J(B0) has the
two displayed endpoint bounds11929/6400 and7333/3840, both
above37/20. Since A0+B0<3 and beta>3/4, the last bracket
exceeds19/140. Hence z0.Z>Q for an actual contained corner,
contradicting Cauchy's inequality. All comparison points and every
original slider role are explicitly distinguished in the proof.

## 4. Complete physical contact cover and normal ownership

Both sources reconstruct the inner-face exclusion with its actual
boundary-neighbor hypothesis. Here kappa=x+1, ell0=1-f,
kappa-ell0=x+f>1, and ell0>=1/2; all original shared-side and
endpoint contacts meet the literal face lemma. Its adjacent-corner
and opposite-corner norm bounds are strict throughout.

The annular normal-cone proof is correct: two intersecting closed
angular intervals of equal length90 degrees contain at least one
endpoint of the first in the second, after choosing overlapping
lifts. At a C vertex this yields a common vertical-up or
horizontal-left supporting axis. The latter is physically forbidden
by the inner-face lemma; the former puts the entire original C above
f. This geometric auxiliary axis is not substituted into the original
stress or torque equation. A side-interior contact has its unique
actual own-axis common normal and gives precisely the wrapper chart.

The block source supplies the corresponding tangent-cone proof and
the extra strictness fact: with an original strictly oblique normal,
an allowed above-floor vertex return cannot be axis aligned. An
axis-aligned northeast corner cannot minimize that original normal;
the northwest choice lies in the forbidden inner halfplane. Thus
the existing strict above-floor section theorem applies in this
entire complementary oblique-return branch as well.

## 5. Exact join boundary

Both local proofs supply the one-sided section estimate needed at a
right aligned endpoint, and reflection gives the corresponding right
endpoint estimate at a left endpoint. They preserve original physical
circle masks, side means, actual support points and all completing
units. The block caller uses the established whole-return-square
positive halfplane exactly where it is declared; the annular local
proof has the weaker scope stated above.

Neither source alone claims that the return sections have the needed
left-to-right order or that an arbitrary seven-cycle has the required
endpoint heights. Those remain assembly hypotheses. For the actual
long-endpoint pair, the order can be justified without another angle
lemma: whole C has x>59/60-sqrt(2)>-1/2 and whole D has
x<1/2 by their actual upper-side contact points and unit diameter.
The reversed section order would have gap less than1, contradicting
an actual set-distance lower bound1. This is a literal additional
join, not an order assumption imported into either local proof.

The entire review used exact continuous arguments and rational or
radical identities. No numerical pose observation is a premise or
verification substitute. No frozen source, original proof gate or
metadata was modified; no Lean compilation, CI or publication was
performed by this review.
