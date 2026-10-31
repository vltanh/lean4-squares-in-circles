# Full independent review: H3.L0124 non-hub-owned side or radial endpoints

Date: October 28, 2026. Reviewer: rooted_blocks.

**Disposition: ACCEPTED, unchanged, at the complete owner/mask scope
stated in the source.** I independently read the whole new source,
the original graph/load cover, the complete balanced-path and physical
moment arguments, the physical embedding and angular-order inputs,
the inward-segment proof, the full operative loaded-two properness
lemma, and the complete old fan endpoint calculation. I re-derived
the new three-force endpoint grouping, the replacement for the old
universal-hub estimate, both endpoint coordinate bounds, and the
final diagonal contradiction. No correction is requested.

The exact reviewed source is

`INNER_PENTAGON_H3_0124_NONHUB_OWNED_OR_RADIAL_ENDPOINTS_EXCLUSION.md`

SHA-256

`c72a8bc51f9c76bd5b6c2d44ad05b6e96f5c8807aab257c27baef8f5a15d5c44`.

This is not an acceptance of the entire H3.L0124 load family or its
graph parent. The source retains the unique-physical-corner free
endpoint cases outside its hypotheses. Root review, any second review
required for another source, and accounting remain separate.

## 1. Original graph, loads, and all actual forces

The original exterior cycle is 0--1--2--3--4--0, and the interior
body H has precisely the spokes H0,H1,H3. The positive rim loads
are exactly {0,1,2,4}. The source's relabeling is literal:

| Local name | Original name | Positive degree | Circle load |
| --- | --- | --- | --- |
| K | 3 | 3 | Zero |
| E1 | 2 | 2 | Positive |
| E2 | 1 | 3 | Positive |
| E3 | 0 | 3 | Positive |
| E4 | 4 | 2 | Positive |
| H | H | 3 | Zero |

The eight positive edges become the actual path E1--E2--E3--E4,
the two contacts K--E1 and K--E4, and H--E2,H--E3,H--K.
The reflection i -> 1-i modulo five preserves the graph, this load
set, K, and H, and exchanges the two endpoint roles. I checked these
facts directly from the integer-labeled original graph as well as
from the full load-cover source.

No inner spoke is deleted. K and H retain degree three, E2 and E3
retain degree three, and only E1 and E4 receive the true loaded-two
equations. The original six-body component and all three remaining
physical squares stay in the packing. A zero circle load is not
converted into a physical clearance statement, apart from H's
already established interior-body geometry.

The whole radius window is 79/40 <= R <= sqrt(1105)/16. The theorem
does not silently use the later same-nine R>2 strengthening.

## 2. Literal input audit

I verified all eight source-table SHA-256 values against current full
files. Their operative uses are as follows.

| Input | Exact pin | Scope checked |
| --- | --- | --- |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434 | H3 graph, whole L0124 load set, degrees and reflection |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708 | Balanced original four-boundary path; every endpoint mean; exact contact-angle bounds |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a | Full degree-free physical orientation of every actual boundary-edge moment |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 0d61292a0aa57084b88b4a72754fc78e123e8b684dac09be966fb074ab58e877 | Lemma 2.1 at each true loaded-two endpoint with its actual boundary-path neighbor |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | 6154eee2ab1114d063b0dbd1a2800c3522cbb1b46ec44a258c1c89d8ffb9e975 | Only the radius-free inward unit-segment lemma, with the correct inward sign |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | 2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449 | Physical center annulus, ordered touching pairs, distinct circle points and corner/resultant order |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a | Selected plane embedding and actual tangent-sector routing, including weak junctions |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | 32dcd0afd0883e4272e95b26278d8c90af0c02639b522fd5c960941bb34dba02 | Only the reproduced endpoint coordinate calculation and final scalar comparison |

The old fan's universal contact-to-hub radius estimate is absent from
the new proof. Its four-force hub equation is also absent. The new
source supplies the needed K geometry using the original K3 equation
and the actual inward segment in each endpoint square.

The properness lemma retains every physical circle mask and does not
place a two-corner endpoint's concurrence inside its square. Its
nonparallel premise is proved by the whole lemma, using the actual
boundary neighbor E2 or E3. Neither H nor K is used as a fictitious
boundary neighbor for that purpose.

## 3. Opposite actual K ports and the inner-spoke grouping

Summing the complete six-body force equations cancels all eight pair
forces and gives F1+F2+F3+F4=0. Each Fi is the full nonzero
positive-total circle resultant. The balanced path theorem therefore
puts every actual pair of endpoint applications on K at distance
greater than one. Since neither normal is K-owned, both applications
are actual K vertices; they are opposite vertices.

With sigma=1/sqrt(2), the source writes these unchanged points as
p1=(x-sigma,h), p4=(x+sigma,h). Rotations and reflections change
coordinates only and leave the original circle origin fixed.

The actual exterior face is K,E1,E2,E3,E4,K. The H spoke uses the
interior K arc, which can be chosen to be the lower arc. This is
justified by the physical selected embedding, not merely by drawing
the abstract graph. A coincident HK application at either endpoint
retains its ordered inward tangent sector. The compatible junction
perturbation preserves that sector order and avoids the real circle
spokes.

I independently recomputed the two determinant signs on both lower
K sides, their full mean intervals, and the bottom-vertex normal cone:

    det(P-p1,n) <= 0,       det(P-p4,n) >= 0.

For example the lower-left side gives -t and 1-t exactly. The lower-
right side and the entire bottom cone have the same signs.

If HK is separate from the endpoints, K's moments about p4 and p1
immediately give nonnegative vertical components for n1 and n4. If
HK coincides with p1 or p4, the moment first constrains the full group
at that endpoint. Within the left vertex cone, the sine decreases
along the actual lower-arc order, so n1 has at least the later
HK vertical component. Within the right cone the last normal n4
has at least the earlier HK component. A nonnegative positive-weight
group component then implies the claimed nonnegative endpoint
component. This explicitly retains the extra positive HK force.

Together with the original K vertex cones this proves

    n1=(-b1,a1), n4=(b4,a4),
    0 <= ai <= bi, ai²+bi²=1, bi >= sigma.

The weak bounds enlarge, rather than shorten, the non-K-owned
normal cones. The genuine side-axis boundary is not secretly used
as a free selected vertex normal.

The same exterior/spoke order places the actual boundary path in
counterclockwise circle order. The degree-free boundary-moment
theorem and the unchanged two endpoint moments yield

    det(p1,n1)>0,       det(p4,n4)<0.

No degree-two torque equation is assigned to E2 or E3.

## 4. The new inward-segment replacement is complete

For the actual endpoint E_i, its inward direction is n_i, because
n_i points from K into E_i. Thus the full segment
p_i+[0,1]n_i belongs to E_i by the radius-free segment lemma.

If x >= sigma, the original point p4+n4 has first coordinate at
least 2sigma+b4 >=3/sqrt(2)>R. The reflected argument handles
x <= -sigma. This proves the strict whole interval

    -sigma < x < sigma,
    X1=sigma-x>0, X4=sigma+x>0, X1+X4=sqrt(2).

The exact squared reserve is 47/256. No contact between H and
an endpoint, or between K and E2/E3, was assumed.

The endpoint moment now reads b1*h-a1*X1>0, hence h>0. The
right endpoint has the corresponding strict reflected moment.
Properness gives q_i=p_i+ell_i*n_i with ell_i>=0 and a positive
scalar multiple of F_i. Both left q and F are strictly upper-left;
both right q and F are strictly upper-right. The case ell_i=0
and every radial weight endpoint are included.

## 5. The complete side-owned endpoint estimate

For the left endpoint the actual frame is

    P=(-X,h), n=(-b,a), k=(-a,-b),
    E=P+[0,1]n+[-rho,1-rho]k,
    N=bX+ah>0, K0=bh-aX>0.

The proof allows the enlarged full interval 0<=rho<=1. The real
normal is still the original endpoint axis. Properness makes the
circle resultant's k component strictly negative. Since the center's
n coordinate is positive, its physical circle corners lie on the
outer n face. Its k coordinate cannot be positive. Therefore, with
Z=K0+rho>=1/2, the full physical mask obeys

    R²=(N+1)²+Z²,
    c_E=(N+1/2)n-(Z-1/2)k,
    X=bN-aK0 >= bN-aZ.

At Z=1/2 both physical circle corners are retained. Their weights
need not be equal; one can be zero. This mask argument is physical
and uses only the sign of their full positive-total resultant.

I checked the center's strict negative horizontal coordinate and
nonnegative vertical coordinate directly. Writing it as
(-r*cos(delta),r*sin(delta)), and phi=atan(a/b), gives
0<=phi<=delta<pi/2 and the displayed own-frame circle equations.

Let d=sqrt(R²-1/4)-1 and r0=d+1/2. For v=delta-phi the exact
identity is

    (r0-r)(r0+r+1)=r*(cos(v)+sin(v)-1).

The complete physical center bound gives r<=r0. With v>=0 and,
at the point where the estimate is used, v<pi/6, this implies
r>=r0-sin(v)/2; v=0 is included by equality. Substitution into
X>=r*cos(delta)-(cos(phi)+sin(phi))/2 gives the source's
parenthesized expression. I re-expanded it as

    (1+sin(delta)*cos(delta))*cos(phi)
                         +sin(delta)²*sin(phi).

Cauchy--Schwarz bounds this by sqrt(1+2sc+s²). Both compared
quantities are nonnegative, and their squared comparison with
c+(6/5)s has exactly the remainder (2/25)s(5c-7s).
The eventual delta<pi/6 makes this nonnegative. Thus the entire
side-owned endpoint has

    X >= d*cos(delta)-(3/5)*sin(delta).

The source derives the needed angular interval later from the whole
physical path, before using this inequality in the final comparison.
There is no circular premise or restriction to a chosen endpoint
frame.

## 6. A genuinely free radial endpoint and all its weight endpoints

If the endpoint does not own the normal but has two physical circle
corners, it is the actual radial S square [d,d+1]e+[-1/2,1/2]k.
The free contact cannot be on a circle corner, so it is an inner
vertex P=d*e+epsilon0*k/2. Strict exposure gives inward normal
A*e-epsilon0*B*k with A,B>0. Its exact origin moment is
-epsilon0*(dB+A/2). The positive left moment forces epsilon0=-1.

This conclusion uses no equal-weight radial resultant. The physical
radial axis e need not be the full circle-resultant direction.

The angular lifts are valid: the K cone places arg(n) between
3pi/4 and pi; arg(e)=arg(n)-atan(B/A) lies between pi/4 and pi.
The actual P direction is arg(e)-atan(1/(2d)). Its lift stays
between -pi/4 and pi, so its already proved strict upper-left
position forces arg(e)>pi/2. Hence the physical center has the
required upper-left form, with 0<delta<pi/2.

The unchanged inner vertex then gives exactly

    X=d*cos(delta)-(1/2)*sin(delta),

which is stronger than the same 3/5 bound. Reflection supplies the
right endpoint. Properness is used only for the full resultant's
upper-quadrant sign and remains valid even if its radial concurrence
is outside the square.

## 7. Joint angular interval and final contradiction

Both physical centers are in the opposite upper quadrants. Their
unchanged path follows the complementary lower arc of length
pi+delta1+delta4. The selected exterior/spoke order supplies this
choice. The full four-resultant balance provides a consistent check:
an upper path between the two strict upper resultant directions
would place all four full resultants in an open half-plane.

Every actual boundary center has radius greater than 5/4, and every
contact center gap is at most sqrt(2). The exact cosine comparison
therefore makes each of the three path angles less than
theta=acos(9/25). With alpha=3theta-pi,

    delta1+delta4<alpha<pi/6,
    cos(alpha)=13959/15625>89/100,
    sin(alpha)<9/20.

These facts supply the angular range used in Section 5. The lower
radius endpoint gives d>9/10, with no appeal to R>2.

The function f(u)=d*cos(u)-(3/5)*sin(u) is positive, strictly
decreasing and concave on [0,alpha]. For a fixed sum, concavity
makes f(u)+f(v) smallest at an endpoint pair. Strict decrease
then uses the strict sum bound to give

    X1+X4 >= f(delta1)+f(delta4)
           > f(0)+f(alpha)
           > (9/10)(1+89/100)-(3/5)(9/20)
           =1431/1000 >10/7 >sqrt(2).

This contradicts the original diagonal identity X1+X4=sqrt(2).
The strictness survives delta_i=0, a_i=0, any side-mean endpoint
allowed by the enlarged scalar domain, and every physical radial
weight endpoint.

## 8. Independent exact checks and the accepted residual

I independently recomputed the following strict rational reserves:

| Comparison | Positive reserve |
| --- | --- |
| 9/2-1105/256 | 47/256 |
| (79/40)²-1/4-(19/10)² | 13/320 |
| (29/40)²-1/2 | 41/1600 |
| (13959/15625)²-3/4 | 46992849/976562500 |
| 13959/15625-89/100 | 211/62500 |
| (9/20)²-[1-(13959/15625)²] | 2424521/3906250000 |
| (5/7)²-1/3 | 26/147 |
| 1431/1000-10/7 | 17/7000 |
| (10/7)²-2 | 2/49 |

The triple-angle value and final 1431/1000 expression were checked
as exact Fraction identities. The original graph degrees and its
reflection were checked directly. The arithmetic/pin record is

`/tmp/rooted_blocks_h3_0124_nonhub_endpoint_exact_checks_2026_10_28.json`

SHA-256

`7bbd6e826425e1aa9feec7f98055ca742bf7e58f60f3197f1f189f7cccb7b1a8`.

The accepted conclusion is exactly: when neither endpoint is
K-owned, the two endpoints cannot both belong to the union of the
endpoint-side-owned and physical-two-corner classes. This includes
mixed endpoint-side/radial and both-free-radial cases. It leaves at
least one free unique-physical-corner endpoint outside that union.
It does not fix that endpoint's other mean or invoke a singleton
selection with an unknown shared-side mean.

All original loads, degrees, forces, means, circle masks, selected
junction conventions and the three extra squares have been retained.
No numerical sample, deleted force, moved square, new post-extraction
normal, Lean/CI run, shared-metadata change or remote mutation was
used. The frozen source is accepted without amendment.
