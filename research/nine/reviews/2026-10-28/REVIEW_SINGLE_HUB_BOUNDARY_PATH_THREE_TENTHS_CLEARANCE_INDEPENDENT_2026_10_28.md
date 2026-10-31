# Independent review: complete single-hub pockets have strict three-tenths clearance

Date: October 28, 2026 UTC. Reviewer: mixed_capacity_review.

**Verdict: PASS at the final frozen source below, after one explicit
winding-exposition clarification.** Every surviving original endpoint
case proves a strict distance greater than 3/10 for the entire actual
outer hub arc. The unchanged physical crosscut and the separately
computed origin winding then give the same strict bound for every
whole additional unit assigned to the actual closing pocket. The
continuous connected-arc export is valid at every inner radius
r_-<rho<=13/10. No original fine or coarse row is closed by this
uniform strengthening alone.

## 1. Exact reviewed source, dependencies and review correction

| Source | SHA256 | Scope read and checked |
| --- | --- | --- |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET_THREE_TENTHS_CLEARANCE.md | e9da91e0b483823838208e9dcca2798afdadbff6451c7c785a6b64599e8a1326 | Entire final new source, every endpoint case and full winding/arc export |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Complete original arbitrary-spoke proof, all equations, cases and actual pocket construction |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | c8c9dc223e11dbcd7be9063818d546a3d3c0bc77b66cdac181b9ea97d51bae69 | Complete strict-clearance connected-arc proof and exact radius comparisons used here |

The author is V-continuation. Root checked the vertical-segment
improvement during author discussion; that is disclosed in the source
and is not counted here as a separate independent review. I did not
contribute a discovery argument to this theorem before reviewing it.

The initially submitted source had SHA256
0e38aac23757ee4d82c30b1fc7cc126f5698dd427b86ffe9e39cf40010c4df22.
Its last sentence in Section 6 asserted without qualification that no
path is moved through an extra's open interior. The actual occupied
crosscut does avoid those interiors, but the auxiliary path through
an endpoint concurrence may leave its square and needs only to avoid
O. The old full proof already distinguishes those roles correctly.

I requested that the new source make the same distinction explicit.
The author replaced only that paragraph: actual occupied-boundary
routing and whole-extra assignment avoid extra interiors; the separate
q_j homotopy computes only winding at O, may leave endpoint squares,
and is not used to transport an extra or its circle intersection.
I checked the final wording and independently verified that reversing
only this paragraph reproduces the initial SHA256 exactly. No theorem
statement, physical hypothesis, metric case, inequality or arc range
changed. The final pin above is the reviewed version.

I also read both complete historical reviews of the original arbitrary-
spoke source, the actual port-order and crosscut Sections 1--2 of the
full-fan source, the degree-free boundary-contact moment lemma, the
true loaded 2 proper-concurrence lemma, and the physical boundary-cycle
exclusion at the precise operative scopes below. The new proof does not
borrow a full-fan center bound or delete a missing internal spoke.

## 2. The complete original component is retained

The positive component is exactly

    U,B_1,...,B_k, 3<=k<=6,
    B_i--B_(i+1) for 1<=i<k,
    U--B_1,U--B_k, and any subset of internal U--B_i spokes.

U is unloaded. Every B_i has positive total circle load. The two path
endpoints are genuinely degree two, while each internal path body
retains all its actual pair forces. The hub retains every positive
spoke with its original magnitude, normal and actual application or
full side mean. The actual exterior-face order is U,B_1,...,B_k,U.
All nine physical units, additional physical zero-weight contacts,
physical circle corners and individual zero coefficients remain.

The theorem requires this to be the entire positive component. It
does not allow an extra nonzero force at U or either path endpoint
to be omitted. Nor does it allow an internal loaded 3 to be promoted
to an endpoint 2. In particular the source cannot be applied directly
to a multi-unloaded-hub H4 component by hiding the second hub.

The upper bound k<=6 is substantive. Any nonconsecutive physical
B_i--B_j contact, even at zero pair weight, would close a physical
boundary cycle on at most six of these units. The complete physical
boundary-graph theorem excludes all such cycles; its seven-cycle
exception is not discarded. Therefore B_1 and B_k are actually
closed-disjoint, their U applications are distinct, and coincident
hub applications can involve only consecutive boundary neighbors.

The original compatible embedding puts every retained internal spoke
on the occupied U arc in its actual path order. Its normals have that
same weak order. At a coincident port the actual tangent-sector order
is kept; shared-side endpoint means retain the weak limiting normal
directions. This argument works for any retained subset of spokes.
It requires no absent internal path body to touch U.

## 3. Full equations, endpoint directions and common strict margins

The complete hub equations are the positive normal sum zero and the
complete torque sum zero about any chosen calculation point. Summing
all original component force equations gives

    sum_i F_i=0.

No force from outside the component is silently removed in obtaining
this identity. The original endpoint torque equations alone give the
opposite strict signs of det(p_1,n_1) and det(p_k,n_k), according to
the actual clockwise or counterclockwise occupied-arc orientation.
The boundary-edge moment input is force-free and degree-free; it
does not require a two-force equation at B_2 or B_(k-1).

The true endpoint loaded 2 lemma supplies

    q_j=tau_j F_j=p_j+ell_j n_j,
    tau_j>0, ell_j>=0, j=1,k.

Its actual physical boundary neighbor is B_2 or B_(k-1), whether or
not that body has a hub spoke. Both physical endpoint circle masks,
zero individual weights and zero proper lengths are retained. The
proof does not assume q_j lies in its square; that would be false in
part of the radial two-corner domain.

Put r=R-sqrt(2). For every point p of an actual physical boundary
unit, a real containing-circle corner and the unit diameter give
|p|>=r. The corner may have zero individual circle coefficient.
The outward neighboring unit has width at least one, so the complete
original support bound p_j dot n_j<=R-1 is also available without
any surrogate force equation.

I checked the three numerical margins used in every case:

    r>=2-sqrt(2)>3/10,
    r/sqrt(2)>=sqrt(2)-1>3/10,
    r^2-1/4>=23/4-4sqrt(2)>9/100.

For the last strict inequality, sqrt(2)<283/200 has exact positive
squared reserve 89/40000 and gives 23/4-4sqrt(2)>9/100. All quantities
under the subsequent square roots are consequently positive. The
comparisons remain strict at the allowed lower radius R=2. No open
lower-radius endpoint was tacitly added.

## 4. All combinations of hub-owned endpoint axes

### 4.1. The same-axis alternatives are genuinely impossible

I checked the old complete force/order argument. With no normal turn,
all retained hub normals equal the same axis and cannot have a positive
zero sum. With a full turn, the actual same-side port order requires
b<=a while the true opposite endpoint moment signs give a<0<b.
Both alternatives contradict the unchanged component. The new source
does not need to assign a clearance to these impossible cases.

### 4.2. Adjacent axes give a whole-arc projection bound

The short quarter-turn normal interval places the entire positive
hub force in a closed quadrant and is impossible. The surviving
three-quarter-turn chart has North and West endpoints. The original
moments put both actual ports in the strict northwest quadrant; the
proper endpoint lines put both resultants there too.

For the unit vector v=(-1,1)/sqrt(2), each port has

    v dot p_j>=|p_j|/sqrt(2)>=r/sqrt(2)>3/10.

The actual outer arc passes through the northwest corner. Its two
whole side segments have v-projection at least the smaller original
endpoint projection. Thus every point of the complete original Gamma,
not only its two endpoints or a replacement chord, has norm>3/10.
The strict v dot F_j signs needed for winding are unchanged.

### 4.3. Opposite axes include every height and side-mean endpoint

The surviving original chart is

    p_1=(a,h), p_k=(b,h-1), a<0,b<0,
    U's left side is x=L, L<=a,b.

Both endpoint resultants lie in the strict left half-plane. The whole
outer arc comprises the top horizontal portion to x=L, the entire
left vertical side, and the bottom horizontal portion to its port.
Moving left from either negative-x port cannot decrease its norm,
so the horizontal portions are at distance at least r.

If the vertical side misses y=0, its nearest endpoint has norm at
least that of the corresponding original port. This again gives
distance at least r. If it meets y=0, then 0<=h<=1. At least one
of h and 1-h is at most 1/2. The corresponding original port has
horizontal magnitude at most|L|, hence

    r^2<=L^2+1/4,
    |L|>=sqrt(r^2-1/4)>3/10.

This bounds every point of the vertical segment. It includes h=0,
h=1, either original side mean at an intersection endpoint, and any
physical shared-side interval. It does not impose h=1/2 or center
the hub. The entire Gamma is therefore strictly beyond 3/10, with
the original left-half-plane direction condition retained.

## 5. Every one-axis/one-oblique endpoint feature

The original whole-path reversal and physical reflections permit the
chart

    U=[L,L+1] times[h-1,h], p_1=(a,h), L<=a<0,

with the oblique endpoint at the top-left or bottom-left vertex.
I checked both short normal intervals against the full hub equation.
For the top-left endpoint all vertical components are nonnegative,
with positive endpoint components; for the bottom-left endpoint all
horizontal components are nonpositive and at least one is negative.
These statements include coincident endpoint-sector forces and use
every actual retained spoke. Thus the occupied arc must be the long
clockwise arc through the right and bottom sides.

The two actual endpoint concurrences and resultants have strictly
negative x coordinates. For the top-left endpoint, the entire outer
arc is the horizontal segment extending left from p_1. Its norm is
at least the actual port norm r.

For the bottom-left endpoint, the outer arc also contains the left
vertical side. Its horizontal portion has the same radius bound. If
the vertical side does not meet y=0, its nearest endpoint is bounded
by the corresponding port radius. If it does, the top port has
horizontal magnitude at most|L| and the bottom port has horizontal
coordinate exactly L. Choosing the port whose absolute height is
at most 1/2 gives the identical bound
|L|>=sqrt(r^2-1/4)>3/10.

This is a complete bound on Gamma in both actual vertex choices. It
retains the full side-mean interval at the axis endpoint and all
physical ownership possibilities at the oblique endpoint. No extra
strictness of an original shared mean has been assumed.

## 6. Both oblique endpoint normals, including endpoint force groups

### 6.1. Adjacent actual vertices

The actual port chart is

    p_1=(x-1/2,h), p_k=(x+1/2,h).

The short top-side occupied arc cannot balance the complete hub force.
The endpoint moments on the other three sides give h>0. I checked
the source's proof of |x|<1: if x>=1, the right endpoint moment
and its outward unit normal force p_k dot n_k>=3/2>R-1;
the reflected left endpoint excludes x<=-1. This uses the actual
contained-neighbor width bound, not a fan-only hub-center estimate.

With |x|<1 one of the two horizontal port magnitudes is at most 1/2.
Its actual boundary radius therefore gives

    h^2>=r^2-1/4>9/100,

and h>0 makes h>3/10. The complete outer Gamma is the side at
that height. The two proper endpoint concurrences have positive
y coordinates and give the required strict upward resultant signs.

### 6.2. Opposite actual vertices

I checked the entire original group argument, not just the final
support inequality. In the horizontal-chord chart put

    sigma=1/sqrt(2),
    p_1=(x-sigma,h), p_k=(x+sigma,h),

and let the occupied arc be the lower arc. Every original force at
each endpoint is included in its original endpoint group. Every other
actual application P on the lower arc satisfies

    det(P-p_1,n)<=0, det(P-p_k,n)>=0.

The complete two torque equations give nonnegative vertical components
for the two endpoint groups. Their actual weak within-vertex order
then gives the same weak vertical sign for the genuine endpoint
normals. Thus the original endpoints satisfy

    n_1=(-b_1,a_1), n_k=(b_k,a_k),
    b_j>0, 0<=a_j<=b_j.

No group is a new physical force or a replacement of an original
application. Coincident applications, shared-side endpoints, zero
vertical components and arbitrary internal spoke subsets remain.

The original support-width contradiction proves -sigma<x<sigma,
including the a_j=0 endpoint where the first support inequality may
be equality. The later comparison sqrt(2)>R-1 remains strict.
Writing X=sigma-x>0 and Y=sigma+x>0, the endpoint moment gives h>0.
Both proper endpoint resultants point strictly upward.

On the two complete upper roof sides the positive supports are

    (X+h)/sqrt(2)>=sqrt(X^2+h^2)/sqrt(2)>=r/sqrt(2),
    (Y+h)/sqrt(2)>=sqrt(Y^2+h^2)/sqrt(2)>=r/sqrt(2).

Each support is against a unit normal and is constant along its
actual side, so it bounds the norm of every point on that side.
Both exceed 3/10. This proves the whole-Gamma assertion on the
entire remaining endpoint feature without a two-force hub surrogate.

The same-axis exits, adjacent/opposite axes, mixed endpoint pair,
and adjacent/opposite oblique vertices exhaust every original normal
type for a square. All surviving cases supply the unchanged common
direction v as well as the improved complete metric margin.

## 7. Actual occupied crosscut and the separate origin-only homotopy

I checked the full construction in the original arbitrary-spoke
source and the full-fan source's Sections 2.1--2.2. It has two
logically distinct uses, now correctly distinguished in the new text.

For the actual barrier only, each original application is replaced
by the extreme of its real U--B_j contact facing the closing gap.
The original point or mean stays in every equation. The U arc between
these physical extremes is a subarc of the already bounded complete
Gamma. The extremes are distinct because the actual endpoint units
are closed-disjoint.

Simple paths through the interiors of the real endpoint units connect
the extremes to their gap-facing physical circle corners. They meet
U only at their contact extremes and avoid every extra's open interior.
Together with the U subarc and the actual closing circle arc they
give the same compatible occupied pocket boundary as in the accepted
source. Weak physical contact subdivisions can restrict its free
side, but cannot move a whole extra through an occupied boundary.
No concurrence point is used as part of the physical barrier.

Every point of its endpoint-unit paths has norm at least r>3/10;
every retained U-arc point has norm>3/10 by the exhaustive case proof;
every closing outer-circle point has norm R>=2>3/10. Thus the whole
actual compact boundary misses the closed radius-3/10 disk.

To determine which side contains O, the independent auxiliary homotopy
is allowed to leave the endpoint units. Every point z of an endpoint
unit satisfies F_j dot z>0, by its real physical circle corners and
the diameter bound. Also F_j dot q_j>0 because q_j=tau_j F_j with
tau_j>0. The original endpoint path can therefore be homotoped in
that strict half-plane to a path through q_j and the resultant ray,
always avoiding O. Moving the circle endpoint within its own actual
angular interval keeps the original closing-arc lift.

The full component balance and at least three distinct nonzero
resultant directions make every consecutive gap strictly less than
pi. Otherwise the remaining directions lie in a closed semicircle
with an interior direction, incompatible with their positive sum zero.
Both endpoint resultants have positive v projection, so the actual
closing resultant gap is their minor arc inside that half-plane.
The final auxiliary loop is consequently contained in v dot z>0
and has winding zero about O.

This computation proves winding zero at O for the actual occupied
boundary. It does not route extras along the auxiliary loop and does
not need that auxiliary homotopy to avoid the entire 3/10 disk or
any extra. The final source now states that distinction expressly.

## 8. Strict transfer to the whole closed extra square

The actual boundary already misses the connected closed 3/10 disk.
Its winding is therefore constant and zero throughout that disk, so
the disk is outside the bounded pocket side and every free subdivision
of that side. This is the unchanged original topological conclusion,
applied to a stronger proved boundary margin.

The strict conclusion requires more than disjointness from the open
disk. Since the actual boundary is compact and every point has norm
strictly greater than 3/10, its minimum norm is 3/10+epsilon for some
epsilon>0. A smaller positive increase in radius still misses it;
winding remains zero on that slightly larger connected disk. Hence
every extra whose open interior is assigned wholly to the actual
pocket has all its interior points beyond that larger disk. Taking
the closure of that unchanged square gives

    dist(O,E)>3/10.

This remains strict when the extra touches an occupied boundary.
No inference from its center direction, an endpoint distance, or a
virtual geometric object is needed. The theorem still requires each
caller's full whole-extra allocation; it does not establish anything
about bounded central faces or another exterior pocket.

## 9. The complete new inner-circle range is literal

The continuous arc source defines

    r_-=sqrt(2*(2+sqrt(2)))*(sqrt(1105/512)-1),
    r_+=1/(2*sin(pi/8)).

I checked its exact comparisons

    r_-<157/128<13/10<r_+.

In particular its proof of sin(pi/8)<5/13 uses the exact positive
square comparison sqrt(2)>238/169, with reserve 478/28561. Thus
rho=13/10 is strictly below the arc theorem's excluded upper
endpoint. The lower bound rho>r_- stays strict; the critical
single-square equality case is not incorrectly included.

For every rho in (r_-,13/10] the new physical conclusion gives

    dist(O,E)>3/10>=rho-1.

This is strict clearance at rho-1 even at rho=13/10. E is one of
the actual contained units, hence is contained in the same disk of
radius sqrt(Q). The complete force-free Theorem B consequently applies:
int(E) intersects that circle in one connected open arc longer than
pi/4, containing the actual radial center point rho*c/|c|.

I checked the operative own-frame cases of that theorem: a>rho,
a<=rho with positive lower transverse coordinate, and the weak
tangent-side residue. The last can disconnect an open intersection
only under weak clearance. Here strict clearance excludes it, so the
connectedness assertion is justified; it is not inferred by taking
a limit of connected arcs. The separate radial-center estimate puts
the stated point in E's actual open incircle.

This is a continuous family of valid inner circles, each common to
all units in a chosen capacity comparison. It supplies no new bound
on the free angular interval of a pocket. In particular a gap proof
at radius 5/4 cannot simply be reused at 13/10; the caller must prove
its actual occupied-crosscut routing at the newly chosen radius.
The new source explicitly keeps that obligation.

## 10. Preserved upstream scope and exact conclusion

The operative underlying physical sources checked at their literal
scopes include:

| Source | SHA256 | Scope used |
| --- | --- | --- |
| CHORDED_HEXAGON_FAN_COMPLETE_EXCLUSION.md | 1a7c37b84b482d33adbd235071a1d64aa5e08b6b866d2bea92534f78551e7a0b | Only actual port/normal order and occupied-crosscut/origin-homotopy Sections 1--2 |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Only degree-free boundary-contact moment Lemma 1.1 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Only true loaded 2 proper-concurrence Lemma 2.1, with actual boundary neighbor |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Physical boundary order and exclusion of cycles of at most six, retaining its seven-cycle exception |

The last row uses the current published bytes. The historical pin
2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449
differs by exactly one terminal LF, as recorded in the recovered
four-family dependency audit. I independently reproduced that historical
hash by appending one LF to the current bytes, and reread the complete
current source. No mathematical statement or proof differs.

I did not transfer a full-fan center estimate or a fan-only load
conclusion into the arbitrary-spoke domain. I did not use an equation
at an internal loaded body as an endpoint equation. The existing
source's force and torque signs remain at their original applications
throughout the metric strengthening.

The accepted export is exactly the stronger whole-Gamma and whole-
closing-extra clearance, together with its strict connected-arc family
on (r_-,13/10]. It creates no original graph/load closure, central
capacity result, allocation theorem, or automatic radius 13/10 angular
routing bound. No new computational exclusion certificate is needed.

No original source, selected normal, positive force, side mean,
physical circle coefficient, unit, graph degree or extra is removed
or altered by this review. No Lean/Lake, CI, workflow, pose mesh,
certificate execution, ledger mutation, commit or remote write was
used. The final source at e9da91e0 passes the full independent review
after the explicitly documented one-paragraph clarification.
