# An S leaf excludes a boundary path with at most one missing spoke per gap

Date: October 26, 2026.

**Status: complete hand proof; full root and separate independent
reviews accepted.** This extends the connected-boundary-neighbor theorem across
one actual intervening boundary body. The whole new original caller is
the S alternative of the four-load house at a hub.

## 1. Full original component

Retain the original nine unit squares, their disjoint open interiors,
the common compatible physical certificate and

    79/40 <= R <= sqrt(1105)/16.

Suppose an entire positive component has the actual edges

    HL;
    B_i B_(i+1), 1<=i<k;
    H B_i, i in I,

where 2<=k<=7, L is a genuine radial S leaf, every B_i physically
touches the circle, and I contains 1,k with consecutive indices
differing by at most two. Missing spokes are absent from the actual
graph, and all actual spokes are kept. Retain each body's true
positive degree, every circle mask and individual zero weight,
every original normal and shared-side mean, and all 7-k other
physical squares. A physical boundary B may have zero total weight.

**Theorem.** This whole original family is impossible.

For k=7 the eight distinct physical boundary units B_i,L already
give a force-free contradiction: every point of each has norm at
least R-sqrt(2)>1/4, and the cap-arc theorem in
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section 1, gives eight
pairwise disjoint open radius-5/4 arcs each longer than pi/4.
The usual nearest-point support of a convex square supplies its
cap premise. Thus assume k<=6 below. This treats rather than
discards the possible physical boundary seven-cycle exception.

Normalize the actual leaf as

    d=sqrt(R^2-1/4)-1,
    L=[d,d+1] times [-1/2,1/2],
    p_HL=(d,0), n_HL=e_x.

Its two positive circle weights are equal. Its total circle
resultant is a nonzero positive multiple of e_x; its origin
moment is zero. H is physically circle-clear. No normal or
force is selected again.

## 2. The existing two-arc separation and the precise new claim

Reflect the whole packing as in S_LEAF_TRIANGLE_EXCLUSION.md,
Section 1: if H is aligned, its slider has t>=0; if it is tilted,
its inward vectors from (d,0) are (-a,-b),(-b,a), with a>=b>0.
Put theta=arctan(3/7). The complete geometric neighbor theorem in
S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md, Section 1, says that all
physical circle corners of every boundary neighbor of H other
than L lie in exactly one of

    J_+=(pi/9, pi-theta),
    J_-=(3pi/2-theta, 2pi-pi/9).                       (1)

The first interval has strictly positive y sign, the second
strictly negative y sign. Both have length less than pi. A
physical edge directly joining two such H neighbors preserves
their interval assignment, by Section 2 of that source.

The new claim needed here is:

**Two-edge gap claim.** Two physical boundary neighbors X,Y of H
cannot belong to opposite intervals in (1) if there is an actual
physical boundary unit Z with contacts X--Z--Y.

Z need not touch H. X,Y,Z can have any actual positive degrees.
The proof below uses no force equation at any of these three bodies.

## 3. Every tilted H: the already proved geometric gap applies unchanged

The full source FOUR_CYCLE_TILTED_S_ARTICULATION_EXCLUSION.md
states explicitly that its force balance is used only in Section 1
to force opposite interval assignments. Its Sections 2--6 give a
geometric contradiction from precisely the two-edge gap premises,
with no root-degree or boundary-degree equation. We already assume
those opposite assignments here and invoke just that argument.

Here are its complete quantitative inputs and its resulting full
case split, so the scope of this invocation is explicit. Set

    sigma=1/sqrt(2), rho=R-sigma, r=R-sqrt(2),
    u=da, v=db, u_0=(d^2+1-r^2)/2.

In the original own frame H=[u-1,u] times [-v,1-v], with
u>=v>0 and u^2+v^2=d^2. The accepted exact bounds are

    3/4<u_0<4/5,       d^2-u_0^2>1/4.

If u<=u_0, the upper-left H vertex has norm below r and v>1/2.
If u>u_0, the lower-left H vertex has norm below r. The equal
threshold belongs to the first case. A boundary center lies within
sigma of H and has radius at least rho. In the first case these
facts give the western center-angle gap

    gamma-beta > pi/2+arccos(3/5);

in the second case they give

    gamma-beta > pi/2+arccos(2/3).                      (2)

These are the full orientation-uniform calculations in that
source's Sections 3--5, including a=b, all physical contact owners
and side means. They use only that X is in J_+ and Y in J_-.

The physical path X--Z--Y must follow their western arc, since
the other arc contains the real leaf L. Circle-corner/center order
preserves each actual contact's consecutive minor arc. Each such
contact spans less than arccos(9/25), because its center distance
is at most sqrt(2) and both boundary-center radii exceed 5/4.
Thus gamma-beta<2 arccos(9/25), contrary to either case of (2).
The weaker bound in (2) still exceeds this upper bound: their
cosines are -sqrt(5)/3 and -463/625, with exact squared reserve

    5*625^2-9*463^2=23804>0.

This proves the two-edge gap claim for the whole tilted family,
without applying an isolated C4 force equation to the present graph.

## 4. The entire aligned family at arbitrary actual root degree

Write the actual aligned H as

    H=[d-1,d] times [t-1/2,t+1/2], 0<=t<=1/2,
    ell=d-1, sigma=1/sqrt(2), rho=R-sigma.

The exact constants of
FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md are

    |ell|<1/10, r=R-sqrt(2)>11/20,
    rho>19/15>5/4, sigma<17/24.                       (3)

Its Section 1 cap rigidity is entirely geometric: the only
contained unit wholly in x>=d is the actual L. Therefore no
other H neighbor can have original normal e_x.

If t=0, every point on H's left side has norm squared less than
1/100+1/4=13/50<r^2. No physical boundary neighbor can meet that
side. Every original H spoke normal would have nonnegative x
component, so the full unchanged equation

    alpha e_x+sum_(i in I) mu_i n_i=0, alpha,mu_i>0,       (4)

is impossible. This is the sole use of H's force equation in the
aligned gap proof, and all actual spokes occur in it. Hence

    0<t<=1/2.                                           (5)

### 4.1. Every upper-interval neighbor has center angle below 135 degrees

For X in J_+, its center angle beta lies in (0,pi). This follows
from its physical corner angles and their center discrepancy below
pi/9, because theta>pi/9. If p is any actual X--H contact, then

    (c_X)_x >= p_x-sigma >= ell-sigma > -1/10-sigma.

If beta>=3pi/4, the boundary-center radius floor would instead give

    (c_X)_x <= -sigma*|c_X| < -(5/4)sigma < -1/10-sigma,

where sigma/4>1/10. This is a contradiction. Thus

    0<beta<3pi/4.                                      (6)

This bound applies to every actual upper neighbor, regardless of
its contact owner or its H-force direction.

### 4.2. Every lower-interval neighbor has its exact top face below H

For Y in J_-, its center angle gamma first obeys

    3pi/2-theta-pi/9<gamma<2pi.

The boundary-center separation from L's actual center direction 0
is greater than 2pi/9. Using theta<pi/6 gives, more loosely,

    7pi/6<gamma<11pi/6,       (c_Y)_y<-rho/2<-5/8.     (7)

Let n be the unchanged H-to-Y normal, with application p. If
n_y>0, p lies on the top side or one of its vertices and has
p_y=t+1/2>1/2. Then (c_Y)_y>=p_y-sigma>-1/4, contradicting (7).
If n_y=0, its east option was excluded by cap rigidity. Its west
option has p=(ell,y). Since |p|>=r and the entire interval
-1/2<=y<=1/2 would give |p|^2<13/50<r^2, necessarily y>1/2.
The same center-height contradiction follows. Thus n_y<0.

If n_x<0, p is the lower-left H vertex, of squared norm less
than 13/50<r^2, impossible. If n_x>0, p=(d,t-1/2). By (5) this
point is in the relative interior of L's left side. The actual
minimum-n support of Y contains p+epsilon n for all sufficiently
small positive epsilon, by the complete square support-point
lemma used in the aligned C4 source. Such points lie in int(L),
which contradicts disjoint interiors. Every singleton and side
owner is retained by that lemma. The only possibility is

    n=-e_y,       max_Y y=y_0=t-1/2 in [-1/2,0].          (8)

The actual H contact is (X,y_0), ell<=X<=d, and X>0. Indeed X<=0
would again give squared norm less than 13/50<r^2. It remains an
arbitrary original shared-side mean if the actual contact is shared.

### 4.3. The lower center angle exceeds 285 degrees

The full top-support geometry lemma in
FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md, Section 3, applies
to (8). It says that a unit with top support height in [-1/2,0],
containing a positive-x point on that support, and with center
x coordinate at most zero, has every squared corner norm at most
9/4+sqrt(2)<(79/40)^2. Its proof keeps both possible tilts and
the aligned endpoint. Since Y physically touches the circle,
its center therefore has positive x coordinate. It also has

    (c_Y)_y<0,       -(c_Y)_y<=1/2+sigma<29/24.

If the center angle from the downward axis were at most pi/12,
its radius floor and cos(pi/12)>24/25 would instead give

    -(c_Y)_y > (19/15)(24/25)=152/125>29/24.

The final gap is exactly 23/3000. Thus

    gamma>19pi/12.                                     (9)

Combining (6),(9), the western gap exceeds 5pi/6. The actual
two-contact boundary path X--Z--Y must follow that western arc,
because the other arc contains L. Each physical contact spans
less than 2pi/5 by CIRCLE_CONTACT_ANGULAR_ORDER.md. Therefore
the same gap is less than 4pi/5, a contradiction. This proves
the two-edge gap claim at every aligned slider value, with the
actual t=0 case already excluded by the full equation (4).

## 5. Propagation across every actual spoke gap and full balance

Every H neighbor B_i, i in I, has one of the assignments (1).
Consecutive actual spoke indices differ by one or two. For a
one-step gap the direct physical contact theorem preserves that
assignment. For a two-step gap the two-edge claim just proved
preserves it. Thus every actual spoke neighbor has the same
assignment.

Consider any intervening B_j without an H spoke. Its two actual
path neighbors have the same assignment. Choose any circle corner
of each of the three bodies and of L. The two physical boundary
contacts follow their consecutive minor-circle order. They cannot
follow the arc containing the selected L corner. Since the two
endpoint corners lie in one interval (1) of length less than pi,
the other arc lies inside that same interval. The chosen B_j
corner must therefore lie there. Repeating this for every physical
corner keeps the entire mask in that same interval, including
zero individual circle weights.

Consequently all B circle atoms have one strict y sign. At least
one has positive weight: otherwise the component would have only
the nonzero S-leaf circle resultant, already incompatible with
full component balance. Summing the original body equations
cancels every internal pair force. Its remaining circle-force sum
has strictly positive or strictly negative y component from the
B bodies, while the actual leaf contributes zero y component.
This is impossible, completing the theorem.

## 6. Whole house caller and exact limits

For the house at hub A, take H=A, the genuine S leaf L at A, and

    (B_1,B_2,B_3,B_4)=(T,D,C,B),       I={1,2,4}.

The original positive edges are precisely AT,AD,AB,TD,DC,CB,AL.
The block loads TDCB make all four B bodies physically boundary.
Their actual degrees are A4,T2,D3,C2,B2,L1. In particular no
degree-two equation was assigned to D and no AC force was added.
The three other original physical squares remain present. The
theorem closes the entire original gate

    M6.B5L.HOUSE.HUB.LTDCB.S.

Together with D_LEAF_BOUNDARY_PATH_SHORT_FACES_EXCLUSION.md it
closes both complete leaf alternatives of this original load
orbit. The other house-hub load orbits and the whole house-hub
parent remain separate obligations. All physical circle masks,
zero weights, original means, reflected frames, tilted thresholds
and radius endpoints occur in the stated full cover.

The proof also gives a uniform S extension for every complete
boundary-path graph with the stated actual spoke-gap condition.
Unlike the D completion argument, it does not require an inner
face-capacity theorem. It does not cover longer missing-spoke
runs, a nonboundary intermediate body, arbitrary bridge arms,
or extra positive forces at H outside the displayed component.
No new normal selection, numerical pose, arithmetic coefficient
certificate, Lean compilation, CI or shared-ledger change is used.
