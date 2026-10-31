# Independent review: asymmetric small origin corner and the entire hub-diamond AP row

Date: October 27, 2026.

Reviewer: c6_next, separately from mixed_blocks, the source author.

**Verdict: ACCEPT without mathematical correction, both for the complete
force-free physical theorem and for the entire stated original hub-diamond
AP graph domain of C2.34.b2.** The C4 AP and page-diamond AP domains remain
separate. This review changes no original gate or shared ledger.

## 1. Frozen source and complete review scope

Read and audited in full:

    ROOTED_ASYMMETRIC_SMALL_ORIGIN_CORNER_AND_HUB_DIAMOND_LEAF_EXCLUSION.md
    SHA256 d776034db6364645fc071c2dd13cd00e6feea86bfb636a739d0c885a645f9aa1.

The first theorem concerns any actual unit

    H=[-a,1-a] x [-b,1-b], 0<=a<=1/60, 0<=b<=1/20,

in a disk with sqrt(17)/2<=R<=sqrt(1105)/16. It proves that at most
two distinct physical boundary units touch H. It assumes no selected
positive edge, normal convention, degree, force, circle weight, or
equilibrium at any of those units. All side and vertex endpoints are
included. The new estimates were checked at this full force-free scope.

The second theorem keeps the original H-A-B triangle, hub diamond
HK,HP,HQ,KP,KQ, and the two genuine leaves at A and P. Its actual degrees
are H5,A3,B2,K3,P3,Q2 and two leaf1 stars. The arbitrary ninth actual unit
remains. I checked the entire A feature cover and the actual B,K,Q load
derivation, with no shortened H or P equation.

## 2. All geometric feature cases in the physical theorem

The center inequalities are correct. The maximum actual corner norm
gives |C|^2+|C|+1/2<=R^2, hence |C|<91/60. A physical circle corner and
the actual half diagonal give |C|>=R-1/sqrt(2) and therefore |C|^2>183/100.
Distinct actual centers are at least one apart by their open radius-one-
half incircles. None of these facts depends on a positive circle weight.

The minimum-support statement p+n in the unit is valid at every actual
support point p: in each own coordinate with nonzero normal component,
p is at the inward endpoint and adding that component stays within the
unit interval. A zero component leaves the coordinate unchanged. This
also covers every side mean and both endpoints.

### 2.1. Both full wall bounds

The complete bound s<1/7 follows from the actual width c+s, the weaker
19/20 wall, R<133/64, and the strictly increasing half-circle sum. The
two actual upper-far corners cover both physical tilt signs and the
aligned endpoint. With c>=1-s/7, the two full squared-coordinate
polynomials are exactly those in Section 2 of the source.

For the 59/60 wall, the first linear coefficient is negative, -1/105;
the proof correctly bounds its entire contribution by -1/735 and retains
the positive quadratic term. The resulting constant reserve is still
strictly positive. The second tilt polynomial has both extra coefficients
positive. For the 19/20 wall both complete tilt polynomials have positive
linear and quadratic coefficients. Reflecting the transverse coordinate
proves both center signs. The two strict strips in the source therefore
hold for every actual unit beyond the respective walls.

### 2.2. The new complete lower transverse bound

For a unit whose highest vertex is p=(A,-b), |A|<=1, b<=1/20, the
contrary center inequality gives u=r+t>=13/10. The three nearby
vertices are strictly inside the radius floor by the stated triangle
inequalities. The opposite vertex is bounded by

    3+b^2+2 sqrt(2-u^2)+2bu
       <=1253/400+sqrt(31)/5<17/4.

The comparison function is strictly decreasing over the entire u range,
and its square-root endpoint comparison is strict. Thus the claimed
C_y>-b-13/20 holds, including the axial endpoint of this vertex frame.

At a strict southeast root-corner contact, a unit vertex has an open
right-angle tangent sector disjoint from the root's open northwest
quadrant. Every such sector has either both inward edge x components
nonnegative or both inward edge y components nonpositive. The first
full alternative has an actual opposite corner outside the disk by the
uniform 2471/6400 reserve. The second is exactly the highest-vertex case.
There is no missing intermediate sector or axis endpoint.

For a relative side-interior contact, the exact center is
C=p+n/2+k j. The contrary low center gives k<0 and the actual side
parameter t=k+1/2 in (0,7/40), with both normal components greater
than 1/3. The first two real corners and Z_+ are strictly interior by
the displayed radius comparisons. For Z_-, if s<=4/5 its squared norm
strictly decreases with t and its t=0 algebraic value is the already
bounded highest-vertex expression. This comparison does not replace the
physical square. If s>4/5, the complete actual coordinate bounds give
0<Z_-,x<39/40<1 and |Z_-,y|<3/2, again strictly interior. Thus every
side-interior frame is covered.

At a south-axis contact, a horizontal top side has the immediate half-
unit center offset. Otherwise its unique highest vertex satisfies the
same complete vertex proof for every actual root-side position, since
|p_x|<=1. This includes side endpoints and any original shared mean.

### 2.3. The upper, longitudinal, and axial bounds

The surviving southeast vertex cases already have negative center height.
In the side-interior case, assuming C_y>=q gives k>0 and the actual
upper-far corner used in (12). Its x estimate follows from
(c+1/c)/2>=1 and the unchanged nonnegative b. For s>=1/2 that corner
already exceeds the radius in its x coordinate. For 0<s<=1/2 the
complete positive-coordinate polynomial has a positive constant excess
and positive remaining coefficients in both ranges. This proves the
upper center strip without a frame or contact restriction.

The longitudinal estimate correctly combines |C-p|^2<=1/2,
|C|^2>183/100, and C_y>-L. The resulting (A^2+K_b)/(2A) decreases
for A<=1 because K_b>1 on both complete parameter rectangles. Its
minimum at A=1 also decreases over the actual b interval. The exact
strict bounds 181/160 and 8309/7200 follow.

For the east axis, the full corresponding wall estimate and the actual
half-width supply the same center rectangle. For the south axis,
-L<C_y<=-1/2 and the boundary-center lower norm give |C_x|>D_0.
The actual contact-point distance excludes its negative branch uniformly,
without imposing any frame on that unit.

Interchanging x and y takes the northwest/north/west cases to the second
range exactly. A southwest support point is too close to O to belong to
any boundary unit. At the northeast corner the actual point W+n in its
neighbor is outside D_R by the strict 2487/6400 reserve. These two
excluded strict corners and the four axes and two retained strict corners
exhaust every actual separating normal.

Every boundary neighbor center therefore lies in one of the two stated
rectangles. Their exact squared diameters are 12613/14400 and
13385/14400, both below one. Each admits at most one actual center, so
the complete physical two-neighbor theorem follows.

## 3. The actual small H vertex and source extraction

I reread the whole Section 1 A feature cover, the complete physical
routing lemma, and all operative tilted and aligned A/B wall arguments
of

    ROOTED_ONE_PRIVATE_LEAF_TRIANGLE_TERMINAL_FOUR_BLOCK_EXCLUSION.md
    SHA256 02b1a5d7525e2cc8d02044b9f842479217009ce33f8ff9149139e5e0a4c8f87e.

Its terminal-four-block cap and shallow-strip tip conclusions are not
used in the new theorem. The actual A3 leaf and B2 equation supply the
parallel wall or tilted owned-side chart at arbitrary complete H forces.
In the tilted strict-AB case, the normal components satisfy n_x<=n_y;
the whole minimum-support span argument gives min B_y>=W_y-n_x>0 for
every B feature. In the aligned parallel case the full actual B lies
above height 1/2. No B physical mask is selected by assumption.

The actual HA point V=(-delta,-Y) is a strict H vertex. In both full
charts it satisfies |V|<=|S| for A's actual lower-right vertex S. Every
other A vertex and every other H vertex exceeds 3 epsilon. These are
actual coordinate inequalities, with unchanged means.

I read the full new angular source and its full independent review:

    ROOTED_ORIGIN_TRIANGLE_ALIGNED_NONPARALLEL_SECOND_LEAF_EXCLUSION.md
    SHA256 b897cade602a3e256516dcf344b122360c256b1bb234ec0417b53bdbe308dab4;
    REVIEW_ORIGIN_ALIGNED_TRIANGLE_SECOND_LEAF_GLOBAL_NEXT_2026_10_27.md
    SHA256 2c8e552035bf1efd04d384c987853eb21f4ac268cd425d2c76833d4a2d106418.

I independently checked all cases of its force-free Sections 1-3:
origin in the closed unit, nearest side, nearest vertex, one/two cutting
faces of the open-origin H, and every actual near-unit endpoint. Its
strict open-interior arc bounds apply to the actual H,A,P here. If V
exceeded 3 epsilon, every H vertex would do so, forcing the actual A
vertex S to be small, contrary to |V|<=|S|. Thus |V|<=3 epsilon.

In H's actual own axes v,u, origin-interiority gives

    sigma=delta*c-Y*s in (0,epsilon],
    w=delta*s+Y*c in (0,3 epsilon].

This is exactly the asymmetric physical domain, including both weak
upper endpoints. The optional local routing of B onto the minimum-v
side also has its full physical opposite-vertex and side-normal cover;
it is not used to lower the degree of a decorated neighbor.

## 4. Complete original hub-diamond feature and load join

The current original-domain and origin pins are exactly

    ROOTED_C2_34_TWO_BRIDGES_THREE_DOMAIN_REDUCTION.md
    8918c0e3e77cbc9f90899a29ebd2233c87858a00ecf1e0ffca2a684ccdd5cb0a;
    ROOTED_DECORATED_TRIANGLE_AND_PRIVATE_LEAF_FOUR_BLOCK_ORIGIN_STRUCTURE.md
    e77c19d2afefb96f4919788d5d69f987377d7b90b299037c0c35a1c717cd8968.

The complete origin theorem was already fully reviewed at its genuine
privately decorated scope. Its original graph match and conclusions were
checked again: H is open-origin, A and P have genuine S leaves and meet
D_epsilon, and neither private leaf is deleted. The entire original
three-domain reduction was read again for the exact hub-diamond row.

The aligned nonparallel A interface has the full b897cade exit, with its
real second leaf and arbitrary degree at P. Its complete origin-only
aligned input and the full independent audit retain every H force. The
aligned parallel A and parallel H interface has the whole 989eae4d
theorem, independently accepted in my separate 91658ec4 review.

The complete tilted A feature list leaves precisely its strict two-
vertex alternative or its A-owned alternatives. The former has the
already fully reviewed origin-only a0cec94c exit with unchanged true
A3/B2 equations. For the parallel-H owned alternative I read the entire
new source and its full independent review:

    ROOTED_TILTED_PARALLEL_TRIANGLE_SECOND_LEAF_EXCLUSION.md
    6f40f89dde97f8c333ee12026873efb09453dd6bfafb621dc5e5d80fc178cbd1;
    REVIEW_TILTED_PARALLEL_TRIANGLE_SECOND_LEAF_GLOBAL_NEXT_2026_10_27.md
    ca925a735e2baf61236b0eae762b1f1314eb6241464f4a30475d3d9774be21af.

I also reread its complete local owned-side chart, all A-owned-top
oblique-B owner cases and aligned-B classification from c1386937, and
the entire strict-AB/free/shared/B-owned cover and actual B corner proof
from d7cb5758 Sections 5-7. The old H-leaf or terminal-Q consequences
are not transferred. The new theorem's two aligned B exits use the
actual circle identities and unchanged full A/B moment sum; its final
B-owned exit uses the full wall theorem and the two actual leaf centers.
All three complete branches pass at arbitrary H and P degrees.

Therefore the only remaining A interfaces are exactly the oblique-H
ones covered by Section 6 of the new source. There Theorem 1 permits
at most two physical boundary neighbors of H. But B2 is loaded because
H,A already touch, and Q2 is loaded because H,K already touch. K retains
its true degree three and neighbors H,P,Q, with H touching both P and Q.
The full compatible selected no-unloaded-diamond-hub theorem applies
with central neighbor H and permits arbitrary degrees and loads at
H,P,Q. It makes K loaded as well. Its current pin is

    NO_UNLOADED_DIAMOND_HUB.md
    82b546953a927a09d8ccabdefd8ffc10eac3e4efc5d8a122840f1343f80a7e2d.

The three actual distinct neighbors B,K,Q are physical boundary units,
contradicting the complete force-free theorem. P3 has never been treated
as a terminal tip, H5 never as a two-force root, and the HK chord remains.

## 5. Exact checks and disposition

An independent rational calculation reconstructed both full wall
polynomials, including all four linear and both quadratic coefficients,
and all displayed 15 principal reserves. It also checked the strict
nearby-corner, side-Z_+, radical, negative-center-branch and angular
reserves. In particular the two decisive diameter reserves are
1787/14400 and 203/2880; the new highest-vertex square-root reserve is
1409/160000. Every squared radical comparison uses positive quantities.
The current source and dependency hashes above were checked against
their actual bytes. No mathematical correction was required.

**The entire force-free asymmetric small-corner theorem and the whole
original C2.34.b2 hub-diamond AP row are independently ACCEPTED.**

This is a whole graph/load/owner/mean domain exit, with all eight positive
bodies and the ninth physical unit retained. It does not close the other
two AP rows, the whole b2 coarse cell, the unrestricted sharp bound, or
the full equality classification. No numerical pose, altered force,
shared-ledger edit, Lean build, CI, workflow or remote mutation was used.
