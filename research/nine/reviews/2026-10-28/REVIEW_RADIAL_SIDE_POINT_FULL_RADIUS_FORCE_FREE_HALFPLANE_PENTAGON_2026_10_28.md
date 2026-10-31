# Independent review of the full-radius force-free radial-side half-plane theorem

Date: October 28, 2026 UTC. Reviewer: pentagon, independent of author house.

**Verdict: PASS on the entire stated domain d>1/sqrt(2), with no upper-radius restriction.** The stronger strict-interior implication is proved without any initial containment, load, degree, equilibrium or support-owner premise. The physical boundary-unit corollary is valid in particular for every R>=2. No repair is required.

## 1. Exact reviewed bytes and mathematical dependencies

The complete reviewed source is

    RADIAL_SIDE_POINT_FULL_RADIUS_FORCE_FREE_HALFPLANE.md

at SHA-256

    baeb2ab8556a773212073d4fbf10eda66efe06a567070f5dfcbd4de3f36625d3.

The exact file was read in full and preserved separately before review. The proof is self-contained: its operative inputs are convexity of a square and of the squared norm, elementary orthonormal coordinate identities, and Cauchy's inequality. It imports no existing geometric exclusion or force lemma.

I also read the earlier RADIAL_SIDE_BOUNDARY_NEIGHBOR_HALFPLANE.md in full to check the claimed relationship. Its high-radius center-box proof is provenance only and is not a premise of this new proof. Its later graph-specific application is not automatically widened or closed by the new theorem.

## 2. Statement and all physical guards

Fix an orthonormal frame n,f about the unchanged circle origin and let

    d>1/sqrt(2),
    R^2=(d+1)^2+1/4.

The actual unit square E contains an actual point Q with

    Q.n>=d, Q.f=1/2.

The theorem assumes, for its stronger implication, that E also has a point of n projection at most d-1. It proves every point of E has norm strictly below R. E need not initially be contained in the disk for this implication.

For a contained physical boundary E, the existence of an actual point of norm R then contradicts this strict conclusion. Therefore every point of the whole closed E has n projection strictly greater than d-1. Reflection gives the case Q.f=-1/2.

The actual Q is permitted to be a vertex, a side point, an endpoint-valued shared mean or an interior point of E. Its height may equal d or exceed d. No contact force is used, so deriving an additional geometric point of E does not replace Q in any equation.

The radius comparison is correct at the closed endpoint R=2:

    d>=sqrt(15)/2-1>9/10>1/sqrt(2),

using 15/4-(19/10)^2=7/50>0 and (9/10)^2>1/2. Thus the conclusion covers R>=2, including the entire old low-radius gap and all larger radii.

## 3. The vertical-slice argument is valid for every orientation

In coordinates x=z.f,y=z.n, write Q=(1/2,q), q>=d and suppose min_E y<=d-1.

A nonaligned square has one lowest vertex. Its two inward side vectors point upward, and each vertical component is at most one. The complete lower hull consists exactly of those two sides joining the lowest vertex to the leftmost and rightmost vertices. Hence the lower endpoint of every nonempty vertical section is at height at most min_E y+1. This includes the degenerate sections at the leftmost or rightmost vertex.

The aligned case has the same bound from its horizontal bottom side. The section x=1/2 is nonempty because it contains the actual Q. Its lower endpoint is at most d and its upper endpoint at least q>=d. Convexity of the closed section therefore gives

    P=(1/2,d) in E.

This covers equality min_E y=d-1, q=d, and a section endpoint. The reasoning does not assume an interior section or a generic orientation.

## 4. Aligned frames and the complete tilted parameter domain

For an aligned unit, vertical extent one and the two opposite inequalities force min_E y=d-1 and q=d. The horizontal interval contains 1/2 and has length one, so

    -1/2<=x<=3/2, d-1<=y<=d.

Since d>1/2, every point has |y|<=d. Therefore

    |z|^2<=d^2+9/4<R^2,

with exact strict margin 2d-1. Both aligned orientation endpoints are fully included here.

For a tilted unit, its actual inward axes at the unique lowest vertex may be named

    e=(c,s), g=(-s,c), c,s>0, c^2+s^2=1.

This describes every nonaligned orientation, after naming the right and left upward sides. Because the actual point P belongs to E, its true coordinates u,v in that square satisfy 0<=u,v<=1, and

    E=P-u e-v g+[0,1]e+[0,1]g.

The alleged low point is equivalent to

    s u+c v>=1.

For fixed actual c,s, this cuts the unit parameter square into exactly the closed triangle with vertices

    (1,1), (1,b), (a,1),
    a=(1-c)/s=s/(1+c),
    b=(1-s)/c=c/(1+s).

Both a,b are strictly between zero and one. The line cannot intersect the bottom or left parameter sides inside their unit intervals because c,s<1. Thus this triangle is the whole feasible domain, not a subset selected for convenience.

For every fixed corner label i,j, the vector

    Z_ij=P+(i-u)e+(j-v)g

is affine in u,v and its squared norm is convex. Every feasible point is a convex combination of the three parameter vertices. Strict corner bounds at all three vertices therefore yield a strict bound at every feasible point. The actual orientation c,s remains arbitrary during this reduction.

## 5. All twelve extremal corners

At (u,v)=(1,1), the full square has

    1/2-c<=x<=1/2+s,
    d-c-s<=y<=d.

Thus |x|<=3/2, and |y|<=d because c+s<=sqrt(2)<2d. All four corners satisfy the common strict bound d^2+9/4<R^2. This is the only comparison where the full threshold d>1/sqrt(2) is needed.

At (u,v)=(1,b), the identities c-bs=b and bc=1-s give exactly the four printed corners:

    (1/2-b, d-1),
    (1/2+bs, d-1+s),
    (1/2-b-s, d-1+c),
    (1/2-s(1-b), d-1+c+s).

For the first three, |x|<=3/2 and |y|<=d; all satisfy the common strict bound. For the fourth, |x|<=1/2 while its height belongs to [d,d+1), since 1<c+s<=sqrt(2)<2. Its squared norm is strictly below 1/4+(d+1)^2. All four corners are therefore covered uniformly.

At (u,v)=(a,1), the identities as=1-c and s-ac=a yield

    Z_00=(1/2+a,d-1),
    Z_10=(1/2+a+c,d-1+s),
    Z_01=(1/2+a-s,d-1+c),
    Z_11=P+(1-a)e.

The first and third satisfy the same |x|<=3/2, |y|<=d bound. The other two require genuine coupled estimates; they are checked independently below.

These counts cover four plus four plus four corners. The convex reduction preserves their correct corner labels; it does not compare a corner of one actual square to an unrelated label of another frame.

## 6. Independent expansion of the two coupled deficits

For Z_10, direct expansion gives

    R^2-|Z_10|^2
      =2d(2-s)-1-c+a-a^2
      =4d-1-(2ds+c)+a-a^2.

To check the cancellation, before using a(1+c)=s the constant terms are

    -1-a-c-a^2-2ac+2s.

Substituting 2s=2a+2ac produces precisely -1-c+a-a^2. Thus the printed identity has the correct signs.

Since 0<a<1 and 2ds+c<=sqrt(4d^2+1),

    R^2-|Z_10|^2>=4d-1-sqrt(4d^2+1)>0.

The last comparison is strict for d>2/3: 4d-1 is positive and the difference of squares is 4d(3d-2)>0. Our domain d>1/sqrt(2)>2/3 supplies this.

For Z_11=P+(1-a)e, expansion first gives

    R^2-|Z_11|^2
      =2d-c-2ds+ac+2das+2a-a^2.

Using as=1-c and ac=s-a gives exactly

    4d-(2d+1)c-(2d-1)s+a-a^2.

Cauchy's inequality bounds the linear combination by sqrt(8d^2+2), yielding

    R^2-|Z_11|^2>=4d-sqrt(8d^2+2)>0.

Here 4d>0, and its squared reserve is 8d^2-2>0 for d>1/2. Again the standing domain is strictly stronger. Neither deficit invokes any radius upper bound or bounds the orientation away from an aligned limit.

## 7. Transfer to the whole original unit

Each of the four corner-norm functions is strictly below R^2 at all three parameter vertices. Convexity therefore puts every corner of the unchanged actual E strictly inside the disk. The entire unit is the convex hull of its corners; its squared norm is at most the maximum of those four strict values. Thus every point of the whole closed E has norm strictly below R.

This proves the stronger implication even when the original E was not assumed contained. If E is physically boundary at radius R, its actual circle point makes the alleged low point impossible. The strict whole-half-plane conclusion follows, including equality of the hypothetical minimum with d-1.

The proof never chooses a normal, changes a contact point, applies a two-force equation, assumes a concurrence lies inside a unit, or distinguishes positive from zero individual circle coefficients. Its force-free statement automatically includes every true degree and all additional physical contacts.

## 8. Accepted scope and caller obligations

For an actual radial S square

    [d,d+1]n+[-1/2,1/2]f,

any actual point Q on either tangential side has the needed projection values. Every physically boundary neighboring unit containing that actual point therefore lies strictly beyond n projection d-1, throughout R>=2 and indeed throughout the stronger stated d domain.

A future caller must still prove its own actual point satisfies those coordinate conditions and that its neighboring unit is physically boundary. The theorem does not assert those hypotheses merely from a force direction, nor does it by itself exclude a whole graph/load family.

The manuscript correctly states these limits. It provides a reusable full-radius geometric strengthening, not an implicit adoption of every old caller or a new original gate closure.

The complete audit used hand coordinate derivation and exact algebra only. No numerical pose search, mesh, optimization, Lean compilation, CI, workflow, shared ledger edit, commit or remote write was performed.

