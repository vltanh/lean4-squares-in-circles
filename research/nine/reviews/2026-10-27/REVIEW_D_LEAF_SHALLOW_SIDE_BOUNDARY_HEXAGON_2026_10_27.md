# Independent review: the force-free shallow-side boundary exclusion at a D root

Date: October 27, 2026.
Reviewer: separate hexagon proof worker.
Source reviewed: D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md.

**Verdict: accepted as a complete force-free geometric lemma.** The
proof really does remove both the endpoint concurrence premise and
the contact-owner preselection. I checked every actual support feature,
including side endpoints and the complete free vertex/vertex sector.

## 1. Complete upper-support cover

The stated D-root chart has the actual occupied leaf, R>2, and
0<a<=1/4. A positive vertical component puts the original H port on
the top side. The northwest vertex has norm squared below r^2 by
r^2-s^2>1/16 and a<=1/4, so no physical boundary unit can contain it.
The remaining normals are exactly north and strictly northeast.

In the north case the actual port (q,a) has
q^2>=r^2-a^2>s^2. Since q>=-s, this forces q>0, rather than
merely a lower bound on |q|. The stronger stated q>sqrt(6)/5 and
r+q>1 follow from r>11/20. The uniform |P|<3/4 bound applies also
to the northeast vertex (r,a). These deductions use the boundary
unit's physical circle contact, with no stress-weight assumption.

## 2. All upward vertex frames, including negative Delta

The representation with inward axes (c,d),(-d,c), c,d>=0, covers
every bottom support vertex, including weak aligned endpoints. Both
adjacent vertices have norm below 7/4, so only the opposite vertex
can physically touch the circle. The actual port radius floor gives
g=r-q<=a^2/(r+q)<1/16.

For Delta>=1/2, the true side P+t(c,d) meets the inner upper D-leaf
edge at t_0=(a+g)/Delta<5/8<1. Its crossing height is positive and
below sigma. Thus it meets the relative interior of the inner leaf
edge, not its outer corner; for slightly larger t it enters the open
leaf. A point of the closed T inside int L already contradicts
interior disjointness. Hence Delta<1/2.

The opposite-corner norm is strictly increasing in Delta throughout
[-1,1/2]. The negative-Delta half is immediate from its derivative;
the positive half uses q>2/5 and a<=1/4. Thus the same upper bound
553/144<4 excludes the entire frame interval without needing the
older concurrence-derived sign Delta>=0. No physical mask or normal
owner has been removed to obtain this estimate.

## 3. North side supports retain all original means

For a north side support, T is the aligned unit
[x,x+1] times [a,a+1]. Membership of the actual contact mean gives
x>=q-1>-1 and x<=q<=r. If x+1>r+a, a horizontal section at a
slightly larger height a+epsilon<sigma meets the open leaf interval
(r+a+epsilon,R-a-epsilon), giving overlap. Therefore x+1<=r+a.
The whole corner set is inside the stated rectangle and has norm
squared below 41/16<4. This handles a positive shared segment and
an aligned singleton at an endpoint without any strict-normal
selection. It does not reset the contact to a convenient point.

## 4. Northeast support owned by a T side

The full side parameter rho is kept in [0,1]. The actual negative-k
side reaches the inner leaf edge at t_0=a/(c+d)<1/4, so rho<=t_0.
The strict bound uses c,d>0 and c+d>1; it still permits a=1/4.

If d<=1/8, then c>7/8 and c-d>3/4. The actual inward unit segment
P+t n crosses the same edge at t_1=a/(c-d)<1/3, with crossing height
t_1 c in (0,sigma). It then enters the leaf. This remains a valid
contradiction when rho is an endpoint and that segment is part of
T's boundary. Thus d>1/8 holds without force or concurrence.

The far normal face dominates the near face because P.n>0. Its
negative-k endpoint has norm below 15/8. The positive-k endpoint is
on the actual segment between P+n and P+n+k. The first has norm
below 7/4. For the second, I checked the exact identity and signs:

    |P+n+k|^2-R^2
      =a^2+2(r+a)c+2(a-r)d-2sqrt(2)r
      <a^2+(9/4)a+(7/4-2sqrt(2))r
      <(65-46sqrt(2))/8<0.

The first inequality uses c<=1, d>1/8 and a-r<0. The second uses
a<=1/4 and the negative coefficient of r together with r>2-sqrt(2).
The final exact comparison is 2*46^2-65^2=7>0. Convexity then
excludes every actual intermediate endpoint, including rho=0 or1.
All four actual corners are therefore strictly inside the circle.

## 5. The entire northeast vertex/vertex normal cone

At P=(r,a), H's inward tangent sector is the southwest quadrant.
An actual disjoint T has an inward right-angle sector with disjoint
interior from that quadrant. With a consistent angular lift, its
counterclockwise side angles are theta,theta+pi/2 with
-pi/2<=theta<=pi/2. For an orthogonal right-angle cone the inward
minimum-support normal lies in that same cone. The strictly northeast
n therefore excludes both endpoint theta values.

If theta<=0, the first side points (c,-d), c>0,d>=0. It crosses
the real inner leaf edge at a/(c+d)<=1/4<1, at a strictly positive
height below sigma, and enters the leaf immediately afterward. Thus
theta>0. Both inward sides then have positive vertical components,
so P is exactly the bottom vertex in Section 2 with q=r. That whole
case has already been excluded. This argument includes every allowed
free normal and uses no perturbation or post-extraction selection.

The actual T minimum-support face is either a side or a vertex, so
Sections 4 and5 exhaust the northeast branch. Together with Section3
and the northwest radius obstruction they exhaust every n_y>0.
Vertical reflection gives the full shallow-bottom counterpart.

The theorem is independent of T's true degree, positive load, other
contacts, circle-corner mask and individual zero weights. It retains
the original H, T and leaf L, with every side mean and every other
physical square. No force equation, canonical pose, concurrence,
sampled pose, numerical certificate, Lean compilation, CI, remote
action or shared-ledger edit was used in this review.
