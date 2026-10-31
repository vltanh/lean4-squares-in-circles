# A circle-boundary unit cannot support a shallow horizontal side of a D-leaf root

Date: October 27, 2026.

**Status: complete force-free geometric lemma; full root and separate
independent reviews accepted.** The lemma removes both the endpoint proper
concurrence and the owned-contact selection from the upper-contact
argument. No neighbor degree or positive circle weight is required.

## 1. Exact physical domain

Keep actual contained, interior-disjoint units H,L,T, with the original
circle origin O and

    2<R<=sqrt(1105)/16,
    r=R-sqrt(2), s=1-r,
    H=[-s,r] times [-b,a], a,b>0, a+b=1,
    0<a<=1/4.

The actual L is the radial D unit with vertices

    (r,0), (r+sigma,sigma), (R,0), (r+sigma,-sigma),
    sigma=1/sqrt(2).

Assume T physically touches both H and the containing circle. Take
any actual common support point p and unit normal n directed from
H into T. This includes every shared-side mean, every point owner,
and any genuine vertex/vertex normal.

**Theorem.** Such a normal cannot have n_y>0.

No stress or force equation is a premise of this theorem. In
particular T may have arbitrary other contacts and zero total
circle weight. The three physical units are not moved.

The exact D margins, proved in
D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, Section 2, are

    1/2<r<2/3, 1/3<s<r, r^2-s^2>1/16.                 (1)

We also use r>11/20. Every point of a physical boundary unit has
norm at least r, by the unit diameter. Therefore, if n_y>0, p lies
on the top side y=a or one of its endpoints. The northwest endpoint
has squared norm s^2+a^2<r^2, so is impossible. Thus n is either
north, or strictly northeast with p=(r,a). At a north contact write
p=(q,a). Then

    q^2>=r^2-a^2>s^2,  -s<=q<=r,
    0<sqrt(6)/5<q<=r,       |p|<3/4.                  (2)

The positive lower bound follows from r>11/20 and a<=1/4. The
norm bound follows from r<2/3 and
4/9+1/16=73/144<9/16. The same bounds with q=r hold for the
northeast vertex. These are bounds for actual physical points.

## 2. An upward vertex contact is impossible, without concurrence

First consider any actual T of the form

    T=P+[0,1]u+[0,1]w,
    P=(q,a), 0<q<=r, |P|>=r,
    u=(c,d), w=(-d,c), c,d>=0, c^2+d^2=1.

This includes every unit whose bottom support is a unique vertex
P; weak axis endpoints are harmless. Put

    Delta=c-d in [-1,1], Sigma=c+d=sqrt(2-Delta^2).

Both adjacent vertices have norm at most |P|+1<7/4<R. The only
possible physical circle corner is the opposite vertex

    Z=(q+Delta,a+Sigma).                               (3)

Set g=r-q>=0. Equation (2) gives r+q>1, and

    g<=a^2/(r+q)<1/16.                                (4)

If Delta>=1/2, the actual side P+t u meets the inner upper D-leaf
edge y=x-r at t_0=(a+g)/Delta<5/8<1. Its height at that meeting
point is (ca+dg)/Delta, strictly between zero and 5/8<sigma.
Hence it is in the relative interior of the leaf edge, and the
side enters int(L) immediately afterwards. A point of the closed
T in int(L) forces interior overlap. Thus

    -1<=Delta<1/2.                                    (5)

For fixed q,a, the derivative of the squared norm in (3) is

    2(q-a Delta/sqrt(2-Delta^2))>0

on the entire interval [-1,1/2]. For Delta<=0 positivity is
immediate; for Delta>=0 use q>2/5 and a<=1/4. In particular no
positive-concurrence premise or sign Delta>=0 is needed. By (1),(5),

    |Z|^2 < (2/3+1/2)^2+(1/4+sqrt(7)/2)^2
            =49/36+29/16+sqrt(7)/4
            <553/144<4<R^2,

using sqrt(7)<8/3. This contradicts the physical circle corner.

## 3. Every north support face is exhausted

If n=e_y and T's bottom support is a vertex, Section 2 applies.
If it is a side, T is aligned and has the full form

    T=[x,x+1] times [a,a+1].

The unchanged contact P=(q,a) belongs to that side. By (2),
x>=q-1>-1 and x<=q<=r. Disjointness from L forces x+1<=r+a:
otherwise choose y=a+epsilon<sigma with x+1>r+y. At that height,
the open horizontal interval of T meets L's interval (r+y,R-y).
This is impossible. Consequently every T corner has

    -1<X<11/12, 0<Y<=5/4,
    X^2+Y^2<1+25/16=41/16<4<R^2.

This includes both positive-length H--T intersections and an
aligned endpoint singleton. It retains every actual side mean.
Thus the complete north case is impossible.

## 4. A northeast contact owned by a T side is impossible

Let n=(cos(phi),sin(phi))=(c,d), 0<phi<pi/2, and P=(r,a).
If T's minimum-n support is a side, write its exact frame as

    k=(-d,c),
    T=P+[0,1]n+[-rho,1-rho]k, 0<=rho<=1.              (6)

Side endpoints are included. The actual side P-t k crosses the
inner upper leaf edge at t_0=a/(c+d)<1/4, at a height in (0,sigma).
If rho>t_0, it enters int(L). Therefore

    rho<=a/(c+d)<1/4.                                (7)

There is a second geometric leaf constraint. If d<=1/8, then
c>7/8 and c-d>3/4. The actual segment P+t n, 0<=t<=1, would
meet the same inner leaf edge at

    t_1=a/(c-d)<1/3<1,
    x-r=y=t_1 c in (0,1/3) subset (0,sigma).

It then enters the open leaf. This remains a contradiction even
when this segment is a T boundary side, since a closed-square
point inside the other square's interior forces interior overlap.
Thus

    d=sin(phi)>1/8.                                   (8)

We now bound every actual T corner. Since P.n>0, the far n-face
has strictly larger corner norms than the near n-face with the
same k coordinate. On the far face its negative-k endpoint has

    |P+n-rho k| <= |P|+sqrt(1+rho^2)
                  <3/4+sqrt(17)/4<15/8<2<R.

Its positive-k endpoint lies on the segment from P+n to P+n+k.
The first point has norm below 7/4<R. For the second, the exact
identity R=r+sqrt(2) and (8) give

    |P+n+k|^2-R^2
      = a^2+2(r+a)c+2(a-r)d-2sqrt(2)r
      < a^2+(9/4)a+(7/4-2sqrt(2))r
      < (65-46sqrt(2))/8 < 0.                         (9)

Here a<=1/4 makes its first two terms at most 5/8; the coefficient
7/4-2sqrt(2) is negative and r>2-sqrt(2). The final comparison
is exact because 2*46^2-65^2=7>0. Convexity of squared norm on
the segment therefore bounds the actual positive-k corner strictly
below R as well. All four T corners are strictly inside the circle,
contradicting physical contact. No radial-mask or weight assumption
entered any of these inequalities.

## 5. Every genuine northeast vertex/vertex contact is also impossible

It remains that P=(r,a) is a vertex of T and the strictly northeast
n is in its minimum-support normal cone. The interior tangent
sector of H at P is the southwest quadrant. T's inward right-angle
sector has disjoint interior from that quadrant. Choose its two
orthogonal inward side directions in counterclockwise order with
angles theta,theta+pi/2. After the consistent lift they satisfy

    -pi/2<=theta<=pi/2.

The northeast n lies in their cone, so theta is strictly between
-pi/2 and pi/2. If theta<=0, the first side direction is (c,-d)
with c>0,d>=0,c^2+d^2=1. The side from P in that direction crosses
the inner upper leaf edge at

    t_0=a/(c+d)<=1/4<1,
    x-r=y=t_0 c in (0,sigma),

and enters the open leaf. Thus theta>0. T now has precisely the
upward vertex form of Section 2, with q=r, which was already
excluded. This covers the entire free vertex/vertex interval,
including every original selected normal; no generic exclusion
or endpoint-normal perturbation was used.

The northwest, north and northeast alternatives exhaust n_y>0.
This proves the theorem at the stated whole physical scope. Its
vertical reflection gives the corresponding shallow bottom-side
statement. The other six original squares, if present, remain
unchanged and unrestricted throughout this local argument.

No force, canonical minimizer, concurrence, degree-two assumption,
new normal choice, numerical pose, coefficient certificate, Lean
compilation or CI is used by this geometric lemma.
