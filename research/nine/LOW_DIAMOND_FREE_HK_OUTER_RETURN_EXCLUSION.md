# The entire bottom and far-vertex return is impossible at a free HK junction

**Status: complete geometric hand proof; author, root and separate
independent full saved-source/direct-prerequisite review passed on
October 25, 2026. See REVIEW_FREE_HK_DIAMOND_2026_10_25.md. No gate
checkbox or ID is added.**

Keep the original nine physical squares, true H5/K3/A2/B2, all original
forces and application means, the intact HXY petal and all three arbitrary
completion squares. A,K,B are physically circle-touching in the declared
radius window; A and K have unique physical circle corners and B retains
either physical mask and every individual weight endpoint.

**Theorem.** In the free HK row of the negative-A upper-left chart, the
whole K-bottom KB side and the far bottom-right KB vertex are impossible.
This includes every bottom-side shared interval and original mean. The
proof also gives the complete KB feature fan and removes its right side.
No force equation is used in this geometric exclusion, and no selected
normal is changed.

## 1. The exact original free-junction chart

Use positively oriented (f,g) coordinates and the original A frame:

    A=[x,x+1] x [b-1,b], P=(x,b-1), T=(x,b),
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    E=su+cv>0, d=sv-cu>0,
    r0=s/E in (0,1), delta=v/E in (0,1),
    V=P+r0 j=T-delta f,
    H=V+[-1,0]n+[-1,0]j,
    K=V+[0,1]f+[0,1]g.

Thus in K coordinates n=(E,d), j=(-d,E). Write V=(X,h).
The original HK force has its actual free normal strictly between n and
g. The equalities above are the physical vertex/vertex row of the accepted
complete HK fan; they do not substitute either endpoint for that force.

The physical angular-order theorem CIRCLE_CONTACT_ANGULAR_ORDER.md
excludes a triangle of three circle-touching squares. Since A touches K
and K touches B, necessarily

    A intersect B is empty.                            (1)

This concerns physical contact, not only a positive stress edge, and is
valid for both physical B masks and every circle-weight endpoint.

## 2. Auxiliary geometric normals give the complete original KB fan

Let ell be the actual H-to-B normal and k the actual K-to-B normal.
The vector n is a geometric H-to-K separator: it is an H side axis,
and K's minimum-n point is V. Likewise -g is a geometric K-to-H
separator owned by K, since H has its unique maximum g coordinate at V.

Apply UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md in the actual HKB
triangle using these two auxiliary support axes. The theorem concerns
physical support directions, so it does not require either axis to equal
the selected free HK normal. It gives

    ell.n>=0, k_g<=0.                                  (2)

Accordingly the whole selected KB support fan is

    k=-f:          K's left side;
    k=+f:          K's right side;
    k=-g:          K's bottom side;
    k_f<0,k_g<0:   near vertex V;
    k_f>0,k_g<0:   far bottom-right vertex V+f.

For k=+f, all B points have f coordinate at least X+1, while

    max_H f=X+d<X+1.

Thus HB is impossible and this whole right-side alternative is excluded,
including its possible shared means. The following two sections exclude
the bottom side and the far vertex without any further owner assumption.

## 3. The actual A square blocks every bottom point beyond T

We prove a stronger pointwise statement. B cannot contain any actual
point

    Q=V+t f=T+epsilon f,
    delta<t<=1, epsilon=t-delta>0.                     (3)

This includes the far vertex t=1. It does not assume that the actual KB
normal is a side axis.

If ell.n=0, then ell is j or -j. Since

    j.Q=j.V-dt, 0<dt<1,

Q lies strictly between the two j supporting lines of H. But B would
have to lie beyond one of those lines to realize ell=j or ell=-j.
This contradicts Q in B.

Therefore ell.n>0. Every maximum-ell support point of H belongs to
its front n side. The original HB application, including any shared
mean, has the form

    Y=V-sigma j=P+(r0-sigma)j, 0<=sigma<=1.             (4)

Because Y and Q belong to the convex square B, the segment YQ belongs
to B. We show it meets A, contradicting (1).

If sigma>=r0, put z=sigma-r0>=0. In the original A coordinates,

    Y=(x+zv,b-1-zu),
    Q=(x+epsilon s,b+epsilon c).

Both x coordinates lie in [x,x+1), the Q coordinate is strictly greater
than x, and the segment runs from at or below A's bottom to above its
top. It therefore meets A. When z=0 the endpoint Y=P is already in A;
when z>0 the segment crosses A's interior.

If sigma<r0, put z=r0-sigma in (0,r0]. Then

    Y=(x-zv,b-1+zu),
    Q=(x+epsilon s,b+epsilon c).

The segment meets A's left supporting line at height

    y_cross=b+epsilon(zE-s)/(zv+epsilon s).              (5)

Its denominator is positive. Since z<=r0=s/E, this height is at most b.
It is strictly greater than b-1, since it is a strict convex combination
of Y's height b-1+zu>b-1 and Q's height above b. Thus the crossing point
belongs to A's left side, including the endpoint T if sigma=0.
Again B meets A, contradicting (1).

This proves the whole pointwise obstruction (3), with every possible HB
owner and original mean still present. In particular the entire strict
far bottom-right KB vertex is excluded.

## 4. The remaining complete bottom-side interval is also impossible

Suppose k=-g. Then B lies in the closed half-plane g<=h and its nonempty
physical contact with K lies on the segment V+[0,1]f. We inspect real
points of that contact set; no such point is substituted for the original
force mean.

Points beyond T are excluded by Section 3. The point T itself belongs to
A and is excluded by (1). It remains to treat points strictly between V
and T and the endpoint V.

### 4.1. The whole open segment VT faces a bounded triangle of area below one

The three distinct physical contacts V,P,T bound the triangle

    Delta=conv(V,P,T).

Its boundary segments VP,PT,TV belong respectively to H,A,K. The height
of P below the base VT is s, and that base has length delta. Thus

    area(Delta)=delta*s/2<1/2.                          (6)

If B contains a contact point in the strict interior of VT while lying
below K, a sufficiently nearby interior point of B lies in int Delta.
The connected open interior of B cannot cross Delta's boundary, which
is contained in the three physical obstacles H,A,K. In detail, an
obstacle boundary point inside int B would give a neighborhood meeting
the obstacle's open interior and hence forbidden interior overlap.
Therefore all of int B would have to lie inside Delta, contradicting
area(B)=1 and (6).

This is the direct bounded-triangle localization used in
CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Section 1. The present triangle
and its three actual boundary segments are explicit, so no artificial
face is introduced. The argument includes a singleton at a B vertex,
a B-side contact and a positive-length shared KB interval.

### 4.2. No unit square below K can contain V

Let theta be the angle from f to n, so 0<theta<pi/2. In the lower-g
half-plane at V, H occupies the right-angle tangent sector from angle
pi+theta to 3pi/2+theta. The two complementary sectors in that half-plane
have apertures theta and pi/2-theta, both strictly below pi/2.

Every point of a unit square has a connected local interior sector of
aperture at least pi/2: pi/2 at a vertex, pi at a side-interior point,
and 2pi at an interior point. Thus no square B lying below K and with
interior disjoint from H can contain V. This exclusion is geometric and
does not depend on strict-normal preselection.

The open segment, T, V, and all points beyond T exhaust K's entire
bottom side. Hence no actual k=-g contact is possible, including every
shared side and every original endpoint-valued mean.

## 5. Exact whole-feature conclusion

Sections 2--4 remove the right side, the entire bottom side and the far
bottom-right vertex from the full free-HK support fan. Only the near
vertex and the left -f side remain in that fan. The near vertex is
excluded, with its possible shared HB handled before coincidence, by
LOW_DIAMOND_FREE_HK_NEAR_RETURN_EXCLUSION.md. The complete left side is
excluded by LOW_DIAMOND_FREE_HK_SIDE_RETURN_EXCLUSION.md, which explicitly
retains the original free-HK K3 force and moment before verifying every
hypothesis of the preserved scalar comparison. It does not change the
free normal to g.

All three sources have passed root and separate independent review.
These exhaustive features exclude the entire free HK row for both
physical B masks UUS and UUU. The separate H-owned n singleton row is not closed by this join.

All arguments above retain both physical B masks, the original H5/K3,
every physical obstacle and every original force mean. They use no
numerical samples, angle subdivision, coefficient table, Lean compilation
or CI. No roadmap checkbox or new ID is introduced here.
