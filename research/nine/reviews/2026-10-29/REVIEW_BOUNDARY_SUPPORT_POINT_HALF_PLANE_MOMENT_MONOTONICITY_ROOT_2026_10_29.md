# Independent review: a support point controls contact moments across a half-plane

Date: October 29, 2026 UTC. Reviewer: current root continuation.

**PASS at the complete stated scope.** This is a new independent review of
`BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md`, SHA256
`c1694bb4265871e2f2c499e16a2e7ac01173b436966558a90e245e79856fbe9b`.
I read its complete source and independently reconstructed the geometric
argument below. The source is unchanged. Its author was the earlier
pentagon continuation; this review is not that author's own reread.

The theorem is force-free except for the hypothesis that the given
nonzero nonnegative resultant of physical circle contacts has a specified
vertical sign. Its star corollary uses the entire displayed force equation
at arbitrary degree. Neither conclusion is a complete original graph/load
exclusion, and no original fine or coarse checkbox follows by itself.

## 1. Exact hypotheses and the universal support budget

The same actual unit squares lie in the disk of radius R about the same
origin, their open interiors are disjoint, and R>sqrt(2). The boundary
square K has an actual minimum-x support point P=(X,h) with X>-1/2 and
h>=0. The horizontal direction need not be an own axis of K. A nonzero
nonnegative combination F of its physical circle corners satisfies F_y<=0.
At every actual K-to-T contact, g is the unchanged outward unit normal
and q is the actual application or unchanged shared-side mean.

For an arbitrary contained square of center z and orthonormal axes u,v,
the farthest-corner identity is

    max |z+(epsilon u+eta v)/2|^2
      = |z|^2+1/2+|z.u|+|z.v|
      >= |z|^2+1/2+|z|.

Thus |z|<=sqrt(R^2-1/4)-1/2. Every unit square has projection halfwidth
at least 1/2 in every unit direction. If an actual neighbor lies in
g.Z>=q.g, its center therefore has g projection at least q.g+1/2, giving

    q.g <= d := sqrt(R^2-1/4)-1 < R-1.                 (A)

This estimate uses the whole neighboring unit; it needs no circle contact,
force, positive degree, orientation or prescribed contact owner at T.

The elementary vector comparison used later is strict. If A>0, B>=0,
g_y>0 and det((A,B),g)<0, then B*g_x>A*g_y>0. Hence g_x>0 and

    (A,B).g > A*g_x + A*g_y^2/g_x = A/g_x >= A.        (B)

This also handles the endpoints of any actual normal cone. If B=0,
the stated premises are impossible, so nothing is divided by B.

## 2. Tilted minimum vertex: complete physical mask and all features

Write K=P+[0,1]u+[0,1]v with u=(c,s), v=(s,-c), c,s>0 and
c^2+s^2=1. This is the entire strictly tilted minimum-x-vertex case.
Put U=P+u, V=P+v, W=P+u+v. The exact norm differences are

    |U|^2-|P|^2 = |W|^2-|V|^2 = 1+2Xc+2hs > 0.

The strict inequality follows already from X>-1/2 and c<1.
Thus neither P nor V can be physical circle corners. Since U_y=h+s>0,
F_y<=0 forces W to be a physical corner with W_y<=0. Consequently

    c>=s, 0<=h<=c-s,
    R^2=(X+c+s)^2+(h+s-c)^2.                           (C)

This argument allows U to be an additional physical circle corner and
keeps zero individual coefficients. It never changes a two-corner mask
into a unique mask merely because one coefficient vanishes.

If X<=0, then 0<X+c+s<=c+s and (C) implies
R^2<=(c+s)^2+(c-s)^2=2, contradiction. Hence X>0. For A=U_x=X+c,

    (A+1)^2-[(A+s)^2+(c-s)^2]
       =2A(1-s)+s(2c-s)>0.

Together with (C), this gives U_x>R-1>d. By (A) and (B), no actual
contact at U can have both positive g_y and negative origin moment.

I checked the entire remaining feature cover. At P, every positive-y
outward normal has negative x component, so X*g_y-h*g_x>0. At V,
both generators -u and v of the outward cone have negative y. At W,
both cone generators have positive x and W_y<=0, so positive g_y
gives positive moment. On P--V and V--W the side normals have negative
y. On P--U the normal is (-s,c), giving positive moment at every point.
On U--W the normal is u, and q=U+t v gives

    det(q,u)=det(U,u)+t, 0<=t<=1,
    q.u=U.u.

A negative moment anywhere on this whole side therefore forces a
negative moment at U with the same support, already excluded. This is
why the proof retains arbitrary original shared means and both endpoints.
The equalities h=0, h=c-s and c=s cause no loss of strictness above.

## 3. Aligned minimum side: coefficient and geometric endpoints retained

In the aligned case K=[X,X+1] times [B,B+1], and the given support point
satisfies B<=h<=B+1 with h>=0. Every circle corner is on the right side,
because its squared norm exceeds that of the matching left corner by
2X+1>0. A nonpositive-y physical corner forced by F_y<=0 must be the
lower right one: B+1>=0, and if B+1=0 the lower corner has strictly
larger norm. Therefore

    -1<=B<=-1/2, R^2=(X+1)^2+B^2.

The endpoint B=-1/2 is precisely the physical two-corner mask and is
retained with all its possible coefficient weights. Since R^2>2 and
B^2<=1, X+1>1 and X>0. At the upper right vertex U,

    R^2<=U_x^2+1<(U_x+1)^2,

so U_x>R-1>d. Its positive-y negative-moment normals are excluded by
(A) and (B). The top side and upper left vertex have strictly positive
moment for positive-y normals. The lower cones and bottom side have
nonpositive y; the two vertical side normals have zero y. This covers
the complete aligned square, not only a chosen application on its face.

Sections 2 and 3 prove the full implication

    det(q,g)<0 implies g_y<=0.

Reflection in the vertical axis reverses the determinant and preserves
the vertical component. It gives exactly the printed maximum-x version
with det(q,g)>0 implying g_y<=0. No origin translation occurs.

## 4. Arbitrary-degree full-star consequence

For the reflected support hypothesis retain the complete equation

    F - sum_i lambda_i N_i + sum_j mu_j g_j = 0,

with every lambda_i,mu_j positive, every incoming (N_i)_y>=0 and every
outgoing original moment det(q_j,g_j)>0. If F_y<0, the reflected
geometric theorem gives every (g_j)_y<=0. The exact vertical projection
then gives F_y=sum lambda_i (N_i)_y-sum mu_j (g_j)_y>=0, contradiction.
If one incoming vertical component is strictly positive, the same
reasoning under F_y<=0 gives a strict contradiction. Hence F_y>=0 in
general and F_y>0 in the stated strict case.

No concurrence, degree-two equation, replacement resultant or deleted
positive force is used. The actual unit's full nonnegative physical
circle mask must still provide a nonzero F; this hypothesis is essential.

## 5. Adoption boundary

The entire source is accepted unchanged for all R>sqrt(2), without an
upper radius restriction. A caller must establish its original support
point, X>-1/2, h>=0, nonzero physical circle resultant, complete incoming
signs and every stated outgoing moment sign. This review does not supply
those hypotheses to any still-open house or block family.

The source cites the equation convention in PHYSICAL_CONTACT_STRESS.md,
SHA256 d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.
The geometric proof and the displayed-equation corollary above are
self-contained; acceptance does not assert the global extraction audit.
No numerical pose search, packing certificate, Lean compilation, CI or
merge was used. No original obligation flag is changed by this review.
