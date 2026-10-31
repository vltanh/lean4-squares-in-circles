# A nonparallel boundary tip on a common hub face cannot own its return contact

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed uniform hand theorem, awaiting full root
and separate independent review.** This is a whole local owner
exclusion with arbitrary hub and return degrees. It is not a closure
of an original graph/load family.

## 1. Full physical statement

Let U,V,W be actual pairwise interior-disjoint closed unit squares,
contained in the same disk of radius R>2 about the unchanged origin.
Keep their physical triangle UV,UW,VW.

The original UV separating normal is an actual side axis of U.
Assume the same U side also supports W on its exterior side, so
the UV and UW normals from U are the same own axis. The UW
contact may be physical with zero pair weight. Its complete
contact set and every original mean remain.

Assume V is loaded, has exactly the two positive pair neighbors
U,W, and its actual frame is not parallel to U. Thus the original
UV contact is V's uniquely supported vertex. Assume W physically
touches the containing circle. The degrees, loads and all other
forces at U and W are arbitrary.

**Theorem.** The original V-to-W normal cannot be a side axis of V.

The conclusion covers either physical circle mask at V, every
individual zero corner weight, all actual V-side means and their
endpoints, and every W frame. It needs no generic-normal
selection and no upper bound on R. No force at U or W is used
or removed.

## 2. Actual port order and the complete owned-axis chart

Rotate about the unchanged origin so the common U side is x=a,
with U on its left and V,W on its right. The unique minimum-x
vertex of V is P=(a,t), an actual point of that length-one U side.

The point P cannot also belong to W. The inward tangent cone of
V at P contains East in its open interior, because V is not
axis-parallel. Any contained W with minimum x=a and containing
P has an inward tangent sector on the right with interior on at
least one side of East. That sector would overlap V's sector.
This contradicts disjoint open interiors.

The minimum-x support set of W is a point or an interval. It
therefore lies wholly above or wholly below P; otherwise it
would contain P. Reflect all data vertically so it lies below.
Choose its actual contact point P_W with U and write

    P_W=(a,t-delta),       0<delta<=1.                 (1)

The upper bound is the actual length of the same U side,
not a substituted mean or a distance estimate between centers.

Write V's actual inward axes from P as

    e_1=(c,-s), e_2=(s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                            (2)

If V owns its VW normal, the physical triangle side-axis
obstruction applied at V gives

    n_VW dot (-East)>=0.

Thus the only possible V axes are -e_1 or -e_2. The first
is impossible: it would put W in
e_1 dot (z-P)<=0, whereas (1) has

    e_1 dot (P_W-P)=s*delta>0.

Hence the actual original normal and its original application are

    n_VW=-e_2,
    M=P+u e_1,       0<=u<=1.                         (3)

This is the full actual side interval on V.

Suppose first W also owns the direction e_2. Its frame is
parallel to V. Since it is on the lower side of (3), its
actual square has the form

    W=P+xi e_1-e_2+[0,1]e_1+[0,1]e_2.

Its minimum x equals a, so xi*c-s=0 and xi=s/c.
Its minimum-x vertex then has height t-1/c. Its contact
with the same U side would require 1/c<=1, impossible
because 0<c<1. This excludes the entire parallel frame,
including a limiting point intersection.

Thus M is an actual uniquely supported W vertex. W
cannot be parallel to the global axes either: its vertex
abscissas would be a and a+1, whereas
M_x=a+u c lies in [a,a+c]. The only possible equality
would be M=P, already excluded above.

Write W's actual axes at its unique leftmost vertex as

    (C,S), (S,-C),       C,S>0, C^2+S^2=1.

Put

    d=Cc-Ss,       e=Cs+Sc.

Its maximum e_2-support cannot be its rightmost vertex,
whose abscissa a+C+S is greater than a+1>a+c.
It cannot be its leftmost or bottom vertex, because
e_2 dot (C,S)=e>0. The zero case d=0 would make e_2
a W side axis, already excluded. Thus d>0 and M is
the actual upper vertex P_W+(C,S).

The two coordinate equalities at M give

    u=C/c,
    delta=S+(C/c)s=e/c.                               (4)

Consequently, with r=s/c,

    d,e>0,       d^2+e^2=1,
    0<u<=1,      u=d+r e,
    r e<=1-d,    r e<=d.                              (5)

The last inequality follows from e<=c in (1),(4):
e^2(1+r^2)<=1 implies r e<=d. These are whole
continuous-domain inequalities from the original two
support contacts. No selected angle or pose is used.

## 3. The complete V2 equations control the actual circle corner

Use the actual orthonormal axes (2) about the original
circle origin and write

    A=P dot e_1, B=P dot e_2,
    X=A+1, Y=B+1.

The original positive pair magnitudes at V are mu on UV
and nu on VW. Its full outward circle resultant F is

    F=mu*East+nu*e_2,
    F_1=mu*c>0, F_2=mu*s+nu>0.                        (6)

If A<-1/2, every physical circle corner has its first
own coordinate A<0, which contradicts F_1>0. The same
argument with F_2 gives B>=-1/2. Therefore

    A,B>=-1/2, X,Y>=1/2,
    Z=(X,Y) is an actual physical circle corner,
    X^2+Y^2=R^2>4.                                   (7)

If B=-1/2, then X>sqrt(15)/2>1, so A>0. The full
original V torque is

    mu*t=nu*(A+u),
    t=-A*s+B*c.                                      (8)

Its left side would be negative and its right side
positive. This is impossible. Hence B>-1/2.

If A>-1/2 as well, Z is the unique physical circle
corner and F_1/F_2=X/Y. If A=-1/2, the complete
physical two-circle mask consists of (-1/2,Y) and
(1/2,Y). Every nonnegative weighting of positive total
weight with F_1>0 satisfies

    0<F_1/F_2<=X/Y.                                  (9)

This retains both individual zero corner weights. In
the unique mask equality holds in (9).

Eliminating mu,nu from (6),(8) gives exactly

    F_1*(B+r u)=F_2*(A+u).                            (10)

The quantity B+r u is positive. Otherwise (10) would
give A+u<=0, hence A,B<=0. Together with (7) that
would imply R^2<=2, impossible.

Substituting (9) into (10) and rearranging yields

    X*(1-r u)<=Y*(1-u).

Here r<1: from (5),
r<=(1-d)/e<1, because d,e>0 and e>1-d.
Thus 1-r u>0. With k=X/Y,

    0<k<= (1-u)/(1-r u)<=1-d.                        (11)

For the last comparison, the difference of the
cross-multiplied sides is

    (1-d)*(1-r u)-(1-u)
      =r*(e-u*(1-d))>=0,

since u<=1 and e>=1-d. In particular

    Y>2/sqrt(1+(1-d)^2)>=sqrt(2).                    (12)

The second weak inequality merely enlarges the domain;
the first is strict because R>2. Every original mean
and both physical corner masks remain in (8)--(12).

## 4. All possible remaining W circle corners are strictly inside the disk

Two W vertices are M, its actual contact with V, and
P_W, its actual contact with U. Neither can be a
physical containing-circle point. For completeness, a
unit touching the circle at a corner has both inward
side axes making strictly negative scalar product with
that corner: the adjacent contained corners give
2 Z dot v+1<=0. Its right-angle tangent sector is
therefore strictly inside the inward open tangent
half-plane. Two such right-angle sectors cannot have
disjoint interiors within that same open half-plane.
Thus a physical circle point cannot be shared by two
packing units.

It remains to check the other two actual W vertices.
In V coordinates the two inward axes from M are

    (-d,-e), (e,-d).

Put

    x=u+e-1, H=1+d.
    0<=x<=e, x<=2d.                                 (13)

Indeed u>=d and d+e>=1 give x>=0; u<=1 gives x<=e;
and r e<=d gives
x=d+r e+e-1<=2d+e-1<=2d.

The first remaining W vertex is

    C_W=(X+x,Y-H).

Its exact squared-radius deficit is

    R^2-|C_W|^2
       =2Y*(H-k x)-(H^2+x^2).                        (14)

We prove this strictly positive over the whole domain
using three elementary intervals for the single scalar
d. These inequalities enlarge the physical domain and
do not enumerate physical poses.

If 0<=d<=1/3, then Y>sqrt(2)>7/5. With (11),(13),

    (14)>(14/5)*(1-d+2d^2)-(1+2d+5d^2)
         =(3/5)*(3-8d+d^2)>=4/15>0.

The last quadratic is decreasing on this interval.

If 1/3<=d<=1/2, then k<=2/3 and
Y>6/sqrt(13)>13/8. The latter squared reserve is

    36/13-169/64=107/832>0.

Thus

    (14)>(13/4)*(1-d+2d^2)-(1+2d+5d^2)
         =(3/4)*(1-2d)*(3-d)>=0.

The initial strict inequality includes d=1/2.

If 1/2<=d<=1, then k<=1/2 and Y>3/2.
Using x<=e and H^2+e^2=2H gives

    (14)>3*(H-(1-d)e)-2H
         =H-3(1-d)e
         >=4d-2>=0.

The strict inequality again includes d=1/2.
The coefficients H-k x used with lower bounds on Y
are positive in all three intervals; the first two
bound them below by 1-d+2d^2>0, and the third by
H-(1-d)e>=2d>=1. This proves |C_W|<R.

For the last vertex, put

    L=d-x, H_2=1+d+e,
    D_W=(X-L,Y-H_2).
    |L|<=1, 2<=H_2<=1+sqrt(2).                       (15)

The elementary concave quadratic satisfies

    2sqrt(2)*H_2-H_2^2>=1                            (16)

on this entire interval: its endpoint values are
4sqrt(2)-4>1 and 1.

If L>=0, then (11)--(12),(15)--(16) give directly

    R^2-|D_W|^2
       =2Y*(H_2+k L)-(H_2^2+L^2)
       >1-L^2>=0.                                    (17)

If L<0, set ell=-L=x-d>0. From (5),(13),

    ell<=min(d+e-1,e-d).

Using e<=1-d^2/2, first on d<=1/2 and then on
d>=1/2, gives

    ell<=3/8,        k*ell<=1/5.                      (18)

Here are the full scalar checks. When d<=1/2,

    ell<=d-d^2/2<=3/8,
    k*ell<=(1-d)(d-d^2/2)
           <=d-(5/4)d^2<=1/5,

where 1/5-[d-(5/4)d^2]=(5/4)(d-2/5)^2.
When d>=1/2,

    ell<=1-d-d^2/2<=3/8,
    k*ell<=(1-d)(1-d-d^2/2)<=3/16<1/5.

For the last bound, both nonnegative factors decrease
on the relevant interval; if the second factor were
negative, ell>0 would already be impossible.

Since H_2-k*ell>=2-1/5>0, (12),(16),(18) yield

    R^2-|D_W|^2
      >1-(2sqrt(2))/5-9/64
      >1-3/5-9/64=83/320>0.                          (19)

Thus |D_W|<R as well.

All four actual W vertices are strictly inside D_R.
By convexity the whole W is strictly circle-clear.
This contradicts its original physical boundary
premise and proves the theorem.

## 5. Literal common-face use and exact limits

In the same-axis branch of the original
M6.B6.HEXAGON.D02.L01345 family, take

    U=2, V=1, W=0.

The actual UV and UW normals may both be the same
side axis of U. If V is nonparallel to U, its physical
UV contact is a singleton. The theorem excludes
every original VW normal owned by V, without
changing the true unloaded U3, loaded V2 or loaded
W3 equations. Only the complete V2 equations are
used in the local contradiction. The three arbitrary
completion units remain irrelevant to that core
owner exclusion.

If both actual UV and UW contacts have positive
length on the same U side, the separate complete
pocket-capacity theorem handles their whole feature.
This source supplies a different, nonparallel
interface and does not silently identify the two.

The actual W-owned VW normal, a free vertex/vertex
normal, and a V frame parallel to U are not excluded
by this theorem alone. The common selected fixed-tip
theorem can remove some free normals when its
physical-unique and fixed-application hypotheses
hold, but that additional selection is not used or
claimed here. In particular no physical two-circle
mask is erased by referring to a unique-circle
selection theorem.

No original fine family, graph parent or coarse cell
is closed by the present local owner result.

## 6. Sources and audit boundary

The only imported geometric implication is
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, SHA-256

    b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207,

used in Section 2 at its complete physical triangle
scope. Its nonobtuse-normal statement applies to an
owned axis even when the other normal is not owned.
All subsequent geometry, circle masks, full V2
equations and scalar estimates are proved above.

The actual original graph/load substitution is from
SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md, SHA-256

    cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1.

All coordinates are in frames of the same actual
squares about the unchanged circle origin. No
force, mean, square or degree is altered. The
inequalities are entire continuous-domain hand
bounds, with their strict endpoint reserves printed.

No numerical pose search, orientation mesh,
computational exclusion certificate, Lean
compilation, CI, workflow, ledger edit, commit,
push or merge is part of this manuscript.

