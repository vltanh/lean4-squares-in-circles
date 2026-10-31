# A radial top neighbor cannot complete a small-side boundary triangle

Date: October 27, 2026.  
Author: topology_final.

**Status: complete fresh physical theorem, frozen for full independent review.**
The result excludes a whole physical two-circle-corner type, with every
contact owner and free vertex contact retained. It uses the actual containing
circle and actual square supports, and requires no force equation at any of
the three units. The closed central endpoint is included.

This is a new manuscript. It is not represented as a restoration of the
missing earlier whole C-mask manuscript.

## 1. Entire local domain

Let H, K and C be interior-disjoint closed unit squares in the disk of
radius R centered at zero. All three physical pair contacts H-K, H-C and
K-C are nonempty. Put

    R^2=(d+1)^2+1/4,       1<=d<61/60.                 (1)

Thus R^2>=17/4. Suppose the actual physical configuration has

    H=[h-1,h] x [G-1,G],
    -1/60<=h<=0,          0<=z<=G<=1,                (2)

and K has its strict minimum-x vertex at the actual point

    T=(h,z),
    K=T+[0,1]a+[0,1]b,
    a=(c,s), b=(s,-c),
    c,s>0, c^2+s^2=1.                               (3)

K touches the containing circle. The actual H-C contact has common
normal E2 from H to C: C has minimum height G and touches H's top
side. Retain its entire physical intersection and any actual contact
mean. Assume that C has two physical containing-circle corners.

**Theorem 1.1.** No configuration satisfying (1)--(3) and these physical
contact conditions exists.

The theorem includes h=0, z=G, G=1 and d=1. It makes no assertion
that the original central contact must be side-owned: at z=G the
contact may be free at H's upper-right corner. There is no owner
premise on K-C. K may initially have either physical circle mask,
and the two physical circle corners of C may have arbitrary
nonnegative individual weights. No weight is used in the proof.

Any further physical packing units and any original positive stress
remain present. A contradiction for the actual three-unit geometry
also excludes every completion of that geometry.

## 2. The actual K circle is its opposite corner, and z>4/5

For the strict minimum-x chart (3), the support vertex and adjacent
corners have squared norms

    |T|^2=h^2+z^2,
    |T+a|^2=h^2+z^2+1+2hc+2zs,
    |T+b|^2=h^2+z^2+1+2hs-2zc.                    (4)

Here h<=0, 0<=z<=1 and c,s>0. Consequently these are respectively
at most

    1+1/3600,       4+1/3600,       2+1/3600,

all strictly below 17/4. The upper adjacent reserve alone is

    17/4-(4+1/3600)=899/3600>0.                    (5)

A circle point of a contained square is a vertex: strict convexity
of the squared norm along a nonconstant side excludes a side-interior
maximum equal to R. Thus the actual physical circle contact of K
must be

    Z_K=T+a+b=(h+c+s,z+s-c).                       (6)

In particular this actual K has one physical circle corner; no
circle-mask reduction was assumed.

Define

    E=h^2+2h(c+s)=h[h+2(c+s)]<=0.                 (7)

The sign follows from -1/60<=h<=0 and c+s>1. The full actual
radius equation is

    R^2=E+2+z^2+2z(s-c).                          (8)

If s<=c, its right-hand side is at most 3, contradicting R^2>=17/4.
Therefore

    s>c.                                          (9)

If z<=4/5, then s-c<=1 and z>=0 give

    R^2<=2+(4/5)^2+2(4/5)=106/25<17/4,
    17/4-106/25=1/100.                            (10)

Hence the entire surviving physical domain satisfies

    4/5<z<=G<=1.                                 (11)

This conclusion comes from the actual K corner, for every c and s.

## 3. Exhaustive radial form of C, including the axis endpoint

A contained unit square with two circle corners has the exact
physical form

    C=[d,d+1]e+[-1/2,1/2]f,                       (12)

where e,f are orthogonal unit vectors. Its two circle corners are
(d+1)e plus or minus f/2. This elementary classification is also
proved in Section 3 of C7_FORCE_POLYGON.md: in the side frame of a
circle corner, both inward distances from zero are at least 1/2,
and a second corner has the same norm exactly when one distance is
1/2. The radius (1) excludes three or four circle corners.

Since every point of C has height at least G>4/5, the average of
its two circle corners has positive height. Therefore e_y>0.

If e_x>0, write e=(q,p), f=(p,-q) with p,q>0. C's unique
minimum-height vertex is d e+f/2. Its horizontal coordinate is
dq+p/2>0. This cannot belong to H's top side, whose horizontal
coordinates are at most h<=0. This entire orientation is impossible.

If e_x=0, then e=E2 and C's minimum height is d. Actual H-C
contact gives d=G. The closed bounds d>=1 and G<=1 force exactly

    d=G=1,    C=[-1/2,1/2] x [1,2].              (13)

This endpoint is excluded directly, as follows. Let

    F=(h+1/2,5/4),  L=5/4-z,
    A=c/2+Ls,      B=s/2-Lc.                     (14)

These are the two own coordinates of F-T in K, so F=T+A a+B b.
Equation (11) gives 1/4<=L<9/20. Both A and B are strictly
positive: A>0 directly, and by (9)

    B>s/2-c/2>0.

Also B<s/2<1/2, and Cauchy--Schwarz gives

    A^2<=1/4+L^2<181/400<1.                      (15)

Thus F is in the open interior of K. If h<0, its horizontal
coordinate is strictly between -1/2 and 1/2, so it is also in the
open interior of the C in (13). If h=0, F lies on C's right side;
because K is open around F, F-epsilon E1 lies in the interiors of
both squares for every sufficiently small positive epsilon. This
contradicts interior disjointness. All axis endpoints in (13) have
therefore been handled.

The complete remaining C chart is consequently

    e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1,
    C=[d,d+1]e+[-1/2,1/2]f.                      (16)

Its minimum-height vertex is the actual H-C application

    T_C=d e-f/2=(-dq-p/2,G),
    G=dp-q/2.                                   (17)

This is a physical singleton, irrespective of the initially
permitted H-C mean. The other inner vertex is

    V=d e+f/2=(V_x,V_y),
    V_x=p/2-dq,     V_y=dp+q/2=G+q.             (18)

From (11), (17) and d<61/60 we also have

    p>G/d>48/61,
    (T_C)_x<-24/61<-1/60<=h.                   (19)

The strict separation reserve in the last comparison is
24/61-1/60=1379/3660.

## 4. The two physical support facts used in the contact cover

The proof uses the following complete physical triangle fact:
for three pairwise touching interior-disjoint unit squares, two
actual outward normals n and m at one square satisfy n.m>=0
whenever n is a side axis of that square. It is the whole theorem
of UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Sections 1--2.

For completeness, if n.m<0 and the square's maximum n support is
H_n, every maximum-m application lies on its minimum-n face at
level H_n-1. For a unit neighbor with minimum-m support at that
same point, the positive n span is strictly less than 1.
At a vertex this follows by writing its two orthogonal inward
axes: at least one has negative n component, and the other
positive component is strictly below 1. At a side application
the inward m axis has negative n component and the tangential
unit component is strictly below 1; the whole actual side interval
is retained. That neighbor is therefore strictly below level H_n,
whereas the other neighbor is at or above H_n. Their physical
contact is impossible. This proves the triangle statement including
the retained equality n.m=0.

We also need the following elementary inner-face fact for (16).
No physical boundary unit can have a common contact with C on its
inner e face using the normal -e from C. To see this, write the
actual point as

    P=d e+t f, |t|<=1/2.

Such a neighboring unit has maximum e support d at P. Its entire
e-coordinate interval is contained in [d-sqrt(2),d], hence in
[-d,d] because d>=1. Its entire f-coordinate interval is contained
in [t-1,t+1], hence in [-3/2,3/2]. At a maximum-e vertex the two
orthogonal inward axes have nonpositive e components and opposite
f signs, giving this transverse span. At a side application the
inward axis is -e and the full actual tangential interval has length
1; the same bounds hold at every slider endpoint.

Every point of that whole neighboring unit therefore has squared
norm at most

    d^2+9/4<R^2,
    R^2-(d^2+9/4)=2d-1>=1.                     (20)

It cannot be K. This is precisely the horizontal-normal part of
C7_FORCE_POLYGON.md, Lemma 2.1, with its full side-point interval
reproduced here; no positive-load or cycle hypothesis is involved.

A containing-circle point cannot be shared by two contained
interior-disjoint unit squares. If Z is such a corner and v_1,v_2
are its orthogonal inward side directions, containment of Z+v_i
gives Z.v_i<=-1/2. Thus -Z points strictly inside each inward
quadrant, and Z-epsilon Z belongs to both open squares for small
epsilon if they shared Z. This is the physical argument in
Section 1 of C7_FORCE_POLYGON.md.

## 5. Every physical C-K contact is at V

Exhaust the whole boundary of the actual C in (16). If a physical
intersection with K meets the relative interior of a C side,
any common supporting normal is that side's outward normal.
The original actual stress normal, when one is present, is among
these same physical normals; none is changed.

On the outer e side the outward normal is e. Since the actual
C-to-H normal is -E2, the physical H-C-K triangle would require

    e.(-E2)=-p>=0,

which is impossible. The same argument excludes the relative
interior of the positive f side, since

    f.(-E2)=-q<0.

The entire negative f side, including T_C, has horizontal
coordinates at most (T_C)_x<h by (19), whereas every point of K
has x>=h. It is closed-disjoint from K.

The relative interior of the inner e side has normal -e and
cannot meet the boundary unit K by (20). The two remaining outer
vertices are the containing-circle corners and cannot be shared,
by Section 4.

All sides and vertices have now been covered. The only possible
actual physical C-K contact is the one inner vertex

    C intersect K={V}.                          (21)

This does not assert a side owner on C-K. In particular a free
vertex contact at V remains in the next step.

## 6. The complete actual K support cover at V

At the C vertex V, every nonzero outward supporting normal is a
nonnegative combination of -e=(q,-p) and f=(p,q). Both generators
have strictly positive x components, so every actual common normal
w from C to K satisfies

    w_x>0.                                      (22)

At K the same V is a minimum-w support point. Put

    A_w=w.a,    B_w=w.b,
    w_x=c A_w+s B_w.

The complete rectangle support cover is as follows.

| Signs of A_w and B_w | Actual minimum-w support of K | Consequence |
| --- | --- | --- |
| A_w>0, B_w>0 | T | Height z<V_y |
| A_w>0, B_w<0 | T+b | Height z-c<V_y |
| A_w>0, B_w=0 | T+[0,1]b | Every height at most z<V_y |
| A_w=0, B_w>0 | T+[0,1]a | Retained |
| A_w<0, B_w>0 | T+a | Retained |
| A_w<=0, B_w<=0 | A nonzero negative own-axis combination | Contradicts w_x>0 |

The last row includes either single zero coefficient; both zero
would give w=0 and are not a normal. Thus this table includes all
axis and vertex endpoints. Since V_y=G+q>z by (11) and q>0, the
retained alternatives give exactly

    V=T+theta a,       0<theta<=1.              (23)

The endpoint theta=1 is allowed. It contains the free K-vertex
possibility and has not been discarded by a strict-side convention.
Taking the actual horizontal coordinate in (23) gives

    theta c=V_x-h,
    c>=V_x-h>=V_x.                              (24)

This necessary relation is purely physical, for every actual
normal at V.

## 7. One whole C-angle estimate forces c>G-2/3

If q>=1/3, then p<=sqrt(8/9)<17/18. From d<61/60,
(17) and q/2>=1/6 we would obtain

    G< (61/60)(17/18)-1/6
      =857/1080<4/5,
    4/5-857/1080=7/1080.                        (25)

This contradicts (11). Consequently

    0<q<1/3.                                   (26)

On this whole interval, sqrt(1-q^2)<1-q^2/2 and the function
1+q-q^2/2 is strictly increasing. Hence

    p+q<1+1/3-1/18=23/18.                       (27)

The exact real coordinates (17)--(18) give

    G-V_x=(d-1/2)(p+q)
           <(31/60)(23/18)
           =713/1080<2/3,
    2/3-713/1080=7/1080.                        (28)

Combining (24) and (28) gives the entire continuous constraint

    c>G-2/3>2/15.                              (29)

No interval of C angles, actual K support normals, or side
applications has been sampled or omitted.

## 8. The complete K radius is too small

Put

    t=G-2/3,       2/15<t<=1/3.                 (30)

Along the positive unit quadrant the function
sqrt(1-c^2)-c is strictly decreasing in c. Therefore (29) gives

    s-c<sqrt(1-t^2)-t.                          (31)

Keep the actual K radius identity (8). Since E<=0, z<=G and
s-c>0, it gives

    R^2<=2+G^2+2G(s-c)
       <2+(t+2/3)^2
              +2(t+2/3)[sqrt(1-t^2)-t]
       =F(t),

    F(t)=22/9-t^2+2(t+2/3)sqrt(1-t^2).           (32)

The first inequality may be equality at the retained h=0,z=G
endpoint. The next inequality is strict by (29)--(31); it does
not require a strict central side position.

Differentiate on the entire closed interval in (30):

    F'(t)=2[1-2t^2-(2/3)t-t sqrt(1-t^2)]
                 /sqrt(1-t^2).                 (33)

Its numerator is uniformly positive, since 0<t<=1/3 yields

    1-2t^2-(2/3)t-t sqrt(1-t^2)
      >=1-2/9-2/9-1/3=2/9>0.                   (34)

Thus F is strictly increasing throughout the whole interval. At
the upper endpoint,

    F(1/3)=7/3+2sqrt(8/9)
           <7/3+17/9=38/9<17/4,
    17/4-38/9=1/36.                             (35)

Here sqrt(8/9)<17/18 is exact because
(17/18)^2-8/9=1/324>0. Equations (32)--(35)
contradict R^2>=17/4. This completes Theorem 1.1.

## 9. Exact original applications and remaining recovery boundary

The accepted fresh original normal form gives, throughout its
B-owned-HB, positive/nonparallel, H-owned singleton-HK feature,

    H=[x,x+1]v+[-y,G]u,
    0<x<=delta<1/60,
    89/120<G<1,
    P_HK=xv+zu, 0<z<G,
    n_HK=-v.

Apply only the same origin-preserving orthogonal map

    P -> (-P.v,P.u).

Then h=-x<0, the actual H becomes the rectangle (2), and the
actual K has a strict minimum-x vertex T=(h,z), hence exactly
the whole positive-axis form (3). The H-owned top-HC alternative
has the actual normal E2 and minimum C height G. All physical
contacts H-K, H-C and K-C remain present.

Every hypothesis of Theorem 1.1 is therefore satisfied if C
has two physical circle corners. That entire physical mask is
impossible. Since a circle-touching square in the original radius
window has one or two physical circle corners, this complete
original top-HC feature forces C to have a unique physical
circle corner.

This conclusion includes either zero individual circle weight,
the full originally retained H-C mean before its physical
singleton is derived, and every actual K-C owner or free normal.
It uses no C2 or K3 equation. The original H4/K3/B3/C2 equations
and all nine physical packing units remain unchanged.

The same local theorem also applies to a separately proved
free-central chart with the same strict minimum-x vertex at
T=(h,G). In that application z=G, which Sections 6 and 8 retain
explicitly. The caller must supply that actual K support chart;
it is not inferred here merely from a free-central graph label.
Even the closed G=1 or d=1 local endpoint has already been
excluded in Sections 2--3 or 8.

The complete fresh original normal form and its full acceptance are:

| Exact source | SHA256 |
| --- | --- |
| POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md | 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce |
| REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md | 705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d |

Its explicit positive/nonparallel B conditions and its separate
HK-singleton premise are retained in this original application.
The local theorem proves none of those antecedents. It does not
claim the missing old global physical-mask artifact has been
restored, and it does not by itself close an original graph gate.
It supplies the stated whole physical C-mask exit wherever this
actual local chart has independently been established.

## 10. Direct physical sources and exact verification

All direct physical inputs are present original sources. Only
their stated physical lemmas, fully reproduced above, enter.

| Present source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual physical support and contact conventions; no force selection |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Section 1 unshareable circle point, Section 2 inner-face metric fact, Section 3 exhaustive physical two-corner form |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete radius-free physical triangle implication, including all side-position endpoints |

The separate exact author record is

    check_small_side_radial_top_boundary_identities.py
    SHA256 332cb329c557aac0f1d1233b87c666c4e023917efc0f0a32247e5451eba0eb79.

It checks sixteen full coordinate, norm or cleared-radical
identities and twenty exact rational values and reserves using
only sparse polynomials and Fraction arithmetic. Its complete
replay passes. Those algebra checks do not replace the continuous
geometric argument or its required whole-source independent review.

An independent reviewer should reconstruct the full C orientation
cover and d=G=1 endpoint, every C side and corner, every K support
sign including theta=1, the two complete angle estimates, and the
entire monotonicity interval. The actual original map and all
unchanged physical hypotheses must also be checked.

The result is analytic and introduces zero computational exclusion
certificates. No numerical pose, angle subdivision, deleted force,
modified mean, K2 or H3 substitution, new normal selection, Lean
invocation, CI workflow, ledger mutation or remote edit appears.
