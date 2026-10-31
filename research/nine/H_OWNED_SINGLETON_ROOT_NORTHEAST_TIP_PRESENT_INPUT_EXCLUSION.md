# An H-owned singleton root has no northeast or vertical tip return

Date: October 27, 2026.  
Author: cert_final_review.  
Original comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

**Status: complete analytic candidate, written for full independent review.**
This is a fresh proof over present inputs. It is not a claimed restoration
of an earlier northeast-return manuscript. It covers the whole northeast
BK feature and its vertical endpoint, every actual central owner, both
genuine B leaves, both physical C masks, and all actual page means. No
computational exclusion packet is used.

## 1. Exact original theorem and unchanged certificate

Retain the original S/S hub-tip positive component

~~~
HK, HB, BK, HC, CK, HL_H, BL_B,
~~~

with true pair degrees H4, K3, B3 and C2. H and B have their two distinct,
occupied genuine radial S leaves. K and C have positive total circle
loads. All physical circle corners, including a possible zero individual
weight at a second corner, and the three additional packing units remain.
Thus all nine physical squares remain in the same disk. Retain the
original simultaneously selected normals, singleton applications and
actual aggregate shared means.

Start on the whole original radius interval

~~~
79/40 <= R <= sqrt(1105)/16,
d=sqrt(R^2-1/4)-1.
~~~

Assume HB is a physical singleton owned by H alone. Normalize the entire
packing by an origin-preserving orthogonal map as in the complete
H-owned-root normal form: H-to-B is E1 and the actual BK normal has
positive height. This is one map of every unit, force and mean, not a
change to an individual contact direction.

**Theorem 1.1.** In that whole original domain, the actual B-to-K normal
cannot have nonnegative first component.

The zero first component is part of the theorem. No central owner,
physical C mask, page normal, concurrence sign or actual mean value is
an additional starting hypothesis.

## 2. Complete present root input and central-axis exits

The entire accepted source
`H_OWNED_SINGLETON_S_ROOT_LOWER_LEAF_AND_UPPER_BOUNDARY_NORMAL_FORM.md`
applies before any central or page restriction. Its full low/equality
radius, initial H-leaf and physical-mask covers give

~~~
d=1+delta, 0<delta<1/60,
R^2=(d+1)^2+1/4, 17/4<R^2<=1105/256, R<25/12,

v_B=(alpha,-beta), w_B=(beta,alpha),
alpha^2+beta^2=1, alpha>6/7, 0<beta<1/2,
P=P_HB=x*v_B-u_B*w_B=(h,-L),
h=alpha*x-beta*u_B, L=beta*x+alpha*u_B,
|h|<=delta, x<=delta, u_B>0,

X=1-h, X^2+A^2=d^2,
H=[h-1,h] x [-A,G], G=1-A,
0<L<A<31/120, 89/120<G<1,
p_H=(-X,-A).
~~~                                                        (1)

The last point is the genuine H leaf application, after the complete
initial H-leaf cover. The two actual B leaf rows remain distinct:

| Genuine B leaf | Exact actual equations |
| --- | --- |
| Adjacent vertex P+v_B | (1+x)^2+u_B^2=d^2, 1+x>0, 0<u_B<2sqrt(delta), r=u_B/(beta+L) |
| Aligned positive-v_B side | x=delta, actual radial leaf mean d*v_B, 0<u_B<1, r=u_B/beta |

The actual BK is a singleton owned by K alone at

~~~
Q=P+w_B=(h+beta,alpha-L),
m_BK=(w_B-r*E1)/|w_B-r*E1|,
r>0, beta*r<1,
t0=beta/(1+alpha), t0^3<=delta, t0<9/35.            (2)
~~~

The last strict bound follows from the same genuine cubic and
(9/35)^3-1/60=173/514500>0, with all quantities positive.

All physical K and C circle corners have positive height. The actual
central normal N from H to K has both components nonnegative, and the
actual page normal M from H to C has M_y>=0. These statements precede
any C-uniqueness inference. K is physically unique, although most of
the proof below needs only its physical circle contact. At a strict
northwest HC at F=(h-1,G), the same complete normal form supplies
physical C uniqueness locally, with both actual leaf equations retained.

Apply the **whole original-feature theorems** of
`H_OWNED_SINGLETON_ROOT_HORIZONTAL_CENTRAL_PRESENT_INPUT_EXCLUSION.md`
and `H_OWNED_SINGLETON_ROOT_VERTICAL_CENTRAL_PRESENT_INPUT_EXCLUSION.md`
to N=E1 and N=E2, respectively. Their original domains include every
central physical type; their complete proofs already treat shared HK.
No separate global central-singleton or distinct-frame theorem is used.

Consequently any remaining N is strictly northeast. The actual H
application is therefore

~~~
W=(h,G).
~~~

Physical shared HK would have a side axis of H as normal, so it is
already absent. Thus HK is a singleton at W, owned by K or free, and
H intersection K is exactly {W}. In particular, neither a third H
force nor any K force has been deleted in passing to this chart.

## 3. The entire northeast central chart, including the vertical BK limit

Suppose the contrary feature m_BK,x>=0 occurs. Write its actual unit
direction and the actual orthogonal K axis as

~~~
m=(c,s), t=(s,-c), c>=0, s>0, c^2+s^2=1,
k=c/s>=0, r=beta-alpha*k>0.
~~~                                                        (3)

Since K alone owns BK, its actual side position is

~~~
K=Q+[0,1]m+[-theta,1-theta]t, 0<theta<1.           (4)
~~~

If K owns the strict northeast central normal N, then c>0 and N=m:
the other three K axes are not strictly northeast. Its actual point W
lies in the relative interior of that same minimum-m side. The first
coordinates of W and Q give

~~~
W=Q-zeta*t, zeta=beta/s, 0<zeta<theta,
ell=theta-zeta>0.
~~~

If the central normal is free, then N.m>0. A negative N.t would select
the other minimum-m vertex Q+(1-theta)t, whose first coordinate is
strictly larger than h, impossible for W. The strict free cone excludes
N.t=0. Therefore N.t>0 and W=Q-theta*t. In this row theta=beta/s and
ell=0. This covers c=0 without division by c; K-owned N=m would then be
the already excluded E2 axis, so only the free row survives at c=0.

The two entire central rows are thus

~~~
K=W+[0,1]m+[-ell,1-ell]t,
Q=W+(beta/s)t,
0<=ell<1-beta/s<1,

ell>0: c>0, N=m;
ell=0: N.m>0, N.t>0, N_x,N_y>0.
~~~                                                        (5)

No endpoint of a physical mean has been selected: theta is the original
strict BK side position, and ell is its derived displacement from the
original W. The vertical coordinates yield the exact equality

~~~
G=alpha-L+beta*k,
A=L+(1-alpha)-beta*k.                              (6)
~~~

Because A>L, this gives k<t0. All quantities in (3)--(6) belong to the
same actual configuration.

## 4. The non-strict two-leaf sign lemma applies literally

Lemma 4.1 of the complete horizontal-central source is a separate,
fully proved scalar statement on the actual two-leaf chart. Its return
height premise is **non-strict**, and it explicitly includes k=0.
Equation (6) supplies that premise with equality. In the aligned row,
its extra equation r=u_B/beta=beta-alpha*k is exactly (2)--(3).
All other premises are (1)--(2). It follows that

~~~
-delta<=h<0,
A^2=d^2-(1-h)^2<d^2-1<121/3600,
0<A<11/60, 49/60<G<1.                              (7)
~~~

This transfer does not import the strict horizontal-central geometry
from that containing paper. Its whole two-row lemma, including its
height equality and vertical k=0 endpoint, is the adopted statement.
The vertex row uses its genuine leaf radius; the aligned row uses its
genuine radial side mean and is never assigned a vertex radius.

We also have

~~~
|W|^2=h^2+G^2=d^2+2(h-A)<d^2,
min_K x=h-ell*s>h-1.                               (8)
~~~

Finally ell<s on the entire chart. Indeed k<t0 gives c<beta, hence
s(1-s)<c^2<beta when c>0. For c=0 the same needed strict inequality
beta>s(1-s)=0 holds. Thus

~~~
ell<1-beta/s<s.                                    (9)
~~~

The side-position inequality is used later with its actual strictness;
it is not a comparison of independent sliders.

## 5. Whole all-mask HC direction cover and the occupied triangle

The already established M_y>=0 leaves the left/right horizontal axes,
the vertical axis and the two upper open quadrants.

If M=-E1, all C lies in x<=h-1. Equation (8) puts all K strictly to its
right, contradicting their physical contact. This argument has no C
mask premise.

The three actual points P,W,Q bound a nondegenerate triangle. Its sides
P-W, W-Q and Q-P lie respectively in H, K and B. The last side is the
actual B side w_B, and W-Q lies on the actual minimum-m K side. Its area
is

~~~
area(PWQ)=beta*(G+L)/2<1/4,
G+L=1-A+L<1.                                      (10)
~~~

An open interior of a different unit cannot meet this triangle and then
leave it: each boundary segment is in one of the three actual occupied
units, and an open point of C on any such segment would overlap that
unit's interior. The open interior of C is connected. It cannot be
contained in this triangle either, because its area is one. This is an
actual occupied-triangle argument, with every other unit still present.

For M=E1, the general loaded-boundary C2 proper-concurrence theorem
applies with the **actual circle resultant**, before uniqueness. All C
circle heights are positive, so the radial concurrence has positive
height. Its actual incoming line is horizontal. The unchanged HC
application T=(h,y) therefore has y>0. If y<G, then -L<y<G, and C's
minimum-x support at T enters the open triangle locally. This is
impossible by (10).

The endpoint y=G is retained. A point-only selected E1 contact at W
cannot be a free vertex/vertex contact, whose selected normal is strict
at H. If C owns E1 at W, its relative-interior vertical side contains
points of H's right side immediately below W, making HC physically
shared. If HC is physically shared from the start, its positive segment
likewise contains such points. In either case a point of that segment
with 0<y<G gives the same open-triangle contradiction. Thus all E1
types and means are excluded.

For a strict northeast M, the actual H point is W. If ell>0, W is in
the relative interior of K's minimum-m side, where c,s>0. Disjointness
forces any third square containing W into the opposite closed
half-plane. Its inward segment W-epsilon*m then lies in that square
and in the open interior of H for small epsilon>0. An open perturbation
gives overlapping interiors. This covers every third-square side or
vertex, so the strict northeast page is impossible when ell>0.
Here the inward-segment fact includes a support vertex: the inward
unit direction -m is a nonnegative combination of its orthogonal axes with
both coefficients at most one. At a side application it is the inward
side axis. Thus the stated short segment really belongs to the third
square, including either endpoint of its normal cone.

Only its free-central endpoint ell=0 needs a separate common-corner
argument. That is the next section. Once it is excluded, the entire
all-mask page cover is exactly TOP M=E2 or FAR M_x<0<M_y.

## 6. Full strict northeast page at the free central endpoint

Here K=W+[0,1]m+[0,1]t, with c>=0, and the actual HC point is W.
Equation (8) makes C physically unique: every point of a physical
two-circle-corner unit has radius at least d, whereas |W|<d.

H cannot own a strict northeast normal. If C owned it, W would be in
the relative interior of C's minimum-M side. But K contains W+epsilon*m,
and M.m>0, so that actual inward K segment enters the open C half-plane
near W. This would overlap interiors. Therefore HC is free, and W is
an actual C vertex.

If CK is a singleton, its physical application is also W, since both
C and K already contain W. The true coincident C2 star forces W
collinear with the unique circle corner. In the own frame of a unique
circle corner (a,b), a,b>1/2, neither adjacent non-circle vertex is
collinear. The opposite vertex is collinear only at a=b=R/sqrt(2).
This is exactly the full coincident case of the present fixed-tip
source; its moment argument does not choose a new normal. It gives

~~~
|W|=R-sqrt(2)<25/12-7/5=41/60<G,                   (11)
~~~

contradicting |W|>=G. The gap against (7) is 2/15. The physical circle
corner itself cannot be shared with H.

If CK is physically shared, C and K are coframed. Across either of K's
two maximum sides, C cannot contain W. Across a minimum side, write
the full tangential translation in (-1,1), the exact interval for
positive side overlap. Since W must be a C vertex, this translation
is zero; the alternative endpoint -1 would have zero overlap. The
only two actual placements are therefore

~~~
C_1=W+[-1,0]m+[0,1]t,
C_2=W+[0,1]m+[-1,0]t.                             (12)
~~~

For C_1 and c>0, W-epsilon*m lies in the open H interior, so the
interiors overlap. At c=0, C_1 shares a positive vertical side with H,
contrary to the actual free HC singleton. This handles that endpoint
without a strict negative first component.

For C_2, all three non-opposite corners of both actual squares have
norm at most |W|+1<d+1<R. Thus their physical circle points must be

~~~
z_K=W+m+t, z_C=W+m-t.
~~~

Their exact squared-norm difference is

~~~
|z_C|^2-|z_K|^2=-4 W.t=-4(h*s-G*c)>0,              (13)
~~~

including c=0 because h<0. Both actual circle norms are R, a
contradiction. The complete four shared translations, their actual
overlap endpoints and all shared CK means have been retained. No K2
law, global C-mask theorem or missing application-separation result
has entered this argument.

## 7. Entire TOP when c>0: exact present local transfers

Assume M=E2 and c>0. The original true C2 is retained, with physical
boundary K, all HC/CK types and means, and the original compatible
fixed-singleton selection.

If C is physically unique, apply the entire local Theorem 1.1 of
`HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md` with the exact identity map

~~~
U=m=(c,s), V=t=(s,-c), a_0=ell, R_0=W.
~~~

Its full domain has -1/60<h<=0, 89/120<G<1, c,s>0 and 0<=a_0<1.
Equations (5) and (7) give all of these. Its actual cone is literal:
N.U=1,N.V=0 for a K-owned central side, and N.U>0,N.V>0 for the free
endpoint. The local theorem treats every singleton/shared HC, every
CK owner and every actual mean, with arbitrary H/K degree. It excludes
this entire unique-C class.

If C has two physical circle corners and ell>0, apply the full purely
physical theorem `HIGH_CORNER_OWNED_CENTRAL_RADIAL_TOP_EXCLUSION.md`
with

~~~
m_local=-t=(-s,c), n_local=m=(c,s),
ell_local=1-ell in (0,1).
~~~

Indeed its exact K is

~~~
W+[-ell_local,1-ell_local]m_local+[0,1]n_local,
~~~

which is the unchanged square (5). Its actual H-to-K normal is
n_local, and W is in the relative side interior. All H/K/C physical
contacts and the full radial C mask are present. No circle-weight or
CK owner premise is added.

For the remaining physical two-corner class ell=0, apply the complete
physical theorem `SMALL_SIDE_RADIAL_TOP_BOUNDARY_EXCLUSION.md`.
Here K has the strict minimum-x vertex W, actual inward axes m and t,
and its local coordinate z is exactly G. The theorem explicitly
includes the closed z=G and h=0 endpoints, every
radial orientation and every CK normal. Our h<0 and G<1 lie in that
domain. It excludes this full remaining mask.

These transfers use only each entire local theorem. No differently
owned original B-root caller of a local source is imported. The
vertical c=0 boundary is treated next, not divided away or put into a
strict-angle theorem.

## 8. Entire TOP at the vertical BK endpoint c=0

Section 3 forces ell=0 at this endpoint. The actual K is exactly

~~~
K=[h,h+1] x [G,G+1], -1/60<h<0, 49/60<G<1.
~~~

Increasing either coordinate from its minimum strictly increases the
norm between the relevant vertices, because 2h+1>0 and 2G+1>0.
Consequently its actual unique circle corner is

~~~
z_K=(h+1,G+1).                                    (14)
~~~

### 8.1. Full physically shared HC

If HC is shared, C is an axis square [l,l+1] x [G,G+1]. The H-top
overlap implies l<h. Its interior cannot overlap K, so l+1<=h.
Physical CK contact then forces l+1=h. Thus C=[h-1,h] x [G,G+1],
and its actual upper-left corner gives

~~~
|(h-1,G+1)|^2-|z_K|^2=-4h>0,                      (15)
~~~

contrary to containment. This covers the whole shared HC mean and
requires no mask or C-force assumption.

### 8.2. Full physical two-circle singleton C

The physical radial form is C=[d,d+1]e+[-1/2,1/2]f. Its positive
minimum height implies e_y>0. If e_x>0, its minimum-height point has
positive x and cannot touch H's top with x<=h<0. If e_x=0, that height
is d>1>G. Hence every remaining such C has

~~~
e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1,
G=d*p-q/2,
V=d*e+f/2=(p/2-d*q,G+q).
~~~

The complete inequality G>89/120 gives q<2/5: otherwise p<11/12 and
G<(61/60)(11/12)-1/5=527/720<89/120. Thus p>9/10 and

~~~
13/300<p/2-d*q<1/2,
G<V_y<G+1.
~~~

Since h<0 and h+1>59/60, this actual vertex V lies strictly inside K.
Every neighborhood of a C vertex contains C interior points, so its
interior overlaps K. No C2 or CK type was used in this entire mask.

### 8.3. Full unique-circle singleton C

The actual HC singleton is C's strict bottom vertex

~~~
T=(T_x,G), h-1<T_x<h<0,
C=T+[0,1]e+[0,1]f,
e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1.
~~~

The complete proper-C2 theorem gives its unchanged concurrence
q_C=r_C*z_C=T+ell_C*E2 in C, with r_C>0 and ell_C>=0. Containment
gives r_C<=1. If z_C were opposite T, writing its height Z_y>G gives
r_C>=G/Z_y. The actual horizontal equality then yields

~~~
2=|z_C-T|^2 <= (1-G/Z_y)^2 R^2 <= (R-G)^2
  < (161/120)^2 < 2.                              (16)
~~~

All factors squared are nonnegative. The circle cannot be T, which is
shared with H. The adjacent candidate T+f has minimum-e coordinate
-T_x*q+G*p>0, whereas any circle corner on a minimum own face has
coordinate at most -1/2. Thus the actual circle is z_C=T+e.

Its minimum-f coordinate is strictly less than -1/2 by physical
uniqueness. Put w0=-T_x>0. The exact own circle coordinates satisfy

~~~
a_C=G*p+w0*q>0, b_C=w0*p-G*q>1/2,
(a_C+1)^2+b_C^2=R^2, a_C<d,
G=a_C*p-b_C*q<d*p-q/2.
~~~

The whole q>=39/100 interval gives p<921/1000 and
G<14827/20000<89/120. Therefore

~~~
q<39/100, p>23/25.                                (17)
~~~

The actual rightmost C vertex T+f has height G+q in (G,G+1) and
first coordinate less than h+1. To avoid the open K rectangle, it
must have T_x+p<=h. Thus z_C has first coordinate at most h-p-q<0,
and

~~~
R^2=|z_C|^2 >= (h-p-q)^2+(G+p)^2.
~~~

But the exact comparison with the real K corner (14) is

~~~
(h-p-q)^2+(G+p)^2-|z_K|^2
 =-2h(1+p+q)+2p*q-q^2-2G(1-p)
 >q*[2p-q-2q/(1+p)]
 > (167/160)q>0.                                 (18)
~~~

For the final uniform bound, 2p>46/25, q<39/100 and
2q/(1+p)<13/32; their exact difference is 167/160. The identity
1-p=q^2/(1+p) uses a positive denominator. This contradiction covers
every actual CK type, owner and mean: none was needed to derive it.

Sections 8.1--8.3 exhaust the vertical TOP endpoint.

## 9. Entire FAR ownership cover, including all shared CK placements

It remains to consider the strict northwest HC normal. Its actual
H application is F=(h-1,G)=(-X,G), and the whole normal form supplies
physical C uniqueness at this genuine far port. HC is a singleton;
it cannot be H-owned because its normal is not a side axis of H.

If CK is singleton, its actual C application differs from F because
min_K x>h-1. The original compatible fixed-singleton selection applies
to these two actual distinct fixed C points. Thus HC and CK have side
owners; HC must be C-owned. No new stress, mean or normal is selected.

If CK is shared, retain the possibility that HC is free. Then C and K
are coframed and F must be an actual C vertex. In the actual (m,t)
coordinates based at W,

~~~
K=[0,1] x [-ell,1-ell], F=(-c,-s).                 (19)
~~~

For c>0, examine all four signed shared translations:

* Across maximum m, C has m-coordinate at least one and cannot contain F.
* Across minimum m, its m interval is [-1,0]. The value -c is strictly
  inside that interval, so F cannot be a C vertex.
* Across maximum t, its t-coordinate is at least 1-ell>0, so it cannot
  contain F.
* Across minimum t, its t interval is [-ell-1,-ell]. By ell<s<1,
  the value -s is strictly inside, so F cannot be a C vertex.

Every tangential translation remains in its full (-1,1) interval;
these exclusions do not choose a shared mean.

At c=0, Section 3 gives ell=0 and (m,t)=(E2,E1). Across maximum m
or maximum t, F is absent. Across minimum m, positive overlap requires
the tangential interval endpoints to be strictly greater than -1,
so F_t=-1 cannot occur at a C vertex. Across minimum t, F can be a
vertex only for the zero m-translation: the other endpoint would give
zero overlap. The resulting actual C is

~~~
C=[h-1,h] x [G,G+1].
~~~

It shares H's entire top, contrary to the current strict northwest
singleton HC. This completes the axis boundary of the four-placement
cover. Therefore the entire remaining FAR feature has C-owned HC,
including any physical shared CK.

## 10. The actual signed C coordinate is positive

Write the whole actual C-owned side chart as

~~~
n=(-u,v), f=(v,u), u,v>0, u^2+v^2=1,
C=F+[0,1]n+[-lambda,1-lambda]f, 0<lambda<1,
a=F.n=X*u+G*v>0,
B0=-F.f=X*v-G*u.
~~~                                                        (20)

The true unique-C2 proper incoming concurrence is F+ell_C*n=r_C*z_C,
ell_C>=0, r_C>0. A unique physical circle corner has nonzero own
coordinates of magnitude greater than 1/2. Its f coordinate has the
same sign as -B0, so B0 is not zero.

If B0<0, then G*u>X*v. The exact identity

~~~
a-X=v*[G-X*v/(1+u)]>0
~~~

follows with a positive denominator. The actual inward unit point
F+n belongs to C. Using X^2+A^2=d^2 and G=1-A gives

~~~
|F+n|^2-R^2=3/4-2A+2(a-d)
 >3/4-11/30-1/30=7/20>0,                          (21)
~~~

because 0<=d-X=delta+h<1/60. This contradicts containment. Thus

~~~
B0>0,
z_C=F+n-lambda*f,
(z_C.n,z_C.f)=(a+1,-B0-lambda),
a<d.                                               (22)
~~~

The circle is on the maximum-n face because a+ell_C>0, and on the
minimum-f face because -B0<0. Its physical minimum-f distance is
B0+lambda>1/2, which proves a<d from the exact circle radius.

## 11. One continuous small budget and one uniform relative-angle bound

The actual coordinates in (20)--(22) give

~~~
a^2+B0^2=d^2+1-2A,
B0^2>1-2A>19/30>(83/120)^2,
83/120<B0<X<61/60.                                (23)
~~~

The last strict upper bound follows from v<1 and u,G>0.

Also u<1/3. The function X*u+G*sqrt(1-u^2) is increasing up to the
actual u because its derivative there is B0/v>0 and the derivative
decreases, with second derivative -G/(1-u^2)^(3/2)<0. If u>=1/3,
then its value is greater than

~~~
1/3+(49/60)(14/15)=493/450>61/60,
~~~

contrary to a<d. Therefore v>14/15, and

~~~
a-G=u*[X-G*u/(1+v)]>(24/29)u>(4/5)u.              (24)
~~~

The exact circle identity is

~~~
lambda^2+2B0*lambda+2(a-G)=2d-11/4+4A<1/60.        (25)
~~~

Its strictly positive left side also gives A>43/240. Applying (23)--(24)
to the same unchanged identity yields the whole continuous bounds

~~~
43/240<A<11/60,
lambda<1/83, u<1/96, v>99/100.                    (26)
~~~

No pose, side mean or angle subinterval has been replaced by a sample.

Define the actual relative projections

~~~
D=v*s-u*c, J=u*s+v*c,
n.m=D, n.t=-J, f.m=J, f.t=D.
~~~                                                        (27)

They satisfy D,J>0 and D^2+J^2=1. Indeed k<9/35<1/3 gives

~~~
D/s=v-u*k>99/100-1/288=7103/7200>0,
J/s=u+v*k<1/96+1/3=11/32,
0<J/D<2475/7103<1/2.                              (28)
~~~

The last exact reserve is 2153/14206. These are the same actual C/K
frames, including c=0. They do not assert a force law at K.

## 12. Every K-alone-owned CK side is excluded

First suppose C does not own CK. It is then a singleton with its
original side owner K, by Section 9's compatible fixed-point result.
Let w be the actual normal from C to K.

At K, the actual H-K-C triangle and the K-owned CK side imply w.N>=0.
For N=m this leaves w in {m,t,-t}. For a free central N with N.m>0
and N.t>0 it leaves only {m,t}, a subset of that same complete list.
At C, its owned HC side gives n.w<=0. Equations (27)--(28) exclude
w=m and w=-t because their n projections are D and J, respectively.
The only remaining actual direction is w=t.

Put eta=1-lambda. Since n.t=-J<0 and f.t=D>0, the actual maximum-t
C application is Z=F+eta*f. The unchanged proper C2 concurrence has
the incoming form F+ell_C*n and outgoing displacement proportional
to t=-J*n+D*f. Comparing these components gives

~~~
ell_C=eta*J/D>0.
~~~

Its unchanged positive radial relation to the actual circle (22)
then gives the exact identity

~~~
B0=a*lambda+eta*(J/D)*(B0+lambda).                 (29)
~~~

This retains the entire K-owned side position: none was assigned or
needed. Using eta<1 and (28),

~~~
B0<a*lambda+(B0+lambda)/2,
B0<2lambda*(a+1/2)<91/2490<83/120,                 (30)
~~~

contradicting (23). All K-alone-owned CK axes are thus excluded on
the whole original domain.

## 13. Every C-owned CK side, including the entire shared possibility

Suppose C owns CK; this class initially includes a physically shared
CK and its full actual mean. With unchanged positive weights its
actual unique-C2 equation is

~~~
kappa_C*z_C=omega*n-gamma*w.
~~~

Projection onto f and (22) show w.f>0. Among the C side axes only
w=f has this property. Since J=f.m>0 and D=f.t>0, K has the unique
minimum-f support point

~~~
Z=W-ell*t.
~~~

In particular a physical shared CK cannot have positive length at
this strict K support. Equivalently, even retaining its unchanged
actual mean, that mean would have to equal this same forced point.
We retain the necessary closed C-side interval 0<=rho<=1 and write

~~~
Z=F+(1-lambda)f+rho*n.
~~~

Projecting the actual equality Z-F=E1-ell*t gives

~~~
lambda=1-v+ell*D,
rho=ell*J-u.                                      (31)
~~~

These identities cover ell=0 as well: then rho=-u<0 is already
physically impossible. Uniformly, since v<1 and D>0,

~~~
rho<ell*J=(lambda-1+v)*(J/D)<lambda/2<1/166.         (32)
~~~

On the other hand the full actual C2 force and origin moment give

~~~
gamma/omega=(B0+lambda)/(a+1)=B0/(a+rho),
rho=(B0-a*lambda)/(B0+lambda).                     (33)
~~~

All denominators are positive; a+rho>=a>0. The same budget (23),(26)
implies

~~~
B0-(25a+24)lambda
 >83/120-(25*(61/60)+24)/83
 =959/9960>0.
~~~

After multiplying by the positive B0+lambda, this is precisely

~~~
rho>24/25.                                        (34)
~~~

Equations (32) and (34) contradict one another. No free side mean
was moved to an endpoint, no K circle corner was selected, and no
degree-two law at K was invoked. This excludes the entire C-owned
class and therefore the whole FAR page.

## 14. Exact original union and proof boundary

The whole original H-owned singleton-HB input first supplies (1)--(2)
and the mask-general physical sign facts. The two complete central-axis
theorems exclude N=E1 and N=E2 on their original full domains, so the
strict northeast chart covers every remaining actual central type.
Under m_BK,x>=0, Sections 3--4 derive one actual chart for K-owned and
free HK with their full side positions, and its exact equality gives
h<0 for both genuine B leaves, including vertical BK.

The mask-general physical page cover is exhaustive. The right side
and its endpoints are excluded by the actual occupied triangle; the
left axis is physically separated from K; the common strict northeast
corner has a full singleton/shared C2 cover. The two remaining page
classes are then excluded completely:

| Actual remaining feature | Entire exit |
| --- | --- |
| TOP, c>0, unique C | Complete local 580c theorem at U=m,V=t,a_0=ell |
| TOP, c>0, physical two-corner C, ell>0 | Complete physical 3b3 theorem at m_local=-t,n_local=m,ell_local=1-ell |
| TOP, c>0, physical two-corner C, ell=0 | Complete physical 64ef theorem at its included z=G endpoint |
| TOP, c=0 | Section 8 covers the whole shared HC, physical radial C and unique singleton C separately |
| FAR, both c>0 and c=0 | Sections 9--13 cover all HC/CK physical types, both outgoing owners and every actual mean |

These rows use no unproved global C-mask or central-owner reduction.
The original positive C load enters only its genuine C2 rows; K keeps
all of its genuine K3 equations throughout. H4 and B3 are retained in
the complete input, with no surrogate root concurrence. Both occupied
leaves and all three other packing units remain physically present.

Therefore the actual BK normal in an H-owned singleton-HB configuration
cannot have nonnegative first component. The complementary strict
northwest BK feature requires its own complete central-type union.
This source alone does not tick an original graph gate, mixed-leaf
parent, ledger row or coarse parent.

The proof is continuous, with exact rational comparisons and elementary
identities. It uses no numerical pose sampling, angle boxes, Bernstein
packet, new certificate, Lean run or CI action. Exact algebra replay
is only validation of the displayed identities and byte pins.

## 15. Frozen present input and acceptance table

The exact source and full-acceptance pins are recorded below. Only each
explicit complete theorem or reproduced local statement is adopted;
historical filenames and missing earlier manuscripts are not premises.

| Complete mathematical input | SHA256 | Exact adopted scope |
| --- | --- | --- |
| H_OWNED_SINGLETON_S_ROOT_LOWER_LEAF_AND_UPPER_BOUNDARY_NORMAL_FORM.md | be67714719a4ad3ce58c8990cfaa0def3bbc8b0f8f01e5852d52b8e1f7e52b36 | Entire original root/leaf/height/owner chart; local far C uniqueness only |
| H_OWNED_SINGLETON_ROOT_HORIZONTAL_CENTRAL_PRESENT_INPUT_EXCLUSION.md | d7936c3d1f2b9ecdabbe2bb3a713f47f08a7ff552db48588ac113290a163b022 | Entire actual E1 central exit and complete non-strict Lemma 4.1 |
| H_OWNED_SINGLETON_ROOT_VERTICAL_CENTRAL_PRESENT_INPUT_EXCLUSION.md | 8b1a82e19a374ef3d754c4058d6810ce4fbe1859436290d7987cfa8bec9c8ee5 | Entire actual E2 central exit; the elementary high-bottom C chart is reproduced in Section 8 |
| HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md | 580c065de7812c889f91d0e06e7319a3126134b31b8bd31c2044960b7819083b | Complete local unique-C top theorem, including a_0=0 and all means |
| HIGH_CORNER_OWNED_CENTRAL_RADIAL_TOP_EXCLUSION.md | 3b3ba081d85d7695e92d524859a15c8a9a1775ca0416cdb7bb95e76a8685ced7 | Complete physical radial top theorem with its actual strict central side position |
| SMALL_SIDE_RADIAL_TOP_BOUNDARY_EXCLUSION.md | 64ef75b5e3c944314a3a1c2795abc8aaea84084104cf160d369e1305873311fb | Complete physical radial top theorem, including the closed z=G endpoint |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original actual forces, moments, shared means and strict singleton convention |
| FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md | a33b15a4a3e7894c256ee1877edfb47f6241fd208558765267113e56e12a1b4e | Whole original H4/K3/B3/C2 graph, positive loads and all nine units |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Entire mask-general loaded-C2 proper ray and unique-C interior consequence |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing simultaneous selection at actual distinct fixed C points, plus full coincident exception |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Entire physical H-K-C owned-axis sign, with equality retained |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical one/two-circle classification and unique-corner own-coordinate facts only |

All six adopted recent mathematical sources have these concrete full
acceptance records; they are not scalar-only or similarly named older
reviews.

| Full acceptance record | SHA256 |
| --- | --- |
| REVIEW_H_OWNED_SINGLETON_LOWER_LEAF_NORMAL_FORM_CERT_INDEPENDENT_2026_10_27.md | cf9a4e53377a571ef10a73130baa1a26f14f8bf74c9245c8ab68df5e75388054 |
| REVIEW_H_OWNED_HORIZONTAL_CENTRAL_PRESENT_ROOTED_INDEPENDENT_2026_10_27.md | d4cde71fae34ffbcb3d86e6d1a9ac07a10d40a6451caeb9ccb16acb1e5e32d3f |
| REVIEW_H_OWNED_VERTICAL_CENTRAL_PRESENT_TOPOLOGY_INDEPENDENT_2026_10_27.md | ee0852c4dd45f1447250bae9665f901b397450b6fd3c4517f3fcb7aa611d2c82 |
| REVIEW_HIGH_CORNER_CENTRAL_TOP_PAGE_CERT_INDEPENDENT_2026_10_27.md | 4b39a8e97f4714a8cb37f91665edb3e3069d2a0ecde9d0b0f19c884f362daa14 |
| REVIEW_HIGH_CORNER_RADIAL_TOP_CERT_INDEPENDENT_2026_10_27.md | db63fd15bbd91e216b2f48405bcc3eb026efba52a141e89e650d53577aa232a6 |
| REVIEW_SMALL_SIDE_RADIAL_TOP_ROOTED_INDEPENDENT_2026_10_27.md | e656d02b5d9d518597d408e234ad516d6cc3095f534b16f934c6551afb92b995 |

These accepted inputs do not substitute for the requested separate
whole-source review of this new original-feature theorem. No accepted
input bytes, original gate, ledger, remote branch, Lean source or CI
workflow were changed in preparing this manuscript.

