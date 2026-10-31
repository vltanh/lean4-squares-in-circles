# A radial top boundary page is impossible throughout the signed root strip

Date: October 27, 2026.  
Author: topology_final.

**Status: complete fresh physical extension, frozen for full independent
review.** The accepted nonpositive-h theorem is unchanged. This source
adds the whole small positive-h domain needed by the genuinely signed
parallel-tip root chart. It keeps the real central slider and all CK
normals and means, with no force equation or computational certificate.

## 1. Entire physical statement and the natural signed strip

Let H,K,C be interior-disjoint physical unit squares with all three
pairwise contacts, in the same origin-centered disk of radius R. Let

```
1<=d<61/60, R^2=(d+1)^2+1/4,
H=[h-1,h] x [G-1,G], W=(h,G),
89/120<G<1,
m=(-c,s), n=(s,c), c,s>0, c^2+s^2=1,
K=W+[-ell,1-ell]m+[0,1]n, 0<ell<1.              (1)
```

The actual H-to-K normal is n, owned by K at its real side-interior
point W. K physically touches the containing circle. C has two
physical adjacent circle corners, minimum height G, and actual
H-to-C normal E2 owned by H. Every original HC and CK type, normal
and full physical shared mean is initially retained. H and K may
have arbitrary other degrees, masks and forces.

**Theorem 1.1 (positive-side physical extension).** Under (1), no such
configuration exists when

```
0<h<=1/60 and |W|<d.                            (2)
```

**Corollary 1.2 (the whole natural signed strip).** Under (1), no such
configuration exists when

```
|h|<=d-1.                                      (3)
```

Indeed, put delta=d-1. Then 0<=delta<1/60. If h<=0, the complete
accepted theorem `HIGH_CORNER_OWNED_CENTRAL_RADIAL_TOP_EXCLUSION.md`
applies directly. If h>0, then delta>0 and

```
|W|^2=h^2+G^2<delta^2+1<(1+delta)^2=d^2,
```

so (2) holds. The case d=1 in (3) has h=0 and is already in the
accepted nonpositive-h theorem. No limit argument at G=1 is claimed;
G<1 is an explicit premise of both complete physical theorems.

All subsequent sections prove the entire positive-h Theorem 1.1.
The additional point-norm hypothesis in (2) is used openly, not
assumed for an arbitrary signed strip. Equation (3) supplies it in
the original application.

## 2. Full C orientation and the same uniform radial-angle bounds

The physical two-circle classification gives

```
C=[d,d+1]e+[-1/2,1/2]f
```

for orthonormal e,f. The radial direction has e_y>0, since the
minimum height G is positive. If e_x>0, write e=(q,p), q,p>0.
Its bottom vertex has horizontal coordinate

```
d*q+p/2 >= (q+p)/2 > 1/2 > h.
```

It cannot lie on H's top. This replaces the nonpositive-h orientation
step by a bound valid on the entire positive strip. If e_x=0 then
e=E2 and G=d>=1, contrary to G<1. Both entire orientation alternatives
and the aligned/shared-HC axis endpoint are excluded.

Thus the actual full C frame is

```
e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1,
T=d*e-f/2=(-d*q-p/2,G),
V=d*e+f/2=(a,G+q),
G=d*p-q/2, a=p/2-d*q.                           (4)
```

T is the actual unique minimum-height vertex. The whole actual HC
application is therefore that physical point, not a newly chosen
representative of a shared mean.

If q>=2/5 then p<=sqrt(21)/5<11/12, and

```
G < (61/60)*(11/12)-1/5
  =527/720<89/120.
```

The two exact reserves are 1/3600 after squaring the radical
comparison and 7/720 in height. Hence

```
0<q<2/5, p>9/10,
13/300<a<1/2.                                  (5)
```

Define the actual horizontal displacement from W to V by

```
b=a-h.
```

Since 0<h<=1/60, (5) gives the whole strict interval

```
2/75<b<a<1/2,
V-W=(b,q),
|V-W|^2=b^2+q^2<41/100<1.                       (6)
```

The lower vertex T has negative horizontal coordinate and height G,
whereas h>0. Therefore

```
(T-W).n=s*(T_x-h)<0,
```

and T is not in K.

## 3. Complete physical CK side and vertex cover

Every possible CK contact is covered before a side owner or a normal
is prescribed. The two outer vertices of C are its physical circle
points and are unshareable with another contained unit.

For the relative interior of its maximum-e side, the actual C-to-K
normal is e and C-to-H is -E2. Their dot product is -p<0, excluded
by the physical H-K-C triangle theorem at C's owned side. The
maximum-f side similarly gives -q<0.

At the minimum-f side the actual C-to-K normal is -f, so K-to-C is
f. Its dot product with the actual K-owned K-to-H normal -n is
`-(s*p+c*q)<0`, again contrary to the same physical triangle theorem.

The relative interior of C's minimum-e face cannot meet any physical
boundary unit. To retain the full support interval, take its actual
point `(d,t)` in the (e,f) frame, |t|<1/2. A disjoint neighbor has
maximum e support d. For a vertex support its two inward unit axes
have nonpositive e components and opposite f signs; for a side
support the full length-one side interval gives the same bounds.
Thus the entire neighbor has e coordinate in `[d-sqrt(2),d]` and
absolute f coordinate at most 3/2. As d>=1, its norm squared is at
most d^2+9/4, strictly below R^2 by 2d-1>=1. It cannot be K.

The lower inner vertex T has already been excluded by its actual
n support. The sole remaining C boundary point is the upper inner
vertex V. A common point cannot be in the open interior of a physical
square with disjoint interiors. Therefore CK is exactly the singleton
{V}; a positive shared segment would contain one of the excluded
relative interiors or vertices. All initially shared means and free
normals are covered by this physical conclusion.

At V the full outward C normal cone is generated by -e and f, both
of strictly positive horizontal component. Hence every actual
C-to-K normal w at this point has w_x>0, including the cone endpoints.
The actual K n-coordinate is

```
theta=(V-W).n=s*b+c*q,
0<theta<1                                      (7)
```

by (6). Thus V is in neither n-face and at no K vertex. It lies in
the relative interior of an m-side. The minimum-m side would have
incoming normal m with negative horizontal component. It is excluded.
The complete actual contact relation is consequently

```
j=1-ell in (0,1),
V=W+j*m+theta*n,
j=s*q-c*b>0, theta=s*b+c*q in (0,1),
w=-m.                                         (8)
```

The incoming normal and point in (8) follow from physical support;
they are not selected after extracting a force certificate. In
particular theta=1 is excluded by the actual norm bound (6), not by
assuming a strict CK owner at the start.

## 4. Three K corners are controlled without a force or mask choice

The two minimum-n corners are W-ell*m and W+j*m. By (2), every one
has norm strictly below d+1<R. This does not choose which physical
K corner might be on the circle.

The two remaining corners are

```
Z_plus=W+j*m+n,
Z_minus=W-(1-j)*m+n.                            (9)
```

The actual C vertex has |V|^2=d^2+1/4. Since
Z_plus=V+(1-theta)n, its whole radius difference is

```
R^2-|Z_plus|^2
 =2*d+theta^2-2*(1-theta)*(h*s+G*c).            (10)
```

Here h*s+G*c=W.n is positive and strictly below |W|<d. Thus

```
R^2-|Z_plus|^2
 =2*(d-W.n)+theta^2+2*theta*(W.n)>0.
```

This is why the exact point-norm premise in (2) is retained. It
comes automatically from the natural original strip (3), but is
not silently extended to all arbitrary positive h and G.

## 5. Whole-angle monotonicity of the remaining corner

Keep d,p,q,h fixed, so a,b,G are fixed. Put

```
u=1-j,
c=sin(phi), s=cos(phi).
```

Since b,q>0, the entire actual j>0 interval is

```
0<phi<phi_star=atan(q/b)<pi/2.
```

Enlarge to the closed interval from zero to phi_star. On its whole
length,

```
0<=j=s*q-c*b<=q<2/5,
u=1-j>3/5,
0<theta=s*b+c*q<=sqrt(b^2+q^2)<1,
u'=theta, c'=s, s'=-c.                          (11)
```

The full norm in this frame, with the actual positive h retained, is

```
N=|Z_minus|^2
 =h^2+G^2+1+u^2+2*h*(u*c+s)+2*G*(c-u*s).
```

Its exact derivative has the following useful grouping:

```
N' =2*u*theta
    +2*c*(G*u-h*(1-theta))
    +2*s*(G*(1-theta)+h*u).                    (12)
```

Every term is nonnegative and the first is strictly positive.
Specifically,

```
G*u-h*(1-theta)
 >(89/120)*(3/5)-1/60=257/600>0.
```

All signs in (12) hold on the entire enlarged angular interval, not
just at an actual pose. Thus N increases strictly and is bounded by
its endpoint at j=0. With

```
c_star=q/sqrt(b^2+q^2),
s_star=b/sqrt(b^2+q^2),
r=(q-b)/sqrt(b^2+q^2),
```

the endpoint value is

```
N <= h^2+G^2+2+2*h*(c_star+s_star)+2*G*r.
```

The complete positive-h contribution is uniformly bounded by

```
h^2+2*h*(c_star+s_star)
 <=1/3600+(1/30)*sqrt(2)
 <1/3600+17/360=19/400.                         (13)
```

Consequently

```
N < G^2+2+2*G*r+19/400.                        (14)
```

No assumed sign of r is used. The positive denominators are justified
by b,q>0. The endpoint j=0 is only a proved scalar enlargement of
the actual j>0 domain; the original ell is not changed.

## 6. The complete three-interval radial cover

For all t>=0 the function

```
F(t)=(t-1)/sqrt(1+t^2)
```

has derivative `(1+t)/(1+t^2)^(3/2)>0`. Thus any upper bound on q/b
gives an upper bound on the whole signed r=F(q/b). The following
three intervals cover 0<q<2/5, including both internal endpoints.

### 6.1. Whole interval 0<q<=1/4

Here p>=sqrt(15/16)>24/25, whose squared reserve is 159/10000.
Thus

```
b=p/2-d*q-h
 >12/25-61/240-1/60=251/1200>1/5.
```

The last reserve is 11/1200. Hence q/b<5/4 and

```
r<1/sqrt(41)<1/6.
```

The last squared comparison has reserve 5/1476. Equation (14) and
0<G<1 give

```
N<1+2+1/3+19/400
 =17/4-1043/1200<17/4<=R^2.                    (15)
```

### 6.2. Whole interval 1/4<=q<=1/3

The upper p comparison sqrt(15/16)<31/32 has squared reserve
1/1024. Therefore

```
G<(61/60)*(31/32)-1/8
 =1651/1920<7/8,
```

with final reserve 29/1920. The lower p comparison
p>=sqrt(8/9)>14/15 gives

```
b>7/15-61/180-1/60=1/9.
```

Hence q/b<3 and

```
r<2/sqrt(10)<2/3,
```

the last squared reserve being 2/45. The whole endpoint bound (14)
then gives

```
N<(7/8)^2+2+(4/3)*(7/8)+19/400
 =17/4-1297/4800<17/4<=R^2.                    (16)
```

### 6.3. Whole interval 1/3<=q<2/5

Here p<=sqrt(8/9)<17/18, so

```
G<(61/60)*(17/18)-1/6
 =857/1080<4/5.
```

The exact height reserve is 7/1080. The whole lower bound b>2/75
from (6) gives q/b<15, and hence

```
r<14/sqrt(226)<15/16.
```

The last squared reserve is 337/28928. Applying (14) uniformly,

```
N<(4/5)^2+2+(15/8)*(4/5)+19/400
 =67/16=17/4-1/16<R^2.                         (17)
```

Equations (15)--(17) exclude the remaining maximum-n K corner
throughout every actual radial angle. Together with Section 4,
all four actual K corners are strictly inside the circle. Their
convex hull is too, contradicting physical K boundary contact.
This proves the complete positive-side Theorem 1.1 and therefore
the whole signed-strip Corollary 1.2.

## 7. Exact conditional transfer from the fresh parallel-tip chart

The complete accepted present normal form

```
PARALLEL_S_TIP_SINGLETON_ROOT_CENTRAL_OWNER_NORMAL_FORM.md
269e67a4053158638ccbe4a5c51933f1aed921a7175b5fa3b9354f30a1b7a62c
```

has full non-contributor acceptance at

```
REVIEW_PARALLEL_S_TIP_SINGLETON_CENTRAL_TOPOLOGY_INDEPENDENT_2026_10_27.md
f50a5b8130cc1bdf278ada5f3b22b9a97d16d0bd4b52ededb78296d2fb9dc801.
```

Its actual intrinsic H chart is

```
H=[x,x+1]v+[-y,1-y]u,
-delta<x<=delta, 0<y<13/60,
d=1+delta, 0<delta<1/60.
```

Reflect only the coordinates by P -> (-P.v,P.u). Then

```
h=-x, G=1-y,
|h|<=delta=d-1,
47/60<G<1,
H=[h-1,h] x [G-1,G], W=(h,G).
```

The same normal form proves that the actual HK is K-owned at W,
with its normal strict in H's upper-right vertex cone. Therefore
its real K side has exactly the complete positive c,s and strict
ell parameterization in (1). Both physical BK types and their
unchanged different means remain.

Whenever the actual HC is the top E2 feature and C physically has
two circle corners, the hypotheses of Corollary 1.2 now hold
without assuming a sign of x. The theorem excludes that whole
physical mask for either genuine H leaf and either BK type.

This is a conditional original page application, not a proof that
all HC directions are top. Any assembly still needs the complete
all-mask actual direction cover before applying it. This source
does not claim a whole parallel-B gate closure or treat the
physically shared-HB feature outside the pinned normal form.

## 8. Complete present inputs, reviews, and proof boundaries

All these complete mathematical sources were read. Their original
physical conclusions are used at their full stated scope; no
force-polygon theorem or smaller-degree law is imported.

| Complete source | Exact SHA256 | Use |
| --- | --- | --- |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | Actual physical side/vertex cones and unchanged contact conventions. |
| `C7_FORCE_POLYGON.md` | `d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089` | Physical two-circle frame and unshareable circle corners; the inner-face bound is fully reproduced. |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207` | Entire physical H-K-C side-normal rule, including the other normal's full cone. |
| `HIGH_CORNER_OWNED_CENTRAL_RADIAL_TOP_EXCLUSION.md` | `3b3ba081d85d7695e92d524859a15c8a9a1775ca0416cdb7bb95e76a8685ced7` | Complete nonpositive-h branch of the signed-strip corollary; no accepted bytes changed. |
| `PARALLEL_S_TIP_SINGLETON_ROOT_CENTRAL_OWNER_NORMAL_FORM.md` | `269e67a4053158638ccbe4a5c51933f1aed921a7175b5fa3b9354f30a1b7a62c` | Entire conditional parallel-tip original chart, with signed x and both actual BK means. |

The physical originals are in `current_pr11/research/nine`; the
two fresh sources are in this recovery directory. The whole
nonpositive-h acceptance is
`REVIEW_HIGH_CORNER_RADIAL_TOP_CERT_INDEPENDENT_2026_10_27.md`,
SHA256 `db63fd15bbd91e216b2f48405bcc3eb026efba52a141e89e650d53577aa232a6`.
The complete parallel normal-form acceptance is pinned in Section 7.
Both complete reviews were read; they do not substitute for the
required full independent review of this new positive-h proof.

The extension keeps h=1/60 where permitted by its physical statement,
all true central side positions, every circle-weight endpoint, the
entire actual C boundary, and both internal q endpoints. Its
|W|<d condition is explicit and is derived before use in the
natural original strip. Its strict G<1 condition is not enlarged.

No computational certificate, new normal selection, chosen shared
mean, hypothetical K2 law, lost physical unit, remote action,
original ledger edit, Lean invocation or CI workflow is introduced.
