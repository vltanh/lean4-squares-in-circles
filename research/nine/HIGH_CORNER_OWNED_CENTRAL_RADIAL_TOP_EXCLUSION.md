# An owned high-corner central side cannot return to a radial top boundary unit

Date: October 27, 2026.  
Author: topology_final.

**Status: complete fresh physical exclusion, frozen for full independent
review.** The theorem treats the entire central-side slider and every
physical contact type. It uses no force equation, C2 concurrence, K2
surrogate, circle-weight restriction, or computational certificate.

## 1. Full physical statement

Let

```
1<=d<61/60, R^2=(d+1)^2+1/4,
-1/60<=h<=0, 89/120<G<1,
H=[h-1,h] x [G-1,G], W=(h,G).
```

Let K and C be closed unit squares contained in the same closed disk
of radius R about the origin. The interiors of H, K, C are pairwise
disjoint, and all three pairs physically contact. K has a physical
circle point. C has two physical adjacent circle corners, regardless
of their stress weights.

The actual H-to-K normal is owned by K at W, with its entire side
position retained:

```
m=(-c,s), n=(s,c), c,s>0, c^2+s^2=1,
K=W+[-ell,1-ell]m+[0,1]n,
0<ell<1.                                            (1)
```

Thus W is in the relative interior of K's minimum-n side. The actual
H-to-C normal is E2, H-owned, and C has minimum height G and touches
H's top. All actual singleton/shared means and all actual CK normals
are initially retained.

**Theorem 1.1.** This configuration is impossible.

The degrees of H and K are unrestricted. Positive force, moment, and
mean equations in any caller may all be retained unchanged, but none
is needed below. In particular the theorem excludes a physical
two-circle mask even if only one of its two circle weights is
positive. A zero circle weight does not change its physical premise.

The closed h=0 endpoint is included. The strict G<1 is an explicit
hypothesis. No assertion at G=1 is needed for the original caller,
which derives that strictness from the whole actual H4 moment.

## 2. The entire physical C frame

The physical two-circle classification at this radius gives

```
C=[d,d+1]e+[-1/2,1/2]f,
|e|=|f|=1, e.f=0.                                  (2)
```

The two outer corners are the two circle points. Since C's minimum
height G is positive, its radial direction has e_y>0. A nonpositive
radial height would give a nonpositive minimum height directly from
(2).

If e_x>0, C's minimum-height point has positive horizontal coordinate:
writing e=(q,p), q,p>0, it is

```
(d*q+p/2, d*p-q/2).
```

It cannot touch H's top, whose horizontal coordinates are at most
h<=0. If e_x=0, then e=E2 and C's minimum height is d>=1, contrary to
G<1. This also excludes the whole possible shared, aligned top side;
no mean from that side is silently chosen.

Therefore C has the unique radial northwest form

```
e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1,
C=[d,d+1]e+[-1/2,1/2]f,
T=d*e-f/2=(-d*q-p/2,G),
G=d*p-q/2,
V=d*e+f/2=(a,G+q), a=p/2-d*q.                      (3)
```

T is C's actual minimum-height vertex. Hence the HC application is
this physical vertex whenever the caller carries a force there; no
new application is selected. The other inner vertex is V.

## 3. Uniform bounds for the whole radial angle

First

```
q<2/5, p>9/10, a>13/300>0.                         (4)
```

Indeed, if q>=2/5 then

```
p<=sqrt(21)/5<11/12,
G=d*p-q/2 < (61/60)*(11/12)-1/5
             =527/720 < 89/120,
```

contrary to the hypothesis. The last gap is 7/720; the squared
comparison `(11/12)^2-21/25` is 1/3600. Thus p^2>21/25>81/100,
and

```
a=p/2-d*q > 9/20-61/150=13/300.
```

Also a<1/2. The actual displacement from W to V has coordinates

```
V-W=(a-h,q),
0<a-h<31/60, 0<q<2/5,
|V-W|^2 < (31/60)^2+(2/5)^2=1537/3600<1.           (5)
```

The actual lower vertex T lies strictly left of W:
`T_x<-9/20<h`, with the possible h=-1/60 endpoint still strict.
In particular, T is not a point of K because

```
(T-W).n=s*(T_x-h)<0.                              (6)
```

The normal support in (1), not a stress sign, proves (6).

## 4. Complete physical CK contact cover

We show that the entire contact C intersection K consists of V. This
step neither assumes a CK side owner nor invokes a finite normal
selection. It covers shared contacts by their physical relative
interiors and keeps their original means until the corresponding
physical possibility is excluded.

The two outer circle vertices of C cannot be shared with another
interior-disjoint unit contained in the same circle. This is the
physical circle-point unshareability statement.

Consider the relative interiors of the four C sides.

* On its maximum-e side the C-to-K normal is e. The C-to-H normal is
  -E2, and `e.(-E2)=-p<0`. The physical triangle side-normal lemma at
  this owned C side excludes the contact.
* On its maximum-f side the corresponding scalar is
  `f.(-E2)=-q<0`, so that side is excluded by the same complete
  physical triangle lemma.
* On its minimum-f side the C-to-K normal is -f. At K, the actual
  K-to-H normal is -n, owned at W by (1), and its K-to-C normal would
  be f. The physical triangle lemma would require
  `(-n).f>=0`, whereas `(-n).f=-(s*p+c*q)<0`.
* The relative interior of C's minimum-e side cannot contact any
  physical boundary unit. Here is the complete norm argument, rather
  than an unstated invocation of a narrower side-owner chart. If
  K touches there at `(d,t)` in the (e,f) frame, |t|<1/2, its entire
  body is in the half-plane with e-coordinate at most d. At a
  maximum-e vertex, its two inward unit axes have nonpositive
  e-components and opposite f-components; at an aligned side the
  same bounds follow from the whole actual side interval. Thus every
  K point has e-coordinate in `[d-sqrt(2),d]` and f-coordinate of
  absolute value at most 3/2. Since d>=1, its e-coordinate has
  absolute value at most d. Therefore its entire norm squared is
  at most `d^2+9/4<R^2`, the exact gap being `2*d-1>=1`.

The inner vertex T is excluded separately by (6); no relative-interior
argument has been applied to that endpoint. The only remaining C
boundary point is V. A contact with the open interior of C would
contradict disjoint interiors. Since CK is a physical contact, it must
therefore occur at V. In particular CK is a physical singleton; any
nontrivial shared segment would contain one of the excluded relative
interiors or circle vertices.

## 5. The actual K side and full position are forced

At the C vertex V, every outward normal is a nonnegative nonzero
combination of -e and f. Both have positive horizontal component.
Thus the actual C-to-K normal w has w_x>0, even at the endpoints of
this whole vertex cone.

The n-coordinate of V relative to W is

```
theta=(V-W).n=s*(a-h)+c*q.
```

Equations (4)--(5) give

```
0<theta<1.                                        (7)
```

Consequently V is in neither n-face of K and cannot be a K vertex.
Since it lies on K's boundary, it lies in the relative interior of one
of the two m-sides. Its minimum-m side would have incoming normal m,
whose horizontal component is -c<0, contrary to w_x>0. Thus V is on
the maximum-m side, and its complete position is

```
j=1-ell in (0,1),
V=W+j*m+theta*n,
j=s*q-c*(a-h)>0,
theta=s*(a-h)+c*q in (0,1),
w=-m.                                             (8)
```

This conclusion is from the actual physical support and normal cone.
It does not select a new CK normal. In particular all initially free
CK and shared CK possibilities have been eliminated by their real
geometry; none is omitted from the original domain.

## 6. Both minimum-n corners of K are strictly inside the circle

The two minimum-n corners are W-ell*m and W+j*m. Both are at distance
at most one from W. From |h|<=1/60 and G<1,

```
|W|^2<1+1/3600<(61/60)^2,
|W-ell*m|, |W+j*m| < 121/60 < R.                  (9)
```

The final squared reserve against the least radius is
`17/4-(121/60)^2=659/3600`. It remains to exclude only the two
maximum-n corners

```
Z_plus=W+j*m+n,
Z_minus=W-(1-j)*m+n.                             (10)
```

No K circle corner has yet been chosen or assumed; (9)--(10) cover all
four physical corners.

## 7. A rigorous enlargement to h=0

Keep d,p,q,c,s fixed, so G and a in (3) are fixed. Define

```
j0=s*q-c*a, theta0=s*a+c*q.
```

Equation (8) gives j=j0+c*h. Since h<=0 and j>0,

```
0<j0<s*q<2/5,
0<theta0<=sqrt(a^2+q^2)<sqrt(41/100)<1.             (11)
```

Use a superscript 0 for the algebraic corner expressions (10) with
h=0 and j=j0. Each actual expression differs from its superscript-0
expression by the same vector:

```
Z_plus=Z_plus^0+h*s*n,
Z_minus=Z_minus^0+h*s*n.                          (12)
```

For either superscript-0 corner, its n-coordinate is `1+c*G`, since
m is perpendicular to n. Hence the exact norm difference is

```
|Z|^2-|Z^0|^2=h*s*(2*(1+c*G)+h*s)<=0.             (13)
```

The second factor is greater than `2-1/60>0`; h=0 gives equality.
Thus it suffices to bound the two algebraic corners at h=0. This is a
proved scalar enlargement only. It does not move an actual unit,
change any force or mean, or assert that the enlarged pose is an
original configuration.

## 8. The first maximum-n corner is inside R uniformly

The actual C vertex has

```
|V|^2=d^2+1/4.
```

At the h=0 enlargement, its coordinates satisfy

```
V=(0,G)+j0*m+theta0*n,
Z_plus^0=V+(1-theta0)*n.
```

Therefore the complete exact radius difference is

```
R^2-|Z_plus^0|^2
    =2*d+theta0^2-2*c*G*(1-theta0)
    >=2*(d-G)+theta0^2>0.                         (14)
```

The inequality uses 0<c<=1 and 0<theta0<1. Its final strictness is
uniform: `G=d*p-q/2<d` for q>0. It is independent of any K circle
mask or force sign.

## 9. The whole remaining K-angle interval is monotone

At h=0 put u=1-j0>0. The other corner's norm squared is

```
N=|Z_minus^0|^2
 =G^2+1+u^2+2*G*(c-u*s),
j0=s*q-c*a.                                      (15)
```

Parameterize the entire first quadrant as

```
c=sin(phi), s=cos(phi).
```

The actual condition j0>0 is exactly

```
0<phi<phi_star=atan(q/a)<pi/2.
```

We may enlarge to the closed endpoint phi_star. Throughout the entire
closed interval from zero to phi_star, not just at the actual angle,

```
0<=j0<=q<2/5, u=1-j0>0,
0<theta0=s*a+c*q<=sqrt(a^2+q^2)<1,
u'=theta0, c'=s, s'=-c.
```

The full derivative is

```
N'=2*u*theta0+2*G*(s*(1-theta0)+u*c)>0.             (16)
```

All factors have the displayed signs on the whole interval. Thus N
is strictly increasing, and its maximum on the enlargement is at
j0=0, where

```
c_star=q/sqrt(a^2+q^2),
s_star=a/sqrt(a^2+q^2),
N <= G^2+2+2*G*(q-a)/sqrt(a^2+q^2).                (17)
```

This endpoint comparison retains the original strict j>0 domain and
explicitly enlarges it to j0=0. No assumed sign of q-a is needed.

## 10. Two full radial-angle intervals finish the proof

The following two intervals exhaust 0<q<2/5, with q=1/3 included in
either comparison.

### 10.1. The complete interval 0<q<=1/3

Here

```
p>=sqrt(8/9)>14/15,
a=p/2-d*q>7/15-61/180=23/180.
```

The exact squared reserve in the p comparison is 4/225. Consequently
q/a<60/23. The function

```
F(t)=(t-1)/sqrt(1+t^2)
```

is strictly increasing for t>=0, since its derivative is
`(1+t)/(1+t^2)^(3/2)`. Therefore

```
(q-a)/sqrt(a^2+q^2)
    <37/sqrt(4129)<3/5.                          (18)
```

The last comparison is exact: `(3/5)^2-1369/4129`
equals `2936/103225>0`. Applying (18) to (17), and using 0<G<1,

```
N < G^2+2+(6/5)*G < 21/5 < 17/4 <= R^2.          (19)
```

The final radius reserve is 1/20. This argument includes every q-a
sign and the entire endpoint q=1/3.

### 10.2. The complete interval 1/3<=q<2/5

Here

```
p<=sqrt(8/9)<17/18,
G=d*p-q/2 < (61/60)*(17/18)-1/6
             =857/1080 < 4/5.                    (20)
```

The two exact reserves are `1/324` for the squared p comparison and
`7/1080` for the final height comparison. Since a>0 and q>0,

```
(q-a)/sqrt(a^2+q^2)<1.
```

Thus the same whole endpoint bound (17) gives

```
N < G^2+2+2*G < 106/25 < 17/4 <= R^2.             (21)
```

The last radius reserve is 1/100.

Together (13)--(21) put both maximum-n corners strictly inside R.
Equation (9) puts both other corners there as well. The whole convex
unit K is consequently strictly inside the disk, contradicting its
physical boundary contact. This proves Theorem 1.1.

## 11. Original caller and exact scope of the reduction

This is a local physical theorem with explicit chart hypotheses. It
does not by itself prove that an arbitrary graph has that chart.

In the fresh B-owned-HB/nonparallel-B/K-owned-HK continuation, the
all-mask direction reduction derives, before assuming C unique,

```
h=-x<0, 89/120<G<1,
W=(h,G),
K=W+[-ell,1-ell](-c,s)+[0,1](s,c),
c,s>0, 0<ell<1,
HC=E2, H-owned, with its entire actual mean.
```

Its genuine H4 argument excludes the top G=1 endpoint. Its actual
central side owner supplies precisely (1), including the real ell.
Both physical BK types and both genuine H leaves remain compatible
with this statement; none enters the proof above. Whenever that
complete original chart has been proved, the whole remaining
two-circle C mask is excluded at once by Theorem 1.1. The unique-C
top row has its separate whole analytic theorem.

The present local theorem does not rely on that forthcoming assembly
for its proof, and does not use it circularly to establish a physical
mask or a normal sign. An original gate must only be marked after the
complete source for its all-mask chart and the other owners has itself
been independently accepted. This manuscript makes no claim to
restore any missing older hash.

## 12. Complete present physical foundations

All three following original sources were read in full. They are
present under `current_pr11/research/nine`.

| Source | Exact SHA256 | Use |
| --- | --- | --- |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | Physical side/vertex normal cones and unchanged actual contact conventions. |
| `C7_FORCE_POLYGON.md` | `d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089` | Physical two-circle classification and circle-point unshareability; the entire needed inner-side norm argument is also reproduced in Section 4. |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207` | Radius-free physical side-normal obstruction at every actual H-K-C contact. |

No C2 lemma, finite normal selection, global C-mask theorem, global
root reduction, or missing recovery artifact is a logical premise of
this local result. Every contact restriction comes from these physical
foundations and the explicit actual square chart in Section 1.
