# Every outer mixed body's extra inner-boundary corner is uniformly small

**Status:** complete hand argument; root and independent full mathematical
reviews passed on 2026-10-30. This note
strengthens the normal selection before the positive graph is classified.
It proves a local corner bound, not by itself the seven-ring capacity
contradiction.

Use the selected physical certificate and entirely loaded seven-ring in
`6241/1600<=q=R^2<=9/2`. Impose the additional compatible open normal
intervals in Section 2 below before selecting the stress. Then every
unique-circle U4/U5 body has its extra inner-boundary corner B satisfying

```text
|B|^2<33/20.                                         (1)
```

The reflected U5 statement is included. Normalize a proposed exception
as in [LOADED_OUTER_MIXED_RESTRICTIONS.md](LOADED_OUTER_MIXED_RESTRICTIONS.md):

```text
C=[X-1,X] x [-Y,1-Y],       w=(X,-Y),
H=Y-1>X>1/2,       X<1,
A=(X-1,-H),       B=(X,-H),
P=(X,-H-t),       0<t<(H-X)/H,
q=X^2+(H+1)^2,       |B|^2>=33/20.                   (2)
```

Here A is the strict opposite-corner V contact and P is the outer S
contact. Both physical neighbors are loaded.

## 1. The exception lies in a narrow rational box

Since `q=|B|^2+2H+1<=9/2`,

```text
H<=37/40,
X^2>=33/20-(37/40)^2=1271/1600>(89/100)^2.
```

Put `epsilon=1-X` and `d=H-X`. Then

```text
89/100<X<H<=37/40,
3/40<epsilon<11/100,
0<d<7/200,
189/100<Y<=77/40,
q>33/20+89/50+1=443/100.                             (3)
```

In particular, writing r=|A|,

```text
r^2=epsilon^2+H^2<34709/40000<1,
q-(r+1)^2=2(X+H)-1-2r>14/25>0.                     (4)
```

Thus no circle vertex of a neighboring square can be at distance at
most one from A.

## 2. Extend the compatible opposite-circle VV exclusion

The proof in
[LOADED_OUTER_VV_NORMAL_EXCLUSION.md](LOADED_OUTER_VV_NORMAL_EXCLUSION.md)
extends to the larger exceptional range (2), as follows. If the pair
at A is VV, (4) makes the neighbor's circle vertex opposite A. That
neighbor is the reflection of C through the line spanned by A. Set

```text
D=H^2-epsilon^2>0,       E=2epsilon*H>0.
```

The common strict normal into the neighbor is `(-c,s)`, where c,s>0,
`c^2+s^2=1`, and its allowable slope interval is

```text
0<k=s/c<E/D.
```

The generic VV restriction forces C's other positive pair to be SS with
an application point in the relative interior of the overlap. The
loaded SS calculation in the outer-mixed note yields

```text
0<t<Z-H<(H-X)/H<7/178,
Z=sqrt(Y^2-2X-1).                                    (5)
```

Force balance and torque require

```text
t=(Y-X)*k/(Y-X*k).                                   (6)
```

Choose the angle midpoint of the common normal cone:

```text
k_mid=epsilon/H>3/37.
```

At this direction, the denominator in (6) is positive, `Y-X>1`, and
`Y-X*k_mid<Y<=77/40`. Consequently

```text
t_mid>120/2849>1/24>7/178.                           (7)
```

The strict rational comparisons are `2880>2849` and `178>168`.
Reflection exchanges the endpoint frames, sending k to
`tan(2*beta-atan(k))`, where `beta=atan(epsilon/H)`. The midpoint is
fixed. Hence (7) holds simultaneously for both endpoints in their own
frames. A nonempty open neighborhood of that midpoint makes both
required t values exceed 1/24, with positive denominators. It excludes
either endpoint from having the exceptional outer role in the later
positive graph, by (5).

Impose these intervals for every geometric opposite-circle VV candidate
whose endpoint frame obeys the stress-independent constraints on X,H,q
and |B|^2 in (2); no application parameter t is used to select candidates.
This enlarges the candidate set in the
earlier selection lemma and uses the same midpoint condition on its old
candidates. The reflection gives identical endpoint parameters, so no
choice of an eventual outer endpoint is needed. The adjacent-circle
candidate set from the all-inner capacity proof is disjoint. The coherent
four-square-junction compatibility and the subsequent finite-polynomial
avoidance hold exactly as recorded in
[PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md):
a coupled opposite pair at such a junction cannot have both endpoints
geometrically circle-loaded in this radius window. All remaining interval
parameters are independent. Select inside the resulting open product,
and only then classify the positive stress graph.

For this selected stress, the pair at A is therefore proper V/S. By (4),
no circle vertex of its S neighbor lies on the contacted side. A radial
neighbor is excluded just as in Section 5 of the earlier VV note: a
perpendicular circle side would put a circle vertex on the contacted
side, and a parallel opposite circle side would make the contact the
radial body's forbidden loaded inner face. The neighbor thus has a unique
circle vertex and an inner-side incidence. The incident mixed exclusion
reduces its possible rows to U1,U6,U7.

## 3. The source-contact radius lemma extends to q>=22/5

We first strengthen
[LOADED_SIDE_SOURCE_CONTACT_RADIUS.md](LOADED_SIDE_SOURCE_CONTACT_RADIUS.md):
for `22/5<=q<=9/2`, every actual application point of a loaded U1 body
has norm strictly greater than one.

Use the same source coordinates and concurrency parameter:

```text
C_0=[U-1,U] x [-V,1-V],       U,V>7/8,
U^2+V^2=q,
P_0=(eta*U,1-V),       Q_0=(U-1,-eta*V),
0<eta<=1.
```

Suppose `|P_0|<=1`, and write `p=eta*U`, `b=eta*V`. Then

```text
p<=1,       b<=V/U,
b^2<=V^3(2-V)/U^2.                                  (8)
```

For `V>=3/2`, the one-sided support bound from the source note applies
to the upper neighbor and gives

```text
q<=(p+1)^2+(V-1)^2<=2+2p<=4,
```

which is impossible. Therefore `7/8<V<3/2`, and U>1. Apply that same
one-sided bound to the left neighbor at Q_0. Each of its vertex squared
norms is at most

```text
M=max((U-1)^2,(U-2)^2)+(b+1)^2,
q-(U-1)^2=2U-1+V^2.                                 (9)
```

The following four rational intervals prove M<q. In the first three
intervals U>3/2, so the maximum in (9) is `(U-1)^2`.

* If `7/8<V<=1`, then U>9/5 and `b<5/9<3/5`, whence
  `q-(U-1)^2>13/5+49/64>64/25>(b+1)^2`.
* If `1<=V<=5/4`, then
  `U^2>=227/80>(42/25)^2` and `b<125/168<3/4`. Hence
  `q-(U-1)^2>84/25>49/16>(b+1)^2`.
* If `5/4<=V<=7/5`, then
  `U^2>=61/25>(39/25)^2` and `b<35/39<9/10`. Hence
  `q-(U-1)^2>78/25-1+25/16=1473/400>361/100>(b+1)^2`.
* If `7/5<=V<3/2`, then
  `U^2>43/20>(73/50)^2`. Therefore
  `max((U-1)^2,(U-2)^2)<(U-1)^2+2/25`.
  The function `V^3(2-V)` increases up to V=3/2 and has value 27/16
  there. Using (8) and `sqrt(3)<7/4` gives
  `b<75sqrt(3)/146<525/584<9/10`. Finally
  `q-(U-1)^2-2/25>146/50-1+49/25-2/25=19/5>361/100>(b+1)^2`.

Thus the left neighbor is circle-clear, contrary to being loaded.
Reflection exchanges the two supports and proves the result for Q_0
as well. This establishes the strengthened source lemma.

For the proposed outer exception, (3)--(4) give `q>443/100>22/5`
and |A|<1. Its S neighbor consequently cannot be U1. It is U6 or U7.

## 4. The outer force fixes a tight frame for that mixed neighbor

Normalize C's circle coefficient to one. Its outer S force is `(-h,0)`
and its V force is `(X+h,-Y)`, with `h*t=Y-X`. Therefore the normal
into the neighbor at A is `n=(-c,s)`, where c,s>0 and

```text
k=s/c=Y/(X+h)=Y*t/(Y-X+X*t).
```

Since `Y-X>1`, (2)--(3) imply

```text
k<Y*d/H<539/7120<1/13,
c=1/sqrt(1+k^2)>99/100.                              (10)
```

Here `539*13=7007<7120`. Also `epsilon=1-H+d`, so

```text
epsilon-H*k>epsilon-Y*d=1-H-H*d
                    >3/40-(37/40)(7/200)=341/8000.   (11)
```

Take the neighbor's positive orthonormal frame

```text
u=(-s,-c),       v=(c,-s)=-n.
```

The contact A has tangent coordinate p and v-coordinate `1-V`, where

```text
p=A dot u=epsilon*s+H*c>0,
V=1+A dot n=1+(epsilon-H*k)*c.
```

By (3), (10), and (11),

```text
V>1+33759/800000>26/25,
V<1+epsilon<111/100.                                 (12)
```

Its opposite parallel circle side has v-coordinate -V. Let the farthest
tangent coordinate on that side have absolute value U, so `U^2+V^2=q`.
The estimates already give U>1. Since the contacted unit tangent
interval contains p>0, its farthest tangent endpoint cannot be -U:
that would make the whole interval `[-U,1-U]` negative. Thus its circle
vertex has coordinates `(U,-V)`, and the neighbor is

```text
C_1=[U-1,U] x [-V,1-V],       A=(p,1-V).
```

Equations (3) and (12) give the more precise bounds

```text
U^2>443/100-(111/100)^2=31979/10000>(89/50)^2,
U^2<9/2-(26/25)^2=4273/1250<(37/20)^2,
89/50<U<37/20.                                       (13)
```

On the other hand, Cauchy--Schwarz and (4) give

```text
p<=|A|<sqrt(34709/40000)<233/250.                     (14)
```

The last squared comparison has exact difference
`(233/250)^2-34709/40000=899/1000000>0`.

## 5. The mixed neighbor's other loaded contact forces p too large

The remaining U6/U7 row at C_1 has its other support at the adjacent
vertex `Q=(U-1,-V)`. Put

```text
a=U-1,       tau=p-U+1.
```

Normalizing this body's circle coefficient to one, its inward V force
at Q is `(U,K)`. Strict vertex support gives K>0. The inner S force is
`(0,-V-K)`, so torque about Q yields

```text
tau*(V+K)=V,
0<tau<1,       K=V*(1-tau)/tau.                     (15)
```

The physical neighbor across Q contains the unit-normal-step point
`Q-(U,K)/N`, where `N=sqrt(U^2+K^2)`. Disk containment is exactly

```text
V*K<=a*(N+U).                                       (16)
```

Here (12)--(13) give `0<a<17/20<1<V`. Hence
`K/(N+U)<=a/V<1`. The half-angle identity

```text
K=2U*z/(1-z^2),       z=K/(N+U),
```

whose right side increases for `0<z<1`, converts (16) to

```text
K<=2U*a*V/(V^2-a^2),
tau>= (V^2-a^2)/(q-1),
p=a+tau>=U*(q+1-2U)/(q-1).                           (17)
```

For fixed U>1 the last expression strictly increases with q, because
its derivative is `2U(U-1)/(q-1)^2>0`. By (3),

```text
p>U*(543-200U)/343.
```

The right side strictly decreases on `89/50<U<37/20`, since its
derivative is `(543-400U)/343<0`. Thus

```text
p>(37/20)*(543-370)/343=6401/6860>233/250.             (18)
```

The final comparison is `6401*250-233*6860=1870>0`.
This contradicts (14). The exception (2) is impossible and proves (1).

The argument uses the exact frame forced by the outer body's small
positive S-contact parameter. It does not assert that every U6/U7
S application point in every loaded ring lies outside the unit disk.
Its conclusion is the uniform bound (1) for the extra corners of all
outer mixed bodies in the newly selected certificate.
