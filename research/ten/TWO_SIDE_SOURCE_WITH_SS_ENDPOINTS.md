# A two-side source with width-two-separated endpoints has a bounded normal form

**Status:** reviewed exact necessary-form and radius reduction; root and
independent mathematical reviews passed on 2026-10-30, including Section 4. This is a whole-branch statement, not a numerical neighborhood
or a completion-capacity theorem.

Work in `79/40<=R<=3/sqrt(2)` and put q=R^2. Let C be a loaded body with
exactly two positive body-pair contacts. Suppose both outward contact
normals are side normals, and its two unloaded degree-two S transmitters
lead to distinct endpoint squares A and B. Suppose A and B are joined
by an SS path, so `dist(A,B)=2`. The endpoint squares may have arbitrary
other contacts and either one or two geometric circle vertices; none of
the arguments below assumes a positive load on A or B.

Assume C has a unique circle vertex. The parallel and outer-side
exclusions in [LSLSLSS_SUPPORT_NORMALIZATION.md](LSLSLSS_SUPPORT_NORMALIZATION.md)
then leave the two inner side normals, its row U-EE. This note proves:

1. The complete source and single-transmitter coordinates in Section 1,
   with two explicit closed alternatives for the transmitter slides.
2. The strict necessary radius bound

   ```text
   q>13/3.                                          (1)
   ```
3. Both source coordinates satisfy `1<X,Y<sqrt(7/2)<15/8`.

The statement applies in particular to the U-EE row of the whole
LSLSLSS case, but also when A or B has additional retained neighbors.

## 1. Exact source coordinates and transmitter slides

Choose C's positively oriented square axes so

```text
C=[X-1,X] x [Y-1,Y],       w=(X,Y),
X,Y>1/2,       X^2+Y^2=q.
```

Its outgoing normals toward A and B are respectively `(-1,0)` and
`(0,-1)`. Normalize C's positive circle coefficient to one. Its two
actual inward pair forces are `(X,0)` and `(0,Y)`. Torque about the
origin gives the common source parameter eta, with contacts on C and
the far endpoint squares

```text
P_A=(X-1,eta*Y),       Q_A=(X-2,eta*Y) in A,
P_B=(eta*X,Y-1),       Q_B=(eta*X,Y-2) in B,
0<eta<=1,
X-1<=eta*X<=X,       Y-1<=eta*Y<=Y.                  (2)
```

Indeed torque is `-X*(P_A)_y+Y*(P_B)_x=0`. At least one of X,Y exceeds
one in the radius window, so membership in that inner side gives
eta>0. Membership in either side gives eta<=1. The path equations give
the displayed unit displacements. These are the actual force points;
no side-interior assumption is imposed.

The endpoint squares are supported in

```text
A subset {x<=X-2},       B subset {y<=Y-2}.           (3)
```

The unit-normal-step lemma puts `(X-3,eta*Y)` in A and
`(eta*X,Y-3)` in B. Consequently

```text
(X-3)^2+eta^2*Y^2<=q,
eta^2*X^2+(Y-3)^2<=q.                               (4)
```

As eta,X,Y are positive, (4) gives `X,Y>3-R>7/8`.
Then q<=9/2 also gives

```text
7/8<X,Y<31/16.                                      (5)
```

For the upper bound, `X^2<9/2-(7/8)^2=239/64<(31/16)^2`,
and likewise for Y. In particular both cap offsets 2-X and 2-Y are
positive, greater than 1/16.

The two single S transmitters necessarily have C's axis-parallel frame.
Their exact square regions and centers are

```text
S_A=[X-2,X-1] x [alpha-1/2,alpha+1/2],
c_(S_A)=(X-3/2,alpha),
eta*Y-1/2<=alpha<=eta*Y+1/2;

S_B=[beta-1/2,beta+1/2] x [Y-2,Y-1],
c_(S_B)=(beta,Y-3/2),
eta*X-1/2<=beta<=eta*X+1/2.                          (6)
```

These closed slide intervals retain applications at support endpoints.
Their disk-containment conditions are exactly

```text
(|X-3/2|+1/2)^2+(|alpha|+1/2)^2<=q,
(|beta|+1/2)^2+(|Y-3/2|+1/2)^2<=q.                  (7)
```

There is also a finite cut that follows from their mutual nonoverlap:

```text
alpha>=Y-1/2       OR       beta>=X-1/2.              (8)
```

Conversely, under (2) and (6), condition (8) is exactly the condition
that the interiors of these two transmitter squares be disjoint.
To see this, S_B's right endpoint is at least eta*X>=X-1, and S_A's
top endpoint is at least eta*Y>=Y-1. Thus their interior x intervals
overlap exactly when `beta-1/2<X-1`, and their interior y intervals
overlap exactly when `alpha-1/2<Y-1`. Disjointness is precisely (8).
Equalities represent permitted side contacts and are retained.

The source center is `(X-1/2,Y-1/2)`. Equations (2), (4), (6)--(8)
therefore provide uniform, finite-branch center-region data for three
of the core bodies, while preserving all continuous slides. They do
not specify the SS transmitters' independent slides or A and B's frames.

## 2. The two endpoint caps couple the source frame to the SS gap

Use the reviewed one-square cap function

```text
Theta_R(a)=atan((sqrt(R^2-(a+1)^2)-1/2)/(a+1/2))
```

from [TRANSMISSION_CAP_ANGLE_BOUND.md](TRANSMISSION_CAP_ANGLE_BOUND.md).
It bounds the deviation of a contained square's center ray from the
normal of a cap `x>=a`; its numerator is nonnegative whenever that
cap contains a square. On its relevant domain Theta_R is decreasing
and concave in a, and increasing in R.

By (3), A's center ray deviates from the negative x-axis by at most
`Theta_R(2-X)`. B's center ray deviates from the negative y-axis by
at most `Theta_R(2-Y)`. Let delta be the minor angle between their center
rays. The triangle inequality for circular angle gives

```text
delta<=pi/2+Theta_R(2-X)+Theta_R(2-Y).                (9)
```

The width-two path independently gives

```text
delta>=pi-2Theta_R(1).                               (10)
```

In particular its existence gives q>=17/4, making Theta_R(1) defined
and nonnegative. Combine (9)--(10), use concavity, and use
`X+Y<=sqrt(2q)` with monotonicity to obtain

```text
pi/2
 <=2Theta_R(1)+Theta_R(2-X)+Theta_R(2-Y)
 <=2Theta_R(1)+2Theta_R(2-(X+Y)/2)
 <=2Theta_R(1)+2Theta_R(2-sqrt(q/2)).
```

All arguments of Theta_R in this chain belong to its relevant domain:
the first two come from actual endpoint squares, their average remains
in that interval, and decreasing the positive cap offset preserves
nonnegativity of the numerator. Thus every realization satisfies

```text
Theta_R(1)+Theta_R(2-sqrt(q/2))>=pi/4.                (11)
```

This inequality is independent of endpoint circle multiplicity, endpoint
forces, and every transmitter slide.

## 3. Exact rational estimates exclude q<=13/3

Suppose q<=13/3. Then

```text
sqrt(q/2)<=sqrt(13/6)<59/40,
2-sqrt(q/2)>21/40,
(59/40)^2-13/6=43/4800>0.                           (12)
```

At the first cap offset, monotonicity in q and `sqrt(1/3)<7/12` give

```text
tan(Theta_R(1))
 <=(sqrt(1/3)-1/2)/(3/2)<1/18.                       (13)
```

For the other cap, monotonicity in its offset and in q gives

```text
tan(Theta_R(2-sqrt(q/2)))
 <(sqrt(13/3-(61/40)^2)-1/2)/(41/40)
 =(sqrt(9637/4800)-1/2)/(41/40)
 <17/19.                                           (14)
```

The final strict comparison follows from the exact positive square gap

```text
(1077/760)^2-9637/4800=83/173280>0,
1/2+(41/40)(17/19)=1077/760.
```

Both angles are nonnegative. Finally

```text
atan(1/18)+atan(17/19)=pi/4,
[(1/18)+(17/19)]/[1-(1/18)(17/19)]=1.
```

Equations (13)--(14) contradict (11). This proves q>13/3.

## 4. Both source coordinates are strictly above one

The sharper unsymmetrized inequality from Section 2 is

```text
2Theta_R(1)+Theta_R(2-X)+Theta_R(2-Y)>=pi/2.           (17)
```

Suppose X<=1; the other coordinate is handled by exchanging axes.
For fixed q and `X<=Y=sqrt(q-X^2)`, put

```text
F_q(X)=Theta_R(2-X)+Theta_R(2-sqrt(q-X^2)).
```

Concavity and negativity of Theta_R's derivative give

```text
F_q'(X)=|Theta_R'(2-X)|-(X/Y)|Theta_R'(2-Y)|>=0.       (18)
```

Indeed X<=Y implies 2-X>=2-Y, so concavity makes the first absolute
derivative at least the second. Both cap offsets stay in their relevant
domain while X increases toward one: the first decreases and the second
increases only to its value at one, where the numerator is positive
throughout `13/3<q<=9/2`. Alternatively, that last fact follows directly
from the explicit radical formula.

At fixed X, F_q(X) increases with q, because R increases and the second
cap offset decreases. Let Theta_* denote the cap function at q=9/2.
Then X<=1 and (18) imply

```text
F_q(X)<=F_(9/2)(1)
       =Theta_*(1)+Theta_*(2-sqrt(7/2))
       <Theta_*(1)+Theta_*(1/8),                     (19)
```

where `sqrt(7/2)<15/8`. Consequently (17) would require

```text
3Theta_*(1)+Theta_*(1/8)>pi/2.                       (20)
```

But the exact tangent bounds are

```text
tan(Theta_*(1))=(sqrt(2)-1)/3<1/7,
tan(Theta_*(1/8))=(sqrt(207)-4)/5<21/10.
```

The first uses `sqrt(2)<10/7`; the second uses `sqrt(207)<29/2`.
Also

```text
tan(3atan(1/7))=73/161,
(73/161)(21/10)=1533/1610<1.
```

The two angles `3atan(1/7)` and `atan(21/10)` are in `(0,pi/2)`;
the product inequality makes their sum less than pi/2. Thus
`3Theta_*(1)+Theta_*(1/8)<pi/2`, contradicting (20). Both X and Y
are strictly above one. The circle equation now gives

```text
1<X,Y<sqrt(q-1)<=sqrt(7/2)<15/8.                     (21)
```

In particular the source's opposite inner corner is in the small-corner
range with both own circle coordinates above one, which is useful in
either a center-cover or a boundary-cap completion argument.

The retained range `13/3<q<=9/2` still contains the known numerical
seven-body candidate. This note neither fixes its symmetric geometry
nor removes the remaining continuous source coordinates and slides.
Those variables must be handled uniformly before a finite center-cover
certificate can exclude the whole U-EE row or a whole cycle signature.
