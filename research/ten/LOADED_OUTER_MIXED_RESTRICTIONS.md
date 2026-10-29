# Exact restrictions on the remaining outer-edge mixed ring body

**Status:** hand necessary-condition calculation; two independent full
mathematical reviews passed on 2026-10-29. This note does not exclude
U4/U5.

Use an entirely loaded seven-ring in `6241/1600<=q=R^2<=9/2`. Up to
reflection and reversal, the remaining outer-edge/opposite-corner mixed
body can be written

```text
C=[X-1,X] x [-Y,1-Y],       w=(X,-Y),
1/2<X<1<Y,       X^2+Y^2=q,
A=(X-1,1-Y),       B=(X,1-Y),
P=(X,1-Y-t),       0<t<=1.                            (1)
```

The strict V incidence is A, and the S incidence P lies on the outer
right side. Put H=Y-1. Normalize the positive circle coefficient to one,
and write the actual inward S force as `(-h,0)`, with h>0. The inward
V force is then `(X+h,-Y)`.

## 1. Torque, loaded-neighbor containment and angle

Taking torque about A gives

```text
h*t=Y-X=H+1-X>0.                                     (2)
```

In particular t>0, so P is strictly below B. The physical neighbor across
the S side has inward normal `(1,0)` at P and contains P+(1,0). Disk
containment gives

```text
(X+1)^2+(H+t)^2<=q=X^2+(H+1)^2,
H*(1-t)>=X+t^2/2.                                    (3)
```

Thus t<1 and

```text
H>X>1/2,
0<t<1-X/H,
h=(H+1-X)/t>H+1-X.                                  (4)
```

The circulating force rays at this body consequently turn by an acute
angle strictly less than pi/4; one of the two actual inward contact forces
is reversed when measuring this turn. Indeed its outer-side ray is horizontal, and
the other ray has slope magnitude `Y/(X+h)<1`, by (4).

These constraints use containment of the actual S neighbor, regardless
of whether that neighbor has S or V support at the pair. They sharpen
the raw alphabet restriction X<1<Y to Y>X+1.

## 2. The extra inner-boundary corner has a nearly sufficient bound

The inner boundary from A to P passes through B. Unlike A, the point B
is adjacent to the circle vertex. From H>X and q=X^2+(H+1)^2,

```text
H>(sqrt(2q-1)-1)/2,
|B|^2=X^2+H^2=q-2H-1<q-sqrt(2q-1)
                              <=9/2-2sqrt(2).         (5)
```

For the last inequality the displayed function increases when q>1.
At the target radius, this bound is approximately 1.671573. It is
strictly above the three-square threshold 425/256:

```text
9/2-2sqrt(2)-425/256=727/256-2sqrt(2)>0,
727^2-8*256^2=4241>0.                                (6)
```

Thus (5) alone cannot extend the 83/50 disk-capacity contradiction.
The limiting corner geometry X=H=sqrt(2)-1/2 is not permitted by (3)
when t>0, but the calculation supplies no uniform positive lower bound
on t and hence no uniform improvement sufficient to close this gap.

## 3. A shared-side S neighbor has an exact overlap interval

If the S pair is SS, its neighbor is parallel to C and lies in
`x in [X,X+1]`. Its farthest horizontal coordinate is X+1. Loading fixes
the absolute value of its farthest vertical coordinate to

```text
Z=sqrt(q-(X+1)^2)=sqrt(Y^2-2X-1).                     (7)
```

The farthest absolute coordinate of any unit interval is at least 1/2,
so Z>=1/2. If the farthest coordinate were positive, the neighbor's
vertical interval would be `[Z-1,Z]`, with lower endpoint at least -1/2.
It could not touch C, whose top is `-H<-1/2`. Therefore its negative
farthest coordinate is selected and its interval is `[-Z,1-Z]`.
Moreover Z<Y, and contact requires Z>=H.
Thus the actual shared overlap is

```text
x=X,       -Z<=y<=-H,
0<=t<=Z-H,
(Z-H)*(Z+H)=2(H-X)>0.                                (8)
```

In particular its inner endpoint is B, and

```text
t<=Z-H=2(H-X)/(Z+H)<(H-X)/H.                         (9)
```

The strict inequality uses Z>H from (4). In the stronger generic
selection, if the opposite V pair is VV, its other SS aggregate point
is in the relative interior of this segment, so both inequalities
`0<t<Z-H` are strict.

Unlike an inner-side SS pair, this pair's geometric inner endpoint B is
not the source body's opposite corner A. This is precisely the extra
corner not covered by the previous core-hull argument. All formulas above
are necessary restrictions, not realizability or exclusion assertions.
