# A small opposite corner for a loaded body with two side supports

**Status:** hand proof; two independent full mathematical reviews passed
on 2026-10-29, including all rational comparisons and the exact local example. This is a local
restriction for another loaded-ring contact type, not a classification of
all ring ownership patterns or an unrestricted ten-square proof.

Consider a unique-circle-vertex loaded body in an entirely loaded positive
ring in the working window `6241/1600<=q=R^2<=9/2`. Suppose its two contact
support faces are the adjacent inner sides. In suitable orthonormal
coordinates write

```
C=[X-1,X] x [-Y,1-Y],
w=(X,-Y),       X,Y>1/2,       X^2+Y^2=q.
```

The two supporting normals into `C` are `(1,0)` and `(0,-1)`. Their
application points may be side endpoints; the assumption concerns the
support faces, rather than requiring geometric side-interior contacts.
The concurrence theorem places their intersection at `eta*w`, with
`eta>0`. Consequently their physical application points are

```
Q=(X-1,-eta*Y),       P=(eta*X,1-Y).                    (1)
```

Both points belong to `C`, hence `eta<=1`. Every physical neighboring
square is contained in `D_R`, and both neighbors have circle vertices.

**Theorem.** The two own-frame circle coordinates satisfy

```
X>7/8,       Y>7/8.                                   (2)
```

Moreover, the opposite corner `A=(X-1,1-Y)` satisfies

```
|A|^2<53/64.                                          (3)
```

Thus two such opposite corners have squared-norm sum below
`53/32<425/256`. The theorem does not assert that every spike is bounded
by two corners of this type.

## 1. A one-sided neighbor bound

Let `P=(x,-H)`, where `x>=0` and `H>=1/2`. Any unit square supported in
`y>=-H` and containing `P` has every vertex `z` bounded by

```
|z|^2<=(x+1)^2+H^2.                                  (4)
```

If `P` is a vertex, choose its incident edges as `(c,s)` and `(-s,c)`,
with `c,s>=0` and `c^2+s^2=1`; reversing their order does not change the
square. Each adjacent vertex has squared norm at most

```
x^2+H^2+1+2x.
```

For the opposite vertex, use

```
x(c-s)-H(c+s)<=x-H
```

to obtain the bound

```
x^2+H^2+2+2x-2H<=x^2+H^2+1+2x.
```

If `P` is in a side interior, that support side is horizontal. The square
is axis-parallel, all vertex absolute horizontal coordinates are at most
`x+1`, and their heights are `-H` or `1-H`, both of absolute value at most
`H`. This proves (4) for that case as well. The point cannot lie in the
square's interior when it is on its supporting line.

## 2. Combining the two physical neighbors

Suppose `X<=1`. The radius window implies `Y>3/2`, so (4) applies to the
neighbor across the top side, with `x=eta*X` and `H=Y-1`. Because this
neighbor has a circle vertex, (4) implies

```
q<=(eta*X+1)^2+(Y-1)^2,
(1-eta^2)X^2-2eta*X+2Y-2<=0.                         (5)
```

The left neighbor has inward supporting normal `(-1,0)` at `Q`. A unit
square contains `Q+n` for any inward supporting unit normal `n` at `Q`;
this elementary fact is proved in
[SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md), Section 4.
Thus it contains `(X-2,-eta*Y)`, and disk containment gives

```
(X-2)^2+eta^2 Y^2<=q,
eta^2<=1-4(1-X)/Y^2.                                 (6)
```

Equivalently, the following exact necessary inequality eliminates `eta`:

```
Y[sqrt(X^2+2Y-1)-1] <= X sqrt(Y^2+4X-4).              (7)
```

The right radical is defined by (6). Both `X,Y` are positive; (5) implies
`eta*X>=sqrt(X^2+2Y-1)-1`, and (6) implies
`eta*Y<=sqrt(Y^2+4X-4)`, proving (7).

The same assertions hold with `X,Y` exchanged, by reflection across the
line `y=-x`, which interchanges the two support faces and their neighbors.

## 3. Proof of the uniform coordinate bound

Assume `X<=7/8`. Then

```
Y^2>=6241/1600-49/64> (177/100)^2,
```

where the last difference is `21/10000`. In particular `Y>177/100`.
For `1/2<X<1`, the function

```
f(X)=4(1-X)/(9/2-X^2)
```

strictly decreases: its derivative has the sign of
`-9/2+2X-X^2<0`. Since `Y^2<=9/2-X^2`, equation (6) yields

```
eta^2<=1-f(X)<=1-f(7/8)=207/239<(14/15)^2.
```

The final difference is `269/53775>0`. Thus `eta<14/15`.
Put `kappa=14/15` and define

```
G(X,Y;kappa)=(1-kappa^2)X^2-2kappa*X+2Y-2.
```

The left side of (5) strictly decreases as `eta` increases. Also
`G` decreases with `X` on `0<X<=7/8` and increases with `Y`. Therefore
that left side is strictly greater than

```
G(7/8,177/100;14/15)=77/14400>0,
```

contradicting (5). This proves `X>7/8`; reflection proves `Y>7/8`.

## 4. Proof of the opposite-corner bound

Suppose, for a contradiction, that

```
(X-1)^2+(Y-1)^2>=53/64.
```

By the reflection symmetry, assume `X<=Y`. If `X>=1`, both coordinates
are at least one. On a circle `X^2+Y^2=q`, this implies
`X+Y>=1+sqrt(q-1)`, and hence

```
|A|^2=q+2-2(X+Y)<=q-2sqrt(q-1)
 <=9/2-sqrt(14)<53/64.
```

The function increases in this radius window. The last strict comparison
follows from `14*64^2-235^2=2119>0`. Thus necessarily `X<1`.
Since `X>7/8`, one has `(1-X)^2<1/64`. It follows that

```
(Y-1)^2>52/64=13/16>(9/10)^2.
```

The radius window and `X<=Y` ensure `Y>1`; thus `Y>19/10`.
Then `X^2<=9/2-Y^2<89/100<(19/20)^2`, so `X<19/20`.

Apply (6) again, using the same decreasing function `f`:

```
eta^2<=1-f(X)<1-f(19/20)=1359/1439<(243/250)^2.
```

The last difference is `34011/89937500>0`. Put `kappa=243/250`.
The function `G` from Section 3 decreases with `X` on `0<X<=19/20`
and increases with `Y`. Since `eta<kappa`, the left side of (5) is
strictly greater than

```
G(19/20,19/10;243/250)=75811/25000000>0,
```

again contradicting (5). This proves (3).
The comparison `53/32<425/256` is the exact inequality `424<425`.

## 5. The stronger bound X>1 cannot be inferred locally for this type

The incoming-vertex argument of
[SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md) proves `X>1`
for the one-chirality pattern. The following exact local configuration
shows that this conclusion does not follow merely from a two-side body's
positive radial concurrence and two geometrically loaded neighbors.

Put

```
q=9/2,
X=19/20,       Y=sqrt(1439)/20,
B=sqrt(1359)/20,
T=sqrt(X^2+2Y-1)-1,
eta=1943/2000.
```

Take three axis-parallel unit squares

```
C =[X-1,X]   x [-Y,1-Y],
C_L=[X-2,X-1] x [-B,1-B],
C_T=[T,T+1]   x [1-Y,2-Y].
```

Each has a unique circle vertex at squared radius `q`: respectively
`(X,-Y)`, `(X-2,-B)`, and `(T+1,1-Y)`. The relevant intervals have fixed
signs (`B,Y>3/2`, `0<T<X<1`), so these are indeed their farthest vertices.
The interiors are disjoint: `C_L` lies immediately to the left of `C`,
`C_T` lies immediately above `C`, and `C_L,C_T` have disjoint horizontal
projections.

The points in (1) belong to the relative interiors of the corresponding
shared side segments. For exact checks, `Y<1897/1000` follows from
`(1897/1000)^2-Y^2=1109/1000000>0`, and

```
(eta*X+1)^2-[X^2+2(1897/1000)-1]
 =1824889/1600000000>0,
B^2-eta^2Y^2=3416689/1600000000>0.
```

Thus `T<eta*X<X` and `eta*Y<B<Y`. Also `(1-eta)Y<1`.
These inequalities verify the claimed strict side-interior memberships.

Apply to `C` the inward contact force `(X,0)` at `Q`, the inward contact
force `(0,-Y)` at `P`, and the inward radial circle force `(-X,Y)` at
`w`. They balance. The two contact torques are `eta*X*Y` and
`-eta*X*Y`, and their force lines concur at `eta*w` inside `C`.
Nevertheless `X=19/20<1`.

This is only a local example. The two neighboring bodies have not been
given balanced positive stresses, and no complete seven-ring or ten-square
packing is asserted. It prevents extending the one-chirality `X>1` lemma
to this support type without a new global argument.
