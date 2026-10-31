# A hand spike-cap bound for a body supported on both inner sides

**Status:** hand proof; two independent full mathematical reviews passed
on 2026-10-29, including the negative-offset case and side endpoints.
This extends the local cap estimate used for a one-chirality ring to a
unique-circle body whose two contact support faces are its adjacent inner
sides. It is a local theorem, not an exclusion of all loaded-ring types.

Use the working window `6241/1600<=q=R^2<=9/2`. The first loaded square is

```text
C=[X-1,X] x [-Y,1-Y],       w=(X,-Y),       X,Y>1/2,
X^2+Y^2=q.
```

Its two force supports are the left and top sides. The concurrence
parameter and physical application points are those of
[LOADED_DOUBLE_SIDE_RESTRICTION.md](LOADED_DOUBLE_SIDE_RESTRICTION.md):

```text
Q=(X-1,-eta*Y),       P=(eta*X,1-Y),       0<eta<=1.
```

The next loaded square has a strict vertex support at P, with its unique
circle vertex adjacent to P along `u'=(cos d,sin d)`. Its other frame
vector is `v'=(-sin d,cos d)`, and `0<d<pi/2`. Thus its opposite corner
is `B=P+v'`. Put

```text
a=X-1, H=Y-1, p=eta*X, t=p-a,
A=(a,-H), P=(p,-H), B=(p-s,c-H),
c=cos d, s=sin d.
```

The two circle vertices are `(a+1,-H-1)` and `P+(c,s)`. Their equal
squared radii determine

```text
p=sqrt(q-(s-H)^2)-c,       0<=t<=1.                  (1)
```

Let K be the closed disk with diameter `[A,B]`, intersected with the
half-plane `z dot u'<=P dot u'` on the inner side of the next square.

**Theorem.** If `X<1`, every point of K has squared norm strictly less
than `83/50`. If `X>=1`, every point of K has squared norm strictly less
than `33/20`, including the possible side endpoint.
Both bounds are strictly below `425/256`, since

```text
425/256-83/50=1/6400>0.
```

Only the first square's two physical neighbors are used to obtain the
additional hypotheses needed when `X<1`.

## 1. Uniform bounds in the new range X<1

Assume `X<1`. The reviewed double-side restriction gives `X>7/8`.
The radius window gives `Y>17/10`, so

```text
-1/8<a<0,       H>7/10.
```

From the equal-radius equation,

```text
p^2+2pc-2Hs=X^2+2H.                                 (2)
```

Because `p=eta X<=X`, equation (2) implies

```text
Xc>=H(1+s).
```

In particular `0<H<X<1`. Moreover

```text
c/(1+s)>=H/X>7/10,
s<51/149<2/5,       c>9/10.                          (3)
```

The middle inequality follows by squaring
`c/(1+s)=sqrt((1-s)/(1+s))`.

Keep X,H,q fixed and vary the contact angle from zero to its physical
value `d_f`. Define p and t by (1), and put

```text
p_0=p(0)=sqrt(X^2+2H+1)-1.
```

The radical stays positive. In fact
`q-(s-H)^2-c^2=X^2+2H(1+s)>0`, so p is positive. Differentiation gives

```text
p'=t'=(ps+Hc)/(p+c)>0.                              (4)
```

Thus `p_0<=p<=p(d_f)<=X`, and `t<=1` throughout this interval.
Also

```text
X^2+2H+1 >49/64+7/5+1>49/16,
p>=p_0>3/4,       t=p-a>3/4.                        (5)
```

All of (3)--(5) therefore hold on the complete auxiliary angle interval,
not just at the final physical pair.

## 2. The zero-angle chord endpoint has squared norm below 83/50

The incoming neighbor at Q contains the point `(X-2,-eta Y)`, by the
unit-normal-step lemma. Its disk containment gives

```text
p(d_f)^2<=X^2-4X^2(1-X)/(H+1)^2.
```

Since p increases with d, the same upper bound holds for `p_0^2`.
Using `p_0^2+2p_0=X^2+2H`, this implies

```text
p_0-H >= 2X^2(1-X)/(H+1)^2.                         (6)
```

Suppose `p_0^2+H^2>=83/50`. The identity

```text
q=p_0^2+H^2+2p_0+1<=9/2
```

gives `p_0<=23/25`. Consequently

```text
H^2>=83/50-(23/25)^2=1017/1250>(9/10)^2,
X^2=p_0^2+2p_0-2H<554/625<(33/35)^2.
```

The last rational comparison has cross-product difference `1975>0`.
It follows that

```text
p_0-H<23/25-9/10=1/50.
```

On the other hand, `X>7/8`, `X<33/35`, and `H<1` give

```text
2X^2(1-X)/(H+1)^2
 > 2(7/8)^2(2/35)/4=49/2240>1/50.
```

This contradicts (6). Therefore

```text
p_0^2+H^2<83/50.                                    (7)
```

The final strict rational gap in the contradiction is
`49/2240-1/50=3/1600`.

## 3. The moving chord endpoint decreases in norm

The line through P,B meets the diameter circle at B and at

```text
V=P+ts v'=(a+tc^2,-H+tsc).
```

The algebraic derivative identity from Section 3 of
[SEVEN_RING_CAP_CHORD_BOUND.md](SEVEN_RING_CAP_CHORD_BOUND.md) is

```text
(p+c)/2 * d|V|^2/dd
 =-sc^2(H^2+ap)-E[sc(2a+t)+H(c^2-s^2)],
E=tp-ac.                                            (8)
```

The identity does not require a to be nonnegative. Here every sign
needed for a strict negative derivative follows from Section 1:

```text
H^2+ap>49/100-1/8>0,
E>0,
2a+t=a+p>-1/8+3/4>0,
c^2-s^2>1-2(2/5)^2>0.
```

Thus `|V|^2` strictly decreases, including at d=0 where the second term
of (8) is strictly negative. Equations (7)--(8) give

```text
|V(d)|^2<=|V(0)|^2=p_0^2+H^2<83/50.                 (9)
```

The other chord endpoint is uniformly small in the auxiliary interval:
`0<p-s<1`, and `0<c-H<3/10`. The latter lower bound follows from
`H<=Xc/(1+s)<c`. Therefore

```text
|B(d)|^2<109/100<83/50.                             (10)
```

No auxiliary farthest-vertex signs of the second square are being assumed
in (9)--(10).

## 4. The diameter disk's farthest point decreases in norm

Let `m=(A+B)/2`, `r=|A-B|/2`, and
`F=m+r*m/|m|`. Work in the moving second-square frame `(u',v')` and put

```text
Z=ps+Hc, h=tc, k=ts,
m_x=(a+t/2)c-Hs, m_y=(1+k)/2-Z.
```

The equal-radius identities used in
[SEVEN_RING_RADIAL_CAP_BOUND.md](SEVEN_RING_RADIAL_CAP_BOUND.md) still
hold algebraically when a is negative:

```text
Z=p-[c/(1+s)](1-t)[a+(1+t)/2]<=p,
(1+s)m_x
 =a[c+s(1-t)]+ct(1-s)/2+s(1-t^2)/2.
```

The first bracket is positive by `a>-1/8` and `t>3/4`.
For the second identity use (3)--(5):

```text
(1+s)m_x > -7/40+81/400=11/400>0.                   (11)
```

Indeed the negative term is greater than `-(1/8)(1+2/5)`, the middle
term exceeds `(9/10)(3/4)(3/5)/2`, and the last term is nonnegative.
Thus m is nonzero, and the farthest point is well defined.

The derivative proof in Section 2 of the radial-cap note now applies
without change: it uses `m_x>0`, `0<=t<=1`, `0<Z<=p`, and `p<2`.
To record the precise inequality, with `E_F=F-A` it gives

```text
E_F dot B' <= (E_F)_x c(p-2)/(2(p+c))<0,
d(|m|+r)/dd=(E_F dot B')/(2r)<0.                     (12)
```

These hypotheses hold here by (3)--(5) and (11). The diameter length
is nonzero because `1-ts>3/5`. This proves strict decrease of `|F|` on
the entire auxiliary interval.

## 5. The farthest point starts outside the retained half-plane

The retained half-plane is `z dot u'<=P dot u'`. At d=0 its condition
for the diameter disk's farthest point is

```text
a+t_0/2 <= t_0 |1/2-H|=t_0(H-1/2),
```

as follows either directly from F or from equation (18) of the
radial-cap note. It is equivalent to

```text
p_0(1-H)<=(1-X)H.                                   (13)
```

But `X>H` implies `p_0>H` by the definition of p_0. Since `0<H<X<1`,

```text
p_0(1-H)>H(1-H)>H(1-X),
```

contradicting (13). Hence F begins strictly outside the retained
half-plane. If it belongs to that half-plane at the final angle,
continuity supplies a first entry, where F equals B or V. Both have
squared norm below `83/50` by (9)--(10). Strict decrease (12) then
gives the same bound at the final angle.

The maximum norm on the compact disk cap occurs at B, V, or F if F is
retained. This proves the cap theorem for `X<1`.

## 6. The already proved range X>=1, including endpoints

For `X>=1`, `Y>1/2`, and `0<t<1`, the chord and radial-cap theorems give
the stronger bound `33/20`.

The endpoint `t=0` is impossible. The equal-radius identity becomes
`a(1-c)+H(1+s)=-1/2`, while the two unique-farthest-vertex signs are
`H>-1/2` and `Z:=as+Hc>1/2`. But

```text
Z-1/2=-[(1+s+c)/s](H+1/2)<0,
```

a contradiction. This is the same endpoint check used in Section 6 of
[SEVEN_RING_OWNERSHIP_ALPHABET.md](SEVEN_RING_OWNERSHIP_ALPHABET.md).

If `t=1`, then p=X and eta=1. The incoming-neighbor containment inequality
in Section 2 gives `X>=1`. The equal-radius identity gives
`H=Xc/(1+s)>0`, so `Y>1`. The second circle vertex has own coordinates

```text
X'=P dot u'+1=Xc-Hs+1=Y,
Y'=-P dot v'=Xs+Hc=X.
```

Thus its opposite corner has exactly the same squared norm as A. Since
both coordinates X,Y are at least one, the elementary corner calculation
in [LOADED_DIAGONAL_VERTEX_RESTRICTION.md](LOADED_DIAGONAL_VERTEX_RESTRICTION.md)
gives `|A|^2=|B|^2<49/64`. Every point of the full diameter disk AB has
squared norm at most `|A|^2+|B|^2`, by the corner-moment bound. Therefore
its entire cap has squared norm below `49/32<33/20`.

This theorem bounds the cap. To place vertices of an inner square in it
when `t=1`, the diameter-disk cut needs the endpoint extension stated in
[SEVEN_RING_INNER_FACE_CAPACITY.md](SEVEN_RING_INNER_FACE_CAPACITY.md).
