# A hand bound for the radial extreme of a loaded-ring spike cap

**Status:** hand proof; independent full mathematical review passed on
2026-10-29. Together with the
[chord-endpoint bound](SEVEN_RING_CAP_CHORD_BOUND.md), this closes the
remaining radial-extreme branch of the local diameter-disk cap problem.
No numerical or interval certificate is used below.

Use the spike notation and incoming-neighbor condition `X>=1` from
[SEVEN_RING_SPIKE_REDUCTION.md](SEVEN_RING_SPIKE_REDUCTION.md) and
[SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md). Fix

```text
q=X^2+Y^2,       6241/1600<=q<=9/2,
X>=1,           Y>=1/2,
a=X-1>=0,       H=Y-1>=-1/2.
```

In particular, `H<1` because `Y^2<=q-1<=7/2<4`.
For an angle `d in (0,pi/2)`, write `c=cos(d)`, `s=sin(d)` and put

```text
L=sqrt(q-(s-H)^2),
t=L-a-c,        p=a+t=L-c,
A=(a,-H),       P=(p,-H),       B=(p-s,c-H).             (1)
```

The circle vertex of the first loaded square is `(a+1,-H-1)`; that of
the second is `P+(c,s)=(L,s-H)`. Thus (1) is precisely their equal-radius
condition. In the physical contact pattern, `0<t<1`.

Let `u'=(c,s)`, `v'=(-s,c)` be the second square's frame, and define

```text
x=P dot u'=pc-Hs,
Z=-P dot v'=ps+Hc.                                     (2)
```

Here the second loaded circle vertex has own coordinates `(x+1,-Z)`;
physically `Z>1/2`. In its frame the two diameter endpoints are

```text
A=(x-h,k-Z),      B=(x,1-Z),
h=tc,            k=ts.
```

Let `m=(A+B)/2`, `r=|A-B|/2`, and let

```text
F=m+r m/|m|                                             (3)
```

be the point of the diameter disk farthest from the original origin.
The proof below also shows that `m!=0` in the relevant parameter domain.
The half-plane through the second square's inner side is

```text
z dot u'<=x.                                           (4)
```

**Theorem.** For every physical pair in this pattern, if `F` belongs to
(4), then `|F|^2<33/20`.

## 1. Three useful identities and bounds

Subtracting the two equal squared radii gives

```text
H(1+s)=a(c+t-1)+ct-(1-t^2)/2.                           (5)
```

Consequently, with `r0=c/(1+s)`,

```text
Z=p-r0(1-t)[a+(1+t)/2]<=p                              (6)
```

whenever `a>=0` and `0<=t<=1`.

On the same domain one always has

```text
p^2<=q-1<=7/2<4,             hence p<2.                 (7)
```

If `H>=0`, use `p=a+t<=a+1` and
`q=(a+1)^2+(H+1)^2>=(a+1)^2+1`.
If `H<=0`, use
`q=(p+c)^2+(s-H)^2>=(p+c)^2+s^2>=p^2+1`.
Here `p>=0` in both cases.

The first coordinate of `m` in the second frame is

```text
m_x=x-h/2=(a+t/2)c-Hs.
```

Using (5), it satisfies

```text
(1+s)m_x
 =a[c+s(1-t)]+ct(1-s)/2+s(1-t^2)/2>0.                 (8)
```

The strict sign is immediate when `t>0`, since `c>0` and `s<1`.
When `t=0`, a zero right side would force `a=s=0`; equation (5)
would then give `H=-1/2` and `q=5/4`, outside the stipulated window.
Thus (8) holds throughout the auxiliary domain

```text
0<=d<pi/2,       0<=t(d)<=1,       Z(d)>=0.              (9)
```

In particular `m!=0`, and (3) is well defined there. Also
`1-k=1-ts>0`, so the diameter length is positive.

## 2. The farthest norm decreases with the contact angle

Keep `a,H,q` fixed and differentiate with respect to `d`.
The radicand defining `L` stays positive on `[0,pi/2)`: since
`-1/2<=H<1`, one has `|s-H|<=3/2`, while `q>13/4>9/4`.
Direct differentiation of (1) gives

```text
t'=s+(H-s)c/L=Z/L=:gamma.
```

In the auxiliary domain (9), equations (6)--(7) give

```text
0<=gamma<=p/(p+c)<1.                                  (10)
```

Since `B'=(t'-c,-s)` in the first frame, in the second frame it is

```text
B'=(c gamma-1,-s gamma).                              (11)
```

Set `E=F-A`. Equation (8) and (3) show

```text
E_x>h/2>=0.                                           (12)
```

Indeed `F_x=m_x(1+r/|m|)>m_x`, while `A_x=m_x-h/2`.
The diameter-circle identity is

```text
|E|^2=E dot (B-A)=h E_x+(1-k)E_y.                      (13)
```

If `E_y<0`, let `u=-E_y/E_x>0`. From (12)--(13),

```text
E_x(1+u^2)=h-(1-k)u,
h u^2+2(1-k)u-h<0.
```

This case has `h>0`; when `h=0`, (13) instead forces `E_y>=0`.
It follows that, in all cases,

```text
E_y>=-rho E_x,
rho=h/[sqrt(h^2+(1-k)^2)+1-k].                         (14)
```

The ratio `h/(1-k)=tc/(1-ts)` increases with `t` on `[0,1]`.
So does the function `v/(sqrt(1+v^2)+1)` for `v>=0`. Therefore

```text
rho<=rho_1=c/[sqrt(2(1-s))+1-s],
c+s rho<=1+c/2.                                       (15)
```

For completeness, the final inequality has a short hand proof.
Put `u=sqrt((1-s)/2)`, so `c=2u sqrt(1-u^2)` and
`rho_1=sqrt(1-u^2)/(1+u)`. Then

```text
c/2+s rho_1
 =sqrt(1-u^2) (1+u-u^2)/(1+u)<=1.
```

Using (10)--(15),

```text
E dot B'
 <=E_x[-1+gamma(c+s rho)]
 <=E_x[-1+p(1+c/2)/(p+c)]
 = E_x c(p-2)/[2(p+c)]<0.                             (16)
```

This bounds the whole diameter disk's farthest point; no half-plane
assumption has been used in this derivative calculation.
Since `A` is fixed, differentiation of its diameter disk gives

```text
d(|m|+r)/dd = (E dot B')/(2r)<0.                       (17)
```

Thus `|F|=|m|+r` strictly decreases on every interval satisfying (9).

## 3. The farthest point starts outside the retained half-plane

Fix the physical final angle `d_f`. Take the connected component containing
`d_f` of the closed subset of `[0,d_f]` defined by
`0<=t(d)<=1` and `Z(d)>=0`. By connectedness it is an interval
`[d_0,d_f]`; the strict physical final inequalities ensure positive length. At a positive left endpoint,
one of `t=0`, `t=1`, or `Z=0` holds. The possibility `t=1` cannot give a
left endpoint: (5) then gives `H=(a+1)c/(1+s)>0`, so `Z>0` and `t'>0`.
Immediately to its right, `t` would exceed one.

We show that `F` is strictly outside (4) at each remaining possible left
endpoint. A useful necessary and sufficient form of (4), obtained by
squaring `r m_x/|m|<=h/2`, is

```text
(1-k)m_x<=h |m_y|,
m_y=(1+k)/2-Z.                                       (18)
```

All quantities whose signs are used in this squaring are nonnegative,
and `m_x>0` by (8).

If `t=0`, then `h=k=0`, so (18) is impossible.

If `d_0=0`, membership in (9) gives `Z=H>=0`. Also `H<1`, and (18)
becomes

```text
a+t/2<=t |1/2-H|<=t/2.
```

It forces `a=0`. If `t=0`, (8) is contradicted; otherwise equality
requires `H=0` or `H=1`. The latter is excluded already, and the former
would give `q=2`, outside the radius window. Thus (18) fails.

Finally suppose `Z=0`. Then `H=-ps/c<=0`, and

```text
x=p/c,        m_y=(1+k)/2.
```

Since `q>13/4` and `Y=H+1<=1`, one has `a>1/2`.
If (18) held, it would give

```text
x(1-k)<=h,
p<=t c^2+pt s,
a=p-t<=ts(p-s)<=tsp<=c/2<=1/2.
```

For the penultimate inequality, use
`H=-ps/c>=-1/2` and `t<=1`. This contradicts `a>1/2`.
Consequently `F` starts strictly outside (4).

## 4. Entry occurs at the already bounded chord endpoint

If `F` belongs to (4) at the physical final angle, continuity gives a first
entry angle `d_* in (d_0,d_f]`. There `F` belongs both to the diameter
circle and to the line through `[P,B]`. These intersect at `B` and at

```text
V=P+t s(-s,c),                                        (19)
```

the orthogonal projection of `A` onto that line.

The option `F=B` is impossible even in the auxiliary domain. To see this,
`F=B` implies

```text
B=sigma(B-A),       A=(sigma-1)(t-s,c),       sigma>0.
```

If `H>0`, the second coordinate of `A` forces `sigma<1`. But
`|s-H|<1` and `q>13/4` give

```text
L>3/2>sqrt(2)>=c+s,
B_x=L-c-s>0.
```

Thus `t-s=B_x/sigma>0`, and the first coordinate of `A` would be
negative, contradicting `a>=0`. If `H=0`, then `sigma=1`, hence
`A=0` and `q=2`, also impossible.

If `H<0`, then `sigma>1` and

```text
a=(-H)(t-s)/c<=(-H)(1-s)/c
 =(-H)c/(1+s)<=-H<=1/2.
```

But `Y<1` and `q>13/4` again give `a>1/2`. This excludes `F=B`.

Therefore `F(d_*)=V(d_*)`. The chord-endpoint theorem applies at this
auxiliary angle: its hypotheses require only the first square's
`X>=1,Y>=1/2`, the equal-radius equation, and `0<=t<=1`.
It does not require the second square's farthest-coordinate signs at the
auxiliary angle. It yields

```text
|F(d_*)|^2=|V(d_*)|^2<33/20.
```

Monotonicity (17) on `[d_*,d_f]` gives the same strict bound at the physical
final angle. This proves the theorem.

The complete cap combines this radial-extreme theorem with the two chord
endpoints. In the physical pair, the endpoint `B` is an opposite corner
and has squared norm below `36/25`; the endpoint `V` is bounded by the
cited chord theorem. Every vertex of an inner square in the spike therefore
lies below squared radius `33/20`. The full packing consequence also uses
the polygon/diameter-disk reductions and the established three-square
optimum; it is not a statement about arbitrary loaded-ring ownership.

## 5. Hand exclusion of the complete one-chirality seven-ring

**Corollary.** A physical positive-stress seven-ring with the fixed
side/vertex ownership of
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md) cannot enclose
three further interior-disjoint unit squares in the working radius window.

For each pair of neighboring loaded squares, intersect the diameter disk
`AB` with the retained half-plane (4). The maximum norm in this compact cap
occurs at `B`, `V`, or its unconstrained radial maximum `F` if `F` is in
the cap. On the straight boundary segment, convexity of the norm leaves
only its endpoints; on the circular arc, the only possible interior
maximum is `F`. The three branches have now been bounded by hand:

```text
|B|^2<36/25<33/20,
|V|^2<33/20,
|F|^2<33/20 when F belongs to the retained half-plane.
```

Let `z` be a vertex of one of the three inner unit squares. The polygon
reduction in Section 2 of
[SEVEN_RING_SPIKE_REDUCTION.md](SEVEN_RING_SPIKE_REDUCTION.md) puts `z`
either in the convex hull of the opposite loaded corners or in a contact
spike. In the first case, the opposite-corner bound and convexity give
`|z|^2<36/25`. In the second, the diameter-disk cut in Section 5 of that
note puts `z` in the cap just bounded, so `|z|^2<33/20`.

All four vertices of every inner square therefore belong to the centered
disk of squared radius `33/20`; convexity places each whole square there.
The established three-square optimum has squared radius `425/256`, and

```text
425/256-33/20=13/1280>0.
```

This is impossible for three interior-disjoint unit squares. The same
three-square theorem and its repository source are recorded in
[SEVEN_RING_CORNER_MOMENT_CAPACITY.md](SEVEN_RING_CORNER_MOMENT_CAPACITY.md),
Section 3.

Thus this contact pattern is excluded by a hand geometric proof, with no
use of the global angle-action interval verifier. The proof does not show
that all possible loaded rings have this ownership. That classification
and the other remaining branches of the unrestricted ten-square problem
are separate open tasks.
