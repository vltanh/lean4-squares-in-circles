# Two interior stabbing points for the upper cap

**Status: proved by hand.** The horizontal-face estimate used below is
proved in the linked companion note by two explicit positive polynomial
identities. No numerical or interval-search premise is used.

Let

```text
P=(a,b)=(27/64,255/256),
Q=(−a,d)=(−27/64,5/4),
R=sqrt(17)/2.
```

Every unit square contained in the closed disk
`|z|<=R` and wholly in `y>=1/2` contains `P` or `Q` in its open interior.
Square orientations are unrestricted.

## 1. Coordinates and the six complement regions

Choose square axes

```text
u=(c,s), v=(−s,c), c=cos(theta), s=sin(theta),
−pi/4<=theta<=pi/4.
```

Write its center as `A u+B v`. The cap condition and disk condition are

```text
sA+cB >= (1+c+|s|)/2,                            (1)
(|A|+1/2)²+(|B|+1/2)² <= 17/4.                 (2)
```

They imply `|A|,|B|<=3/2` and center norm at most `3/2`. They also imply
`B>0`: otherwise `sA+cB<=3|s|/2`, while
`1+c>2|s|` makes (1) strictly larger.

The point coordinates in this frame are

```text
Pu=ac+bs,       Pv=−as+bc,
Qu=−ac+ds,      Qv=as+dc.
```

Always `Pu>Qu`, since `2a>d−b` and `c>=|s|`. Put

```text
alpha=atan((d−b)/(2a))=atan(65/216).
```

Then `Pv<=Qv` exactly when `theta>=−alpha`.

The open translation rectangles corresponding to containment of `P` and
`Q` overlap in both coordinates, since `|P−Q|<1`. If neither point is in
the square's interior, its center belongs to one of the following closed
regions:

* one of the four outer regions
  `A>=Pu+1/2`, `A<=Qu−1/2`,
  `B>=max(Pv,Qv)+1/2`, `B<=min(Pv,Qv)−1/2`;
* if `theta>=−alpha`, one of the two corner regions
  `A>=Qu+1/2, B>=Pv+1/2` or
  `A<=Pu−1/2, B<=Qv−1/2`;
* if `theta<=−alpha`, one of the two corner regions
  `A<=Pu−1/2, B>=Qv+1/2` or
  `A>=Qu+1/2, B<=Pv−1/2`.

This is simply the complement of two overlapping axis-parallel open
rectangles. The following sections exclude these possibilities.

## 2. The two vertical outer regions

First, `max(Pv,Qv)>1` for every allowed angle. If `theta>=0`, the concave
function `Qv=a sin(theta)+d cos(theta)` has minimum at an endpoint of
`[0,pi/4]`; both endpoint values exceed one. If `theta=−phi<=0` and
`phi<=pi/12`, then

```text
Qv=d cos(phi)−a sin(phi)
   > d(19/20)−a/3 = 67/64 > 1.
```

For `pi/12<=phi<=pi/4`, the positive concave function
`Pv=a sin(phi)+b cos(phi)` again has its minimum at an endpoint. At
`pi/12`, use `sin(pi/12)>1/4` and `cos(pi/12)>19/20`; at `pi/4`, use

```text
Pv=363/(256 sqrt(2))>1,
363²>2(256)².
```

Thus `B>=max(Pv,Qv)+1/2` contradicts `B<=3/2`.

For the lower outer region, first let `theta>0`. Since `Pv<=Qv`, the
condition `B<=Pv−1/2` and (1) imply

```text
s(A−1/2) >= 1/2+c+a cs−b c² > s.
```

The strict inequality follows from

```text
1/2+c−c²−s = (c−s)(1−(c+s)/2) >= 0
```

and `(1−b)c²+a cs>0`. It forces `A>3/2`, a contradiction.

For `theta=−phi<0`, put `t=sin(phi)>0`, `c=cos(phi)`. Since
`min(Pv,Qv)<=Qv`, the same lower-region condition implies
`B<=Qv−1/2`, and (1) gives

```text
−t(A+1/2) >= 1/2+c+a ct−d c² > t.
```

For the final strict inequality, set `w=t/c` in `[0,1]`. Its difference,
divided by `c²`, is at least

```text
1/4 + w²/2 − (1−a)w > 0.
```

Indeed, `(1−w)/c>=1−w`, and the displayed quadratic has negative
discriminant because `(1−a)²=(37/64)²<1/2`. This forces `A<−3/2`.
At `theta=0`, the cap requires `B>=1`, whereas the lower-region condition
requires `B<=b−1/2<1`. The vertical outer cases are all excluded.

## 3. The two horizontal outer regions

The needed inequalities are

```text
A < Pu+1/2,             A > Qu−1/2.              (3)
```

Both are proved, with the same constants and signed-angle convention, in
[ONE_NECK_CAP_SIDE_FACES.md](ONE_NECK_CAP_SIDE_FACES.md). That proof bounds
the norm of a vertex using the cap half-plane and the violated side-face
half-plane. The two required degree-six numerator polynomials are expressed
as positive linear combinations of
`binomial(6,i)(2z)^i(1−2z)^(6−i)` on `0<=z<=1/2`, so both inequalities
are strict throughout the full orientation interval. This excludes the
two horizontal outer regions.

## 4. The upper-right corner region

We exclude `A>=Qu+1/2, B>=Pv+1/2` for every angle, which is stronger than
needed in the six-region decomposition.

Suppose first that `theta>=0`. Both lower coordinate bounds are positive.
An opposite vertex therefore has squared norm at least

```text
F=(1−ac+ds)²+(1−as+bc)².
```

With `z=tan(theta/2)` in `[0,sqrt(2)−1]`, direct expansion gives

```text
65536(1+z²)²(F−17/4)
 = N(z)
 = 4497−31312z+7966z²+465488z³−146031z⁴.
```

Since `z<1/2`, the coefficient `465488−146031z` is greater than
`375744=12(31312)`. Moreover

```text
z³−z/12+1/108 = (z−1/6)²(z+1/3) >= 0.
```

Consequently `N(z)>=4497−31312/9=9161/9>0`, contradicting (2).

If `theta=−phi<=0`, put `z=tan(phi/2)`. The concave function
`Pv=a sin(phi)+b cos(phi)` is at least `b` throughout `[0,pi/4]`.
For `z>=1/128`, it is in fact greater than one: the numerator of `Pv−1`
is, up to the positive factor `256(1+z²)`,

```text
−511z²+216z−1.
```

This concave polynomial is positive at both endpoints of
`[1/128,sqrt(2)−1]`. At the first endpoint this is direct rational
arithmetic; at the second it is `363/(256 sqrt(2))>1` as above.
Then `B>3/2`, impossible.

For `0<=z<=1/128`, we have `sin(phi)<=1/64` and

```text
Qu>=−a−d/64=−113/256,
A>=15/256,            B>=b+1/2=383/256.
```

The opposite vertex has squared norm at least

```text
(143²+511²)/65536=281570/65536>17/4.
```

This finishes the upper-right corner case.

## 5. The lower-left corner when theta>=−alpha

Suppose `A<=Pu−1/2` and `B<=Qv−1/2`. For `theta>=0`, substituting these
upper bounds into (1) would require

```text
1/2+c+s <= 2a cs+b s²+d c²
          <= d+a((c+s)²−1).
```

This is impossible. Set `w=c+s` in `[1,sqrt(2)]`; the difference of
right and left sides is the convex quadratic

```text
a w²−w+(d−a−1/2).
```

Its values at both interval endpoints are negative: at `1` it is `−1/4`,
and at `sqrt(2)` it is `3/4+a−sqrt(2)<0`.

It remains to consider `theta=−phi` with `0<=phi<=alpha`. Put
`t=sin(phi)`, `c=cos(phi)`, `X=−A+1/2`, and `Y=B+1/2`. Here `A<0`,
so `(X,Y)` is a far-vertex coordinate pair and `X<=R`. The hypotheses give

```text
tX+cY >= 1/2+t+c,
Y <= dc−at.
```

From `tan(phi)<=65/216` one checks `c>=19/20` and `t<=3/10`.
Using also `R<33/16`, the right side of the necessary inequality
`Rt+dc²−act>=1/2+t+c` minus its left target is at most

```text
d−1/2−19/20 + (3/10)(33/16−1−a(19/20))
 = −19/12800 < 0.
```

This contradiction excludes the whole lower-left corner case.

## 6. The two remaining corners when theta<=−alpha

Write `theta=−phi`, with `alpha<=phi<=pi/4`, and again put
`t=sin(phi)`, `c=cos(phi)`, `X=−A+1/2`, `Y=B+1/2`.

For `A>=Qu+1/2, B<=Pv−1/2`, we have

```text
X<=ac+dt,              Y<=at+bc.
```

Together with the cap condition, this would give

```text
1/2+t+c <= 2a ct+d t²+b c²
          <= d+a((c+t)²−1).
```

The same convex-quadratic calculation as in Section 5 excludes it.

Finally suppose `A<=Pu−1/2, B>=Qv+1/2`. Then `A<0`, `B>0`, and the
far vertex satisfies

```text
X>=1−ac+bt,       Y>=1−at+dc,
X+Y>=2+(b−a)t+(d−a)c > 47/16.                   (4)
```

For the last strict inequality, note that `sin(alpha)>1/4`, directly
from `tan(alpha)=65/216`. The function
`(b−a)sin(phi)+(d−a)cos(phi)` is positive and concave on
`[asin(1/4),pi/4]`, so its minimum is at an endpoint. At the first
endpoint its value is

```text
(147+212 sqrt(15))/1024 > 15/16,
```

using `sqrt(15)>27/7`. At the second it is
`359/(256 sqrt(2))>15/16`, using `sqrt(2)<10/7`.
This proves (4). Consequently

```text
X²+Y² >= (X+Y)²/2 > 2209/512 > 17/4,
```

contradicting disk containment and completing the adjacent-face cases.

Every region in Section 1 has now been excluded. Thus the square contains
at least one of `P,Q` in its open interior, proving the lemma.

## A symmetric three-point corollary

Every square satisfying the same cap and disk hypotheses contains an
interior point from

```text
P+=(27/64,255/256),
P−=(−27/64,255/256),
O=(0,5/4).
```

Indeed, if it misses the interiors of both `P+` and `P−`, the proved
two-point lemma forces `Q−=(−27/64,5/4)` into its interior. Applying the
horizontally reflected lemma forces `Q+=(27/64,5/4)` into its interior.
The interior of a square is convex, so it contains their midpoint `O`.
This corollary concerns squares wholly above `y=1/2`; extending it to the
original upper region requires a separate argument for lower squares.
