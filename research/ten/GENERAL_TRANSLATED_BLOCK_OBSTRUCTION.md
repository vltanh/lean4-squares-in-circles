# Every translated solid two-by-two core admits at most five more squares

Let four unit squares tile a solid square of side two, and suppose their
four centres lie in the closed unit disk. Then at most five additional
unit squares, with arbitrary independent orientations and pairwise
disjoint interiors, can lie outside the core in the origin-centred disk
`D` of squared radius `9/2`.

This is a hand theorem for every translation and rotation of the solid
block. It removes both the single-coordinate translation assumption in
[TRANSLATED_BLOCK_OBSTRUCTION.md](TRANSLATED_BLOCK_OBSTRUCTION.md) and the
radial-count hypothesis in
[LOCALIZED_BLOCK_OBSTRUCTION.md](LOCALIZED_BLOCK_OBSTRUCTION.md).
Its proof uses the hand cap lemmas
[THREE_SQUARE_CAP.md](THREE_SQUARE_CAP.md) and
[SEVEN_EIGHTHS_CAP_STABBING.md](SEVEN_EIGHTHS_CAP_STABBING.md), and no
computer-assisted count certificate. It still assumes an exact solid
block; arbitrary four-square cores are not reduced to this form here.

## 1. Coordinates and moving an oblique separator into contact

Rotate and reflect coordinates so that the core is

```text
K=[s-1,s+1] x [t-1,t+1],     0<=t<=s.
```

The four core centres have norm at most one precisely when

```text
s²+t²+s+t<=1/2.                                  (1)
```

In particular `s<=(sqrt(3)-1)/2<2/5`, `t<1/4`, and every absolute
coordinate of a corner of `K` exceeds `3/5`.

Every unit-square centre `p` in `D` has

```text
|p|<25/16,                                        (2)
```

because its farthest squared vertex norm is at least
`|p|²+|p|+1/2`, and that expression at `|p|=25/16` is `1153/256>9/2`.

Let `S` be an additional square. The separating-axis theorem for two
rectangles says that an edge-normal of `K` or of `S` weakly separates
them. If a coordinate axis separates them, `S` lies wholly beyond one
side of `K`. Otherwise a non-coordinate edge-normal `n` of `S` points
outward through a corner `q` of `K`, and

```text
n dot S >= n dot q >= n dot K.
```

Translate `S` inward along `n` until its inner edge lies on the line
through `q`; call the resulting square `S'`. The translation preserves
containment in `D`: if its distance is `d>=0`, every `p'` in `S'` satisfies
`n dot p'>=n dot q>0`, and

```text
|p'+dn|²=|p'|²+2d(n dot p')+d²>=|p'|².
```

The corner `q` belongs to the inner edge segment of `S'`. Indeed, if it
lay beyond an endpoint, the signs of the tangent and outward-normal
components would put all of `S'` beyond one coordinate side of `K`.
Translating outward to `S` preserves that coordinate separation,
contradicting the current case.

Any outward coordinate half-plane containing `S'` also contains `S`.
We can therefore prove such half-plane bounds after moving into contact.

## 2. A general corner bound

Reflect coordinates to write the contact corner and outward normal as

```text
q=(-a,-b), n=(-c,-eta),
a,b>0, c,eta>0, c²+eta²=1.
```

Use tangent `v=(eta,-c)`. Since `q` lies on the inner unit edge, the two
outer-edge vertices have normal projection `n dot q+1`, and their
largest absolute tangent projection is at least `|v dot q|`. Hence the
largest squared vertex norm satisfies

```text
F >= (n dot q+1)²+(v dot q)²
   = a²+b²+2(ac+b eta)+1
   > a²+b²+2 min(a,b)+1.                          (3)
```

The strict inequality uses `c+eta>1`.

If `s<=1/16`, then `t<=1/16`, and all corner coordinates have absolute
value at least `15/16`. Formula (3) would give

```text
F>2(15/16)²+2(15/16)+1=593/128>9/2.
```

So every additional square is coordinate-separated from `K`. Each of
the four side caps begins at distance at least `15/16>7/8` from the
origin. The narrow-cap lemma allows at most one square in each, hence
at most four in total. From now on suppose

```text
s>1/16.                                          (4)
```

No additional square can lie wholly to the right of `K`: its centre
would have `x>=s+3/2>25/16`, contradicting (2).

Oblique separation at either right-hand corner is impossible as well.
At the upper-right corner, (3) gives `F>5`. At the lower-right corner,
`a=1+s` and `b=1-t`, with `a>=b`, so

```text
F>5+2s-4t+s²+t²>=5-2t>9/2.                       (5)
```

Only the two left-hand corners remain.

## 3. Dominant normal components force a coordinate half-cap

We prove a useful general assertion. At a corner `q=(-a,-b)` as above,
suppose the opposite core centre

```text
p=(3/2-a,3/2-b)
```

has norm at most one and `a>1/2`. If `c>=eta`, then the whole contact
square lies in `x<-1/2`. By reflecting or interchanging coordinates, the
same assertion applies to any corner and the outward coordinate of the
larger normal component.

Since `q` belongs to the inner edge, write its rightmost inner vertex as
`q+delta v`, where `0<=delta<=1`, and put

```text
X=a-delta eta,
Y=b-(1-delta)c,
w=c+eta.
```

One outer vertex is `(-(X+c),-(Y+w))`. Suppose, for a contradiction,
that `X<=1/2`. Write the opposite core centre as `(p_x,p_y)`. Then

```text
p_x=3/2-X-delta eta,
Y+w=3/2+eta+(c/eta)(3/2-X)-(c/eta)p_x-p_y.
```

Cauchy's inequality and `|p|<=1` give

```text
Y+w >= A(X):=3/2+eta+(c/eta)(3/2-X)-1/eta.         (6)
```

Put `tau=eta/(1+c)=tan(theta/2)`, where
`0<theta<=pi/4`. For `X<=1/2`,

```text
A(X)>=A(1/2)=3/2+eta-tau=3/2+tau c>=3/2.
```

Thus

```text
F>=(X+c)²+A(X)²=:f(X).
```

On `X<=1/2`,

```text
f'(X)=2(X+c)-2(c/eta)A(X)<=3-3(c/eta)<=0.
```

Consequently

```text
F>=f(1/2)=(1/2+c)²+(3/2+tau c)²
          =5/2+c(2+3tau-tau²).
```

Subtracting `9/2` gives exactly

```text
tau(3-5tau-3tau²+tau³)/(1+tau²)>0,                (7)
```

because `0<tau<=sqrt(2)-1<5/12` and
`3-5tau-3tau²>=19/48>0`. This contradicts containment in `D`.
Therefore `X>1/2`, and `x<=-X<-1/2` throughout the square. The zero-angle
case, if allowed, follows immediately from `X=a>1/2`.

Every corner of our core meets the opposite-centre hypothesis by (1).
Thus an oblique square separated at the lower-left corner lies wholly
in `x<-1/2` or in `y<-1/2`. At the upper-left corner it lies wholly in
`x<-1/2` or is separated by a predominantly upward normal. We sharpen
the latter alternative next.

## 4. An upward corner square lies in the narrow top cap

At the upper-left corner, write

```text
q=(-a,b), a=1-s>3/5, b=1+t>=1,
n=(-eta,c), 0<eta<=c, c²+eta²=1.
```

The two outer-edge endpoints have normal projection `n dot q+1` and
tangent projections differing by one. Their maximum squared norm is
therefore at least `(n dot q+1)²+1/4`. Containment gives

```text
a eta+b c <= sqrt(17)/2-1 < 17/16.                (8)
```

We claim `eta<1/8`. Otherwise `eta` lies in `[1/8,1/sqrt(2)]`. The
concave function

```text
g(eta)=(3/5)eta+sqrt(1-eta²)
```

has its minimum at an endpoint of this interval. At the first endpoint,

```text
g(1/8)=3/40+sqrt(63)/8>3/40+99/100=213/200>17/16.
```

At the second,

```text
g(1/sqrt(2))=8/(5sqrt(2))>16/15>17/16.
```

Since `a eta+b c>=g(eta)`, both contradict (8), proving the claim.

The inner edge contains `q`, and its vertical extent below `q` is at
most `eta`; moving to the outer edge increases height. Hence every
point of the contact square has

```text
y>=b-eta>7/8.
```

The outward translation back to the original square only increases
height, so this entire family lies in the narrow cap `y>7/8`.

## 5. Counting the three remaining caps

By the preceding sections, every additional square belongs to at least
one of

```text
L: the square lies wholly in x<=-1/2,
B: the square lies wholly in y<=-1/2,
T: the square lies wholly in y>=7/8.
```

This includes coordinate-separated squares: the left and lower sides of
`K` have coordinates less than `-1/2`, its upper side is at least `1`,
and the right side is unavailable by (4).

The narrow-cap stabbing theorem permits at most one square in `T`.
The sharp three-square cap theorem permits at most two in each of `L`
and `B` here. To see why its equality case cannot add a third, three
squares in `L` would include the axis-parallel square centred at `(-1,1)`.
That square overlaps the interior of `K`, since `s<1/2` and `t<1/2`.
Likewise three in `B` would include the axis-parallel square centred at
`(1,-1)`, which also overlaps `K`. Both are impossible.

Therefore the number of additional squares is at most `2+2+1=5`.
Together with the small-translation case this proves the theorem.
