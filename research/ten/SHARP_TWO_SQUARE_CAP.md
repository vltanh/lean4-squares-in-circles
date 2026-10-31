# The sharp two-square cap at squared radius 9/2

Put

```text
a=sqrt(7/2)-1,
p=a+1/2=sqrt(7/2)-1/2,
P=(p,0).
```

Every unit square in the origin-centred disk of squared radius `9/2`
that lies wholly in `x>=a` contains `P`. Except for the two axis-parallel
squares centred at `(p,1/2)` and `(p,-1/2)`, it contains `P` in its open
interior. Consequently the cap contains two interior-disjoint unit squares
only in that exact configuration; it never contains three. In the strict
cap `x>a`, or in a smaller containing disk, it contains at most one.

This is a hand theorem. In particular it strengthens the rational-offset
one-square cap theorem in
[SEVEN_EIGHTHS_CAP_STABBING.md](SEVEN_EIGHTHS_CAP_STABBING.md), since
`a<7/8`.

## 1. Coordinates and a comparison retaining horizontal slack

For a square with centre `(x,y)`, reflect vertically so that `y>=0` and
write its frame as `theta` or `-theta`, where

```text
0<=theta<=pi/4,
c=cos(theta), s=sin(theta), w=c+s, z=c-s,
x0=a+w/2.
```

The cap condition is `x>=x0>=p`. Its largest squared vertex norm `F`
satisfies `F>=r²+r+1/2`, where `r` is the centre norm. Thus `r<25/16`,
since that expression at `25/16` equals `1153/256>9/2`.

Also `p>4/3`, since `7/2>(11/6)²`. Therefore `0<=y<1<x`: indeed
`y²<(25/16)²-(4/3)²<1`. The two frame signs give

```text
F=x²+y²+1/2+max(xz+yw,xw-yz),
F=x²+y²+1/2+xw+yz.
```

The second is at least the first. Write the first expression as `G(x,y)`.
Each of its two branches has derivative in `x` greater than `1/2` for
`x>=x0`. Hence

```text
F>=G(x0,y)+(x-x0)/2.                              (1)
```

Subtract `(a+1)²+(y+1/2)²` from `G(x0,y)`. The difference is

```text
D(y)=x0²-(a+1)²+1/4
      +max(x0 z+y(w-1),x0 w-y(z+1)).
```

Its minimum occurs where the affine branches meet, at `y0=x0 s/c`:

```text
D(y)>=D(y0)=x0²-(a+1)²+1/4+x0(1-s)/c.             (2)
```

Set `tau=tan(theta/2)`. The square's farthest horizontal coordinate is
at least `a+w`, so

```text
w<=sqrt(9/2)-a
  =1+1/(sqrt(9/2)+sqrt(7/2))
  <1+4/15=19/15<47/37.
```

Here the two square roots exceed `2` and `7/4`, respectively. Since `w`
increases on `0<=theta<=pi/4` and equals `47/37` at `tau=1/6`, we have
`0<=tau<1/6`.

The exact half-angle expansion of (2) gives

```text
D(y0)-(w-1)/4
 = tau [1-2tau-(8a+2)tau²-6tau³+(1-8a)tau⁴]
     /[2(1+tau)(1+tau²)²].                        (3)
```

Because `a<1`, the bracket is at least

```text
1-2tau-10tau²-6tau³-7tau⁴
 >=1-(1/3+10/36+6/216+7/1296)
 =461/1296>0.
```

Thus `D(y0)>=(w-1)/4=(x0-p)/2`. Combining (1)--(3) yields the useful
one-square estimate

```text
F>=(a+1)²+(|y|+1/2)²+(x-p)/2.                    (4)
```

## 2. A common point and all equality cases

Put `d=x-p>=0`. Since `p>4/3` and `x<25/16`,

```text
0<=d<11/48<4/17.
```

Using `(a+1)²=7/2`, (4) gives

```text
(|y|+1/2)²<=1-d/2,
|y|<=sqrt(1-d/2)-1/2<=1/2-d/4.
```

The last inequality is the elementary tangent bound for the square root,
or follows by squaring `sqrt(1-d/2)<=1-d/4`. Consequently

```text
|(x,y)-P|²<=d²+(1/2-d/4)²
            =1/4+d(17d/16-1/4)<=1/4.             (5)
```

If `d>0`, the final inequality is strict because `d<4/17`. If `d=0`,
then `x=p` and the cap condition forces `w=1`, so the square is
axis-parallel. Equality in (5) then requires `|y|=1/2`.

The square's closed inscribed radius-`1/2` disk therefore contains `P`,
and contains it in its interior except in the two stated cases. A square
whose interior contains `P` cannot coexist with another cap square:
the latter contains `P`, and its interior has points arbitrarily close
to `P`, which would enter the first square's interior.

The only possible pair is consequently the two axis-parallel exceptional
squares. They do fit: their extreme outer vertices are
`(sqrt(7/2),1)` and `(sqrt(7/2),-1)`, of squared norm `9/2`, and their
interiors are separated by `y=0`. Their left edges lie at `x=a`.
This also proves the assertions about strict caps and smaller disks.
