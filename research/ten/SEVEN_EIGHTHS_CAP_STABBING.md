# A cap beginning at 7/8 contains at most one unit square

Every closed unit square contained in the origin-centred disk `D` of
squared radius `9/2` and in the half-plane `x>=7/8` contains

```text
P=(23/16,0)
```

in its open interior. Consequently this cap contains at most one member
of an interior-disjoint packing. The statement allows arbitrary square
orientation and rotates with the cap. It strengthens
[NARROW_CAP_STABBING.md](NARROW_CAP_STABBING.md).

This is a hand proof. It does not use numerical optimization or an interval
certificate.

## 1. An axis-parallel comparison

Put `a=7/8`. Let the square have centre `(x,y)`, and reflect vertically to
make `y>=0`. Write its frame angle as `theta` or `-theta`, with

```text
0<=theta<=pi/4,
c=cos(theta), s=sin(theta), w=c+s, z=c-s,
x0=a+w/2.
```

The cap condition is `x>=x0>=11/8`. If `F` is the largest squared vertex
norm and `r` the centre norm, then

```text
F>=r²+r+1/2,
r<25/16.
```

Indeed `(25/16)²+25/16+1/2=1153/256>9/2`. In particular
`y²<(25/16)²-(11/8)²=141/256<1`, so `0<=y<1<x`.

The two frame signs give, respectively,

```text
F=x²+y²+1/2+max(xz+yw,xw-yz),
F=x²+y²+1/2+xw+yz.
```

The second expression is at least the first, because `x>=y>=0` and
`c>=s>=0`. Both branches of the first increase with `x`, so replace `x`
there by `x0`. Subtracting `(a+1)²+(y+1/2)²` leaves

```text
D(y)=x0²-(a+1)²+1/4
       +max(x0 z+y(w-1),x0 w-y(z+1)).
```

The two affine terms meet at `y0=x0 s/c`; one is nondecreasing and the
other decreasing. Thus

```text
D(y)>=D(y0)=x0²-(a+1)²+1/4+x0(1-s)/c.             (1)
```

The farthest horizontal coordinate is at least `a+w`, whence

```text
w<=3/sqrt(2)-7/8<17/8-7/8=5/4.
```

For `tau=tan(theta/2)`, this implies `0<=tau<1/4`: `w` increases with
`theta`, and at `tau=1/4` it equals `23/17>5/4`. Substitution in (1)
gives the exact identity

```text
D(y0)=tau [1-tau-(9/2)tau²-3tau³-(7/2)tau⁴]
        /[(1+tau)(1+tau²)²].                       (2)
```

The bracket is positive, since its subtracted terms sum to at most

```text
1/4+9/32+3/64+7/512=303/512<1.
```

Therefore

```text
F>=(15/8)²+(|y|+1/2)².                            (3)
```

## 2. One common interior point

From (3),

```text
|y|<=sqrt(63)/8-1/2<63/128,
```

where the strict inequality follows from
`63<(127/16)²=63+1/256`.

If `11/8<=x<=3/2`, then `|x-23/16|<=1/16`, and hence

```text
|(x,y)-P|²<(1/16)²+(63/128)²=4033/16384<1/4.
```

If `3/2<=x<25/16`, then `|x-23/16|<1/8` and

```text
y²<(25/16)²-(3/2)²=49/256.
```

Consequently `|(x,y)-P|²<53/256<1/4` in this case also.

Thus `P` lies in the open inscribed radius-`1/2` disk of the square, and
therefore in its open interior. This proves the assertion.
