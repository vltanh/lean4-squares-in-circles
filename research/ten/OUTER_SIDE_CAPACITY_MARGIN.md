# The outer-side cap lies below the three-square capacity threshold

**Status:** complete conditional hand argument; two independent full
mathematical reviews passed on 2026-10-30, including all closed-domain
endpoints, both radical arcs, and the strict rational capacity margin.
The extra-corner estimate `|B|^2<=33/20` is an explicit hypothesis.
This note converts it into the stronger cap estimate needed by the
seven-loaded-ring argument; it does not establish that hypothesis or
claim a complete C04 exclusion by itself.

## 1. A closed-domain algebraic estimate

Suppose real numbers X,H satisfy

```text
1/2<=X<=H,
X^2+H^2<=33/20,
X^2+(H+1)^2<=9/2.
```

Then

```text
E(X,H):=X^2+H^2+5(H-X)^2/(6H) <83/50.                (1)
```

The denominator is positive since `H>=1/2`. The circle constraint and
`X>=1/2` give

```text
H<=Hmax:=sqrt(17)/2-1<17/16.                          (2)
```

The last strict comparison follows by squaring the positive quantities:
`17/4=1088/256<1089/256=(33/16)^2`.

For fixed H, E is a convex quadratic in X, with

```text
partial_X^2 E=2+5/(3H)>0.
```

The admissible X interval is

```text
1/2<=X<=min{H, sqrt(33/20-H^2),
                 sqrt(7/2-2H-H^2)}.                 (3)
```

The radicands are nonnegative whenever this interval is nonempty.
Convexity reduces (1) to its lower endpoint and each possible active
upper endpoint. Ties between upper endpoints cause no difficulty.

### The lower endpoint X=1/2

For H>=1/2,

```text
d/dH E(1/2,H)=2H+(5/6)(1-1/(4H^2))>0.
```

Consequently (2) yields

```text
E(1/2,H)<E(1/2,17/16)=7081/4352<83/50,
83/50-7081/4352=3583/108800>0.                        (4)
```

### The upper endpoint X=H

At this endpoint,

```text
E(H,H)=2H^2<=33/20<83/50.                            (5)
```

### The upper endpoint X=sqrt(33/20-H^2)

For this to be an active endpoint in (3), comparison with the other two
upper endpoints gives

```text
sqrt(33/40)<=H<=37/40.                               (6)
```

Indeed, `X<=H` gives the first inequality, while
`33/20-H^2<=7/2-2H-H^2` gives the second. In this interval,

```text
H>=sqrt(33/40)>9/10,
X^2>=33/20-(37/40)^2=1271/1600>(89/100)^2,
1271/1600-(89/100)^2=91/40000>0.
```

Since X<=H, these imply

```text
0<=H-X<37/40-89/100=7/200.
```

Thus the cap correction is small enough even when the corner bound is
attained:

```text
E(X,H)<33/20+5(7/200)^2/(6*(9/10))
      =33/20+49/43200<33/20+1/100=83/50.              (7)
```

The last comparison is the integer inequality `49<432`.

### The upper endpoint X=sqrt(7/2-2H-H^2)

Comparison with the other radical endpoint in (3) gives `H>=37/40`.
Together with (2), it suffices to consider the whole interval

```text
37/40<=H<=Hmax.
```

Put `x(H)=sqrt(7/2-2H-H^2)`. It is positive on this interval, with
`x(Hmax)=1/2`. On this arc the expression becomes

```text
E(x(H),H)
 =7/2-2H+(5/6)*(7/(2H)-2-2x(H)).                    (8)
```

Since `x(H)^2=9/2-(H+1)^2`, differentiation gives

```text
x''(H)=-(9/2)/x(H)^3,
d^2/dH^2 E(x(H),H)=(5/6)*(7/H^3+9/x(H)^3)>0.
```

Hence (8) is convex and bounded by the larger of its two endpoint
values. At `H=37/40`, this is exactly the endpoint in (6)--(7), because

```text
x(37/40)^2=1271/1600=33/20-(37/40)^2.
```

At `H=Hmax`, it is the lower-X endpoint bounded in (4). Both are
strictly below `83/50`, so the entire arc is as well. This completes
the proof of (1).

## 2. Application to an outer proper-contact spike

Use the setup of
[OUTER_SIDE_SPIKE_CAP_BOUND.md](OUTER_SIDE_SPIKE_CAP_BOUND.md):

```text
C=[X-1,X] x [-H-1,-H],
B=(X,-H),       P=(X,-H-t),
1/2<X<H,       q=X^2+(H+1)^2<=9/2,
6241/1600<=q,
u=(c,-s),      v=(s,c),      c,s>0,      c^2+s^2=1,
D=P+v,
T=conv{B,P,D}.
```

The neighbor at P has strict vertex support and an adjacent circle
vertex `P+u`. If `|B|^2<=33/20`, every vertex z of an inner unit square
lying in T satisfies

```text
|z|^2 <= |V|^2
       < |B|^2+5(H-X)^2/(6H)
       = E(X,H)
       <83/50,
V=(X+tcs,-H-ts^2).                                  (9)
```

The first two comparisons are the diameter-cap and exact correction
estimates of that note. The last is (1). In particular the small cap
outside B is controlled, rather than merely its extra corner.

The comparison with the known squared-radius threshold for three unit
squares is strict and exact:

```text
83/50<425/256,
425/256-83/50=1/6400.                               (10)
```

For a complete ring exclusion, the separate global argument must place
every inner-square vertex either in a region already controlled below
`83/50` or in one of the outer spikes covered by (9), and must justify
the extra-corner hypothesis for every such outer body. This note
provides precisely the algebraic margin for that assembly.
