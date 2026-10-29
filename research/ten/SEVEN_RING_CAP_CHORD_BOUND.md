# A hand bound for the chord endpoints of a loaded-ring spike cap

**Status:** exact proof of one branch of the local cap problem. Independent
full mathematical review passed on 2026-10-29, including symbolic expansion
of the derivative identity and all 40 positive Bernstein coefficients. This note bounds the two endpoints where the diameter
circle meets the second loaded square's inner side line. The circle's
radial extreme, when it lies in the retained half-plane, is a separate
remaining branch. No unrestricted ring exclusion is claimed here.

Use the one-chirality spike notation in
[SEVEN_RING_SPIKE_REDUCTION.md](SEVEN_RING_SPIKE_REDUCTION.md), with the
physical incoming-neighbor consequence `X=R cos(a)>1` from
[SEVEN_RING_FORCE_RATIO.md](SEVEN_RING_FORCE_RATIO.md). Write

```
q=R^2,       6241/1600<=q<=9/2,
X=R cos(a)>=1,       Y=R sin(a)>=1/2,
X^2+Y^2=q,
d in [0,pi/2],       c=cos(d), s=sin(d),
t=1-lambda in [0,1].
```

Closed endpoints are deliberately allowed for the inequality below. The
first loaded circle vertex is `(X,-Y)`. The two opposite corners and their
contact are

```
A=(X-1,1-Y),
P=(X-1+t,1-Y),
B=P+(-s,c).
```

The second loaded circle vertex is `P+(c,s)`. Equality of its squared norm
with `q` gives

```
t=-(X-1)-c+sqrt(X^2+(1+s)(2Y-1-s)).                 (1)
```

The circle with diameter `[A,B]` meets the line through `[P,B]` at `B`
and at the orthogonal projection of `A` onto that line:

```
V=P+t*s*(-s,c)
 =(X-1+t*c^2, 1-Y+t*s*c).                          (2)
```

**Theorem.** Every such endpoint `V` obeys `|V|^2<33/20`.
For a physical spike, the other endpoint `B` already satisfies
`|B|^2<36/25<33/20` by the opposite-corner lemma. The bound includes every physical spike in this
contact pattern; its proof does not use the other five loaded squares.

## 1. The largest containing radius is the worst case for V

Keep `Y,d` fixed and increase `X` until `X^2+Y^2=9/2`. Put

```
K=(1+s)(2Y-1-s),       Z=sqrt(X^2+K),
t=1-X-c+Z,            t_X=-1+X/Z.
```

If `K>=0`, then `t_X` lies in `[-1,0]`, and `t` decreases toward the
nonnegative limit `1-c`. If `K<0`, `t_X>0`, and `t` increases toward the
limit `1-c<=1`. Hence an initially feasible `t in [0,1]` remains feasible
during this increase. Also `X>=1` remains valid.

Differentiate (2):

```
(1/2) partial_X |V|^2
 =V_x+t_X(V_x*c^2+V_y*s*c).                         (3)
```

For `K<0`, one has `Y<1`; both coordinates of `V` are nonnegative, so
(3) is nonnegative. For `K>=0,Y>=1`, if the parenthesized factor in (3)
is negative, (3) is at least `V_x>=0`. Otherwise `t_X>=-1` gives

```
(3) >= V_x*s^2-V_y*s*c
     =(X-1)*s^2+(Y-1)*s*c>=0.
```

It remains to consider `K>=0,Y<1`. The radius window implies
`X^2=q-Y^2>6241/1600-1>289/100`, so `X>17/10`. Also

```
0<=K<=(1+s)(1-s)<=1,
|t_X|=1-1/sqrt(1+K/X^2)<=K/(2X^2)<1/5.
```

The elementary inequality used here follows by differentiating
`u/2-1+1/sqrt(1+u)` for `u>=0`. Since `0<=V_y<=1`, `s*c<=1/2` and
`V_x>=X-1>7/10`, equation (3) is at least

```
(4/5)V_x-1/10>0.
```

This proves monotonicity. For the rest of the proof set `q=9/2` and
`X=sqrt(9/2-Y^2)`, with `1/2<=Y<=sqrt(7/2)`.

## 2. The range Y<=3/2: a simple coordinate box

We prove

```
0<=V_x<=23/20,       -1/2<=V_y<=4/7.               (4)
```

These imply

```
|V|^2 <=529/400+16/49=32321/19600
       <32340/19600=33/20.                         (5)
```

### 2.1. Horizontal coordinate

Put `N=1+s-Y`. Equation (1) also gives

```
Z=sqrt(9/2-N^2),
V_x=s^2*sqrt(9/2-Y^2)+c^2*sqrt(9/2-N^2)-s^2-c^3.
```

Concavity of the square root, followed by completing the square in `Y`,
yields

```
s^2*sqrt(9/2-Y^2)+c^2*sqrt(9/2-N^2)
 <=sqrt(9/2-s^2*Y^2-c^2*N^2)
 <=sqrt(9/2-s^2*c^2*(1+s)^2).
```

The univariate inequality

```
sqrt(9/2-s^2*c^2*(1+s)^2)-s^2-c^3<=23/20           (6)
```

holds for nonnegative `s,c` with `s^2+c^2=1`. The exact polynomial proof
is supplied in Section 4.1. This proves the horizontal bound in (4).

### 2.2. Vertical coordinate

For fixed `d`, differentiate with respect to `Y` along `q=9/2`:

```
t_Y=Y/sqrt(9/2-Y^2)+N/sqrt(9/2-N^2).
```

On `1/2<=Y<=3/2`, both `Y,N<=3/2` and `N>=-1/2`, so each displayed
ratio is at most one. Thus `t_Y<=2` and

```
partial_Y V_y=-1+s*c*t_Y<=0.
```

It follows that `V_y` is largest at `Y=1/2`, where `X=sqrt(17)/2` and

```
t=sqrt(X^2-s(1+s))-X+1-c
 <=1-c-s(1+s)/(2X)
 <1-c-(8/33)s(1+s).
```

The first inequality is the tangent inequality for the square root; the
second uses `X<33/16`. At `s=0`, replace the final strict sign by equality,
which is enough for the bound. Section 4.2 proves the univariate inequality

```
s*c[1-c-(8/33)s(1+s)]<=1/14.                       (7)
```

Therefore `V_y<=1/2+1/14=4/7`. The lower bound is immediate from
`V_y=1-Y+t*s*c>=1-Y>=-1/2`. This completes (4)--(5).

## 3. The range Y>=3/2: the angle-zero endpoint is the worst case

Now `1<=X<=3/2`. Put

```
a=X-1,       H=Y-1,       p=a+t,
E=t*p-a*c.
```

Here `a>=0` and `1/2<=H<7/8`. Differentiating the equal-radius equation,
with `X,Y` fixed, gives

```
t_d=[s*p+c*H]/(p+c)>0.                              (8)
```

For `d<pi/2`, direct differentiation of (2) simplifies to

```
(p+c) (1/2) d(|V|^2)/dd
 =-s*c^2*(H^2+a*p)
  -E[s*c*(2a+t)+H*(c^2-s^2)].                       (9)
```

We show both factors in the second product are nonnegative.

First, `E` increases with `d`: `t` increases by (8), and `c` decreases.
At `d=0`, put `Z_0=sqrt(X^2+2Y-1)`, so `t_0=Z_0-X`. Then

```
E_0=X^2+2Y-(X+1)Z_0>0.
```

To check the sign, both quantities being compared are positive, and the
difference of their squares is

```
F(X,Y)=-2X^3+2X^2Y-4XY+2X+4Y^2-2Y+1.
```

Its `Y` derivative is `2(X-1)^2+8Y-4>=8` in this range. At `Y=3/2`,

```
F(X,3/2)=-2X^3+3X^2-4X+7
```

strictly decreases on `[1,3/2]` and has value one at `X=3/2`. Therefore
`F>=1`, proving `E_0>0` and hence `E>0`.

For the bracket in (9), there is nothing to prove when `d<=pi/4`.
Suppose `d>pi/4`. The equal-radius equation is increasing in `t`; using
`t<=1` in that equation gives

```
H<=X*c/(1+s).
```

Since `H>=1/2` and `X<=3/2`, it follows that `c/(1+s)>=1/3`, and hence
`s<=4/5`. On this angle range, therefore,

```
s*c>=12/25,       c^2-s^2>=-7/25.
```

Furthermore, `t>=t_0>11/20`: the smallest `t_0` for `X<=3/2,Y>=3/2`
is `(sqrt(17)-3)/2>11/20`. Consequently

```
s*c*(2a+t)+H*(c^2-s^2)
 >=(12/25)(11/20)-(7/8)(7/25)=19/1000>0.
```

Equation (9) is nonpositive. Thus `|V|^2` decreases with `d` throughout
the feasible interval, and its maximum occurs at `d=0`. There

```
|V|^2=11/2-2sqrt(9/2-(Y-1)^2)
 <=11/2-2*14^(1/4)<33/20.                          (10)
```

The maximum is at `Y=sqrt(7/2)`. The last strict comparison follows from
`14>(77/40)^4`, with integer difference
`14*40^4-77^4=686959>0`. This closes the second range.

## 4. Two short polynomial positivity checks

For a polynomial `P` of degree at most `n`, its Bernstein representation
on `[l,r]` is

```
P(l+(r-l)z)=sum_(j=0)^n b_j binom(n,j) z^j(1-z)^(n-j).
```

If all `b_j` are positive, the polynomial is positive throughout the
closed interval. The coefficients below are exact identities that can be
checked by expansion. This is a fixed pair of univariate inequalities,
not a numerical sampling argument.

### 4.1. Proof of (6)

Its right side after moving terms is positive, so square the desired
inequality. Substitute

```
z=tan(d/2) in [0,1],
s=2z/(1+z^2),       c=(1-z^2)/(1+z^2).
```

The difference of squared sides equals `P(z)/(400(1+z^2)^6)`, where

```
P(z)= -1791z^12-7946z^10+6400z^9+23615z^8-6400z^7
      -14540z^6-6400z^5+5295z^4+6400z^3-1546z^2+49.
```

In degree 12 on `[0,1]`, the Bernstein coefficients multiplied by `693`
are, in increasing index order,

```
33957, 33957, 17724, 5418, 24612, 104692, 260352,
458584, 596624, 571536, 512064, 1086624, 2173248.
```

They are all positive, proving (6).

### 4.2. Proof of (7)

Under the same substitution, the difference between `1/14` and the left
side of (7) equals `Q(z)/(462(1+z^2)^4)`, where

```
Q(z)=33z^8+1848z^7-316z^6-896z^5+198z^4-952z^3+580z^2+33.
```

The following three intervals cover `[0,1]`. Each row gives a positive
common denominator `D`, followed by the nine integers `D*b_0,...,D*b_8`
in the degree-eight Bernstein representation on that interval.

```
[0,2/3], D=76545:
2525985, 2525985, 3230685, 4254525, 5254713,
5769945, 4983285, 2444085, 882385.

[2/3,3/4], D=5016453120:
57827983360, 45034536960, 33242050560, 22799969280, 14108629248,
7624886400, 3868268400, 3427685100, 6968733345.

[3/4,1], D=2293760:
3186435, 8043840, 29286560, 75131840, 156637184,
288512000, 490127360, 786759680, 1211105280.
```

All entries are positive. This proves (7) and completes the endpoint
bound. The remaining radial-extreme branch of the diameter-disk cap is
not included in this theorem.
