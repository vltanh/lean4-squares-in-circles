# An incident opposite-vertex/side source cannot feed width-two-separated endpoints

**Status:** reviewed hand exclusion; root and independent mathematical
reviews passed on 2026-10-30.
This excludes the entire U-VE-I row in
[LSLSLSS_SUPPORT_NORMALIZATION.md](LSLSLSS_SUPPORT_NORMALIZATION.md).
It does not close the other central rows or the whole LSLSLSS signature.

Work in `79/40<=R<=3/sqrt(2)`. Let a uniquely circle-loaded body C have
exactly two positive pair contacts. Suppose one is its opposite vertex
with a strict normal and the other is an incident inner side. Two
unloaded degree-two S transmitters lead from these contacts to endpoint
squares A and B. Suppose A and B are joined by an SS path, so
`dist(A,B)=2`. Endpoint loading, support ownership, circle multiplicity,
and additional endpoint forces are unrestricted.

We prove these hypotheses impossible.

## 1. Force and torque give a one-variable contact direction

Use the U-VE-I coordinates, exchanging axes if necessary:

```text
C=[X-1,X] x [Y-1,Y],       w=(X,Y),
X,Y>1/2,       X^2+Y^2=R^2<=9/2,
I=(X-1,Y-1),       P=(X-1+t,Y-1),       0<t<=1.
```

The outgoing forces at I and P are `(-u,-v)` and `(0,-z)`, with all
three coefficients positive. Normalize C's circle coefficient to one.
The reviewed force and torque identities give

```text
u=X,       v+z=Y,       t*z=Y-X,
u-v=(1-t)*z>=0.
```

In particular Y>X. Put

```text
k=v/u,       r=Y/X,
0<k<=1,       r>1,
t=(r-1)/(r-k),
p=1/sqrt(1+k^2),       s=k/sqrt(1+k^2).
```

The outgoing unit direction at I is `(-p,-s)`. The actual far S
endpoint contacts therefore are

```text
Q_A=(X-1-p,Y-1-s) in A,
Q_B=(X-1+t,Y-2) in B.
```

Their squared distance is

```text
D^2:=|Q_B-Q_A|^2
    =(t+p)^2+(1-s)^2
    =t^2+2tp+2-2s.                                 (1)
```

Since dist(A,B)=2, these two particular points must satisfy D^2>=4.

## 2. The endpoint distance forces a large coordinate ratio

Suppose r<=7/2. For fixed k, `(r-1)/(r-k)` is nondecreasing in r,
with derivative `(1-k)/(r-k)^2>=0`. Thus

```text
t<=5/(7-2k).
```

Also p<=1 and `s=k/sqrt(1+k^2)>=k/sqrt(2)>7k/10`, because k>0
and `sqrt(2)<10/7`. Equation (1) gives

```text
D^2 < F(k):=25/(7-2k)^2+10/(7-2k)+2-7k/5.           (2)
```

The function F is convex on [0,1]: each positive reciprocal-power term
has positive second derivative, and its remaining term is affine.
Consequently its maximum is at an endpoint. The exact values are

```text
F(0)=193/49<4,
F(1)=18/5<4.
```

This contradicts D^2>=4. Therefore r>7/2, and the circle bound yields

```text
X^2=R^2/(1+r^2)<(9/2)/(1+49/4)=18/53<9/25,
X<3/5.                                              (3)
```

## 3. The same distance forces an almost horizontal vertex normal

Since t<=1, equation (1) also gives

```text
4<=D^2<=3+2(p-s),       p-s>=1/2.                    (4)
```

If s>=3/7, then `p<=sqrt(40)/7`, so
`p-s<1/2` from `sqrt(40)<13/2`, contrary to (4).
Thus

```text
s<3/7,
p^2=1-s^2>40/49>81/100,
p>9/10.                                             (5)
```

Here `4000>3969` is the last rational comparison. Also r>7/2 and
X>1/2 imply Y>7/4, while `Y<R<=3/sqrt(2)<17/8`.

## 4. The far neighbor's normal step is outside the circle

The unit-normal-step lemma applied to A at Q_A puts

```text
Q_A+(-p,-s)=(X-1-2p,Y-1-2s)
```

inside A and hence inside the containing disk. Subtracting
`X^2+Y^2=R^2` from its squared norm, using `p^2+s^2=1`, gives the
necessary inequality

```text
3<=X+Y+2(X-1)p+2(Y-1)s.                             (6)
```

But (3)--(5), with X<1<Y, bound the right side from above by

```text
X+2(X-1)p < 3/5-2(2/5)(9/10)=-3/25,
Y+2(Y-1)s < 17/8+2(9/8)(3/7)=173/56.
```

Therefore

```text
X+Y+2(X-1)p+2(Y-1)s
 < -3/25+173/56=4157/1400<3,
3-4157/1400=43/1400>0.                              (7)
```

This contradicts (6). The incident opposite-vertex/inner-side source
cannot occur with the stated S paths and width-two endpoint separation.
The argument keeps the possible E application endpoint t=1 and never
assumes a unique circle vertex or a particular support feature on A or B.
