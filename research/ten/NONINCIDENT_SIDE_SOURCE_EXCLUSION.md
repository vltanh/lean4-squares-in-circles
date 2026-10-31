# A nonincident vertex/side source cannot feed two positive-width paths

**Status:** reviewed exact hand proof; root and independent full mathematical
reviews passed on 2026-10-31, including both rational table margins and
the extension to arbitrary transmission widths at least one.
This is a shared local exclusion, not a completion bound or a whole-cycle
claim. It uses no circle load, force balance, or degree assumption at the
two far endpoint squares.

Let a loaded degree-two unit square C have a unique circle vertex in a
packing contained in the centered disk of radius `R<=3/sqrt(2)`. Suppose
its two positive outgoing contact forces start transmission paths of
widths `W_A,W_B>=1`. The usual exact path convention means that a path
starting at P in outward unit direction n terminates at `P+W n` on a
unit square supported there with inward normal n. The two paths may
therefore be S, D, or SS paths whenever their other hypotheses hold.

Choose C's axes so that its circle vertex is Z=(X,Y), where X,Y>1/2,
and put `q=X^2+Y^2=R^2<=9/2`. Assume that its contacts have the
nonincident vertex/side form

```text
C=[X-1,X] x [Y-1,Y],
J=(X-1,Y),             P=(X-h,Y-1),       0<h<1,
outgoing forces at J,P: (-u,v), (0,-z),  u,v,z>0.
```

Thus J has a strict vertex normal, while P has the downward side normal.
This is the U-VE-N row of
[LSLSLSS_SUPPORT_NORMALIZATION.md](LSLSLSS_SUPPORT_NORMALIZATION.md),
with h=1-t. Reflection and exchange of the two square axes are included.

**Theorem.** This source form is impossible.

## 1. Two disk tests and the exact force ratio

Scale the positive circle coefficient to one. Force and torque balance
at C give

```text
u=X,       z-v=Y,       v=h z,
v=hY/(1-h).
```

Write the outward unit normal at J as `(-p,s)`, where p,s>0 and
`p^2+s^2=1`. The ratio v/u gives

```text
s/p = hY/((1-h)X),
h = Xs/(Yp+Xs).                                      (1)
```

A supported unit square with inward unit normal n at Q contains Q+n;
the vertex and side cases of this unit-normal-step lemma are proved in
[SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md).
Consequently each far endpoint contains `P_i+(W_i+1)n_i`. Since
`W_i>=1`, convexity of the containing disk, together with `P_i` in the
disk, puts `P_i+2n_i` in the disk too. This argument does not require
that this intermediate point itself belong to the endpoint square.

Applying this at J and P gives the necessary tests

```text
(X-1-2p)^2+(Y+2s)^2 <= X^2+Y^2,
(X-h)^2+(Y-3)^2     <= X^2+Y^2.
```

After expansion these are

```text
9-6X + 4(X-1)(1-p) + 4Ys <= 0,                       (2)
9-6Y - 2Xh + h^2 <= 0.                               (3)
```

## 2. A compact parameter interval forced by the two tests

First X>3/2. Indeed, before the rearrangement in (2), its left side is
`5-2X+4(1-X)p+4Ys`. This is positive for X<=1. For
`1<X<=3/2`, equation (2) makes it strictly larger than `9-6X>=0`.
Since q<=9/2, it follows that Y<3/2. Define

```text
delta=3/2-Y>0,
r=(3/2+Y)/(3/2+X)<1.
```

The radius bound supplies

```text
(X-3/2)(X+3/2) <= (3/2-Y)(3/2+Y),
X-3/2 <= delta r,
X+Y<3.                                               (4)
```

For fixed X>3/2 the function `2Xh-h^2` strictly increases on [0,1].
Equation (3) and h<1 therefore give

```text
9-6Y <= 2Xh-h^2 < 2X-1,
Y > (5-X)/3.                                         (5)
```

These inequalities imply the useful rational bounds

```text
X<37/20,       Y>21/20.                               (6)
```

To see the first, the function `x^2+((5-x)/3)^2` increases for x>1/2,
and its value at x=37/20 is `9/2+1/40`. If X>=37/20,
(5) would contradict q<=9/2. The second assertion follows directly
from (5). All quantities squared here are positive: X<=R<17/8<5.

Since X>1 and p<1, (2) also gives

```text
s < (3/2)(X-3/2)/Y < 1/2,
p > sqrt(3)/2 > 6/7.                                (7)
```

For the middle bound, insert X<37/20 and Y>21/20. The final comparison
follows from `3/4-36/49=3/196>0`.

## 3. A necessary inequality contradicted by two rational rows

Equation (3) implies `2Xh>=6delta+h^2`, hence
`h>3delta/X`. Substituting (1) gives

```text
X(X-3delta)s > 3delta Yp.                             (8)
```

In particular X-3delta>0. Use (7) and then (4) to bound s from above
in (8), and cancel the positive factor `3delta/(2Y)`. The result is
the necessary strict inequality

```text
X(X-3delta)r > 2pY^2.                                (9)
```

The following two rows cover the entire remaining interval for Y and
contradict (9). Every displayed left bound is an upper bound, and every
right bound is a lower bound.

| Range | Bounds used on the left | `X(X-3delta)r` is less than | `2pY^2` is greater than | Right minus left |
| --- | --- | --- | --- | --- |
| `21/20<Y<=5/4` | `X<37/20`, `X-3delta<11/10`, `r<11/12` | `4477/2400` | `1323/700` | `59/2400` |
| `5/4<=Y<3/2` | `X<7/4`, `X-3delta<3/2`, `r<1` | `21/8` | `75/28` | `3/56` |

Here are the individual checks. In the first row,
`X-3delta=X+3Y-9/2<37/20+15/4-9/2=11/10`, and
`r<(11/4)/3=11/12`. The lower bound is
`2(6/7)(21/20)^2=1323/700`.

In the second row, `X^2<=9/2-25/16=47/16<49/16`.
Equation (4) gives
`X-3delta=X+3Y-9/2<2Y-3/2<3/2`.
The lower bound is `2(6/7)(5/4)^2=75/28`.
The shared endpoint Y=5/4 is harmless; either row applies there.

Both rational differences are positive, so (9) is impossible. This
proves the theorem.

## 4. Scope for the finite case classification

The entire U-VE-N row in LSLSLSS is excluded, for arbitrary transmitter
slides and arbitrary support types or circle multiplicities at its far
endpoints. More generally the proof excludes the same local source form
whenever both incident transmission widths are at least one, including
applications in other mixed cycles or branching graphs where C still
has exactly the displayed two outgoing forces and one positive circle
load. Extra endpoint forces are unrestricted.

The theorem does not concern a direct loaded-loaded contact of width
zero. It does not exclude U-EE, U-VV-A, U-VV-O, or the remaining radial
R-VV endpoint forms. No whole signature or global progress count is
changed by this note alone.
