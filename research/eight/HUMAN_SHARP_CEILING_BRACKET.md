# The sharp rational ceiling from two explicit test poses

This note proves the exact radius bracket needed by the sharp-ceiling
capture and monotone pullback. It uses the small analytic stationary
calculation in
[HUMAN_BROAD_TERMINAL_ARITHMETIC.md](HUMAN_BROAD_TERMINAL_ARITHMETIC.md),
the global family uniqueness theorem, and eight displayed rational
square-root brackets. There is no assumption that a numerical solver has
isolated the correct stationary root. Independent review of this replacement
is pending.

## 1. The two rational radii

Define the terminating decimals as exact rational numbers:

\[
q_c=3.91553413751747532652,\qquad
q_-=q_c-2\cdot10^{-16},\qquad
Q_\sharp=q_c+10^{-16}.
\]

Then

\[
\boxed{q_-<q_*<Q_\sharp,\qquad Q_\sharp-q_-=3\cdot10^{-16}.}
\tag{1}
\]

Here q_* is the exact family radius selected globally in
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md), rather than a radius
defined by the decimal q_c.

Use the fixed test coordinates

\[
y_0=-0.92065667800760613175,\qquad
z_0=0.06189741100766035970,\qquad t_0=2\arctan z_0.
\tag{2}
\]

These are test points, not assertions about the exact minimizing coordinates.

## 2. Eight square-root brackets

Use the radicals and F from the broad terminal note. In the following table
let D=10^30. Each indicated positive radical lies strictly between N/D and
(N+k)/D.

| Squared radius | Radical | N | k |
|---|---|---:|---:|
| q_- | x_1 | 1751549433717893721308920688242 | 1 |
| q_- | x_2 | 1658478860518848668734905536484 | 1 |
| q_- | y_3 | 1454597940959173928318723969998 | 2 |
| q_- | -x_4 | 1902122690972247036667590000343 | 2 |
| Q_sharp | x_1 | 1751549433717893806947382904866 | 1 |
| Q_sharp | x_2 | 1658478860518848759179229893487 | 1 |
| Q_sharp | y_3 | 1454597940959174114853411962263 | 2 |
| Q_sharp | -x_4 | 1902122690972247169012577055225 | 2 |

These are ordinary integer-square comparisons. The first two radicands are
the exact rationals q-y_0^2 and q-(y_0+2)^2. For the third, substitute the
preceding interval for x_2 into q-(x_2-3)^2; because x_2-3<0, the lower
radicand is q-(x_{2,low}-3)^2 and the upper is
q-(x_{2,high}-3)^2. For the fourth use the same rule on q-(y_3-2)^2.
Squaring N/D and (N+k)/D bounds those full closed radicand intervals.

The two trigonometric values are exact rational functions of z_0:

\[
c_0=\frac{1-z_0^2}{1+z_0^2},\qquad s_0=\frac{2z_0}{1+z_0^2}.
\]

Substituting the eight brackets into the displayed formulas for F, F_y and
F_t gives the following deliberately loose bounds:

| Radius | Defect bound at (y_0,t_0) | Derivative bounds |
|---|---|---|
| q_- | F>7/10^16 | \(|F_y|<10^{-14},\ |F_t|<10^{-14}\) |
| Q_sharp | F<-3/10^16 | \(|F_y|<10^{-14},\ |F_t|<10^{-14}\) |

Every operation after the eight squarings is rational addition,
multiplication or division with its denominator sign fixed. The short
[transcription checker](verify_hand_sharp_ceiling_bracket.py) performs
exactly these rational comparisons; it has no square-root routine, solver
or subdivision algorithm. The table itself is the arithmetic input to the
argument.

## 3. The lower test pose bounds the whole family

Both q_- and Q_sharp lie in [7831/2000,9789/2500]. On the stationary
chart, the broad terminal calculation gives

\[
F_{yy}>6,\qquad |F_{yt}|<6,\qquad
M_{tt}>3/4,
\]

where M(q,t)=F(q,Y(q,t),t) and F_y(q,Y(q,t),t)=0. It also proves that
the unique global family minimum lies in this chart.

Strong convexity in y and the mean-value theorem imply

\[
M(q,t_0)\ge F(q,y_0,t_0)-F_y(q,y_0,t_0)^2/12,
\]

and

\[
|M_t(q,t_0)|\le|F_t(q,y_0,t_0)|+|F_y(q,y_0,t_0)|.
\]

Strong convexity in t then gives

\[
\min_t M(q,t)\ge F(q,y_0,t_0)-F_y(q,y_0,t_0)^2/12
-\frac23\bigl(|F_t(q,y_0,t_0)|+|F_y(q,y_0,t_0)|\bigr)^2.
\tag{3}
\]

At q=q_- the displayed test bounds make the right-hand side larger than

\[
\frac7{10^{16}}-\frac1{12\cdot10^{28}}-
\frac{8}{3\cdot10^{28}}
=\frac7{10^{16}}-\frac{11}{4\cdot10^{28}}>0.
\tag{4}
\]

At q=Q_sharp, minimizing can only lower the test value, so

\[
\min_t M(Q_\sharp,t)\le F(Q_\sharp,y_0,t_0)<0.
\tag{5}
\]

The global family theorem proves continuity, strict radius monotonicity,
and a unique zero of this minimum. Equations (4)--(5) therefore prove (1).

This argument supplies the exact ceiling comparison used in the
[outer-radius pullback](OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md).
It does not assert that the full global capture inequalities are already
hand-proved.
