# Same-side two-square cap obstruction for a full open near-axis frame neighborhood

Research continuation, 2026-10-12. This excludes a
**continuous interval of pairs of square frames** in the
still-open n=8 side-status branches. It is *not* a general
all-frame same-sign theorem and does not exclude every
remaining S2 or S4 configuration.

## Theorem (two freely positioned squares, near-axis frames)

Let two distinct unit squares of **independently chosen
orientations** have disjoint open interiors inside
\[
D_R,\qquad R^2\le q_+:=9789/2500,
\]
and suppose both are wholly contained in the same
outward cap
\[
\{y\ge h\},\qquad h\ge7/24.
\]

Write their centers as \(p_1,p_2\). Suppose the two
*transverse center coordinates* have the **same weak sign**:
\[
p_{1,x},p_{2,x}\ge0
\quad\text{or}\quad
p_{1,x},p_{2,x}\le0.
\]
Let \(\theta_i\in[-\pi/4,\pi/4]\) be each square's
unsigned-side-frame angle relative to the cap-aligned
horizontal/vertical axes, normalized modulo right angles.
Suppose both frames obey
\[
|\theta_1|,\ |\theta_2|\le1/3000\ \text{radians}.
\]

**Conclusion: these assumptions are incompatible.**
Equivalently, under the same-side-center and whole-cap
hypotheses, at least one actual square frame must have
nonzero axis deviation
\[
\boxed{\max(|\theta_1|,|\theta_2|)>1/3000.}        \tag{1}
\]
No assumption on a square-square physical contact is used.

## 1. A common axis-parallel inscribed square

For a unit square with frame angle
\(|\theta|\le1/3000\), its intersection of
two supporting frame-coordinate inequalities is
\[
|e\cdot(x-p)|\le1/2,\qquad
|f\cdot(x-p)|\le1/2.
\]
Any axis-parallel square centered at p with side
\[
t=\frac{3000}{3001}
=\frac{1}{1+1/3000}
\]
lies inside it: every displacement
\(v=(v_x,v_y)\) with \(|v_x|,|v_y|\le t/2\)
satisfies
\[
|e\cdot v|,\ |f\cdot v|
\le(t/2)(|\cos\theta|+|\sin\theta|)
\le(t/2)(1+|\theta|)
\le1/2.
\]
The last inequalities use \(\cos\theta\le1\),
\(|\sin\theta|\le|\theta|\).
Thus **each** of the two actual unit squares
contains a closed centered *axis-parallel*
square of common side t.

Both smaller squares lie in the same disk and
the same outward cap. Their open interiors
are disjoint since they are subsets of the
disjoint actual unit-square interiors.
Their centers are the actual unit-square
centers, so the same-side center-sign
hypothesis is preserved.

## 2. Exact two-square cap bound in a common axis frame

We prove a simple size-t lemma:

> If two axis-parallel squares of side \(t>0\) have
> disjoint open interiors, are wholly in the cap
> \(y\ge h\ge0\), and both center x coordinates
> have the same weak sign, the containing disk
> necessarily satisfies
> \[
> R^2\ge (h+t)^2+\frac{9t^2}{4}.                \tag{2}
> \]

Reflect the x axis if needed so both center
x coordinates are nonnegative.
For two disjoint axis-parallel t-squares,
their centers differ either by at least t
horizontally or by at least t vertically.

**Horizontal separation.** If
\(|x_1-x_2|\ge t\) and both \(x_i\ge0\),
one center has x coordinate \(\ge t\).
Its square has a vertex with
\(x\ge3t/2\) and
\(y\ge h+t\), because whole-cap membership
forces its center y coordinate \(\ge h+t/2\).
The squared norm of that true vertex is at
least \(9t^2/4+(h+t)^2\).

**Vertical separation.** If
\(|y_1-y_2|\ge t\), the top center y coordinate
is \(\ge h+3t/2\). Its actual square has a
vertex with \(y\ge h+2t\) and
\(x\ge t/2\) (its center x is nonnegative).
That vertex's squared norm is at least
\[
(h+2t)^2+t^2/4
=(h+t)^2+9t^2/4+2ht+t^2,
\]
which is strictly *larger* than the right side
of (2). Hence (2) holds in both cases,
including possible contact boundaries. QED.

## 3. A strict exact rational contradiction

Apply (2) to the two actual centered t-squares,
using \(h\ge7/24\) and \(t=3000/3001\).
Then
\[
R^2\ge
\left(\frac7{24}+\frac{3000}{3001}\right)^2
+\frac94\left(\frac{3000}{3001}\right)^2.
\]
Subtract the current disk ceiling:
\[
\begin{aligned}
&\left(\frac7{24}+\frac{3000}{3001}\right)^2
+\frac94\left(\frac{3000}{3001}\right)^2
-\frac{9789}{2500}\\
&\qquad=\frac{1435675009}{3242160360000}>0.
\end{aligned}
\]
Therefore \(R^2>9789/2500\), contradicting
the hypothesis. This proves (1). QED.

At exact parallelism \(t=1\), the same proof
gives the familiar sharper threshold
\[
R^2\ge(1+h)^2+9/4\ge2257/576
=9789/2500+1009/360000.
\]
The present note adds an explicit **open
two-frame neighborhood** with completely
arbitrary centers and no selected pair contact.

## Consequences for the n=8 status queue

For either **exclusive S2=(3+0,2+2)** or
**exclusive S4=(2+1,2+2)**, the nearer
2+2 whole cap has offset
\[
h_{\rm near}=1/2-|t_C|>7/24,
\]
by the already proved opposite-two-cap
capacity theorem (here \(t_C\) is the
central square's signed coordinate along
the 2+2 axis).

If the *two distinct* near-side square centers
lie in the same transverse weak half-plane,
their frames **cannot both lie within
1/3000 radians of the central-square axes**.
At least one of the two actual squares must
be more substantially tilted, or the
centers must be split across the transverse
origin diameter.

For the remaining S2/k=4 case, the separate
[HUMAN_MIXED_NEAR_CAP_POLARITY.md](HUMAN_MIXED_NEAR_CAP_POLARITY.md)
proves a stronger inner/outer *center-ray*
separation \(>3/4\) radians and, in the
same-*strict*-sign subcases, quantitative
inner/outer transverse center bounds. Neither
statement implies the other without its
additional hypotheses.

The theorem is **conditional on near-axis
square frames**; it makes **no** claim that
an arbitrary rotated same-sign cap pair
is impossible. The real S4/k=7 equality
construction and its continuous slider
freedoms remain valid. The unrestricted
global lower bound \(R_8\ge\widehat R\)
remains OPEN.

[verify_same_side_near_axis_cap.py](verify_same_side_near_axis_cap.py)
audits the final rational margin only, not the
geometric containment and separating proof or
any global eight-square theorem.
