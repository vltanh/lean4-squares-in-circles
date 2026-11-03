# A three-link replacement row with inward endpoint tilts

November 2, 2026, America/Chicago. Complete pen-and-paper reduction after numerical
exploration of the scalar owner problem. No Lean, Lake, or CI.
The numerical exploration is not a premise. Every intermediate square
frame and every owned physical separating axis is retained.

## 1. A global-angle four-original row theorem

Let P0,P1,P2,P3 be four distinct, physically interior-disjoint unit
squares, with original centers in strict horizontal order. In the
unchanged coordinate frame, suppose

\[
 U=|y_1-y_0|+|y_2-y_1|+|y_3-y_2|\le\frac13.
 \tag{1}
\]

For each original, fold only the representation of its square frame:
\(t_i=|\tan\theta_i|\in[0,1]\),
\(r_i=\sqrt{1+t_i^2}\),
\(\alpha_i=1/r_i\), \(\beta_i=t_i/r_i\), and
\(h_i=(\alpha_i+\beta_i)/2\).
Define the normalized signed endpoint toll function

\[
 \sigma(t)=\frac{1+(23/32)t}{\sqrt{1+t^2}}-1.
 \tag{2}
\]

Then the following purely physical row inequality holds, independently
of the signs of all four original frames:

\[
 \boxed{x_3-x_0-h_0-h_3+\sigma(t_0)+\sigma(t_3)\ge2.}
 \tag{3}
\]

Equality in (3) forces all four original squares to be aligned with
the coordinate axes and every consecutive horizontal center gap to
equal one. The signs of the endpoint frames matter only when (3) is
paired with signed circle caps in Section 5. No small-angle assumption,
local center cylinder, or actual projection link is needed for (3).

## 2. Every physical link supplies an owner and a width difference

For consecutive originals let \(d=x_{i+1}-x_i>0\) and
\(v=y_{i+1}-y_i\). Their original inscribed open disks of radius
one half give

\[
 d\ge\sqrt{1-v^2}\ge\frac{2\sqrt2}{3}>|v|.
\]

Choose any actual physical owned separating axis of the two squares,
and let s be its owner's folded slope. The complete owned-support
estimate in Section 1 of
`WEAK_OUTER_NUMERIC_NEAR_HORIZONTAL_REPLACEMENT_ROW_HAND_TERMINAL.md`
gives

\[
 d\ge1+|h_i-h_{i+1}|+\sqrt{1+s^2}-1-|v|s.
 \tag{4}
\]

That estimate retains both owners, every sign, and both shallow and
steep owned axes. To recall why a steep axis is included, its maximum
possible center projection is
\(\beta d+\alpha|v|\le\alpha d+\beta|v|\), since
\(d\ge|v|\). Centered square support is unchanged by a quarter turn,
and the support sum is at least
\(1+\alpha|h_i-h_{i+1}|\). Division by \(\alpha>0\) gives (4).

Choose one physical owner for each of the three links, and let their
folded slopes be \(s_1,s_2,s_3\). Put

\[
 s=\max(s_1,s_2,s_3),\qquad
 V=|h_0-h_1|+|h_1-h_2|+|h_2-h_3|.
\]

At least one of the original four squares has folded slope s. The
triangle inequality along the original row, split at that square,
therefore gives

\[
 V\ge |h_0-h(s)|+|h_3-h(s)|.
 \tag{5}
\]

The same owner may be used twice, and the square of slope s may be an
endpoint. Neither circumstance changes (5). Also,

\[
 \sum_{j=1}^3(\sqrt{1+s_j^2}-1)\ge\sqrt{1+s^2}-1,
 \qquad
 \sum_{j=1}^3 |v_j|s_j\le Us\le s/3.
 \tag{6}
\]

## 3. A complete scalar endpoint payment

Write \(r(t)=\sqrt{1+t^2}\),
\(h(t)=(1+t)/(2r(t))\), and

\[
 f(t)=\sigma(t)-h(t)+\frac12
     =\frac{\alpha(t)}2+\frac7{32}\beta(t)-\frac12.
\]

For fixed \(s\in[0,1]\), put

\[
 K(s)=\min\left\{f(s),\ \sigma(1)+\frac12-h(s)\right\}.
 \tag{7}
\]

### 3.1. Endpoint reduction

For every \(t\in[0,1]\),

\[
 f(t)+|h(t)-h(s)|\ge K(s).
 \tag{8}
\]

The function h is increasing. If \(t\le s\), the left side is

\[
 h(s)-\frac12-\frac9{32}\beta(t)
 \ge h(s)-\frac12-\frac9{32}\beta(s)=f(s).
\]

If \(t\ge s\), it is
\(\sigma(t)+1/2-h(s)\). In the angle
\(\vartheta=\arctan t\), the function
\(\sigma=\cos\vartheta+(23/32)\sin\vartheta-1\)
is strictly concave on \([0,\pi/4]\). Its minimum on
\([\arctan s,\pi/4]\) is therefore at an endpoint, proving (8).

### 3.2. The two scalar branches

For every \(s\in[0,1]\),

\[
 \boxed{2K(s)+\sqrt{1+s^2}-1-s/3\ge0,}
 \tag{9}
\]

and the inequality is strict if \(s>0\).

For the first entry \(K=f(s)\), put \(r=\sqrt{1+s^2}\).
Multiplication of the left side of (9) by r gives exactly

\[
 (r-1)^2+s\left(\frac7{16}-\frac r3\right).
 \tag{10}
\]

If \(r\le21/16\), both terms are nonnegative and the first is
positive for s>0. If \(r\ge21/16\), use \(s\le1\) and
\(r\le\sqrt2<3/2\) to bound (10) strictly from below by

\[
 \frac{25}{256}-\frac1{16}=\frac9{256}>0.
\]

For the second entry \(K=\sigma(1)+1/2-h(s)\), the left side of
(9) is

\[
 2\sigma(1)-\left(\frac{s-s^2}{\sqrt{1+s^2}}+\frac s3\right).
 \tag{11}
\]

The bracket is strictly less than 5/12 on [0,1]. Here is a complete
rational check. First,
\(\sqrt{1+s^2}\ge1+s^2/3\), since the difference of squares is
\(s^2/3-s^4/9\ge0\). Hence it suffices to prove

\[
 \frac{3(s-s^2)}{3+s^2}+\frac s3<\frac5{12}.
\]

After multiplication by the positive denominator \(12(3+s^2)\),
this is the positivity of

\[
 p(s)=15-48s+41s^2-4s^3.
\]

On [0,1], \(p''(s)=82-24s\ge58\). At \(s_0=2/3\),
\(p(s_0)=1/27\) and \(p'(s_0)=4/3\). The quadratic lower support
and completing the square give

\[
 p(s)\ge\frac1{27}+\frac43(s-2/3)+29(s-2/3)^2
       \ge\frac1{27}-\frac4{261}=\frac{17}{783}>0.
 \tag{12}
\]

Finally,

\[
 2\sigma(1)=\frac{55\sqrt2}{32}-2>\frac5{12},
\]

because the equivalent positive-root comparison
\(165\sqrt2>232\) has squared reserve
\(2\cdot165^2-232^2=626>0\).
Thus (11) is strictly positive on its entire domain. This proves (9)
including both possible minima in (7), every boundary face, and its
stated strictness.

## 4. Sum the three unchanged physical links

Adding (4), subtracting the two endpoint widths, and adding their
tolls shows that the left side of (3), minus two, is at least

\[
 V+f(t_0)+f(t_3)
 +\sum_{j=1}^3(\sqrt{1+s_j^2}-1)-\sum_{j=1}^3|v_j|s_j.
\]

Equations (5), (8), (6), and (9), in that order, bound this by zero
from below. This proves (3).

If equality holds, (9) forces s=0. Therefore each chosen owner is
aligned and both sums involving \(s_j\) vanish. Also \(f(t)>0\)
for \(t>0\): in the angle variable,
\(2f=\cos\vartheta+(7/16)\sin\vartheta-1\) is strictly concave,
zero at 0, and positive at \(\pi/4\), where its positivity is
\(23\sqrt2>32\), with squared reserve 34. Consequently equality
forces \(t_0=t_3=0\) and V=0. Every h_i is then one half, so all
four original squares are aligned. Their individual vertical gaps
are at most one third, so physical nonoverlap forces every horizontal
gap to be at least one. Equality in (3) makes the total gap three;
all three gaps are exactly one.

## 5. Complete analytic terminal in the original weak-outer caller

Retain the original-nine strict `001/00` predicate at
\(R^2\le Q=1105/256\), normalized by
\(x_D-x_C\ge y_D-y_C\ge2/3\). Let H,I be the two distinct unchanged
extras. Suppose

\[
 x_A\le x_H\le x_I\le x_D,
 \qquad
 |y_H-y_A|+|y_I-y_H|+|y_D-y_I|\le\frac13,
 \tag{13}
\]

and the signed original A frame is nonpositive while the signed
original D frame is nonnegative. The x ties in (13) are impossible:
the corresponding vertical gap is at most one third, whereas two
original centers must be at distance at least one. Thus the strict
horizontal-order hypotheses of (3) are satisfied.

The independently established original orders and overlap bounds are

\[
 y_E>y_A,\quad |x_E-x_A|<1,
 \qquad y_G>y_D,\quad |x_G-x_D|<1.
\]

Hence every usable A-to-E or D-to-G physical owned normal points
upward. The signed original caps therefore supply, respectively,

\[
\begin{split}
 46(-x_A-h_A)+\tfrac{27}2(-x_E-h_E)+46\sigma(t_A)&\le\tfrac{211}4,\\
 46(x_D-h_D)+\tfrac{27}2(x_G-h_G)+46\sigma(t_D)&\le\tfrac{211}4.
\end{split}
 \tag{14}
\]

For the right cap this is the horizontal reflection of the signed
left cap; its nonnegative original D tilt becomes nonpositive in
that reflection. These are separate inequalities on the two
distinct original endpoint pairs. No two tolls for a single pair
are added.

The three-link theorem (3) bounds the adjusted A-to-D span with its
two tolls by at least two. The actual E/F and F/G comparisons give
\(x_G-x_E-h_E-h_G\ge2h_F\ge1\). Adding (14) thus forces equality
in all these inequalities, since \(2\cdot46+27/2=211/2\).
In particular the new row is aligned and \(x_D-x_A=3\).

There is a short way to exclude this equality inside the original
strict mask. The original A/B and B/C actual links and C/D cone-inset
comparison give

\[
\begin{split}
 3=x_D-x_A
 &\ge h_A+2h_B+h_C+g_C+g_D\\
 &=1+2h_B+(h_C+g_C)\ge3,
\end{split}
 \tag{15}
\]

where the middle equality uses the already forced original A,D
alignment. Since \(h_B\ge1/2\) and

\[
 h_C+g_C-1=h_C+\frac1{4h_C}-1
            =\frac{(2h_C-1)^2}{4h_C}\ge0,
\]

equality in (15) forces B and C aligned as well. The original C,D
cone says \(d\ge|v|\), and the strict weak bit now says d<1.
Two aligned unit squares cannot be physically disjoint when both
coordinate center gaps are less than one. This is the contradiction.

Thus the entire closed region (13), with the two stated endpoint
signs, is excluded even at Q. The result is global in all nine original
angles and retains all original physical constraints. It is not a
claim that every remaining original-nine configuration enters (13).

## 6. Exhaustive necessary escape alternatives

After sorting only the two unrestricted extra labels so x_H<=x_I,
the complement of (13) in the inward-endpoint sign domain is covered
by

\[
 x_H\le x_A,\qquad x_I\ge x_D,
\]

or one of the eight closed signed inequalities

\[
 \epsilon_1(y_H-y_A)+\epsilon_2(y_I-y_H)
   +\epsilon_3(y_D-y_I)\ge\frac13,
 \qquad (\epsilon_1,\epsilon_2,\epsilon_3)\in\{-1,1\}^3.
\]

This cover follows from the maximum formula for the sum of three
absolute values. It deliberately retains all shared boundary faces.
A caller may instead invoke (13) directly when every point of its
exact necessary box satisfies that theorem. A floating candidate
near the row is not a proof that its whole box lies there.

The exact scalar companion
`weak_outer_inward_three_link_row_arithmetic.py` checks every new
rational identity and squared-root reserve. The complete continuous
support, concavity, equality, and original-caller arguments are the
ones given above. No whole-mask count is changed by this component
alone.
