# A universal physical pair cap retaining the main endpoint's tilt

November 2, 2026. Computer-assisted discovery followed by the complete
hand reduction below, a rational cover of all scalar cases, and a separate
directed-integer replay. No Lean or CI. The root agent independently
reviewed the full physical reduction and freshly replayed all 404 leaves
and damaged controls; its acceptance is recorded in
`root_wide_pair/NEXT_GATE_ROOT_INDEPENDENT_REVIEWS.md`.

This is a reusable original-pair inequality. It does not by itself close
the complete `001/00` or `100/00` nine-square mask. The exact eight-square
control described at the end prevents that mistaken inference.

## 1. The original physical theorem

Put

\[
 Q=1105/256,\quad a=46,\quad b=27/2,\quad k=207/16,
 \qquad T=211/4.
\]

Let M and B be two original physical unit squares, with disjoint open
interiors, contained in the disk centered at zero with radius
\(R\le\sqrt Q\). Choose any unit direction e. Write

\[
 h_S(v)=\frac{|v\cdot u_S|+|v\cdot v_S|}{2},\qquad
 \alpha_M=\max(|e\cdot u_M|,|e\cdot v_M|),\quad
 \beta_M=\min(|e\cdot u_M|,|e\cdot v_M|).
\]

Thus \(\alpha_M^2+\beta_M^2=1\) and
\(\alpha_M\ge\beta_M\ge0\). Set

\[
 \tau_M=\max\{4\beta_M,\ 10\beta_M-46(1-\alpha_M)\}.
 \tag{1}
\]

**Theorem.** The unchanged original pair satisfies

\[
 \boxed{46[-e\cdot c_M-h_M(e)]
       +\frac{27}{2}[-e\cdot c_B-h_B(e)]+\tau_M\le\frac{211}{4}.}
 \tag{2}
\]

The inequality is strict when \(R<\sqrt Q\). Neither original frame,
center, physical separator owner, nor height is restricted. The names M
and B distinguish their weights; the orientation toll is on M.

## 2. Retain the physical owner and every original frame

The physical separating-axis theorem supplies a signed unit normal n,
parallel to an axis of M or B, with

\[
 n\cdot(c_B-c_M)\ge h_M(n)+h_B(n).
\]

Set \(c=e\cdot n\), \(s=\sqrt{1-c^2}\). Reflection perpendicular to e
allows the nonnegative sine without changing (2). Circle support in the
directions \(-ae-kn\) on M and \(-be+kn\) on B gives

\[
 \operatorname{load}\le H(c)-P_M-P_B,
\]

where

\[
 L_w(c)=\sqrt{w^2+k^2+2wkc},\qquad
 H(c)=\sqrt Q\,[L_a(c)+L_b(-c)],
\]

\[
 P_M=a h_M(e)+h_M(ae+kn)+k h_M(n),\qquad
 P_B=b h_B(e)+h_B(be-kn)+k h_B(n).
 \tag{3}
\]

Replacing R by \(\sqrt Q\) is strict for a smaller disk because the
sum of these two vector lengths is positive.

The already accepted physical pair proof identifies each P as the
side-length sum of the bounding rectangle of its three-vector triangle.
For an unmodified free frame its minimum is achieved when a triangle edge
is parallel to a frame axis. The three values, written without branch
choices, are

\[
 E_w(c)=w+k[s+\max(c,0)],
\]

\[
 N_w(c)=\frac{w|c|+2ws+|wc+k|+k}{2},
\]

\[
 D_w(c)=\frac{L_w(c)^2+w^2+wkc+2wks+k|wc+k|}{2L_w(c)}.
 \tag{4}
\]

If that square owns n, its value is exactly N. The signed c in the B
expressions is -c.

### The two main-frame toll branches preserve the finite reduction

Triangle inequality for centered support implies

\[
 P_M\ge 2a h_M(e)=a(\alpha_M+\beta_M).
 \tag{5}
\]

Partition the orientation circle at the triangle's projection-sign
changes and at the 45-degree folded-angle boundaries. On each interval
\(\alpha_M,\beta_M\) are fixed sine/cosine expressions, and P is linear
in the same expressions. For the first toll branch,

\[
 (P_M-4\beta_M)''=-P_M+4\beta_M
   \le-a\alpha_M-(a-4)\beta_M<0.
\]

For the second branch,

\[
 [P_M-10\beta_M+a(1-\alpha_M)]''
   =-P_M+10\beta_M+a\alpha_M
   \le-(a-10)\beta_M\le0.
\]

Each branch therefore has its minimum at an interval endpoint. The
minimum of their pointwise minimum is also attained among those same
endpoints. These are exactly the frames parallel to e, n, ae+kn, or the
45-degree folded-angle frame. No physical chirality or separator owner is
dropped by this reduction.

For the owned frame put

\[
 (\alpha_N,\beta_N)=(\max(|c|,s),\min(|c|,s)).
\]

For the main diagonal frame put

\[
 (\alpha_D,\beta_D)=
 \frac{(\max(a+kc,ks),\min(a+kc,ks))}{L_a(c)}.
 \tag{6}
\]

Here \(a+kc>0\) because \(a>k\). The 45-degree value is

\[
 P_{45,a}(c)=
 \frac{a+\max(a+kc,ks)+k\max(|c|,s)}{\sqrt2},
 \quad \alpha_{45}=\beta_{45}=1/\sqrt2.
 \tag{7}
\]

## 3. The complete scalar union

Using \(\tau(\alpha,\beta)=\max(4\beta,10\beta-a(1-\alpha))\), define

\[
 \begin{aligned}
 F_0&=T-H+N_a(c)+E_b(-c)-\tau(\alpha_N,\beta_N),\\
 F_1&=T-H+N_a(c)+N_b(-c)-\tau(\alpha_N,\beta_N),\\
 F_2&=T-H+N_a(c)+D_b(-c)-\tau(\alpha_N,\beta_N),\\
 F_3&=T-H+D_a(c)+N_b(-c)-\tau(\alpha_D,\beta_D),\\
 F_4&=T-H+P_{45,a}(c)+N_b(-c)-\tau(1/\sqrt2,1/\sqrt2).
 \end{aligned}
 \tag{8}
\]

M-owned normals give the first three rows. B-owned normals give the
second, fourth and fifth rows, together with
\(T-H+E_a(c)+N_b(-c)\ge0\); that last row has zero main toll and is
already proved in the original physical pair cap. This is the entire
physical owner/frame union.

### The two equality neighborhoods

The original support proof gives
\(H(c)\le H(0)+(k/2)c\),
\(H(0)=a+b+2k+T\), and \(s\ge1-c^2\).
For \(|c|\le1/32\), the N branches in (4) are fixed,
\(\beta_N=|c|\), and \(\tau\le10|c|\).
Substitution in (8) gives the following exact lower bounds:

| Row and sign | Lower bound |
|---|---:|
| F0, \(0\le c\le1/32\) | \((14177/512)c\) |
| F0, \(-1/32\le c\le0\) | \((3873/512)|c|\) |
| F1, \(0\le c\le1/32\) | \((1771/64)c\) |
| F1, \(-1/32\le c\le0\) | \((519/64)|c|\) |

The coefficients are respectively

\[
 a-k/2-10-(a+k)/32,\quad 3k/2-10-(a+k)/32,
\]

\[
 a-k/2-10-(a+b)/32,\quad b+k/2-10-(a+b)/32.
\]

All are positive, so the shared point c=0 and both closed neighborhood
boundaries are covered.

## 4. Complete exact complement table

`main_endpoint_tilt_toll_cover.json` records the complete binary trees.
Their strict leaf counts and rounded-down rational reserves are:

| Row | Closed root | Leaves | Lower bound at every leaf |
|---|---|---:|---:|
| F0 | \([-1,-1/32]\) | 33 | \(8255/10^6\) |
| F0 | \([1/32,1]\) | 19 | \(163167/10^6\) |
| F1 | \([-1,-1/32]\) | 33 | \(49722/10^6\) |
| F1 | \([1/32,1]\) | 21 | \(248045/10^6\) |
| F2 | \([-1,1]\) | 60 | \(201265/10^6\) |
| F3 | \([-1,1]\) | 229 | \(5367/10^6\) |
| F4 | \([-1,1]\) | 9 | \(1211735/10^6\) |

All 404 leaves, 801 nodes, maximum depth 14, passed a separate exact
replay. The producer uses rational intervals with outward 80-bit square
roots and evaluates both the piecewise and absolute-support forms. The
independent checker uses outward 64-bit integer dyadic intervals and
reconstructs (4) directly, importing no producer code. Every split retains
both closed children; there is no omitted endpoint or unresolved frontier.

The least exact replayed reserve is

\[
 \frac{49504665116902281}{9223372036854775808}>0.
\]

Certificate SHA256:
`5fa9873f9918be06e08dfaf3bcac6b7962c8494f620ae841e4e2f8a92b4ceaf5`.
Four deliberately damaged controls were rejected: a changed root, an
unknown split rule, an omitted child, and a false single-leaf whole root.
The complete printed rational leaf appendix is
`MAIN_ENDPOINT_TILT_TOLL_COMPLETE_RATIONAL_TABLE.md`.

The analytic neighborhoods, complete complement table, and the inherited
zero-toll row prove every row of the physical union, hence (2).

## 5. Safe use together with existing shoulder tolls

Let \(\tau_B\) be any separately accepted shoulder toll for this same
original weighted pair. Combining the two inequalities permits

\[
             \operatorname{load}+\max(\tau_M,\tau_B)\le T.
 \tag{9}
\]

Adding the two tolls is not justified. The two separate proofs use the same
available support deficit. In particular no summed-toll assertion is a
premise of the weak-outer-mask work.

For the original `001/00` chain A,B,C,D and actual short chain E,F,G,
the two endpoint caps now imply the genuine necessary inequality

\[
 46(x_D-x_A-h_A-h_D)+\frac{27}{2}(x_G-x_E-h_E-h_G)
       +\tau_A+\tau_D\le\frac{211}{2}.
 \tag{10}
\]

Each toll belongs to a different original endpoint pair, so the addition
in (10) is legitimate. Reversal gives the identical `100/00` consequence.
All other originals, including the ninth square, remain part of the mask.

## 6. Why this remains a gate, not a complete mask closure

`verify_eight_original_cone_obstruction.py` gives a corrected version of
the earlier exact eight-square obstruction. It keeps all earlier x
coordinates and frames and changes only

\[
       y_A=17/50,\qquad y_B=1/10+110/101.
\]

The independent rational computation verifies 32 corners, all 28 physical
pairs and all five designated cone/bit comparisons. It has mask `100/00`,
and exact simultaneous chain reversal gives `001/00`. Its smallest
strict corner reserve is \(430373/16160000\). Thus even all original
seven witness squares plus one arbitrary eighth square do not imply Q.
Any complete closure must use the ninth physical original or an equivalent
proved consequence. Equation (10) does not change a fixed-mask or
positional-root count by itself.
