# Candidate mismatch: from 3/200 to 1/1000

## 1. Statement and previously proved hypotheses

Set

\[
Q=3.915534138=\frac{1957767069}{500000000}.
\]

Use the cyclic roles \((H,G,A,B,T,D,E)\), numbered \(0,\ldots,6\),
and the quarter word \(k=(0,1,0,1,0,1,1)\). Each vertex may
independently be on either radial boundary, core or outer. The center
order and frame lift satisfy

\[
\sum_i\delta_i=2\pi,\qquad \delta_i>19/25,\qquad
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i=k_i\pi/2+d_i,
\quad |d_i|\le7/10.                                      \tag{1}
\]

Write \(u_i=\tan\alpha_i\). The closed tangent domains and retained
original separating axes are as follows. Axis numbers refer to (4),
before any reflection or reversal used in the support calculation.

| Role / outgoing edge | Tangent domain | Allowed original axes |
|---|---|---|
| H / HG | \([1/2,1]\) | \(1,3\) |
| G / GA | \([-4/5,-1/20]\) | \(1,2,3,4\) |
| A / AB | \([0,1]\) | \(1,3\) |
| B / BT | \([-1,0]\) | \(3,4\) |
| T / TD | \([1/20,4/5]\) | \(1,3\) |
| D / DE | \([-1,-1/2]\) | \(3,4\) |
| E / EH | \([-1,0]\) | \(1,2,3,4\) |

Let

\[
I=\{0,2,3,4,5\},\qquad S=\sum_{i\in I}|d_i|.
\]

**Theorem.** Under these hypotheses, \(S\le3/200\) implies
\(S<1/1000\).

Here G/T and H/D come from their established tangent exclusions;
E is normalized by the reflected reversal fixing E. The other signs
and the zero-quarter axis restrictions follow from the hand mismatch
bootstrap at \(S\le1/10\). The BT and DE restrictions follow from the
independently reviewed quarter-owner theorem at \(S\le3/200\).
The preceding mismatch theorem supplies \(S\le3/200\).

Both mixed edges retain all four original axes and their complete
frame-difference ranges \([-7/10,7/10]\). Consequently this theorem
does not assume mixed-owner capture or a tilt bound. Those are used
only after the conclusion \(S<1/1000\).

This statement concerns the radial-boundary representative at the fixed
ceiling Q. The separate fixed-ceiling transfer theorem connects it to
an original packing, retaining the actual separating witnesses. No
assertion that radial deformation preserves a vertex's tangent is used.

## 2. Boundary arcs and the continuous pair inequality

In its own frame a center has coordinates \((a,-\sigma b)\), where
\(0\le b\le a\), \(v=b/a\), and \(u=\sigma v\). The boundary equations
are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\qquad(0\le v\le6/7),\\
  &(a-1/2)^2+(b-1/2)^2=1/144\qquad(6/7\le v\le1).
\end{array}                                                   \tag{2}
\]

The immutable data list 456 closed rational arcs covering all 14
nonempty role/kind/sign domains. Every arc carries a rational affine
marker

\[
L=c+pa+qb.                                                  \tag{3}
\]

The sign is encoded in the coefficients. Core arcs are split at the
exact transition \(6/7\). At a shared endpoint choose one containing
arc for a vertex, and use that same marker on both incident edges.
All pairs of containing arcs are covered, so the sum of marker
differences vanishes even if formulas at a cut differ. A zero tangent
may use the nonempty sign branch of its stated closed domain.

For the source \((a,-\sigma b)\), target
\(R_\phi(A,-\tau B)\), and
\(W=(1+|\sin\phi|+|\cos\phi|)/2\), the four forward SAT margins are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.                 \tag{4}
\end{aligned}
\]

The preceding geometric theorems supply at least one nonnegative
margin among the declared original axes at each edge. Put

\[
h(x)=\frac{\sin x+\cos x-1}{2},\qquad
\beta_i=\begin{cases}1/20&i\in I,\\0&i\notin I.\end{cases}
\]

Every row supplies a rational multiplier \(\lambda\ge0\) and proves
on its complete state arcs and angle interval that

\[
\phi-\beta_i h(|d_i|)+L_s-L_t-\gamma_i-\lambda M_j>0. \tag{5}
\]

The exact edge constants are

\[
\gamma_i=.897595\quad(0\le i\le5),\qquad
\gamma_6=.8975925,\qquad
\Gamma=\sum_i\gamma_i=6.2831625=\frac{502653}{80000}.    \tag{6}
\]

For an actual nonnegative margin, (5) implies the corresponding
strict charged pair bound.

The continuous proof of (5) is the independently reviewed affine-arc
one-angle support lemma. Subtracting \(\lambda M_j\) separates both
state variables. Reflection and reversal reduce axes 2 and 3 to axes
4 and 1, changing the marker pair to \((-L_t,-L_s)\) and reversing
the signs. The source support has constant coefficients. The target
uses a certified monotone endpoint, both endpoints of a concave arc,
or the whole-circle support. Straight core sides always use endpoints.

For a circle centered at \((c_0,c_0)\) with radius \(R_0\), the latter
bound is

\[
Xa+Yb\ge c_0(X+Y)-R_0\sqrt{X^2+Y^2}.                  \tag{7}
\]

It is replaced by a rational polynomial using, for any rational
\(h_0>0\) and \(V\ge0\),

\[
\begin{aligned}
T(V)&=\frac{5h_0+15V/h_0-5V^2/h_0^3+V^3/h_0^5}{16},\\
T(V)-\sqrt V&=
\frac{(\sqrt V-h_0)^4(V+4h_0\sqrt V+5h_0^2)}{16h_0^5}
\ge0.                                                     \tag{8}
\end{aligned}
\]

Thus no uncomputed minimization over either boundary state remains.
Every endpoint monotonicity or concavity premise is checked by a
fixed polynomial inequality on the row's whole angle interval.

## 3. Fixed rational table and exhaustive cover

Each row has \(\phi=k\pi/2+r x\), \(r=\pm1\), and a declared
rational interval in \([0,7/10]\). Alternating Taylor bounds for
sine through degree 9 and cosine through degree 10, with exact
pointwise remainder intervals, give polynomial lower bounds.
The rational power-to-Bernstein identity proves nonnegative support
premises and strictly positive costs.

The verification has no search or adaptive subdivision: every arc,
row interval, support choice, multiplier and radical majorant is
already present in the fixed input. The complete replay gives:

| Object | Count |
|---|---:|
| Closed state arcs | 456 |
| Nonempty original-axis angle chains | 129,368 |
| Fixed one-angle rows | 144,709 |
| Premise and cost polynomials | 399,773 |
| Rational coefficient lower bounds | 3,183,184 |

The smallest printed cost coefficient lower bound is
\(3986139/100000000000000>0\).

Since the other six gaps exceed \(19/25\), (1) implies
\(19/25<\delta_i<710/113-114/25\). For source and target arc-angle
endpoints \([s_-,s_+]\) and \([t_-,t_+]\), all possible relative
angles lie in

\[
[19/25-s_++t_-,\;710/113-114/25-s_-+t_+]
\cap[k\pi/2-\rho_i,k\pi/2+\rho_i],                  \tag{9}
\]

where \(\rho_i=3/200\) on I and \(7/10\) on the mixed edges.
Directed rational arctangent and Machin bounds enclose the endpoints.
For every pair of arcs, every declared original axis and both angle
signs, the rows form a complete closed cover of (9), including
nonempty point intervals. The separate assembly auditor recomputes
the state unions, signed intersections and original-axis covers.

The compact report retains each polynomial's degree and a lower bound
for all its coefficients. The complete coefficients are uniquely
reproduced by the input and frozen verifier; their exact output hash is

```
ba5e037e9d9da8369526f546275fa7037477c6d0225c33c82a5df317f8a25924
```

## 4. Summation forces the final mismatch threshold

Choose a containing arc once per vertex and an actual separating axis
per edge. Sum (5). The markers cancel, and (1) gives
\(\sum_i\phi_i=2\pi\). Therefore

\[
2\pi-\frac1{20}\sum_{i\in I}h(|d_i|)>\Gamma.         \tag{10}
\]

On \([0,3/200]\), h is increasing and concave with h(0)=0. For
nonnegative numbers of total S, concavity gives

\[
\sum_i h(|d_i|)\ge h(S).                               \tag{11}
\]

Indeed, if S>0, each term is at least \((|d_i|/S)h(S)\);
if S=0 both sides vanish. If \(S\ge1/1000\), the alternating
sine and cosine bounds imply

\[
h(S)\ge h(1/1000)>
\frac{1/1000}{2}-\frac{(1/1000)^2}{4}-\frac{(1/1000)^3}{12}
=\frac{5996999}{12000000000}.                          \tag{12}
\]

For \(A_n(q)=\sum_{j=0}^n(-1)^j/((2j+1)q^{2j+1})\), Machin's
identity and the alternating series give the short rational bound

\[
2\pi<32A_6(5)-8A_3(239)<6.28318531.                    \tag{13}
\]

Finally the exact reserve is

\[
\Gamma+\frac1{20}\frac{5996999}{12000000000}-6.28318531
=\frac{522599}{240000000000}>0.                        \tag{14}
\]

Equations (10)--(14) contradict \(S\ge1/1000\), proving the theorem.

## 5. Reproduction and use in the complete proof

The immutable table and compact record are
`MISMATCH_015_TO_001_AFFINE_HAND_DATA.json` and
`MISMATCH_015_TO_001_AFFINE_HAND_COMPACT_REPORT.json`.
The frozen verifier `verify_mismatch_015_to_001_affine_hand.js` is
byte-identical to the independently reviewed conditional affine-arc
kernel, SHA-256

```
6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697
```

Run `python replay_mismatch_015_to_001_hand.py` to reproduce every
coefficient and compare the full-output hash and compact rows.
Use `--save-full` to retain the optional large report. Run
`python audit_mismatch_015_to_001_hand_assembly.py` for the separate
exact state, conditional-angle, original-axis and summation audit.
The independent review is recorded in the final manifest.

This conclusion meets exactly the input threshold of
`HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md`. Its already reviewed
mixed-owner and signed-error tilt theorems supply the nominal owner
pattern and \(.1<t<.16\). The automatic-slider terminal then proves
the sharp lower bound. The fixed-ceiling transfer carries that lower
bound to the original packing and retains the equality witnesses for
the separately proved classification. No smaller mismatch or center
proximity assumption is required.

Only the stated rational data, support lemma and fixed polynomial
identities are proof premises. The optimization used to propose the
markers and rows is not part of the theorem.
