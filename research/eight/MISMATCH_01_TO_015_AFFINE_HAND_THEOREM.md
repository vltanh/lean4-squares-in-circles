# Candidate mismatch: from 1/10 to 3/200

## 1. The conditional gate

Let the squared circle ceiling be the exact rational number

\[
Q=3.915534138=\frac{1957767069}{500000000}.
\]

Use the cyclic roles \((H,G,A,B,T,D,E)\), numbered \(0,\ldots,6\),
and the quarter word \(k=(0,1,0,1,0,1,1)\). Every vertex may
independently be on the core or outer radial boundary. Assume the
previously established center order and frame lift:

\[
\sum_i\delta_i=2\pi,\quad \delta_i>19/25,\quad
\phi_i=\delta_i+\alpha_{i+1}-\alpha_i=k_i\pi/2+d_i,
\qquad |d_i|\le7/10.                                      \tag{1}
\]

The adjacent squares are separated. Write \(u_i=\tan\alpha_i\),
and assume the following closed tangent domains:

| Role | Tangent domain |
|---|---|
| H | \([0,1]\) |
| G | \([-4/5,-1/20]\) |
| A | \([0,1]\) |
| B | \([-1,0]\) |
| T | \([1/20,4/5]\) |
| D | \([-1,0]\) |
| E | \([-1,0]\) |

Set \(I=\{0,2,3,4,5\}\) and \(S=\sum_{i\in I}|d_i|\).

**Theorem.** Under these hypotheses, \(S\le1/10\) implies
\(S<3/200\).

The G/T domains come from the four established tangent exclusions.
The signs at the other vertices follow from the hand mismatch bootstrap
at \(S\le1/10\). This theorem does not require the stronger H or D
cuts or a selected SAT owner: its table covers all four original
forward separating axes at every edge. The two mixed edges retain their
entire frame-difference range \([-7/10,7/10]\).

The statement concerns the boundary representative. Applying it to an
original packing uses the existing radial reduction and sharp-radius
pullback lemmas; this statement makes no assumption that the initial
radial deformation preserves a vertex's tangent.

## 2. Exact arcs and the continuous support inequality

In its own frame write a center as \((a,-\sigma b)\), with
\(0\le b\le a\), \(v=b/a\), \(u=\sigma v\). The two boundary
types are

\[
\begin{array}{ll}
O:&(a+1/2)^2+(b+1/2)^2=Q,\\
C:&a=7/12\quad(0\le v\le6/7),\\
  &(a-1/2)^2+(b-1/2)^2=1/144\quad(6/7\le v\le1).
\end{array}                                                   \tag{2}
\]

The data file lists 335 closed rational arcs, covering all 14 nonempty
role/kind/sign domains. Each arc carries an affine marker
\(L=c+pa+qb\) with rational coefficients. The sign is already
encoded in this marker's coefficients. Core arcs are split at the
exact transition \(6/7\).

At a shared arc endpoint choose a containing arc once for that vertex,
then use its marker on both incident edges. All such source/target
choices are covered, so the markers telescope even if two formulas
differ at a cut. A zero tangent may use the nonempty sign branch in
the stated closed domain.

For source \((a,-\sigma b)\), target \(R_\phi(A,-\tau B)\), and
\(W=(1+|\sin\phi|+|\cos\phi|)/2\), the four retained margins are

\[
\begin{aligned}
M_1&=\sigma b+A\sin\phi-\tau B\cos\phi-W,\\
M_2&=A-a\cos\phi+\sigma b\sin\phi-W,\\
M_3&=a\sin\phi+\sigma b\cos\phi-\tau B-W,\\
M_4&=a-A\cos\phi-\tau B\sin\phi-W.                 \tag{3}
\end{aligned}
\]

The common-point axis theorem supplies a nonnegative margin from (3).
Put

\[
h(x)=\frac{\sin x+\cos x-1}{2},\qquad 0\le x\le7/10,
\quad \beta_i=\begin{cases}1/200&i\in I,\\0&i\notin I.\end{cases}
\]

Every fixed row gives a nonnegative rational multiplier \(\lambda\)
and proves, on its complete source arc, target arc and angle interval,

\[
\phi-\beta_i h(|d_i|)+L_s-L_t-\gamma_i-\lambda M_j>0. \tag{4}
\]

The seven exact constants are

\[
(\gamma_0,\ldots,\gamma_6)=
(.8975928,.8975928,.8975928,.8975928,.8975928,
 .89759275,.8975917).
                                                               \tag{5}
\]

Their sum is \(\Gamma=6.28314845=125662969/20000000\).
Because \(M_j\ge0\), (4) implies the corresponding strict charged
pair bound.

For completeness, the proof mechanism of (4) is the independently
reviewed affine-arc one-angle kernel. Subtracting \(\lambda M_j\)
separates both state coordinates. Reflection and reversal reduce axes
2 and 3 to axes 4 and 1, replacing the markers by \((-L_t,-L_s)\)
and reversing their signs. The source support has constant coefficients.
The target uses one of four exhaustive lower bounds: a monotone lower
endpoint, a monotone upper endpoint, both endpoints of a concave arc,
or the whole-circle support. Straight core sides always use endpoints.

For a circle with center \((h_0,h_0)\) and radius \(R_0\), the last
support is

\[
Xa+Yb\ge h_0(X+Y)-R_0\sqrt{X^2+Y^2}.                 \tag{6}
\]

Its radical is replaced by a rational polynomial majorant. For \(V\ge0\)
and a row's positive rational \(h_0'\),

\[
\begin{split}
T(V)&=\frac{5h_0'+15V/h_0'-5V^2/(h_0')^3+V^3/(h_0')^5}{16},\\
T(V)-\sqrt V
&=\frac{(\sqrt V-h_0')^4(V+4h_0'\sqrt V+5(h_0')^2)}{16(h_0')^5}
\ge0.                                                       \tag{7}
\end{split}
\]

Thus there is no omitted minimization over either state. The endpoint
monotonicity or concavity premises are themselves fixed polynomial
inequalities on the full declared angle interval.

## 3. Fixed polynomial table and complete domain cover

Write \(\phi=k\pi/2+r x\), \(r=\pm1\), on the row's fixed
rational interval inside \([0,.7]\). Alternating Taylor bounds for
\(\sin x\) through degree 9 and \(\cos x\) through degree 10,
with pointwise remainder coefficients in their rational intervals,
give lower polynomials. The exact power-to-Bernstein change of basis
proves nonnegative premises and strictly positive costs.

The data contain a fixed finite table; its verifier performs no search
or adaptive subdivision. Its complete replay has the following counts:

| Object | Count |
|---|---:|
| Closed state arcs | 335 |
| Nonempty original-axis angle chains | 101,280 |
| Fixed one-angle rows | 107,196 |
| Premise and cost polynomials | 292,119 |
| Rational coefficient lower bounds | 2,468,184 |

The smallest printed cost coefficient lower bound is
\(576987/25000000000000>0\).

The center-order inequalities in (1) imply
\(19/25<\delta_i<710/113-114/25\). For source and target arc
angle endpoints \([s_-,s_+]\) and \([t_-,t_+]\), the entire possible
relative angle therefore lies in

\[
[19/25-s_++t_-,\;710/113-114/25-s_-+t_+]
\cap[k\pi/2-\rho_i,k\pi/2+\rho_i],                 \tag{8}
\]

where \(\rho_i=1/10\) on \(I\) and \(7/10\) on the mixed edges.
The table includes complete closed covers of (8) for every pair of arcs,
every original axis and both angle signs, including nonempty point
intervals. Directed rational arctangent and Machin bounds supply the
outward endpoints. The separate assembly script recomputes these bounds
with a different rational square-root mesh and checks all unions again.

The compact report records every polynomial's degree and a lower bound
for all its coefficients. The full coefficient lists are uniquely
reproduced from the data and frozen kernel. Their exact output SHA-256 is

```
014c06a9373077acb965a78690669b863214eb42dc650f30619eb63553e60df3
```

## 4. Summation and the mismatch contraction

Choose one containing arc per vertex and an actual separating axis per
edge. Summing (4), the markers and local state angles telescope, giving

\[
2\pi-\frac1{200}\sum_{i\in I}h(|d_i|)>\Gamma.        \tag{9}
\]

On \([0,1/10]\), \(h\) is increasing and concave with \(h(0)=0\).
For nonnegative \(x_j\) of total \(S\le1/10\), concavity gives
\(h(x_j)\ge(x_j/S)h(S)\) when \(S>0\). Hence

\[
\sum_jh(x_j)\ge h(S).                                \tag{10}
\]

The same conclusion holds when \(S=0\). If \(S\ge3/200\), then
the alternating sine and cosine inequalities give

\[
h(S)\ge h(3/200)>
\frac{3/200}{2}-\frac{(3/200)^2}{4}-\frac{(3/200)^3}{12}
=\frac{238191}{32000000}.                            \tag{11}
\]

The needed rational upper bound is \(2\pi<6.28318531\). It follows
directly from Machin's identity: if
\(A_n(q)=\sum_{j=0}^n(-1)^j/((2j+1)q^{2j+1})\), then

\[
2\pi<32A_6(5)-8A_3(239)<6.28318531.                  \tag{12}
\]

The last comparison is a single positive rational difference, checked
by the companion assembly script. Finally,

\[
\Gamma+\frac1{200}\frac{238191}{32000000}-6.28318531
=\frac{2287}{6400000000}>0.                          \tag{13}
\]

Equations (9)--(13) contradict \(S\ge3/200\), proving the theorem.

## 5. Reproduction and review

The immutable input and compact report are
`MISMATCH_01_TO_015_AFFINE_HAND_DATA.json` and
`MISMATCH_01_TO_015_AFFINE_HAND_COMPACT_REPORT.json`. The frozen
verifier is byte-identical to the independently reviewed conditional
affine-arc kernel, SHA-256

```
6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697
```

Run `python replay_mismatch_01_to_015_hand.py` to reconstruct every
coefficient and compare the recorded full-output hash and compact rows.
Add `--save-full` to retain the optional full report. Run
`python audit_mismatch_01_to_015_hand_assembly.py` to check the exact
state/angle unions, scope, hashes and rational contraction separately.
The independent reviewer's audit is bound in the final manifest when
complete. Discovery proposals and intermediate refinements are not
theorem premises or part of the immutable proof input.
