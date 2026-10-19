# Independent review of the middle mismatch contraction

**Result: PASS.** The continuous scope, signed-range interpretation,
complete state/angle unions and exact contraction argument pass independent
review. The completed fixed coefficient replay is bound to the immutable
DATA and the previously reviewed kernel. Every explicit coefficient list
was additionally scanned for its exact minimum, positivity and ordered
row index. This is a complete review of the stated conditional mismatch
theorem; it does not claim a second derivation of its polynomial table.

The independent union check detected the one missing angle group in the
provisional `middle026_hand_v2.json`: `(edge 0, source 35, target 143,
original axis 1, r=-1)`. The replacement fixed DATA, hash
`3230d71cdb3f1aa513aa74de04dc49429bb6ff2759a115cd55d98b160e1fedf4`,
now covers all 123,168 required original-axis angle chains with 401 arcs
and 131,255 fixed rows. Its complete coefficient replay and all strict
cost inequalities pass. No earlier incomplete report is used.

## 1. Continuous theorem and exact hypotheses

The proved implication is

\[
S\le13/50\quad\Longrightarrow\quad S<1/10
\]

for a boundary neighbor cycle at
\(Q=1957767069/500000000\), with cyclic roles `(H,G,A,B,T,D,E)`
and quarter word `0101011`. Core and outer radial types are independent
at every vertex. The existing center-order and frame theorems supply
\(\delta_i>19/25\), \(\sum_i\delta_i=2\pi\), and signed frame
differences in \([-7/10,7/10]\).

The tangent domains are H in \([1/2,1]\), G in \([-4/5,-1/20]\),
A and B each in \([-1,1]\), T in \([1/20,4/5]\), D in
\([-1,-1/2]\), and E in \([-1,0]\). Both A/B signs remain explicit.
All four original forward separating axes are included. Neither the
later A/B sign conclusion nor a quarter-owner conclusion is used as an
input.

The fixed G/T/H/D cuts and E normalization come from preceding gates.
The coarse printed-reserve theorem gives \(S<13/50\), which is stronger
than this stage's closed input bound. Once this stage is proved, the
mismatch sign lemma applies at \(S<1/10\), and the already reviewed
\(1/10\)-to-\(3/200\) theorem accepts those signs and weaker H/D
domains. This ordering has no circular owner or sign assumption.

## 2. State arcs, markers and original-angle ranges

The declared domains have 18 nonempty role/kind/sign pieces. Each core
curve is split at \(b/a=6/7\) into its side segment and corner arc.
All arc endpoints are closed. A/B zero-tangent states may choose either
available sign representation once per vertex. At any marker cut, choose
one containing arc and use that same marker on both incident edges.
Covering every source/target arc combination then makes the cyclic marker
sum telescope even if the alternative marker formulas differ at a cut.

With \(I=\{0,2,3,4,5\}\), the input bound implies
\(|d_i|\le13/50\) on \(I\). The other two edges keep their full
\([-7/10,7/10]\) difference interval. These restrictions are imposed
on the original directed edge before normalizing target-owned axes.

The independent checker computes the necessary relative-angle enclosure

\[
\left[19/25-s_++t_-,\;
710/113-114/25-s_-+t_+\right]
\]

from the source and target state-angle endpoints. It intersects this
with \(\phi=k\pi/2+r x\), \(x\ge0\), and the stated original
signed-difference interval. For \(r=-1\), the latter interval is
negated with its endpoints reversed. Every nonempty resulting interval,
including an isolated endpoint, must be covered separately for all four
original axes.

The arctangent bounds are independently reconstructed using

\[
\arctan v=\arctan(1/2)+
\arctan\!\left(\frac{2v-1}{v+2}\right),\qquad 0\le v\le1,
\]

with alternating rational partial sums and outward denominator
\(10^{26}\). This uses neither the production square-root mesh nor
the author's geometric-cover routine.

The complete independent required-chain counts for the replacement are
13,828, 32,240, 14,424, 28,756, 14,204, 11,520 and 8,196 on edges
0 through 6. All 18 state unions and all seven angle unions pass, and no
required point interval is dropped by the check. The actual replacement
has no isolated point chain under this independent enclosure.

## 3. Pair inequality and exact cyclic contraction

The same independently reviewed conditional affine-arc kernel is used.
Its four true SAT margins have the stated signs. For an actual separator,
\(M_j\ge0\), and every nonnegative row multiplier converts

\[
\phi-\beta_i h(|d_i|)+L_s-L_t-\gamma-\lambda M_j>0
\]

into the required charged pair lower bound. The state supports range over
entire arcs; endpoint monotonicity, concavity and circle-majorant premises
are part of the fixed univariate proof. A side segment is not treated as
a circle. The charge remains attached to its original edge when the
owner normalization reverses and reflects the pair.

Here \(\gamma=448791/500000\) and \(\beta_i=1/400\) on \(I\),
zero otherwise. Every required row is proved, so consistent arc and
separator choices give

\[
2\pi>7\gamma+\frac1{400}\sum_{i\in I}h(|d_i|),
\qquad h(x)=\frac{\sin x+\cos x-1}{2}.
\]

On \([0,13/50]\), \(h\) is increasing and concave, with \(h(0)=0\).
For \(S>0\), the chord inequality yields
\(h(|d_i|)\ge(|d_i|/S)h(S)\), hence the sum is at least \(h(S)\).
The \(S=0\) case already has the desired conclusion.

If \(S\ge1/10\), the elementary Taylor lower bound gives

\[
h(S)\ge h(1/10)\ge\frac{569}{12000}.
\]

The exact contradiction reserve is

\[
7\frac{448791}{500000}
+\frac1{400}\frac{569}{12000}-\frac{710}{113}
=\frac{18173}{2712000000}>0.
\]

Together with \(2\pi<710/113\), this proves the claimed contraction.
Strictness remains at
\(S=1/10\), every sign endpoint and every state or angle cut.

## 4. Complete fixed arithmetic and independent binding

The frozen kernel is byte-identical to the independently reviewed
conditional affine-arc kernel:

```
6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697
```

The decisive full coefficient output has hash

```
13a7dc18a78aaa4bbdeef9dc0d83b8f0098ba6c0e6e68ba55401d41849ef0f24
```

It has zero failures, every result index from 0 to 131,254 exactly once,
and a complete 123,168-chain cover. The independent explicit-list scan
checks that every printed reserve equals the exact minimum of its listed
coefficient bounds. Every premise bound is nonnegative and every cost
bound is strictly positive. The totals are:

| Object | Count |
|---|---:|
| Closed state arcs | 401 |
| Nonempty state domains | 18 |
| Original-axis angle chains | 123,168 |
| Fixed rows | 131,255 |
| Premise and cost polynomials | 354,398 |
| Rational coefficient lower bounds | 2,903,573 |

The least strict cost coefficient is
\(76173/20000000000000>0\). These exact counts and the three immutable
input hashes are recorded in
`MISMATCH_026_TO_01_INDEPENDENT_FULL_REPORT_BINDING.json`.

`compact_mismatch_026_to_01_report_independently.py` extracts the compact
degree/minimum record from that completed output. It verifies every
coefficient minimum and every input hash, and uses exclusive creation so
it cannot overwrite an already published compact record. It changes no
author DATA, kernel or manuscript.

`audit_mismatch_026_to_01_independently.py` binds that compact record to
the complete replay and independently reconstructs all state and angle
unions and the exact contraction. It imports no production angle or
discovery code. Its final output is
`MISMATCH_026_TO_01_INDEPENDENT_ASSEMBLY.json`. Its historical
`--prepare` mode remains explicit about its limited geometric scope and
cannot emit a table-proof PASS.

Run the final audit in the flat directory containing the bound inputs:

```sh
python audit_mismatch_026_to_01_independently.py
```

No mathematical correction was needed in the final continuous theorem.
No frozen capture or generator source was changed during this review.
