# Independent review of the final mismatch contraction

**Result: PASS.** The complete declared state, original-axis and angle
unions, and the exact cyclic contraction pass independent review. The
completed fixed coefficient replay is bound to the immutable DATA and
the previously independently reviewed kernel. This audit independently
reconstructs the continuous/domain/charge assembly; it does not claim a
second full expansion of the coefficient table.

The fixed DATA hash is
`da456f7eb49a2e0dc702054c684afc14da52a5e55c042add695ef862d7a6c1a2`.
It has 456 arcs and 144,709 rows. The independent geometric audit finds
14 nonempty state domains and covers all 129,368 required original-axis
angle chains, with no omitted endpoint chain or uncovered interval.

## 1. Exact scope and noncircular owner hypotheses

The proposed implication is

\[
 S\le\frac3{200}\quad\Longrightarrow\quad S<\frac1{1000}
\]

for the candidate boundary cycle at
\(Q=1957767069/500000000=3.915534138\). Its cyclic roles are
`(H,G,A,B,T,D,E)` and its quarter word is `0101011`. Each vertex may
independently have the core or outer radial type. The preceding geometric
theorems supply the true center order, every center gap greater than
\(19/25\), total center turn \(2\pi\), and lifted frame range below
\(7/10\).

The exact signed tangent domains are:

| Role | Domain |
|---|---|
| H | \([1/2,1]\) |
| G | \([-4/5,-1/20]\) |
| A | \([0,1]\) |
| B | \([-1,0]\) |
| T | \([1/20,4/5]\) |
| D | \([-1,-1/2]\) |
| E | \([-1,0]\) |

The G/T/H/D exclusions, E reflection normalization and preceding sign
lemma justify these hypotheses before the present contraction is used.
They are not consequences inferred from this same table.

Let \(I=\{0,2,3,4,5\}\) and
\(S=\sum_{i\in I}|d_i|\). The exact original-axis domains are:

| Edge | Allowed original axes | Prior justification |
|---|---|---|
| H→G | 1, 3 | Zero-quarter theorem at \(S\le2/5\) |
| G→A | 1, 2, 3, 4 | All retained axes |
| A→B | 1, 3 | Zero-quarter theorem at \(S\le2/5\) |
| B→T | 3, 4 | Quarter theorem at \(S\le3/200\) |
| T→D | 1, 3 | Zero-quarter theorem at \(S\le2/5\) |
| D→E | 3, 4 | Quarter theorem at \(S\le3/200\) |
| E→H | 1, 2, 3, 4 | All retained axes |

Here \(Q<9789/2500\) and \(3/200<2/5\), so both preceding
owner theorems apply. Their assertions exclude every forbidden feasible
separator, including ties with an allowed separator. In particular, the
quarter theorem keeps all four possibilities on each mixed edge while
proving its result. The present pair table likewise keeps all four mixed
axes. It does not assume the later mixed-owner theorem at \(S\le1/1000\).
That theorem is used only after the present contraction has been proved.

The five charged differences have the closed range
\([-3/200,3/200]\); the mixed differences keep
\([-7/10,7/10]\). These hypotheses are attached to the original
directed edge before any axis normalization or reflection.

## 2. Independent continuous state and angle covers

All state arcs have rational endpoints and rational affine labels.
The independent audit checks every arc lies in its declared
role/kind/sign domain, and that all 14 nonempty domains have complete
closed coverage. Every core arc is split at the exact side/corner
transition \(6/7\). No side segment is treated as a circle.

At a zero-tangent endpoint, the nonempty sign branch contains that state.
At any shared arc endpoint, choose one containing arc once for the
vertex, and use its label on both adjacent edges. Every source/target arc
combination is checked. Consequently the cyclic marker cancellation is
valid even when alternative arc labels differ at their shared endpoint.

For source state-angle range \([s_-,s_+]\) and target range
\([t_-,t_+]\), the true relative angle
\(\phi=\delta+\alpha_t-\alpha_s\) lies in the closed enclosure

\[
 \left[\frac{19}{25}-s_++t_-,\;
 \frac{710}{113}-\frac{114}{25}-s_-+t_+\right].
\]

The upper bound uses the six other center gaps and
\(2\pi<710/113\). The independent audit intersects this enclosure
with \(\phi=k\pi/2+r x\), \(x\ge0\), and the original signed
difference range. For \(r=-1\), the signed interval is negated with
its endpoints reversed. A required point interval is retained.
This calculation uses the original source, target and axis, including
target-owned axes that the support kernel later reverses and reflects.

The source-angle endpoints are enclosed by a separate rational method:

\[
 \arctan v=\arctan(1/2)+
 \arctan\!\left(\frac{2v-1}{v+2}\right),\qquad0\le v\le1.
\]

The second argument is in \([-1/2,1/3]\). Alternating partial sums
through indices 60 and 61, followed by outward rounding to denominator
\(10^{26}\), enclose both terms. Machin's identity supplies an
independent rational enclosure of \(\pi/2\). The audit imports no
production angle routine or discovery code.

For each resulting nonempty angle interval, it demands a complete union
separately for every declared original axis. The counts are:

| Edge | Required original-axis angle chains |
|---|---:|
| H→G | 16,034 |
| G→A | 38,944 |
| A→B | 11,644 |
| B→T | 16,704 |
| T→D | 16,312 |
| D→E | 11,670 |
| E→H | 18,060 |
| **Total** | **129,368** |

All these unions pass for the fixed DATA. There is no isolated point
chain in this particular enclosure. Every fixed row has the correct
source/target roles, quarter index, original axis, angle sign and
nonnegative multiplier. Circle mode is allowed only for an outer arc or
a core corner after the appropriate normalization. Each row's cost
threshold is at least its declared edge threshold.

## 3. Fixed support proof and complete arithmetic binding

The frozen verifier hash is

```
6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697
```

It is byte-identical to the previously independently reviewed conditional
affine-arc kernel. The mathematical row implication is

\[
 \phi-\beta_i h(|d_i|)+L_s-L_t-\gamma_i-\lambda M_j>0,
 \qquad \lambda\ge0,
\]

where a true separating axis satisfies \(M_j\ge0\). Subtracting
\(\lambda M_j\) therefore gives the pair lower bound in the correct
direction. It also separates the two state supports into linear arc
problems. The endpoint, monotonicity and concavity modes bound the whole
arc. Circle mode uses the entire containing circle and the exact
polynomial radical majorant; it does not assume that a coupled interior
contact minimum is absent.

The complete fixed coefficient replay proves every premise polynomial
nonnegative and every cost polynomial strictly positive. Its immutable
output hash is

```
ba5e037e9d9da8369526f546275fa7037477c6d0225c33c82a5df317f8a25924
```

The independent audit binds that completed replay to this DATA and the
frozen kernel, checks every compact premise and strict cost bound, and
independently reconstructs the totals:

| Object | Count |
|---|---:|
| Fixed angle rows | 144,709 |
| Premise and cost polynomials | 399,773 |
| Rational coefficient lower bounds | 3,183,184 |

The least printed strict cost bound is exactly
\(3986139/100000000000000\). Every required row passed; no incomplete
coefficient report, changed input or unreviewed kernel variant is used.

## 4. Exact cyclic contraction

The first six edge thresholds are \(179519/200000\); the last is
\(359037/400000\). Thus

\[
 \Gamma=\sum_{i=0}^6\gamma_i=\frac{502653}{80000}.
\]

The charge is \(\beta_i=1/20\) for \(i\in I\), zero otherwise.
All rows have passed. Choose the consistent state label at each vertex and
an actual feasible separator from each declared axis set. Both the state
labels and the state-angle differences telescope. The resulting strict
inequality is

\[
 2\pi>\Gamma+\frac1{20}\sum_{i\in I}h(|d_i|),
 \qquad h(x)=\frac{\sin x+\cos x-1}{2}.
\]

On \([0,3/200]\), \(h\) is increasing and concave and \(h(0)=0\).
For \(S>0\), concavity gives
\(h(|d_i|)\ge(|d_i|/S)h(S)\); summing gives
\(\sum h(|d_i|)\ge h(S)\). If \(S=0\), the desired conclusion
already holds.

If \(S\ge1/1000\), the elementary strict Taylor bound yields

\[
 h(S)\ge h(1/1000)>
 \frac{1/1000}{2}-\frac{(1/1000)^2}{4}
 -\frac{(1/1000)^3}{12}
 =\frac{5996999}{12000000000}.
\]

The independent rational calculation proves
\(2\pi<6.28318531\) by Machin's identity and reconstructs

\[
 \Gamma+\frac1{20}\frac{5996999}{12000000000}
 -6.28318531
 =\frac{522599}{240000000000}>0.
\]

This contradicts the strict cyclic pair sum and proves
\(S<1/1000\) under the explicit preceding hypotheses. It retains the total
mismatch and does not replace it by independent per-edge error budgets.

## 5. Reproduction and artifact boundary

`audit_mismatch_015_to_001_independently.py` independently reconstructs
the state, angle and axis unions and the rational contraction. Its
`--prepare` mode cannot issue a table-proof PASS. Its final mode is bound
to the completed coefficient-output hash and checks every compact premise
and strict cost lower bound, all counts, the unchanged source hashes,
the complete independent unions and the exact contraction. It writes
`MISMATCH_015_TO_001_INDEPENDENT_ASSEMBLY.json`.

Run in the flat directory containing the four bound author inputs:

```sh
python audit_mismatch_015_to_001_independently.py
```

The report binds the author theorem, exact data, compact coefficient
record and frozen verifier, and includes the independent checker hash.
The larger completed coefficient output is identified by its immutable
hash; the author's replay wrapper reconstructs it when requested. No
frozen author source or data was changed during this review. No
mathematical or coverage correction was needed.
