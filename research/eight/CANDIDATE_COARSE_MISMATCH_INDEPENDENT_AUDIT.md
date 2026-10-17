# Independent review of the first candidate mismatch bound

**Result: PASS.** The continuous charged-pair argument, complete state and
original-axis coverage, exact cyclic contraction, and zero-quarter owner
corollary all pass independent review. A private full replay also reproduces
every one of the 2,961,120 printed coefficient bounds.

## 1. Exact scope and source binding

The reviewed author manuscript is
`CANDIDATE_COARSE_MISMATCH_HAND_PROOF.md`, initially reviewed at SHA-256

```
c789d8b49f88024923e76f64734b0c70b2f94645202ddd235ef0c43229843809
```

It uses the roles `(H,G,A,B,T,D,E)`, word `(0,1,0,1,0,1,1)`,
and squared radius \(Q=3915534138/10^9\). Its only extra tangent cuts are

\[
 u_G\in[-4/5,-1/20],\qquad u_T\in[1/20,4/5],\qquad u_E\in[-1,0].
\]

There is no H or D tangent cut, no smaller frame-mismatch assumption,
and no selected-owner hypothesis in the pair table. Both radial kinds
and all four retained original SAT axes are covered.

The immutable input bindings are:

| File | SHA-256 |
|---|---|
| `CANDIDATE_COARSE_MISMATCH_HAND_DATA.json` | `ffa48df0d02e18880314907a72a70fcc6aaceea4ee1060ea76b4fdb04c23a5fa` |
| `CANDIDATE_COARSE_MISMATCH_HAND_COMPACT_REPORT.json` | `995c1c652957c00ac0aa40e0a3dede26db689e15e281e78dac2b5ae8091f963f` |
| `verify_candidate_coarse_mismatch_hand.js` | `6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697` |

The verifier is byte-identical to the conditional affine-arc kernel whose
range/axis interface I previously independently reviewed. Here every
declared difference range is the full interval `[-7/10,7/10]`, and all
four axes remain available. Its conditional facilities introduce no extra
geometric assumption in this theorem.

## 2. Continuous charged-pair argument

For an original edge i the prescribed charge is

\[
 \beta_i=\begin{cases}99/5000&i\in I=\{0,2,3,4,5\},\\0&i\notin I,
 \end{cases}
 \qquad \gamma_i=89727/100000.
\]

I checked the own-frame coordinates, all four SAT signs, and the
reflection/reversal normalization. That normalization swaps the states
and negates their labels appropriately, while preserving the angle phi.
The charge is read using the original edge index and therefore remains
\(-\beta_i h(\phi)\); neither its sign nor its edge assignment changes.

For a nonnegative feasible SAT margin M and a nonnegative multiplier,
subtracting \(\lambda M\) gives a lower bound for the charged cost.
The source and target affine coordinate functionals are then bounded on
their complete declared arcs. The constant-side minimum, concave
endpoint rule, derivative-sign rules, and full-circle support all have
the claimed lower-bound direction. Every circular core piece is separated
from its straight side at the exact tangent `6/7`.

The whole-circle radical majorant is valid for every nonnegative squared
norm. The Taylor remainder coefficient intervals give pointwise lower
polynomials on nonnegative angle coordinates; no derivative of an unknown
Taylor remainder is used. The additional width term is exactly

\[
 -\frac{\beta_i}{2}(\sin x+\cos x-1),
 \qquad \phi=k_i\pi/2\mathbin{\pm}x,
 \quad 0\le x\le7/10.
\]

Thus the already reviewed Bernstein argument proves every complete
fixed-angle row, including its support premises. This confirms the
continuous pair inequality before any contact owner is eliminated.

## 3. Independently reconstructed domain unions

`audit_coarse_mismatch_assembly.py` does not import a discovery routine,
the JavaScript verifier, or its arithmetic implementation. It checks all
exact state and row declarations, including the same-sign state endpoints,
the core junction, original axis numbers, nonnegative multipliers, and
every row's target bound.

The author kernel uses a square-root half-angle identity to bound
arctangents. The independent audit instead uses

\[
 \arctan t=\arctan(1/2)
       +\arctan\!\left(\frac{2t-1}{t+2}\right),\qquad 0\le t\le1.
\]

The second argument lies in `[-1/2,1/3]`. Direct alternating series,
with terms numbered 0 through 60 or 61, provide the two-sided bounds.
Outward rounding uses denominator \(10^{26}\). Machin's identity
is separately evaluated with the same direct-series implementation.

From these bounds the audit reconstructs

\[
 \frac{19}{25}-\alpha_s^++\alpha_t^-
 \le\phi\le
 \frac{710}{113}-\frac{114}{25}-\alpha_s^-+\alpha_t^+,
\]

intersects with both full quarter-angle halves, and verifies the closed
interval unions for each original axis. All **462 arcs**, **22 state
domains**, and **121,808 necessary angle chains** pass. The counts are
recomputed from the data; no discovered feasible state is used to omit a
case. Shared state endpoints are harmless because one containing label
is chosen once per actual vertex and retained on both incident edges.

## 4. Private complete arithmetic replay

`replay_coarse_mismatch_independently.py` runs the frozen verifier in a
separate process and writes only to an exclusive temporary output file.
It checks both the exit status and empty stderr, rehashes all unchanged
inputs, and compares every polynomial record with the compact report.
The full results array is decoded one object at a time to avoid holding
the large output twice in memory.

The independently reproduced totals are:

| Quantity | Count |
|---|---:|
| Passing fixed scalar rows | 129,031 |
| Premise and cost polynomials | 354,720 |
| Individually compared coefficient bounds | 2,961,120 |

Every premise coefficient lower bound is nonnegative and every cost
coefficient lower bound is positive. The least strict cost lower bound is
\(642432521/10^{14}\). The 191,944,947-byte full output has SHA-256

```
9e44e1fe7a0df8c7f2f4e7203a2c5f5f154fd07322852574539ccddb6df19b11
```

This matches the committed compact report exactly. The two detailed
records are `CANDIDATE_COARSE_MISMATCH_INDEPENDENT_ASSEMBLY.json` and
`CANDIDATE_COARSE_MISMATCH_INDEPENDENT_REPLAY.json`.

## 5. Cyclic contraction and zero-quarter owners

Let \(S=\sum_{i\in I}|d_i|\). On `[0,7/10]`, h is concave and
h(0)=0. An independent lower Taylor substitution using S7 and C6 gives

\[
 \frac{S_7(7/10)+C_6(7/10)-1}{2}
 -\frac{29}{100}\frac7{10}
 =\frac{22020061}{14400000000}>0.
\]

The chord inequality is therefore \(h(x)\ge(29/100)x\). Summing
the full-SAT pair bounds and telescoping the consistently chosen labels
gives

\[
 2\pi>7\gamma+\beta\sum_{i\in I}h(|d_i|)
       \ge7\gamma+\beta\frac{29}{100}S.
\]

The exact reserve

\[
 7\gamma+\beta\frac{29}{100}\frac25-\frac{710}{113}
 =\frac{271}{282500000}>0
\]

proves \(S<2/5\), as claimed.

I also independently reconstructed the owner corollary. Core avoidance,
\(b\le a\), and containment give
\(447/800<a<283/200\). For a zero-quarter edge put
\(x=|d|\le2/5\). Since \(\cos x-\sin x>0\), either primary
margin 2 or 4 is bounded above by

\[
 \frac{183}{200}-\frac{847}{800}\cos x
       +\frac{47}{800}\sin x
 \le\frac{183}{200}-\frac{847}{800}\frac{23}{25}
       +\frac{47}{800}\frac25
 =-\frac{711}{20000}<0.
\]

This applies precisely to the three zero-quarter edges indexed 0, 2,
and 4, all belonging to the charged set. Their remaining possible
separators are original axes 1 and 3. Both signs of d, both radial kinds,
and endpoint ties are included. These owner exclusions are consequences
of the full four-axis budget, so the argument is not circular.

## 6. A further hand corollary without new pair rows

The separate note `COARSE_MISMATCH_CONCAVITY_STRENGTHENING.md` gives
the stronger consequence \(S<109/400\). After \(S<2/5\) is known,
concavity and h(0)=0 imply
\(\sum_i h(|d_i|)\ge h(S)\), while h is increasing on this interval.
One positive rational substitution at `109/400` then contradicts the
same cyclic inequality if S reaches that endpoint. Its complete argument
and exact polynomial are printed in that note, and the two endpoint
substitutions are reproduced by
`verify_coarse_mismatch_concavity_strengthening.py`.

The stronger corollary introduces no H/D cut or selected owner and no
additional pair input. It may be used to narrow the five charged frame
ranges in a later conditional table. The two uncharged ranges require
their own argument. Neither the initial nor the strengthened bound alone
claims the remaining candidate owners, tilt interval, or terminal closure.
