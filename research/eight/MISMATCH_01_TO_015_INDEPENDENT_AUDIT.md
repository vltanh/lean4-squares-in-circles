# Independent audit: mismatch 1/10 implies mismatch below 3/200

**Result: PASS.** The declared state domains, all original separating axes,
the signed angle restrictions, every closed cover and the rational
contraction have been independently reconstructed. The fixed verifier is
byte-identical to the already independently reviewed conditional
affine-arc kernel. The complete author coefficient replay is finished and
bound to the exact data; this audit does not claim a second full expansion
of those coefficients.

Reviewed theorem: `MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md`.
No author source or fixed data was changed in this review.

## 1. Scope and prior hypotheses

The roles are `(H,G,A,B,T,D,E)` and the quarter word is `0101011`.
The exact ceiling is \(Q=1957767069/500000000\). This is a theorem for
the radial boundary representative, with either the core or outer type
permitted independently at every vertex. It assumes the established
center order, center gaps greater than \(19/25\), total center turn
\(2\pi\), frame differences in \([-7/10,7/10]\), and the input bound
\(S\le1/10\).

The signed tangent intervals are exactly:

| Role | Domain |
|---|---|
| H | \([0,1]\) |
| G | \([-4/5,-1/20]\) |
| A | \([0,1]\) |
| B | \([-1,0]\) |
| T | \([1/20,4/5]\) |
| D | \([-1,0]\) |
| E | \([-1,0]\) |

The data impose neither \(u_H\ge1/2\) nor \(u_D\le-1/2\).
They also impose no selected-owner restriction: axes 1, 2, 3 and 4
are included at every edge. The H/A/B/D signs are preceding mismatch
bootstrap consequences; the G/T exclusions and E normalization remain
explicit inputs. The present result is not used to justify any of these
premises in its own proof.

On the five charged edges \(I=\{0,2,3,4,5\}\), the implication
\(|d_i|\le S\le1/10\) permits the signed interval
\([-1/10,1/10]\). The two mixed edges 1 and 6 keep their entire
\([-7/10,7/10]\) interval. Both restrictions are applied to the original
directed edge before any axis normalization. This agrees with the
mathematical interface of the reviewed conditional kernel.

## 2. State coverage and consistent marker choice

The 335 listed rational arcs cover exactly the 14 nonempty
role/kind/sign domains. The independent audit checks every arc lies
inside its declared domain, has positive tangent length, and has rational
affine-marker coefficients. Every core arc stays on one side of, or has
an endpoint at, the exact transition \(6/7\). Thus a core side is never
treated as a corner circle.

Each state union includes both outer endpoints. If a signed domain ends
at zero, its nonempty sign branch contains that endpoint and supplies a
valid representation of the zero-tangent state. No extra isolated
opposite-sign representation is needed for coverage.

At any shared arc endpoint, choose one containing arc for that vertex
and use its marker on both incident edges. The pair cover includes every
source/target arc combination, so this simultaneous choice is valid.
No equality between two marker formulas at a cut is required. This is
the reason the vertex markers telescope in the cyclic sum even when
their piecewise definition is discontinuous.

## 3. Independent angle and axis unions

For a source arc with state angles \([s_-,s_+]\) and target arc
\([t_-,t_+]\), the original relative frame angle is
\(\phi=\delta+\alpha_t-\alpha_s\). The other six gaps exceed
\(6(19/25)=114/25\), so every feasible pair lies inside the closed
outer enclosure

\[
\left[\frac{19}{25}-s_++t_-,\;
\frac{710}{113}-\frac{114}{25}-s_-+t_+\right].
\]

The independent checker intersects this enclosure with
\(\phi=k\pi/2+r x\), \(x\ge0\), and the original edge's exact signed
difference interval. For \(r=-1\), an interval \([l,h]\) for the signed
difference becomes \([-h,-l]\) for \(x\), as required. This calculation
uses the original source and target even for axes 2 and 3; the subsequent
owner normalization cannot alter which actual pair angles must be covered.

The angle endpoints were recomputed by an independent rational method:

\[
\arctan t=\arctan(1/2)+
\arctan\!\left(\frac{2t-1}{t+2}\right),\qquad0\le t\le1.
\]

The second argument lies in \([-1/2,1/3]\). Alternating partial sums
through indices 60 and 61 enclose each arctangent, with sign reversal
handled explicitly; results are rounded outward to denominator
\(10^{26}\). Machin's identity independently encloses \(\pi/2\).
This uses neither the production square-root mesh nor the author's
assembly routines.

For every nonempty resulting interval, including a point if one occurs,
the checker demands a complete closed union for all four original axes.
It does not discard a chain merely because its endpoints agree. The
actual frozen input has no isolated point chain under this independent
enclosure. The complete count is:

| Edge | Required original-axis angle chains |
|---|---:|
| H→G | 14,624 |
| G→A | 17,172 |
| A→B | 12,864 |
| B→T | 15,096 |
| T→D | 15,116 |
| D→E | 14,392 |
| E→H | 12,016 |
| **Total** | **101,280** |

All these unions pass. Every row additionally has the correct directed
edge, source and target roles, quarter index, angle sign, nonnegative
multiplier and admissible support mode. Its threshold is at least the
declared edge threshold. A circle support is allowed only for an outer
arc or a core corner arc after the stated normalization; the independent
checker verifies this constraint too.

## 4. Continuous support and fixed coefficient binding

For a separating axis, \(M_j\ge0\). A row's proven inequality is

\[
\phi-\beta_i h(|d_i|)+L_s-L_t-\gamma_i-\lambda M_j>0,
\qquad\lambda\ge0.
\]

It therefore implies the charged pair bound with the correct strict
direction. Subtracting \(\lambda M_j\) makes the source and target state
terms separate linear supports. The reviewed endpoint, monotonicity and
concavity modes bound the entire declared arc; the circle mode uses an
unrestricted circle support and is consequently also a valid lower bound.
Its polynomial radical majorant has the exact nonnegative remainder
identity stated in the author's Section 2. No coupled state minimizer is
assumed absent.

The frozen kernel hash is

```
6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697
```

This is the same conditional kernel previously independently reviewed
for signed-range and original-axis coverage. The author has completed the
full deterministic coefficient replay, with exact output hash

```
014c06a9373077acb965a78690669b863214eb42dc650f30619eb63553e60df3
```

The present audit binds that replay to the frozen data and compact
records, checks every compact premise bound is nonnegative and every
cost bound is strictly positive, and independently reproduces the totals:

| Object | Count |
|---|---:|
| Fixed angle rows | 107,196 |
| Premise and cost polynomials | 292,119 |
| Coefficient lower bounds | 2,468,184 |

The least printed strict cost coefficient is exactly
\(576987/25000000000000\). No unresolved row, changed input or
unreviewed kernel variant is used.

## 5. Cyclic contraction

Choose the consistent arc at each vertex and an actual separating axis
on each edge. The marker terms cancel. The state-angle terms also cancel
because \(\phi_i=\delta_i+\alpha_{i+1}-\alpha_i\). With
\(\beta_i=1/200\) on \(I\) and zero otherwise, the strict pair bounds
give

\[
2\pi>\Gamma+\frac1{200}\sum_{i\in I}h(|d_i|),
\qquad \Gamma=\frac{125662969}{20000000}.
\]

For \(0\le x\le1/10\),
\(h(x)=(\sin x+\cos x-1)/2\) is increasing and concave, with
\(h(0)=0\). Hence, if \(S>0\), each term satisfies
\(h(|d_i|)\ge (|d_i|/S)h(S)\), and the sum is at least \(h(S)\).
The zero case is immediate. This argument retains the total mismatch;
it does not replace it with independent edge error budgets.

If \(S\ge3/200\), the strict elementary Taylor lower bound gives

\[
h(S)\ge h(3/200)>
\frac{3/200}{2}-\frac{(3/200)^2}{4}-\frac{(3/200)^3}{12}
=\frac{238191}{32000000}.
\]

The independent rational checker proves the Machin bound

\[
2\pi<32A_6(5)-8A_3(239)<6.28318531
\]

and reconstructs exactly

\[
\Gamma+\frac1{200}\frac{238191}{32000000}-6.28318531
=\frac{2287}{6400000000}>0.
\]

This contradicts the strict cyclic pair sum, proving \(S<3/200\).
The implication is established on the stated boundary representative.
Transfer to original centers remains the explicit preceding radial and
radius-transfer argument; this audit makes no assertion that the first
radial deformation preserves each signed tangent.

## 6. Reproduction and artifact boundary

The independent checker is `audit_mismatch_01_to_015_independently.py`.
It imports no author proof or discovery code and writes
`MISMATCH_01_TO_015_INDEPENDENT_ASSEMBLY.json`. The report binds the
theorem, exact data, compact coefficient report, frozen kernel, author
replay source, author assembly source and its report. It also records the
independent checker hash, all edge-chain counts and the exact contraction.

Run in the flat directory containing those inputs:

```sh
python audit_mismatch_01_to_015_independently.py
```

No mathematical or coverage correction was required.
