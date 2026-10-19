# Table-free hand proof: current gates and remaining capture work

**PR #10:** `formalize/eight-uncompiled-draft`.
**Mode:** hand mathematics only; no Lean changes, compilation, or CI.
**Target:** the unrestricted sharp eight-unit-square radius theorem and
its complete five-parameter equality family, with no numerical lookup
table in the mathematical dependency chain.

## 1. Current mathematical status

**G2 is closed.** Both residual wrong words now have complete table-free
assemblies. The finite quarter-word classification and all six exclusions
are assembled in
[HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md).
The only surviving word is 0101011. Its reflection permits \(u_E\le0\).
The unrestricted sharp theorem still requires global candidate capture.

| Gate | Status | Exact boundary |
|---|---|---|
| G0 | Closed on paper | Central core, physical gaps, fixed-axis boundary reduction and radius expansion. |
| G1 | Closed on paper | Complete frame concentration, with real frame spread < .7. |
| G2 | Closed on paper | All six wrong words excluded; 0101011 is the only survivor. |
| G3 | E normalization closed; six cuts open | The reflection proves \(u_E\le0\), not the G/T/H/D tangent bounds. |
| G4 | Open | Coarse mismatch contractions \(S<.4\), then \(S<.26\). |
| G5 | Open | \(.26\to.1\), sign rigidity, and \(.1\to.015\). |
| G6 | Conditionally closed on paper | Quarter-owner rigidity under its stated signed cuts and \(S\le.015\). |
| G7 | Last contraction open; mixed owners conditionally closed | Must prove \(.015\to.001\) without assuming the mixed owners first. |
| G8 | Conditionally closed on paper | Complete positive-tilt tails under the captured cuts, owners and \(S\le.001\). |
| G9 | Required components closed on paper | Stationary construction/uniqueness, conditional sharp terminal and full conditional equality family. |
| G10 | Open | Unrestricted assembly after G3--G5 and the remaining G7 contraction. |

These are hand-proof statuses, not new Lean verification or compilation
claims. The existing Lean files and historical generated tables remain
unchanged.

## 2. What counts as a table-free closure

A complete theorem must establish its inequality on the full stated
continuous domain, including the core side/corner join, outer-arc endpoints,
both angle signs, every original feasible axis, and all ties.

Permitted ingredients are circle support, exact contact identities,
monotonicity, convexity, explicit polynomial positivity, and individual
rational reference comparisons proved by squaring or alternating series.
Short finite classifications of actual geometrical alternatives are
permitted. In particular, the two angle signs, three boundary charts,
four original axes and seven quarter-word classes are intrinsic data.

A state/angle mesh, Bernstein-sign row inventory, affine arc lookup,
recursive owner table, sampled minimum, or asserted numerical PASS is
not a proof premise. A smaller numerical table is still a table.
Defining an uncomputed potential by an infimum does not prove its needed
pair or cycle inequalities.

Choose a signed/radial representation and any chart-boundary marker once
per vertex. Use that identical label on both incident edges. Original
axes cannot be discarded merely because a preferred axis is feasible too.
A pointwise label comparison inside a pair proof is not permission to
change the actual labels in the cycle sum.

## 3. The completed global entry and word gates

[HAND_CENTRAL_BANDS_WITHOUT_TABLES](HAND_CENTRAL_BANDS_WITHOUT_TABLES.md)
replaces the central common-point coefficient rows. With the original
analytic central-existence and forbidden-width arguments it gives the
one-twelfth core and the strict exterior gap.
[HAND_EXTERIOR_FRAME_CONCENTRATION](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
binds the complete table-free four-type pair proofs and the closed-tour
argument giving spread below .7.

[HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
then excludes **every** original primary zero-edge axis before any
candidate cut or mismatch contraction. This actual-cycle theorem is
available throughout the remaining work; it must not be misquoted as an
isolated-pair marker theorem.

[HAND_GLOBAL_CORE_CYCLE](HAND_GLOBAL_CORE_CYCLE.md) gives the global
at-most-one core/core neighboring edge. It does not license deletion
of an independently quantified local pair theorem.

[HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES](HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md)
assembles all ten core/core, nineteen mixed, and ten outer/outer reflection
classes. Its exact cycle reserve over \(710/113\) is \(823/2260000\).

[HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES](HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md)
assembles every 0010111 component with the original affine role labels.
It covers all 76 directed radial/sign cases and the 304 original-axis
over-cover. Its outer-quarter map covers all 48 owners and all 96 full
angle halves; it imports neither the six old near-aligned patches nor
the 140 scalar-table tails. Its exact reserve over \(710/113\) is
\(121/565000\).

The new word-selection theorem rederives the seven-word classification
from the already table-free G1 gap. It explicitly does **not** import
the historical Bernstein appendix in `SEVEN_QUARTER_WORDS.md` Section 1.
The four double-increment words use their common whole-domain geometric
pair lemmas and reserve \(13/1400\) over \(44/7\). This completes G2.

## 4. The precise remaining candidate problem

Name the cyclic roles \((H,G,A,B,T,D,E)\). Their word and nominal quarter
representatives are
\[
 k=(0,1,0,1,0,1,1),\qquad m=(0,0,1,1,2,2,3).
\]
Every state is \((a_i,-\sigma_i b_i)\) in its own nearest-axis frame;
write \(u_i=\sigma_i b_i/a_i\). The reflection in the new G2 theorem
proves \(u_E\le0\). Do not assume other signs or radial kinds from the
role names.

Let \(d_i\) be the real frame increment after subtracting \(k_i\pi/2\).
Then
\[
 \sum_i d_i=0,\quad |d_i|<.7,\quad
 \phi_i=k_i\pi/2+d_i,
\]
\[
 g_i=\phi_i+\sigma_i\arctan(b_i/a_i)
              -\sigma_{i+1}\arctan(b_{i+1}/a_{i+1})>.76,
 \qquad\sum_i g_i=2\pi.
\]
The mismatch sum uses the five non-mixed edges
\(I=\{H,A,B,T,D\}\):
\[
 S=\sum_{i\in I}|d_i|,\qquad J=I^c=\{G,E\}.
\]
Use the same frame errors in every incident constraint. The two mixed
errors have sum minus the five aligned errors; they are not independent
error budgets.

For each actual edge, at least one of the four original signed SAT
margins is nonnegative. The zero-primary theorem restricts zero edges
only. No further quarter or mixed owner restriction is available before
its prerequisites below.

### G3: structural tangent cuts

At the appropriate radius ceiling, prove in dependency order
\[
 -4/5<u_G<-1/20,\qquad1/20<u_T<4/5,
 \qquad u_H>1/2,\qquad u_D<-1/2.
\]
The G cuts precede T. H/D may use a preceding coarse mismatch theorem
only if that theorem did not already assume the desired H/D cuts.
A forbidden tail must contradict a full-domain support or cyclic
inequality. A table value for that tail is not an admissible premise.

### G4: coarse mismatch

Under the actually proved E/G/T cuts, prove
\[
                              S<2/5,\qquad S<13/50.
\]
The target is one coherent seven-cycle inequality, or a completely
proved compatible set of analytical vertex potentials. Adjacent pair
states share their vertex variables. A global core-edge restriction
must be used globally, not inserted as a false local restriction.

[HAND_CLOSED_TOUR_CHARGE_COMPRESSION](HAND_CLOSED_TOUR_CHARGE_COMPRESSION.md)
is already proved. For \(U_K=\sum_{i\in K}h(|d_i|)\),
\(h(x)=(\sin x+\cos x-1)/2\), it gives
\[
 S\ge.4\Rightarrow U_I+(19/125)U_J>1117/6250,
\]
\[
 S\ge.26\Rightarrow U_I+(17/200)U_J>12119/100000.
\]
These are consequences of a bad mismatch, not the missing geometric
upper bound on the charged cycle.

[HAND_COARSE_POSITIVE_ZERO_CONTACT_WITHOUT_TABLES](HAND_COARSE_POSITIVE_ZERO_CONTACT_WITHOUT_TABLES.md)
proves one exact quintic-potential contact family:
\[
 (111/112)\delta+F(b)-F(1-B)\ge0\qquad(0\le\delta\le.7).
\]
It covers both original transverse owners for the positive \((+,-)\)
zero edge and all contained radial states; equality is precisely the
aligned contact continuum. The other signs, quarter families, compatible
role potentials and cyclic sum are still required. Do not report this
one-family theorem as a coarse contraction.

### G5: middle contraction and signs

In the stated order, prove
\[
 S\le.26\Rightarrow S<.1,
\]
then the required role signs, and
\[
 S\le.1\Rightarrow S<.015.
\]
A uniform first-order cycle stress with a controlled quadratic remainder
is admissible. The desired signs must not enter the preceding contraction
as unproved inputs.

### G6 and G7: quarter owners, last contraction, mixed owners

[HAND_QUARTER_OWNER_CLOSURE](HAND_QUARTER_OWNER_CLOSURE.md)
proves the quarter-owner component under the candidate frame, signed
cuts, zero owners, \(q\le Q_0\), and \(S\le.015\).
It preserves all feasible original-axis ties.

The remaining G7 contraction is
\[
                         S\le.015\Rightarrow S<.001.
\]
It may use the quarter owners but cannot assume the mixed owners.
Only afterwards apply
[HAND_MIXED_OWNER_CLOSURE](HAND_MIXED_OWNER_CLOSURE.md), with its analytic
companions, to obtain the full original zero-based owner restriction
\[
 (\{0,2\},\{0\},\{0,2\},\{2,3\},\{0,2\},\{2,3\},\{1\}).
\]

## 5. The conditional terminal is retained, not reapplied prematurely

[HAND_POSITIVE_TILT_CLOSURE](HAND_POSITIVE_TILT_CLOSURE.md) and
[HAND_POSITIVE_TILT_NOMINAL_GAP](HAND_POSITIVE_TILT_NOMINAL_GAP.md)
exclude both entire positive tilt tails with the original cuts, owners,
radius ceiling and \(S\le.001\). The negative tilt argument is the
existing analytic owner geometry. This is G8's conditional theorem.

[HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
provides stationary existence and the exact upper construction using
compact minimization, an intermediate-value argument and a continuous
five-circle stress. The family uniqueness argument is geometric.

[HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS](HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md)
and
[HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md)
prove the whole terminal reserve and center-square completion under the
captured hypotheses. In particular its nonnegative terms give
\[
 r_0\ge q_*+\mu_HM(q_*,t)
 +\sum_{i=A,B,D,E,H}\mu_i\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +S/500\ge q_*.
\]
This statement is about the original centers, covers all allowed owner
ties, and needs none of the old local root/position/derivative tables.
It does not prove that an arbitrary cycle satisfies its input hypotheses.

[HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md)
proves the complete weak five-parameter family, its converse and the
independent noncongruent parameter box under the terminal classification.
This must be applied only after unrestricted capture has been established.

## 6. Research discipline and closure condition

The next work is G3/G4 global capture, not further pruning of already
closed wrong-word cases. Falsify a proposed cycle stress or compatible
potential early on the full domain. Keep original axes, both signs,
chart junctions and shared vertices. A locally possible pair that defeats
one potential does not refute a genuinely coupled cycle inequality.
A counterexample invalidates the proposed inequality and must be recorded;
do not conceal it with a finer grid.

If a one-vertex potential is too weak, use a two-edge elimination retaining
the common vertex or a direct cycle stress. Multiplier coefficients need
an equilibrium/support explanation. Discovery computations may suggest
such formulas, but their output is never the proof premise.

A gate is closed only when all its continuous hypotheses and conclusions
are proved. A bounded number of intrinsic geometric alternatives is
acceptable; an endless progression through numerical subdivisions is not.
Keep conditional results explicitly conditional. Commit each completed
argument with `[skip ci]`, and leave Lean and historical generated inputs
unchanged until the unrestricted hand chain is complete.

G10 requires the forward chain
\[
 \text{packing}\Rightarrow\text{core/boundary/frame}
 \Rightarrow0101011\Rightarrow\text{cuts/mismatch/owners/tilt}
 \Rightarrow q\ge q_*.
\]
At equality, return to the untouched original centers and prove both
directions of the complete family classification. No final conclusion
may be used in reverse to justify an earlier capture gate.

## 7. Published closure milestones and retained history

- `452d5ad937e441b2ef3008af79d5f5214d5cf15f`: complete 0010111 table-free
  component assembly, exact original-axis cover and cyclic contradiction.
- `201a6ac3b1d15fc7716f48a3408c8d6b03dfe2a0`: full G2 selection theorem,
  direct seven-word classification without the historical gap appendix,
  and the reflection-only E-sign normalization.

The earlier detailed strategy, inventories and component-by-component
progress remain in the version of this roadmap at commit
`bbe15f74b3406647b89eb26710629c0bb3a54f11` and in its linked hand notes.
Those source inventories are historical counts, not new compilation
measurements. Git records retain the individual commit timestamps.
