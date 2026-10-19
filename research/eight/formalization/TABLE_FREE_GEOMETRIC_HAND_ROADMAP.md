# Table-free hand proof: global capture remains; final contraction retired

**PR #10:** `formalize/eight-uncompiled-draft`.
**Mode:** hand mathematics only; no Lean changes, compilation, or CI.
**Target:** the unrestricted sharp eight-unit-square radius theorem and
its complete five-parameter equality family, without a numerical lookup
table in the mathematical dependency chain.

## 1. Current mathematical status — 19 October 2026

The unrestricted table-free proof is **not complete**. Its remaining
substantive work is global candidate capture in G3--G5.

The old final contraction `S<=3/200 => S<1/1000` is now **unnecessary**.
Mixed-owner rigidity, both tilt signs, the complete positive tilt tails,
the sharp terminal, and the equality classification have a forward hand
chain at `S<=3/200`. The new tilt and terminal use the same actual
ED-owner/H frame; no unjustified conversion to the old A/G tilt is used.

| Gate | Hand-proof status | Exact boundary |
|---|---|---|
| G0 | Closed on paper | Central core, physical gaps, fixed-axis boundary reduction and documented radius transfer. |
| G1 | Closed on paper | Complete four-type frame concentration; real frame spread below 7/10. |
| G2 | Closed on paper | All six wrong words excluded; only 0101011 survives. Reflection gives the weak E sign. |
| G3 | Open, except E normalization | Six structural tangent cuts on G,T,H,D are still required globally. |
| G4 | Open | Coarse mismatch bounds S<2/5 and S<13/50. |
| G5 | Contractions open; sign subgate closed conditionally | 13/50 to 1/10 and 1/10 to 3/200 remain open; signs follow from S<=1/10. |
| G6 | Closed conditionally at S<=3/200 | Intended quarter owners, with the stated earlier cuts and zero owners. |
| G7 | Closed conditionally at S<=3/200; old contraction retired | Every original mixed owner is G0/E1, without an S<=1/1000 premise. |
| G8 | Closed conditionally at S<=3/200 | t>S and 1/10<tau<4/25, where tau is the actual ED-owner/H frame difference. |
| G9 | Closed conditionally at S<=3/200 | Sharp owner-frame inequality with S/5000, all five completed anchors, and the full equality family. |
| G10 | Open | Unrestricted assembly after global G3--G5 capture and the stated original-center transfers. |

These are mathematical hand-proof statuses, not Lean verification claims.
Historical certificate files and the uncompiled Lean draft remain unchanged.
Removing a mathematical dependency does not claim that its old Lean import
has already been removed or that compilation time has been measured.

## 2. Exact remaining global problem

Use cyclic roles `(H,G,A,B,T,D,E)` and the surviving quarter word

\[
 k=(0,1,0,1,0,1,1),\qquad m=(0,0,1,1,2,2,3).
\]

An own-frame center is `(a_i,-sigma_i b_i)`, with `a_i>=b_i>=0` and
signed tangent `u_i=sigma_i b_i/a_i`. Let d_i be its real frame increment
after subtracting the prescribed quarter turn. The entry theorems give

\[
 \sum_i d_i=0,\quad |d_i|<7/10,
\]
\[
 g_i=k_i\pi/2+d_i+\sigma_i\arctan(b_i/a_i)
                  -\sigma_{i+1}\arctan(b_{i+1}/a_{i+1})>19/25,
 \qquad\sum_i g_i=2\pi.
\]

The mismatch is

\[
 I=\{H,A,B,T,D\},\qquad S=\sum_{i\in I}|d_i|.
\]

The two remaining errors belong to the same closed frame tour. They
cannot be assigned independent angular budgets. Every actual edge has
at least one feasible original signed SAT witness; only the already
proved zero-primary exclusion can restrict owners before later gates.

### G3: the six missing tangent cuts

The reflection proves `u_E<=0`, but not

\[
 -4/5<u_G<-1/20,\qquad 1/20<u_T<4/5,
 \qquad u_H>1/2,\qquad u_D<-1/2.
\]

The G cuts precede T in the historical route. H/D may use an earlier
coarse mismatch result only if that result did not assume H/D first.
A full-domain support or coupled-cycle contradiction is needed for
each forbidden tail. Existing fitted arc values are not hand premises.

### G4: the missing coarse mismatch bounds

Under only the cuts actually established at that point, prove

\[
                            S<2/5,\qquad S<13/50.
\]

The proved closed-tour charge compression says, for
`U_K=sum_(i in K) h(|d_i|)` and `h(x)=(sin x+cos x-1)/2`,

\[
 S\ge2/5\Longrightarrow U_I+(19/125)U_{I^c}>1117/6250,
\]
\[
 S\ge13/50\Longrightarrow U_I+(17/200)U_{I^c}>12119/100000.
\]

These are consequences of a bad mismatch, not the still-missing geometric
upper bounds. See [closed-tour compression](HAND_CLOSED_TOUR_CHARGE_COMPRESSION.md)
and [the exact cycle-stress interface](HAND_CYCLE_STRESS_INTERFACE.md).

[The quintic positive zero-edge contact theorem](HAND_COARSE_POSITIVE_ZERO_CONTACT_WITHOUT_TABLES.md)
closes one complete contact family, preserving its aligned continuum.
The other signs, quarter families, compatible role potentials and cyclic
sum are not supplied by that one-family theorem.

### G5: the two missing middle contractions

In forward order, prove

\[
 S\le13/50\Longrightarrow S<1/10,
 \qquad S\le1/10\Longrightarrow S<3/200.
\]

Between these steps,
[the zero-edge sign theorem](HAND_ZERO_EDGE_SIGN_RIGIDITY_AT_ONE_TENTH.md)
already gives `(sigma_H,sigma_G,sigma_A,sigma_B,sigma_T,sigma_D)
=(+,-,+,-,+,-)` from `S<=1/10`, without G/T/H/D cuts or a preferred
SAT owner. Together with reflection, E has its weak negative sign.
Do not use those signs to justify the preceding contraction.

## 3. Completed entry and word dependencies

[Central-band identities](HAND_CENTRAL_BANDS_WITHOUT_TABLES.md), with their
specified analytic central-existence and forbidden-width arguments,
supply the core and physical gaps.
[Exterior-frame concentration](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
assembles the full table-free four-type pair proofs and the closed tour.

[Zero-primary cyclic exclusion](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
excludes every originally feasible zero-primary witness before any
candidate cut or mismatch contraction. It is a theorem about the actual
cycle, not an independently quantified local pair assertion.
[The global core-cycle theorem](HAND_GLOBAL_CORE_CYCLE.md) similarly
restricts neighboring core/core edges only in a coherent cycle.

[Quarter-word selection](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md)
assembles every wrong word without the old numerical gap appendix.
Its two residual component assemblies are
[0011011](HAND_WRONG_0011011_COMPLETE_WITHOUT_TABLES.md) and
[0010111](HAND_SHORT_WORD_COMPLETE_WITHOUT_TABLES.md).
The only surviving word is 0101011. Its reflection changes E's sign and
preserves the whole word, giving `u_E<=0`.

## 4. The completed downstream chain at S<=3/200

This section is a **conditional theorem**, not a claim that an arbitrary
packing satisfies its inputs. Work with an actual candidate satisfying
the earlier signed cuts, zero owners, core avoidance, corner containment
and `S<=3/200`. For the lower-bound problem it suffices to consider
squared radius at most `Q1=1957767069/500000000`, because the stationary
construction proves `q_*<Q1`. The owner lemmas use the weaker ceiling
`Q0=9789/2500`.

First apply [quarter-owner rigidity](HAND_QUARTER_OWNER_CLOSURE.md).
The complete mixed-owner extension is then assembled by

- [E2/E3 exclusion](HAND_E_OWNER_CHAIN_AT_THREE_TWO_HUNDREDTHS.md);
- [G2/G3 exclusion](HAND_G_HIGH_INDEX_OWNERS_AT_THREE_TWO_HUNDREDTHS.md);
- [near-zero mixed-tilt exclusion](HAND_NEAR_ZERO_MIXED_TILT_AT_THREE_TWO_HUNDREDTHS.md);
- [positive G1/E1 exclusion](HAND_MIXED_PRIMARY_AT_THREE_TWO_HUNDREDTHS.md);
- [full mixed-owner rigidity](HAND_MIXED_OWNER_CLOSURE_AT_THREE_TWO_HUNDREDTHS.md).

They prove the original zero-based owner sets

\[
 (\{0,2\},\{0\},\{0,2\},\{2,3\},\{0,2\},\{2,3\},\{1\})
\]

for **every** feasible original witness, including ties. No final
mismatch contraction or tilt window is an input to those lemmas.

Next, [the full negative-tilt proof](HAND_NEGATIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md)
combines with the near-zero theorem to prove `t>S`.
Choose the actual ED owner once, call its physical frame d0, and set
`tau=theta_H-d0`. The
[owner-frame positive-tail theorem](HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md)
proves

\[
                              1/10<\tau<4/25.
\]

Its exact seven-force identity makes `F_E=delta f_0-epsilon f_tau`
constant in all five errors at fixed tau. Thus the inverse-sine E-norm
remainder is absent. The proof uses one continuous stress and one shared
error budget on both full positive tails.

Finally, apply the [sharp owner-frame terminal](HAND_OWNER_GAUGE_SHARP_TERMINAL_AT_THREE_TWO_HUNDREDTHS.md)
with this **same** tau and the same selected owners. Its stationary strip
`1-.7 tan(tau)<u<1-.6 tan(tau)` and whole-domain torque estimates give

\[
 r_0\ge q_*+\mu_H M(q_*,\tau)
 +\sum_{i=A,B,D,E,H}\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +S/5000\ge q_*.
\]

At equality, S=0, tau=t_*, and all five actual anchors are fixed.
[The full weak five-parameter equality family](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md)
and its converse then apply. Its stationary prerequisites are
[existence and uniqueness](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md),
[position and slider bounds](HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md),
and [the original continuous weight identities](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md).

The owner-frame tilt is not silently substituted for the old A/G tilt:
only `|tau-t|<=S` holds before rigidity. The new terminal was proved in
the frame actually delivered by capture. At equality S=0 the frames
coincide as required.

**Therefore the entire S<=3/200 downstream chain is complete.** The old
`3/200 to 1/1000` contraction and the old small-mismatch positive-tail
and terminal estimates are not premises of this route. The earlier
direct-E support theorem remains valid but is not needed for this assembly.

The global caller must still supply the stated actual candidate
hypotheses through the documented boundary/radius transfers. A boundary
representative cannot be substituted for the original centers in the
sharpness or equality step; no preservation of a tangent is assumed
unless the relevant transfer theorem establishes it.

## 5. Proof discipline and exact global stopping condition

A gate closes only on its entire continuous domain: both signs, all
original feasible axes, chart joins, outer endpoints and weak ties.
Use the same signed/radial label at a shared vertex on both incident
edges. Never change a selected witness merely because another is also
feasible. Core restrictions and angular closure must be used globally.

Permitted ingredients include exact support identities, monotonicity,
convexity, explicit polynomial positivity, and isolated rational reference
comparisons justified by squaring or alternating series. Intrinsic finite
classifications, such as actual owners and signs, are permitted.
A state or angle mesh, generated Bernstein row inventory, recursive owner
table, sampled minimum or numerical PASS is not a proof premise.
An uncomputed potential defined by an infimum is not its own proof.

The next work is **G3--G5 global capture**, not further treatment of the
now-completed mixed-owner, tilt, or terminal stages. If a proposed
one-vertex potential is false, record the obstruction and retain coupled
vertices in a two-edge or whole-cycle argument; do not conceal it by
refining a grid. Later-stage signs, cuts and owners cannot be used in
reverse to justify an earlier stage.

The remaining unrestricted implication is

\[
 \text{packing}\Longrightarrow\text{G0--G2 actual candidate}
 \Longrightarrow\text{G3 cuts and G4--G5 }S<3/200.
\]

Only after that implication and its original-center transfers are
established may Section 4 close G10 and the unrestricted theorem.

## 6. Published milestones and retained history

The new downstream proofs were pushed on 19 October 2026:

- `fec79e3634c09b79882271bbbdf06b7c35511e68`: complete nonpositive-tilt exclusion at S<=3/200.
- `62de8f125f16fbb11156ec4198bb7ff8f71d1a7e`: both positive tails in the actual ED-owner/H frame, with the exact all-owner scalar identity.
- `6f2dff31474c36bdb73a46445b17fc8c65d6270a`: sharp owner-frame terminal and full equality implications at S<=3/200.
- `a33bfd4d9dfdfdc5b8b06adf2d34bad4405ec6a9`: normalized mathematical typesetting of that terminal; all exact estimates retained.

The preceding full mixed-owner extension is in the history ending at
`79ce198ae3b5d87c54dc5ff8d93e1317b604a41f`.
Earlier entry milestones include `34eafad16ea7f7810aae68c627a3aa3ecf6d32d5`
for conditional sign rigidity, `452d5ad937e441b2ef3008af79d5f5214d5cf15f`
for the complete short-word assembly, and
`201a6ac3b1d15fc7716f48a3408c8d6b03dfe2a0` for G2 selection.

Git retains every individual commit timestamp. The earlier detailed
roadmap and component inventories remain in its versions at
`ca9567729c0839a68e439a91ab63b29e7419b0d4` and
`bbe15f74b3406647b89eb26710629c0bb3a54f11`.
Historical table counts are not new compilation measurements.
