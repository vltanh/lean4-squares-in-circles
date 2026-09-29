# Roadmap after supplied normalization integration

## Current mathematical sources

[HAND_PROOF.md](HAND_PROOF.md) is the current assembly and interface document.
[NORMALIZATION_PROOF.md](NORMALIZATION_PROOF.md) replaces the former §2.3.
[HAND_PROOF_PRE_NORMALIZATION.md](HAND_PROOF_PRE_NORMALIZATION.md) preserves
all previous downstream details; its old normalization sketches and status
paragraphs are historical, not competing current instructions.

The old roadmap is preserved byte-for-byte as
[LEAN_ROADMAP_PRE_NORMALIZATION.md](LEAN_ROADMAP_PRE_NORMALIZATION.md), Git
blob `4d3286c9af740a4ee6cd4379493a6475b98e5de2`. Its later drafting phases
remain useful, subject to the source mapping and dependency corrections below.
Its old normalization-only research checklist is superseded by this document.

## Normalization integration completed in this stage

The supplied manuscript supplies every normalization output (N16)–(N27),
with 78 explicit scalar predicates and four algebraic identities. Local replay
accepted all 78 scalar inequalities and 23 direct certificate groups, with no
unresolved boxes. All 14 sharpness controls behaved as expected. The executed
backend was the separately named exact-dyadic implementation, not native Arb.
See NORMALIZATION_INTEGRATION.md and normalization_cert/README.md.

These are hand-proof and arithmetic-check milestones, not a Lean build or a
new independent re-audit of the existing downstream A1/A2 argument. In
particular N27 still uses the retained Appendix A with the full hypotheses
listed in HAND_PROOF.md. Do not equate a certificate's success with kernel
acceptance of the unrestricted six-square theorem.

## Formalization dependency order

| Stage | Output | May depend on |
|---|---|---|
| Input | Unique containing square; genuine Seven markers and N7 | Existing central/exterior and marker results |
| Cap geometry | K1–K6 | Containment, elementary support, S1–S8, I1 |
| Strong box | Proposition A: N23; then N16 | N7, genuine marker point, K, Lemma A scalar leaves |
| Chart bounds | Lemma B: N17, N20, no secondary separator | Strong box, containment and S10–S12 |
| Pins and labels | Lemma C: N19 | Lemma B and scalar pin inequalities |
| Windows and order | D1–D4: N18, N21 | Pin labels, chart bounds, SAT, one diagonal normalization |
| Piercing and budgets | N22, N24, N25, N26 | K4–K5, Lemma G; both-cardinal hypotheses for N26 |
| D own-primary | N27 | Appendix A, strong box, N22, D3–D4; no A2 input |
| Global bound / equality | Existing A2 and survivor chain | The complete normalization interface |

There must be no arrow from A2, fixed pins, or sectors back into Proposition A.
The old roadmap's horizontal-reflection instruction is invalid and must not
be implemented. The only global reflection after the initial sign convention
is the diagonal reflection used to put phi_D at most 5*pi/4.

## Next Lean implementation work

First formalize the constants and exact identities I1–I4. Keep q_* distinct
from the rational ceiling Q0, and c0=rho0-1 distinct from any candidate-radius
constant with a similar name.

Translate the 78 named scalar predicates without changing their domains or
strictness. Most nonconstant leaves are one-variable; S5, S30 and S32a are
two-variable. The tests' sampled numerical minima are not bounds to import.
Prove the scalar statements using rational inequalities and the relevant
analytic lemmas. An exact interval checker is not a theorem axiom.

Formalize the geometry in the dependency order above, including chart ties,
closed-square versus open-interior reasoning, modular marker intervals,
the five-pin counting argument, and all SAT directions in D4. The forbidden
arc lemma has the strict premise cx>c0; it is false at cx=c0. Retain a boundary
regression example rather than accidentally strengthening the theorem.

At the downstream interface, encode N26 as an implication with BOTH opposite
cardinal-separator hypotheses. P26-1 uses E/W cardinal; P16 uses N/S cardinal.
State the strong central box explicitly in Appendix A before applying it for
N27. Do not use a reflection to transfer a survivor while retaining the old
D-angle range.

Then apply the retained roadmap's later drafting/module stages to the updated
source assembly. Draft admissions, if used during development, must remain
visibly draft-only. Acceptance of the final theorem requires an actual local
Lean build and kernel/axiom audit, not merely a completed manuscript.

## Acceptance record

Before promoting the unrestricted Lean endpoint, record:

- the exact Lean/mathlib toolchain and commands actually executed;
- the normalization theorem with all outputs and no circular assumptions;
- the mapping of every A1/A2 input to that theorem, including N26 hypotheses;
- successful compilation and the final theorem's axiom dependencies.

No such Lean acceptance is claimed by the normalization integration commits.
Do not modify Challenge.lean, public optimum declarations, root entry points,
or workflow configuration merely to make a draft appear accepted. GitHub is
used for source commits only; the local certificate runner does not dispatch
Actions or any other remote computation.
