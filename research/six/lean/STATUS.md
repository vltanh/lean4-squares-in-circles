# n=6 proof status: human-analytic conversion

**The requested human-analytic n=6 proof is not complete.**
The current acceptance criterion is `HUMAN_ANALYTIC_STANDARD.md`, and the active
conversion ledger is `ANALYTIC_PROGRESS.md`. Earlier source-completion checklists
record progress on a computer-assisted route; their checked boxes are not proof
of compliance with the new mathematical requirement.

## What exists, and what is not accepted as finished

The branch contains Lean source for the unrestricted lower bound, uniqueness,
equality reconstruction and public Optimum 6 integration. Those sources still
transitively use computational normalization, fixed-stress classification and
pair-envelope certificates. They are therefore NOT accepted as the requested
human-analytic proof, irrespective of eventual kernel acceptance.

The new analytic checkpoint is `SquaresInCircles/Six/Analytic.lean`. Its current
scope is deliberately smaller and explicit. It collects ordinary geometric,
algebraic and calculus arguments without the unfinished computational chain.

## Completed analytic replacements in this continuation

1. Both A22 stress-angle sign checks are replaced by the shifted-sine identity.
2. Candidate constant algebra is separated from packing normalization; the
   diagonal stress-coefficient bound is proved by rational algebra rather than
   a zero-dimensional certificate.
3. The diagonal vertex inequality is proved by a diamond-domain reduction,
   trigonometric concavity and two explicit quartic chord inequalities. The
   two cases are the two boundary pieces of the diamond, not a searched grid.
4. Both cap and vertex branches, the genuine support switch, nonnegativity and
   the unique-zero condition are assembled in `Stress/DiagonalRemainder`.
5. The real support formula and balanced-pair definitions no longer import
   computational reification merely to state ordinary real identities.
6. The six cardinal-facing angle checks are replaced by one short-transverse-
   coordinate cap obstruction and the four cardinal-coordinate identities.

The conventional proof is written in `ANALYTIC_DIAGONAL_PROOF.md`, including
all relevant constants, the branch condition, the two quartics and their exact
endpoint fractions. The separate `SixAnalyticAxiomAudit.lean` contains deferred
audit commands, not an execution log.

## Scope boundaries that remain important

The analytic diagonal theorem assumes its explicit DiagonalDomain. The current
proof that every packing reaches that domain still depends on fixed stress
rows and tails, and must be replaced. The new cardinal-angle refinement uses
the broad windows and strong-core bounds of PinPacking; it does not yet replace
the certificate-based construction of those inputs.

The principal remaining blocks are: analytic strong-core and pin/window
construction; W/D and Appendix A reductions; analytic D-edge classification
and tails in place of the large fixed tables; and the common adjacent-pair
lower envelope in place of its outer and derivative covers. Only after those
are replaced can the existing final stress/equality algebra be regarded as
an analytic-only proof of the unrestricted endpoints.

## Execution and historical evidence

Compilation is deferred at the user's request. No Lean compilation or kernel
acceptance is claimed for the new source. No numerical search, certificate
replay or generated-table verification was used to establish these replacements.
No GitHub runner or remote computation service was used.

`UPLOAD_AUDIT.md`, `UPLOAD_AUDIT_RESULTS.json`, and earlier mirror/build records
remain historical accounts of the computational route. They are not proof
premises of the analytic checkpoint and do not establish the human-analytic
acceptance criterion. Their old counts and hashes must not be presented as
validation of this new source.

The original Packing and Congruent predicates and public problem statements
are unchanged in this conversion. The isolated analytic checkpoint does not
claim to replace the full n=6 theorem until its remaining dependency gaps are
closed.
