# Hand-proof closure ledger

Reorientation base: `6aa2ff635707ad2117048d6be983ef3fa124aa81`.
The ten-commit saved patch starts at `bd095cb3f2e8380233691bc396d7580df2529037`;
it is not the same history as the six intervening remote commits.
This note supplements both roadmaps without overwriting either history.

## Fixed target

Let R8 be the attained least radius for eight interior-disjoint unit squares.
Let Rhat be the unique stationary five-corner radius selected in
HUMAN_FAMILY_CLOSURE.md. The existing construction gives R8 <= Rhat.
The missing assertion is R8 >= Rhat, not existence of another stationary
configuration and not a definition of Rhat by unrestricted minimization.

Computer calculations in this continuation may discover or test identities,
inequalities, and counterexamples. A claimed theorem must have a written
argument covering its full stated domain. No finite sample closes a case.

## Reconciliation

The remote HUMAN_CONTACT_COMPONENTS.md covers the principal connected-stress
and actual-component conclusions developed independently in the saved patch.
The remote HUMAN_ACTUAL_BRIDGES.md additionally treats actual, not merely
positive-weight, bridges. HUMAN_CENTRAL_COMPACTNESS.md gives semicircle
capacity and a uniform, unspecified positive central core.
HUMAN_CYCLE_BOUNDARY_COUNT.md forces an interior square on an exterior
five-cycle, but expressly does not prove that its actual degree is two.

The saved three-square cap theorem and opposite 3+2 cap consequence are
potential additional inputs. They require audit before being promoted into
the remote dependency chain. Their existence does not by itself assign
corner-separated squares to central-side caps.

## Atomic remaining implications

| ID | Claim required | Status |
| --- | --- | --- |
| A1 | Audit the saved three-square cap theorem, including all orientation branches and equality cases. | Pending |
| A2 | Integrate the opposite 3+2 exclusion with the two-square cap theorem. | Pending A1 |
| B1 | State whole-square side memberships and genuine corner exceptions for all seven exterior squares; retain overlaps between memberships. | Existing definitions; not a global classification |
| B2 | Couple each corner exception to its adjacent side populations, rather than dropping its exterior-owned separator. | Open |
| B3 | Obtain a forbidden 3+2 occupancy, a sufficient projected chain, or a complete alternative bound in every surviving occupancy. | Open |
| C1 | For an exterior moment cycle of length 5, account for both unused exterior squares and all extra contacts of its interior vertex. | Open |
| C2 | For length 6, account for the remaining exterior square, including both possible winding regions. | Open |
| C3 | For length 7, derive the sharp projected obstruction without assuming common frames. | Open |
| D1 | Treat central stress degree two in both the side and diagonal transmission forms, retaining zero-weight actual contacts. | Partial results only |
| D2 | Reduce central stress degree at least three by a simultaneous feasible motion, or prove a sharp bound for it. | Open |
| E1 | If the twin motif is obtained, establish the placement of all four other squares. | Open |
| E2 | Derive both final oblique inequalities using the same P1, P4, P5 and the same orthonormal frame. | Open |
| F1 | Apply the established conditional theorem only after its five hypotheses have actually been produced. | Pending a complete route through B, C, D or E |
| F2 | Combine the lower bound with the existing construction and check the endpoint. | Pending F1 |

B, C/D, and E are alternative or overlapping routes, not a requirement to
prove a maximal contact classification before a radius theorem. An interior
cycle vertex, a connected contact cluster, and a nonzero moment circulation
are necessary conditions; none is being substituted for F1.

## Publication rule

Commit reviewable mathematical results and corrections with [skip ci].
Verify the remote commit after writing. Keep all changes in research/eight/.
No Lean proof is attempted. Closure will be recorded only when F1 and F2
have complete hand proofs; this ledger does not claim them.
