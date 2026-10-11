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

## Reconciliation and completed steps

The remote HUMAN_CONTACT_COMPONENTS.md covers the principal connected-stress
and actual-component conclusions developed independently in the saved patch.
The remote HUMAN_ACTUAL_BRIDGES.md additionally treats actual, not merely
positive-weight, bridges. HUMAN_CENTRAL_COMPACTNESS.md gives semicircle
capacity and a uniform, unspecified positive central core.
HUMAN_CYCLE_BOUNDARY_COUNT.md forces an interior square on an exterior
five-cycle, but expressly does not prove that its actual degree is two.

The saved three-square cap argument has now been checked and integrated as
HUMAN_THREE_SQUARE_CAP.md. It proves R^2>=(h+1)^2+9/4 for 0<=h<=1/3,
including the complete equality family. The rational identity checked in
that note is equation (15) in its condensed version. Together with the
existing two-square cap theorem, HUMAN_OPPOSITE_CAP_OCCUPANCY.md excludes
opposite central-side populations of three and two below q=2257/576.
These statements concern whole-square cap membership, not merely centers.

Three new hand-proof steps are also complete:

* HUMAN_BOUNDARY_VISIBILITY.md: a square with center norm at least one has
  a center ray missing every other circle-contact square. Consequently no
  component separated from the origin solely by boundary squares and the
  circle can contain another whole packed unit square. Empty pockets are
  not excluded.
* HUMAN_HIGH_SLICE_BOUND.md: for h>=1/10 and 63/100<=d<=71/100, a square
  tangent to x=h whose chord at x=h+1/2 is wholly above y=d has a vertex
  with squared norm greater than 1+(d+1)^2. The full orientation range is
  covered by derivative signs and an explicit concavity estimate.
* HUMAN_OUTER_INTERIOR_TRANSMITTER.md: in a minimum-contact radius minimizer
  with sqrt(2)+1/2<R<=sqrt(9789)/50, a nonisolated circle-free square at
  distance greater than sqrt(R^2-1)-1 has exactly two actual neighbors.
  Their contacts are on opposite sides perpendicular to its nearest-point
  side. This excludes additional zero-weight actual contacts too. Isolated
  squares and the complementary near-distance case are not eliminated.

## Atomic remaining implications

| ID | Claim required | Status |
| --- | --- | --- |
| A1 | Audit the three-square cap theorem, including all orientation branches and equality cases. | Complete; HUMAN_THREE_SQUARE_CAP.md |
| A2 | Integrate the opposite 3+2 exclusion with the two-square cap theorem. | Complete; HUMAN_OPPOSITE_CAP_OCCUPANCY.md |
| B1 | State whole-square side memberships and genuine corner exceptions for all seven exterior squares; retain overlaps between memberships. | Existing definitions; not a global classification |
| B2 | Couple each corner exception to its adjacent side populations, rather than dropping its exterior-owned separator. | Open |
| B3 | Obtain a forbidden 3+2 occupancy, a sufficient projected chain, or a complete alternative bound in every surviving occupancy. | Open |
| C0 | Exclude a whole unit in a pocket separated from zero only by circle-contact squares. | Complete; HUMAN_BOUNDARY_VISIBILITY.md |
| C1a | Exclude additional actual neighbors of an outer circle-free cycle vertex above the explicit distance threshold. | Complete; HUMAN_OUTER_INTERIOR_TRANSMITTER.md |
| C1b | Handle a circle-free cycle vertex at distance at most sqrt(R^2-1)-1. | Open; no degree-two conclusion is assumed |
| C1 | For an exterior moment cycle of length 5, account for both unused exterior squares and all extra contacts of its interior vertices. | Open; C0 and C1a are inputs only |
| C2 | For length 6, account for the remaining exterior square, including both possible winding regions. | Open |
| C3 | For length 7, derive the sharp projected obstruction without assuming common frames. | Open |
| D1 | Treat central stress degree two in both side and diagonal transmission forms, retaining zero-weight actual contacts. | Partial results only |
| D2 | Reduce central stress degree at least three by a simultaneous feasible motion, or prove a sharp bound for it. | Open |
| E1 | If the twin motif is obtained, establish the placement of all four other squares. | Open |
| E2 | Derive both final oblique inequalities using the same P1, P4, P5 and the same orthonormal frame. | Open |
| F1 | Apply the established conditional theorem only after its five hypotheses have actually been produced. | Pending a complete route through B, C, D or E |
| F2 | Combine the lower bound with the existing construction and check the endpoint. | Pending F1 |

B, C/D, and E are alternative or overlapping routes, not a requirement to
prove a maximal contact classification before a radius theorem. An interior
cycle vertex, a connected contact cluster, and a nonzero moment circulation
are necessary conditions; none is being substituted for F1.

## Computational checks and their limits

Symbolic differentiation checked the high-slice second derivative and its
endpoint identities; the note displays the resulting whole-interval sign
proof. Exploratory constrained optimizations were also used to examine near
three-force branches. They do not exhaust that branch, establish a global
lower bound, or certify any output having a negative separation residual.
No optimizer value is promoted to a theorem in the dependency chain.

## Exact stopping point of the present argument

The new outer-distance dichotomy does not say that a five-cycle's known
interior vertex is necessarily on its outer side. It does not make a pair
of degree-two vertices share their neighbors. The pocket theorem does not
close a pocket after a strictly interior square has been removed from its
boundary. The cap theorem does not assign corner-separated squares to caps.

Thus the unrestricted sharp inequality R8>=Rhat has not been derived by
these notes. The available hand proofs give restrictions and the existing
upper construction, not the asserted equality. The remaining theorem
must cover the indicated near-center and global occupancy cases, or replace
them with a single sharp inequality valid for arbitrary eight-square packings.

## Publication rule

Commit reviewable mathematical results and corrections with [skip ci].
Verify the remote commit after writing. Keep all changes in research/eight/.
No Lean proof is attempted. Closure will be recorded only when F1 and F2
have complete hand proofs; this ledger does not claim them.
