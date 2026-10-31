# A transverse port strip with only one fixed external contact

Date: October 29, 2026 UTC. Author: block_roots continuation.

**Status: complete proposed uniform hand theorem, frozen for a separate
full independent review.** This extends the earlier two-fixed-external
strip theorem by allowing one external contact to retain its entire
original shared-side mean, including either endpoint. Its proof is
written in full here; the earlier theorem's hypotheses are not silently
widened.

## 1. Exact physical and original-star domain

Retain all nine actual interior-disjoint unit squares in the circle
about O=0, on the original radius window

    79/40 <= R <= sqrt(1105)/16.

Use the original compatible selected physical certificate, including
the already simultaneous fixed-tip normal selection before extraction.
Let P,Q be distinct actual true-degree-two units, with positive edge
PQ and other positive neighbors A,C respectively. A,C are each distinct
from P,Q; A=C is permitted. No force, degree, boundary or circle-load
assumption is made at A or C.

Both P and Q are positively circle-loaded and each has exactly one
physical circle corner. Physical corner multiplicity is not inferred
from a coefficient: a physical two-corner mask with one zero coefficient
is outside these explicitly stated hypotheses.

Let R0 and S0 be the unchanged actual applications of PA and QC, and
let N and M be their actual outward unit normals from P to A and from
Q to C. Require:

* N is genuinely owned by P. R0 is on that actual supporting side.
  PA may be a physical singleton or have positive shared length; its
  complete original mean and either endpoint are permitted.
* QC is a physical singleton at its fixed actual point S0. M is
  genuinely owned by Q, and S0 lies in the relative interior of that
  actual Q side.

Thus, in particular, the entire actual unit normal segments

    R0-[0,1]N in P,       S0-[0,1]M in Q                 (1)

are present. Neither translated endpoint is a substituted application.

Put J equal to counterclockwise quarter rotation, and define

    U=JN, V=JM, beta=-M.U=N.V, D=R0-S0.

**Theorem.** The complete original situation is impossible if

    beta>0,       0<D.U<beta,       0<D.V<beta.          (2)

The exchanged version allows QC to retain a shared mean and requires
PA to be the fixed singleton. This follows by exchanging the bodies
and orienting the quarter rotation consistently; it is not needed by
the literal caller below.

The force convention throughout is

    F_circle + sum(original outward pair forces)=0.

Equivalently the circle resultant equals the sum of incoming pair
forces. No equation is shortened and no circle weight is discarded.

## 2. A positive unique-corner circle resultant is not an own axis

Choose either body's actual orthonormal own coordinates with its unique
physical circle corner Z=(a,b) and its unit square

    [a-1,a] times [b-1,b].

Containment of the two adjacent corners gives a,b>=1/2. Equality in
either comparison would put the corresponding adjacent corner on the
circle too. Physical uniqueness therefore makes a,b>1/2.

The circle resultant is a strictly positive multiple of Z and hence
is not parallel to any own side axis. In the complete loaded two-force
star, if one pair normal is an own axis, the other cannot be parallel
or antiparallel to it: otherwise the full pair-force sum, including a
possible zero sum, could not equal the negative of that nonzero circle
resultant. This excludes both signs directly.

## 3. The joining edge has an actual side-axis owner

If PQ has positive shared length, its actual joining normal is
perpendicular to that shared side and is owned by both bodies. Keep
its entire original mean, including both endpoints.

Otherwise PQ is a physical singleton at its fixed actual point F.
We apply the pre-existing fixed-tip selector at Q, where both physical
pair intersections are singletons. They are distinct: if F=S0, the
relative side-interior premise at S0 makes every nonzero Q support
normal there equal to M. Both actual Q pair normals would be M,
contrary to Section 2.

Consequently Q has exactly the literal selector hypotheses: a physical
unique circle corner, true degree two, distinct fixed physical singleton
applications S0,F, and the actual distinct neighbors C,P. The complete
simultaneous fixed-tip theorem forbids a free vertex/vertex normal at
PQ. Its actual joining normal is therefore owned by P or Q.

This is a use of the already selected original certificate. The list
of fixed applications and normal constraints was made before force
extraction. Nothing about the variable PA mean is inserted into that
list: the call is at Q, whose external contact is physically fixed.
The coincident radial-D exception cannot enter because coincidence at
S0 has already been excluded by its genuine side interior and full
force equation.

## 4. Complete joining-axis cover

Write n for the actual outward joining normal from P to Q. If P owns
it, n is N,-N,U or -U. Section 2 excludes the two N-axis choices.
The remaining original support equalities are as follows.

| Actual P-to-Q direction | Actual support and membership consequence | Contradiction |
| --- | --- | --- |
| U | R0.U <= max_P U = min_Q U <= S0.U | D.U<=0 |
| -U | R0.U >= min_P U = max_Q U >= (S0-M).U = S0.U+beta | D.U>=beta |

The point S0-M used in the second row is actual by (1). These inequalities
do not depend on which point of the original PQ mean interval is used.

If Q owns its actual outward joining normal toward P, that normal is
M,-M,V or -V. Section 2 excludes the two M-axis choices. The other two
directions give the complete reflected support cover:

| Actual Q-to-P direction | Actual support and membership consequence | Contradiction |
| --- | --- | --- |
| V | S0.V <= max_Q V = min_P V <= (R0-N).V = R0.V-beta | D.V>=beta |
| -V | S0.V >= min_Q V = max_P V >= R0.V | D.V<=0 |

Here R0-N is actual by (1), even when R0 is an endpoint of P's side or
of the physical PA overlap. Thus this cover preserves all original
external and joining means, all endpoints and every possible owner.
Section 3 provides an owner, and (2) excludes every row. The theorem
follows.

## 5. Exact inputs and scope

| Complete input | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual full loaded-two stars, support equalities, positive circle resultants and original mean intervals |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Its complete distinct-fixed-physical-application theorem, applied only at Q after Section 3 verifies every premise |

Both operative inputs were read at their complete consumed scope. The
earlier two-fixed-external theorem is provenance, not a widened premise:

    TWO_LOADED_UNIQUE_CORNERS_OWNED_EXTERNAL_SIDES_TRANSVERSE_PORT_STRIP_EXCLUSION_2026_10_29.md
    16bca69aa6911c2ce1dc171733104254fea5682b9012a99c69b2a6420ac37dc9

This theorem is independent of the external support heights N.R0 and
M.S0, of all A,C loads and degrees, and of whether PA is shared. The
physical unique masks, positive loads, true degrees, fixed singleton
QC, its genuine Q side interior and the strict tests (2) remain required.
They must all be verified in each literal graph caller.

All nine actual bodies, every original force, selected normal, physical
mask, zero coefficient and side mean remain. No physical motion, sampled
pose, numerical packing certificate, post-extraction normal choice,
Lean/Lake compilation, CI, remote mutation or original-flag edit is used.
