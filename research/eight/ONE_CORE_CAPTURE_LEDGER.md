# One-core finite capture: two terminal branches

The one-core finite capture is complete. All46 ordinary exclusion inputs have
complete exact manifests, and all46 have independent binding/coverage audits.
The rational finite-domain audit passes the sequential prefix, the two
disjoint core phases, and the final conditional cuts with no domain gap.
Both terminal angular-budget and owner-complement compositions also pass
exactly. The broad center-free local theorem and its exact stationary graph
are now also proved. The terminal interface note explicitly applies that
theorem below q*, closing both one-core branches.

## 1. Role convention and initial symmetry

Label the unique core state0, with counterclockwise physical word
`(C0,O1,O2,O3,O4,O5,O6)`. Reflection followed by reversal of the role order
maps `t_i` to `-t_(-i mod7)`. It preserves the unique-core word and permits the
closed sign choice `t0 in[-1,0]`. No comparison between different outer
tangents is used in this one-core cover.

The exact baseline inputs `one_core_b0` and `one_core_b1_v2` exclude respectively
`t0 in[-1,-1/2]` and `t0 in[-1/8,0]`, with all other roles unrestricted.
They leave `t0 in[-1/2,-1/8]`.

The14 inputs indexed by
`audit_capture/one_core_coarse_prefix_ready.json` restrict outer roles in
the sequential order1,2,3,4,5,6. Each role's exclusions already assume the
previously established bounds. Their complete target is

| Role | C/O type | Coarse tangent interval |
|---|---|---|
| 0 | C | [-1/2,-1/8] |
| 1 | O | [1/8,3/4] |
| 2 | O | [-3/4,-1/8] |
| 3 | O | [0,1/4] |
| 4 | O | [-1,-3/4] |
| 5 | O | [-1/8,1/8] |
| 6 | O | [3/4,1] |

All pair costs use the exact sharp circle ceiling
`Qsharp=97888353437936885663/25000000000000000000`.

## 2. An exhaustive split into the two core phases

Four ordinary inputs exclude the following closed core intervals while all
other roles stay in the coarse box:

| Input stem, before `_candidate_v2.json` | Excluded role0 interval |
|---|---|
| one_core_t_anchor_left | [-1/2,-9/32] |
| one_core_t_anchor_right | [-17/64,-1/4] |
| one_core_g_anchor_left | [-1/4,-15/64] |
| one_core_g_anchor_right | [-7/32,-1/8] |

The retained intervals are therefore

\[
t_0\in[-9/32,-17/64]\quad\hbox{or}\quad
t_0\in[-15/64,-7/32].
\]

These are called the T-core and G-core phases. The names identify the terminal
local-dual roles; they are not extra assumptions about an arbitrary input ring.
Their local-dual assignments are respectively the reflected ring
`(T,B,A,G,H,E,D)` and the ring `(G,A,B,T,D,E,H)`.

## 3. All26 role-side exclusions and the final captured boxes

The23 first-stage inputs are indexed by
`one_core_t_first_screened.json` and `one_core_g_first_screened.json`.
Each first-stage input assumes only the coarse prefix and its selected core
interval, so those exclusions can be combined without a circular dependence.
The T phase has11 such inputs, and the G phase has12.

The T phase additionally uses
`one_core_t_a_lower_stronger_complete_round0_candidate.json`, which excludes
`t2 in[-3/4,-11/32]`. This replaces the weaker discovery cut ending at
`-23/64`; the stronger endpoint is needed for the exact common-tilt chart.

Two final conditional cuts use the narrowed other roles:

| Input | Closed excluded side |
|---|---|
| one_core_t_final_r4_high_complete_round0_candidate.json | role4 in[-59/64,-3/4] |
| one_core_g_final_r4_low_complete_round0_candidate.json | role4 in[-1,-57/64] |

The T final cut was proved on a box slightly larger in role2 than the actual
captured box. Exact subset inclusion, rather than an assumption of equality,
is used in that interface.

The resulting terminal boxes are:

| Role | T-core named square | T-core tangent | G-core named square | G-core tangent |
|---|---|---|---|---|
| 0 | T | [-9/32,-17/64] | G | [-15/64,-7/32] |
| 1 | B | [31/64,33/64] | A | [21/64,23/64] |
| 2 | A | [-11/32,-21/64] | B | [-33/64,-31/64] |
| 3 | G | [5/64,7/64] | T | [7/64,9/64] |
| 4 | H | [-61/64,-59/64] | D | [-57/64,-55/64] |
| 5 | E | [1/64,3/64] | E | [-3/64,-1/64] |
| 6 | D | [55/64,57/64] | H | [59/64,61/64] |

The immutable targets are `one_core_t_capture_target.json` and
`one_core_g_capture_target.json`. Both lie inside their corresponding frozen
charged-budget domains. The T budget deliberately keeps its broader original
role2 interval `[-23/64,-21/64]`.

## 4. Reproducible finite-union and binding audit

Run `python global_attack/audit_one_core_cover.py`. It verifies using exact
rationals:

- Every input's circle ceiling, physical word, ordered edges, zero penalty,
  and strict rational sum of pair constants above the sharp upper bound for
  `2pi`.
- Every actual excluded box is contained in the input's declared signed domain.
- Retained intervals and excluded closed sides cover every preceding role
  interval with no gap, including all shared endpoints.
- The coarse prefix is used in its actual sequential order.
- The two core phases exhaust the surviving anchor interval, and each final
  role4 cut assumes only bounds already established in its phase.
- Both final boxes are subsets of the immutable terminal-budget domains.
- Every ordinary input is compared by all mathematical proof fields to the
  frozen exact-checker registry; the matched manifest's SHA256 is checked.

The output `one_core_domain_cover_audit.json` reports all46 inputs individually,
their exact covered boxes, and their manifest and independent-audit matches.
Its completed status is46/46 exact manifests,46/46 independent audits, and
zero pending inputs. The audit also checks core radius1/12, the full unmasked
SAT scope, the ordered nonsymmetric edge convention, each manifest's passed
status, and its exact binding to the frozen data hash. The unchanged screen
index files preserve discovery provenance; the complete exact manifests are
the acceptance evidence.

## 5. Terminal gates

Each phase has its own frozen angular budget and wrong-axis complement:
`one_core_t_aligned_budget_v1.json`, `one_core_g_aligned_budget_v1.json`,
`one_core_t_owner_capture_v1.json`, and `one_core_g_owner_capture_v1.json`.
The cyclic deficits are below `9/10^7`. Both full-SAT budget/owner
compositions have now passed exact validation on their declared domains:

| Phase | Selected budget initial pieces | Exact nodes | Maximum depth |
|---|---|---|---|
| T core | 7168 | 20056 | 19 |
| G core | 7168 | 20436 | 18 |

The T selected-budget manifest is
`m5_agent/one_core_t_terminal_v1_selected_budget_piece_logs_checked/manifest.json`,
SHA256 `63b85cf8b9b0e4597e26807fba8509893984dfdfe890d3dc9c421816de360a0b`.
The G selected-budget manifest is
`m5_agent/one_core_g_terminal_v1_selected_budget_piece_logs_checked/manifest.json`,
SHA256 `3e42cc4e5b0a98b1a67220e58204e66b2e0c6c6207bb6a6006f731ce7799d7ea`.
Each composition independently reaudits its wrong-axis complement, with
7168 initial pieces passing without subdivision. Their respective manifest
hashes are `fcfa2ed35b8baf7b9b384a6c5fb8f7832e8245c3fb05f9aedfe6da9ed89c007c`
and `aedb39689efb324c8d1b5e5733905caf9dab0324c9703fe5acb3b338836b561d`.

The exact scalar audit `verify_endpoint_terminal_angles.py` already checks,
conditionally on those pair theorems and the captured domains, all five
canonical quarter-turn choices and the common-tilt interval `[1/10,4/25]`.
The T enclosure is approximately `[.1043068266,.1548525029]`; the G enclosure
is approximately `[.1032710841,.1341550352]`. Only exact rational enclosures,
not these printed decimals, enter the proof.

The precise angular, owner, and projected-slider passage to the broad
center-free local dual is recorded in `ONE_CORE_TERMINAL_INTERFACE.md`.
The ordinary46-case domain cover and both terminal compositions are now
complete. The separately completed broad local-dual arithmetic supplies
the h2 range and center-free inequality. Their explicit invocation at the
end of the terminal interface note gives the final contradiction in both
one-core phases.
