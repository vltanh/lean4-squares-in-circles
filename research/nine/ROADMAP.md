# n=9 — current roadmap: remaining tree families P and Y; cyclic branch open

**Checkpoint:** 2026-10-23 origin-pocket continuation. **The unrestricted n=9 proof is NOT finished.** New hand arguments close the entire TREE.03 profile and the full point-only contact branch TREE.02.P. All surviving tree configurations are now covered by two explicit completion skeletons, P and Y. Their capacity bounds and the separate cyclic branch remain open. Independent full audit and Lean verification are outstanding.

## Current authoritative documents

- [DEEP_GATED_ROADMAP.md](DEEP_GATED_ROADMAP.md): full G0–G8 contracts and updated subgates.
- [FINITE_TREE_CASE_LEDGER.md](FINITE_TREE_CASE_LEDGER.md): original six profiles, exact checked cases and P/Y survivor cover.
- [G2_SUBGATES.md](G2_SUBGATES.md): live G2 mathematical status.
- [ORIGIN_POCKET_PROGRESS.md](ORIGIN_POCKET_PROGRESS.md): newest UTC proof commits and actual pinned execution.
- [PROGRESS_LEDGER.md](PROGRESS_LEDGER.md): preceding append-only checkpoints.
- [README.md](README.md): source index and handoff.

## Target and previously closed results

The exact construction attains Q=1105/256. The missing theorem is R^2>=Q for **all nine independently rotated physical unit squares**, followed by complete equality necessity/converse.

The common-coordinate-separable class is already closed by hand. Unrestricted minimizers have a physical force-and-torque stress, actual contact points, radial positive bridges and controlled tree geometry. The <=19 planar translational support and <=27 physical incidence certificate are distinct; the body-pair graph need not be planar.

In the declared radius window 79/40<=R<=sqrt(Q), the positive-tree reduction forces R^2=17/4 and exactly six unloaded origin-incidence profiles. The lower window is an explicit imported n=8 dependency unless separately proved by hand.

## Updated six-case tree ledger

| Case | Entire original profile | Current completion status |
|---|---|---|
| TREE.20 | Two side-origin bodies | OPEN, included in P.ALL |
| TREE.11 | Side-origin plus vertex-origin body | Exact core normal form CLOSED; Y.ALL or P boundary capacity OPEN |
| TREE.12 | Side-origin plus two vertex-origin bodies | CLOSED hand: cardinal cage <=8 total |
| TREE.02 | Two vertex-origin bodies | Point-only TREE.02.P CLOSED; shared-edge TREE.02.E reduces to P endpoint |
| TREE.03 | Three vertex-origin bodies | **NEW CLOSED hand: annular angular capacity <=8 total** |
| TREE.04 | Four vertex-origin bodies | CLOSED hand: central 2x2 block <=8 total |

These cases retain all continuous parameters and every unstressed physical square. Counts of closed rows are not percentages of unrestricted proof completion.

## What was proved in this continuation

### TREE.03: three vertex-origin squares leave room for at most five others

[THREE_VERTEX_ORIGIN_CAPACITY.md](THREE_VERTEX_ORIGIN_CAPACITY.md) starts from physical packing alone at q=17/4. Three right-angle origin cones leave angular gaps totaling pi/2. The actual central-square exclusion and center-distance bounds put all other centers in those gaps at radii between 1/sqrt(2) and 3/2. Two such centers with angular separation <=pi/6 are strictly closer than one. Six extras distributed among at most three gaps would require >pi/2. Thus at most eight squares fit, with arbitrary extra rotations.

### TREE.02.P: the entire point-only central-contact family is excluded

[TREE02_POINT_CONTACT_COMPLETION.md](TREE02_POINT_CONTACT_COMPLETION.md) uses the selected **strictly exposing** normal at the two roots' point-only contact. Both roots then require two positive radial terminal loads, yielding four distinct S terminals and a six-body core.

[RADIAL_SECTOR_POCKET_CAPACITY.md](RADIAL_SECTOR_POCKET_CAPACITY.md) supplies physical ray screens and all-angle pocket capacities. An acute pocket is empty; a right-angle pocket admits one unique square; a moderately obtuse pocket through angle 2 arctan(2) admits at most two. Terminal separation makes this range exhaustive for the two complementary pockets. At most two extras fit, again eight total.

The shared-edge root boundary is not falsely excluded: it is exactly the endpoint path with both inner heights +1/2 or its reflection. Arbitrary non-strict origin-normal stress is a different certificate and is retained as a negative control.

### Exhaustive remaining-tree reduction: only P and Y

[REMAINING_TREE_TWO_FAMILY_REDUCTION.md](REMAINING_TREE_TWO_FAMILY_REDUCTION.md) proves that every surviving tree candidate contains one of these skeletons:

**P.ALL, OPEN:** four aligned squares centered at

    (-3/2,0), (-1/2,tau_1), (1/2,tau_2), (3/2,0),
    -1/2<=tau_1,tau_2<=1/2,

with FIVE further arbitrary physical unit squares in D_(17/4). The flat row is excluded, but the entire staggered parameter square is not.

**Y.ALL, OPEN:** for 0<alpha<1 and 0<theta<pi/2,

    H=[-alpha,1-alpha]x[0,1],
    u=(cos(theta),-sin(theta)), v=(-sin(theta),-cos(theta)),
    K={a u+b v:0<=a,b<=1},

together with S(up),S(u),S(v), each radial terminal centered at (3/2) times its direction, and FOUR further arbitrary squares. Force balance gives the exact terminal-weight ratios sin(theta),cos(theta). The theta endpoints reduce to P. A genuine nonaligned five-body core exists, so its completion capacity—not core impossibility—is the missing theorem.

This is an exhaustive necessary normal form for the remaining tree branch, not a proof of P.ALL or Y.ALL.

## Exact executed validation

The committed [check_origin_pockets.py](check_origin_pockets.py), source `607d51b10bb9c96de47d17f984b1632282101b79`, was matched to its Git blob and SHA-256 before execution. The pinned run passed at **2026-10-23 14:29:10–14:29:11 UTC**, Python 3.13.5, exit 0; an identical rerun passed at 14:44:50 UTC.

[ORIGIN_POCKET_EXACT_CHECK.json](ORIGIN_POCKET_EXACT_CHECK.json) records **1,716 exact rational checks**, sharp physical attainment, a strict-normal six-body core and shared-edge/non-strict-normal controls, with every corner, SAT pair, application point and force/torque equation checked exactly. These are finite regressions, not an all-angle proof, independent audit or Lean certificate.

## Remaining mathematical work

1. **P.ALL:** exclude five additional physical squares for every staggered path, without a false two-per-side assumption.
2. **Y.ALL:** exclude four additional physical squares for every side/vertex fan, with all alpha/theta values and true oblique separators.
3. **CYCLIC:** a sharp exhaustive physical cover or global inequality when every selected positive stress component has a cycle. Tree radiality does not apply to nonbridge edges.
4. Include the explicit lower-window dependency, assemble unrestricted optimality, prove every equality family, independently audit and formalize through the standard Lean kernel.

PR #11 remains draft. No unrestricted completion, independent full audit, Lean compilation or CI success is claimed.