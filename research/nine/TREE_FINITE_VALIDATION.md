# Finite-tree continuation: proof checks, physical witnesses, and verification boundary

**Checkpoint 2026-10-23.** Companion to TREE_BODY_LOCALIZATION.md, TREE_RADIUS_QUANTIZATION.md, TREE_FINITE_COMPLETIONS.md and FINITE_TREE_CASE_LEDGER.md. The new manuscripts are hand arguments, not independently audited or Lean-verified. The executed script below checks finite witnesses and displayed identities; it is not a proof of all cases.

## 1. Exact executed source and result

- Script: [check_finite_tree_cases.py](check_finite_tree_cases.py), committed as `8a6eea10cd83379e11190a81309248537d5c6cc8`.
- Before execution the local source matched the GitHub file's blob SHA-1 `4262f357214c9067124212dbeb2d2a2d2cd9ec34`.
- Source SHA-256: `5501e227abf47b5c2f9a714dec8a69113c22f59717b4f7d552096c9e59570c9a`.
- Actual run: 2026-10-23 **13:20:52.173306–13:20:52.299435 UTC**, Python **3.13.5**, exit status **0**.
- Report: [FINITE_TREE_EXACT_CHECK.json](FINITE_TREE_EXACT_CHECK.json), commit `dad17aec9e8b6f2729db7c78044e85782f22c144`.
- Command:

```sh
python check_finite_tree_cases.py \
  --source-commit 8a6eea10cd83379e11190a81309248537d5c6cc8 \
  --output FINITE_TREE_EXACT_CHECK.json
```

The script uses exact rational arithmetic and the exact quadratic field Q(sqrt(2)), implemented with Fraction. It does not use floating-point inequalities, external solvers, a numerical optimizer or an external package.

**Passed:** 909 rational checks; all six integer incidence profiles; seven physical force/torque-balanced tree examples; an eight-square cardinal-cage packing; a larger-radius cage negative control; and a staggered-row negative control. Each physical example checks every square corner, all pairwise true SAT alternatives, each force point's membership in both actual squares, support-face signs, all center balances and all angular balances. Circle weights are normalized to sum to one.

The rational-parameter identity checks are **finite regressions**, not an all-angle exhaustive proof. The all-angle theorem is the symbolic factorization and geometric argument in TREE_FINITE_COMPLETIONS.md.

## 2. Nonaligned TREE.11 really exists as a stressed five-body core

Let

    e=(0,1), u=(1,-1)/sqrt(2), v=(-1,-1)/sqrt(2).

Take five squares:

1. H centered at (0,1/2), standard axes;
2. K centered at (u+v)/2=(0,-1/sqrt(2)), side axes u,v;
3. S_e centered at (3/2)e, side axes e,Je;
4. S_u centered at (3/2)u, side axes u,Ju;
5. S_v centered at (3/2)v, side axes v,Jv.

All fit the disk of squared radius 17/4, with physically disjoint open interiors. H contains zero in the relative interior of its lower side; K contains zero at its upper vertex. Thus this is case (s,v)=(1,1), with genuinely different square frames.

Use the directed positive contacts below; normals point from tail to head:

| Tail -> head | Point | Normal | Raw weight |
|---|---|---|---|
| H -> S_e | e | e | sqrt(2) |
| H -> K | 0 | -e | sqrt(2) |
| K -> S_u | u | u | 1 |
| K -> S_v | v | v | 1 |

At a radial S leaf in direction d, its two outer circle vertices are 2d +/- (1/2)Jd. If its contact weight is mu, give each outer circle atom raw multiplier mu/8; their total gradient is mu*d and balances the incoming contact. Normalize every multiplier by the total raw circle weight (sqrt(2)+2)/4.

The two unloaded bodies have zero net contact force. Each contact line is radial; consequently their force balance also gives zero angular moment. The exact script checks the full original equations rather than relying solely on this description.

**Negative-control meaning:** it is FALSE that all nonaligned positive trees or all three-loaded trees are impossible at radius sqrt(17/4). The missing TREE.11 theorem must bound the capacity of the **four other physical squares**. It must not declare this five-body stress infeasible.

## 3. TREE.12 has a physical seven-body core, despite its ninth-square completion being impossible

Let the unloaded central squares have centers

    H=(0,1/2), L=(-1/2,-1/2), B=(1/2,-1/2),

and add the four cardinal S leaves N,E,S,W centered at (0,3/2),(3/2,0),(0,-3/2),(-3/2,0). All seven squares are axis-aligned.

There is a positive **tree** certificate with six raw unit-weight contacts:

    H->N at (0,1), normal up;
    H->L at 0, normal down;
    L->B at 0, normal right;
    L->W at (-1,0), normal left;
    L->S at (0,-1), normal down;
    B->E at (1,0), normal right.

Each of the four leaves has two outer circle atoms of weight 1/8 each, so the total circle weight is one. Every contact belongs to the physical intersection and all center/angular equations vanish exactly. Other physical contacts with zero weight are allowed.

This realizes TREE.12 with only seven squares. The new theorem closes **all completions to nine**, using the cardinal cage's capacity <=8. It does not falsely exclude the seven-body core itself.

## 4. Boundary and below-window controls

- The four-square two-loaded path with inner offsets (tau_1,tau_2)=(1/3,-2/5) realizes TREE.20.
- Offset (1/2,0) changes the central incidence to TREE.11.
- Offset (1/2,-1/2) changes it to TREE.02.
- The flat path (0,0) is also checked.
- The five-square plus configuration at q=5/2 carries a positive star stress with an origin-interior unloaded hub. This lies **below** the declared 79/40 lower-radius window. It refutes any version of the star/interior-root exclusion that forgets that premise.
- A unit square centered at (1,1), together with the four cardinal cage squares, fits q=9/2. Thus the cage proof's q=17/4 restriction is essential.

All of these controls were checked in exact arithmetic, not inferred from drawings.

## 5. A tempting staggered-completion shortcut is false

The four squares centered at

    (-3/2,0), (-1/2,-1/2), (1/2,-1/2), (3/2,0)

have three further disjoint squares above them, centered at

    (-1/2,1/2), (1/2,1/2), (0,3/2).

All seven fit q=17/4. Therefore it is **false** that every side of every staggered four-chain holds at most two squares. Any proof of TREE.20 must couple both complementary regions or use another whole-configuration invariant. The extra square at (0,-3/2) gives a feasible eight-square cross.

This negative control prevents replacing the open two-slider completion problem by an incorrect independent two-per-side capacity bound.

## 6. Local completeness clarification for TREE.F1.4

In the off-origin unloaded-body proof, force balance requires not only an incoming edge but also an outgoing edge. If all incident edges were incoming, they would act at the body's unique nearest point and all have the same nonzero parallel sign, so their positive weighted sum could not vanish. Thus an outgoing S neighbor exists before applying the far-face circle-intersection argument. This supplies explicitly the implication used in TREE_BODY_LOCALIZATION.md, Section 5.

## 7. Verification and status limits

The universal six-case coverage follows from the analytic tree-radius/origin-cone proof, not from enumerating the six integer pairs in Python. The two closed capacity cases use symbolic geometric arguments. The script is a reproducible check of identities, positive stress examples, tangent boundary cases and falsification controls.

**Not performed:** independent full mathematical audit, Lean compilation, CI, or a universal proof for the four remaining tree completions or cyclic components. The unrestricted n=9 theorem remains open.