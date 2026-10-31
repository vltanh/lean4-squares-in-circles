# n=9 — Global proof reorientation: seek mechanisms, not load-row checkpoints

> **Substantive continuation now available:** [ADOPTION_PHYSICAL_CAP_AND_GLOBAL_CUT_THEOREMS_2026_10_31.md](ADOPTION_PHYSICAL_CAP_AND_GLOBAL_CUT_THEOREMS_2026_10_31.md) proves and hand-reviews a physical cap inequality giving an unrestricted 4+3 projection-chain terminal, a full-cut unloaded-tree bound, a universal boundary-contact margin, arbitrary-degree common-side endblock pressure, and a whole-angle restriction on negative neighboring circle access. These are actual broad lemmas, not proposed gates. They do not establish universal chain extraction, cyclic/branching completion or arbitrary mixed-side endblock incompatibility. Original counts remain unchanged. The research programs below retain those exact missing scopes.

October 31, 2026. **This is the current research strategy for PR #11.** It supersedes the proposed four-row R1 attack in the former N9_RESET_HAND_PROOF_GATES_2026_10_31.md. The 58 coarse and 2,513 fine original IDs remain fixed, but **their enumeration is NOT the discovery order**. The project must prove whole-family structural results across sizes, not treat individual load rows as the principal research target.

**Status:** No new original full-row proof in this strategy reset. Radius target R² >= 1105/256 and equality remain OPEN. Original ledger is 37/58 coarse, 2373/2513 fine, six-body exterior table 18/38. Do not confuse a complete proper-feature manuscript or an exploratory calculation with a canonical closure. No Lean/CI or external mathematical proof scripts.

## 1. Why the previous reset was still inefficient

The former first-priority proposal targeted four entire graph/load rows by a new joint exterior-pocket theorem. Even successful closure would change 2373/2513 to 2377/2513 fine and **leave all 21 coarse parents open**. Its proof might be as hard as a whole coarse parent. Closing the final A-only UU mask of D02.L135 would advance just one other fine row, and D02.L1345 and the six-body coarse parent would remain.

These are legitimate endgame activities, but not the best use of exploratory hand-proof effort. The coarse ledger is a coverage test, not a good mathematical decomposition. Repeatedly splitting actual contact features has made hundreds of valid local results without revealing a universal reason that nine squares cannot fit.

Change the discovery basis to: **occupied annular arcs; central square obstruction; signed positive-stress transmission and its branching defects; and effective endblock force/torque cuts.** Let the original graph/load rows become final theorem instantiations once a mechanism is complete.

## 2. Strong existing facts that are already independent of the case table

Let Q=1105/256 and assume the established radius window 2<R<=sqrt(Q) for an original nine-square minimizing candidate.

### 2.1 Unconditional boundary-gap inequality [PROVED in the existing hand source]

For any t>=2 distinct actual circle-touching squares S_i in the cyclic order of their actual boundary corners, let D_i=dist(S_i,S_(i+1)). Then

    sum_i D_i < tau*(8-t),    tau=5*pi/16<1.             (G)

This has **no stress, degree, chord, contact-graph, force or orientation premise**. It follows from the fact that every actual boundary square contains an open arc longer than pi/4 on |x|=5/4 and its boundary-corner direction lies in that same arc. The sum of inter-arc circular distances pays for the actual set gaps. Source:

    OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md, Theorem 1 and Sections 2–4.

A useful exact corollary not requiring ANY positive graph is the following. If k of the t consecutive set gaps have D_i>=1, then

    k <= sum_i D_i < tau*(8-t) < 8-t,

so by integrality

    k <= 7-t.                                           (G1)

For t=7 there is no such gap; for t=6 at most one; for t=5 at most two. This is one universal boundary-resource law, not a new fine proof checkbox. It should be applied first *before* introducing 38 graph/load orbits.

### 2.2 Unconditional inner-arc occupancy [PROVED in existing hand sources]

Every actual square with center norm at least 1 occupies an inner circle |x|=5/4 arc longer than pi/4, and thus at most seven actual squares may have center norm >=1; every nine-square packing has at least two centers inside |x|<1. Related universal central-clearance and connected-center arc inputs are in

    ANNULAR_CENTER_ARC_BUDGET.md;
    UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md;
    ANNULAR_CENTER_ARC_AT_23_25.md.

These facts do NOT say there are exactly two central squares, and do NOT by themselves exclude nine squares. A direct nine-square proof would have to relate the arrangement of the two-or-more near squares to how much annular space the others lose.

### 2.3 What is already closed at larger scopes [PROVED under printed hypotheses]

1. A compatible *simple positive cycle* whose nonboundary internal vertices have genuine degree two has at most seven bodies. The strong marked-cycle theorem permits arbitrary additional degree at its boundary marks; it does not permit arbitrary additional force at a circle-clear internal branch.
2. With only degree-two single-transmitter channels between loaded bodies, every complete simple cycle has at most two additional physical square completions, by an injective assignment to actual near-origin units. This closes all bare C6 but is not automatically sharp for a C7 with two extras.
3. The entire actual physically boundary C7 branch, all true long-run simple-cycle cases, two-RR short C7, and simple m>=8 cycles already have hand exits at their precise scopes.
4. All same-root triangle petals and several return-free three-root/leaf arrangements have full-degree local capacity or pressure theorems, but their signs are not automatically inherited by arbitrary endblocks.

None of these statements makes an arbitrary chorded block into a simple cycle.

## 3. Why we cannot merely replace every branching vertex by one unit of boundary gap

A literal counterexample is the *five-square cross* in a disk of radius sqrt(5/2), which is comfortably below sqrt(Q):

    C=[-1/2,1/2] x [-1/2,1/2],
    N=[-1/2,1/2] x [1/2,3/2],
    E=[1/2,3/2] x [-1/2,1/2],
    S=[-1/2,1/2] x [-3/2,-1/2],
    W=[-3/2,-1/2] x [-1/2,1/2].

Their open interiors are pairwise disjoint and every farthest corner has norm at most sqrt(5/2). C has four actual side contacts and can be force-balanced by equal normal forces along opposite pairs. N and E are consecutive exterior bodies connected via C, but they *also share the point (1/2,1/2)*, so dist(N,E)=0.

Consequently a false direct generalization of the straight true-degree-two result would assert dist(N,E)>=1 merely because C is intermediate. This is false even when the intermediate unit has balanced positive contacts. The physical branching unit is spending *central room* instead of *outer-circle angular gap*.

The new central challenge is to quantify this tradeoff without discarding the other squares: **a loss of straight-run width at a branching clear square must be paid for by an occupied central region or an alternative angular/force obstruction**. This is a research direction, not a proved charged-width lemma.

## 4. THREE mathematical research programs, with early falsification before large proofs

These are competing routes, not a chronological 20-row case crawl. A successful strong enough program may bypass the others. Run simple exact hand tests first on *opposite extremes*, not months of angle subgates.

### Program A — A global two-resource packing inequality (no stress in the final statement) [OPEN, highest leverage]

Aim for a **single direct geometric invariant** coupling occupied annular arcs with the area/angle of squares crossing the central disk. The proved boundary gap budget (G), the occupied arcs for center >=1, and the small-disk/three-near-square lemmas are inputs. The resource is not just an annular angle and not just the number of near squares; the five-square cross shows these are interchangeable in certain local patterns.

A possible form to investigate is a charge for each square to exactly one of:

* a disjoint occupied inner-circle arc;
* a genuine crossing/blockage of a fixed inner-disk radial sector;
* a joint center-cluster arrangement which strictly reduces the available complementary annular arcs.

No charge may be used twice. The desired output is a quantitative upper bound of **eight total units for R<sqrt(Q)**, with a separate sharp equality analysis when R=sqrt(Q), independent of the selected stress and 58 coarse profiles.

**Short feasibility tests BEFORE proving a grand theorem:**

A1. Classify the exact annular sectors of the five-square cross. Any proposed center charge must be correct there (this is a *negative control*, not a nine-square counterexample).

A2. Check its sharp behavior on the known nine-square construction at radius sqrt(Q). A proposed **strict** inequality valid all the way through equality that excludes all nine is false; a valid inequality must have an allowed equality configuration or use strict R<sqrt(Q).

A3. Derive an actual **two-/three-near-unit angular-loss lemma** with a continuous angle bound and a concrete premise, rather than conjecturing that exactly two units meet the central disk. A lemma with no falsifiable scalar reserve is not ready for a large proof project.

**Go/no-go:** if no additional angular loss can be proved on both the cross and the sharp nine-square witness, keep this path as exploratory and redirect to Program B. Do not expand it into hundreds of center-offset cases.

### Program B — Branch-compensated exterior-cycle/width theorem [OPEN; potentially covers 11 one-block parents]

Take the outer facial cycle of a selected positive biconnected block and mark its actual boundary bodies. On every intervening segment with true unloaded degree-two internal vertices, the existing telescope gives

    D_i >= sum_(internal j) 2*h_j(n) >= #internal vertices.

At a circle-clear branching vertex, two successive positive normals need not match, and this lower bound can fail by an entire unit (five-square cross). A correct extension must introduce a physically grounded **branch defect**: either establish a strictly positive angular gap, or identify a *distinct actual occupied central obstruction* that can be charged once in the nine-square completion.

A plausible design is to route the outer face through its **original actual contacts**, not delete its chords. For each turning/branching clear square, prove a local dichotomy using its complete positive force/torque star and circle-clear geometry:

* **gap case:** a certified positive lower bound for the actual boundary set gap;
* **center case:** an actual full unit occupying a central sector, with a proven reduction in joint remaining-square capacity.

The dichotomy must compose without overlapping charges, and the final inequality must retain all 9-m extras. It may need a local shared-corner junction correction. Do NOT assume a branch can simply be straightened or promoted while keeping the same stress.

**Short feasibility tests:**

B1. Use the physical five-square cross to refute any overstrong width claim.

B2. Apply the *same proposed dichotomy* first to a six-body D02 chorded rim with two clear branching hubs and to a nine-body chorded block with no extras. If the hypotheses cannot even be formulated at both extremes, it is not yet a uniform mechanism.

B3. Test the seven-body one-/zero-RR survivor with two extras: an argument that counts only the seven core bodies is not a nine-square contradiction.

**Potential reach:** all 11 original one-block open cells, including the size-5/bridge exception, if attachments and the whole positive stars are handled. In particular the 10 one-block parents having cyclic block order >=6, distributed 4+3+2+1 over block sizes 6,7,8,9, should be approached as *one structural family*, not as 10 unrelated angle charts. This reach is conditional; no full one-block theorem is claimed.

### Program C — Effective endblock wrench and articulation obstruction [OPEN; potentially covers ten two-block parents]

There is a universally valid **hand algebraic cut identity** which should be made the shared starting point, instead of treating each 2-block graph/load row separately.

Let U be the vertices on one side of a genuine cut attached to the rest of the positive graph only through a single articulation A. Assume the selected physical equilibrium has, on each u in U, original pair forces F_e at their actual shared application p_e, and outward circle vectors lambda_(u,z) z with lambda>=0. Choose F_e to be the force *into U* from an edge crossing the cut. Summing all original force equations over u in U cancels every internal pair force, giving

    sum_(crossing e) F_e = sum_(u in U) sum_(z physical corner of u)
                              lambda_(u,z) * z.           (W1)

Summing their origin moments cancels internal pair torques because the two forces on each positive edge share their original actual application, and every circle vector is radial along z. Consequently

    sum_(crossing e) p_e wedge F_e = 0.                  (W2)

Here (W1) uses the usual original convention that the circle's inward force on u is -lambda*z; if a source uses the reverse force sign, reverse both sides consistently. The actual original shared-side mean p_e, true degrees, zero individual circle coefficients and every edge to A remain present. These identities hold for *arbitrary internal block shape and degrees*; they are elementary balances, not a sharp geometric exclusion.

The difficult part is to turn this two-component **resultant + origin-moment wrench** into a restricted cone of physically possible interfaces at A. If two genuine endblocks force incompatible interface wrenches at one articulation, all their internal load/mean masks close together. Do not assume a universal positive projection at A: the older petal sign theorem has additional original geometry and cannot automatically transfer to an arbitrary endblock.

**Short feasibility tests:** apply (W1)--(W2) literally to the smallest open two-block cell C2.35.b0 and the no-extra extreme C2.55.b0. Attempt one **quantitative full-star interface cone obstruction** including both block masks. If the desired sign fails in either, preserve the exact geometric counterexample, and split by physically meaningful terminal-block form (triangle/4/5+/attachment), not a new infinite subdivision of angles.

**Potential reach:** all 10 open two-block parents, with 2-block sizes 35,36,37,45,46,55 and varying attachments. The exact old coarse names remain in CYCLIC_CELL_LEDGER.md.

## 5. Structural target matrix — this replaces “finish four D02-related load rows first”

| Remaining structure | Coarse IDs | Best candidate mechanism | Status |
| --- | --- | --- | --- |
| One cyclic block of order 5 plus two bridges | C1.5.b2 (1) | B with attachments, or A | OPEN |
| One cyclic block of order 6 and 0–3 bridges | C1.6.b0,b1,b2,b3 (4) | B; A as bypass | OPEN |
| One cyclic block of order 7 and 0–2 bridges | C1.7.b0,b1,b2 (3) | B plus existing long-run/true-two theorems | OPEN |
| One cyclic block of order 8 and 0–1 bridges | C1.8.b0,b1 (2) | B; existing true-two cycle bound removes a large subdomain | OPEN |
| One cyclic block of order 9 | C1.9.b0 (1) | B; existing simple 9-cycle exclusion applies only at its true-degree scope | OPEN |
| Two cyclic blocks sharing an articulation and any allowed bridges | 10 original C2.* cells | C; A as possible bypass | OPEN |
| **TOTAL** | **21** | **Three reusable directions, not 21 new separate proof projects** | **OPEN** |

These are **aspirational scopes**. A proposed lemma is not considered broadly applicable until its hypotheses have been checked at both a small and a maximal representative. In particular “one-block” must not be silently replaced with “simple cycle,” and “two-block” must not omit the articulation's other positive forces.

## 6. Research sequencing and hard stop rules

This is a **mechanism-discovery loop**, not a sequence of giant endgame tasks.

- First derive, in short hand arguments, **either** an exact branch-width/central-charge dichotomy (B), **or** a strict near-center angular-loss inequality (A), **or** a signed block-interface cone obstruction from (W1)--(W2) (C). Prefer a result with a declared valid range covering multiple original block orders or both ends of the two-block table.
- Require an explicit **negative control and positive test** for every conjectured lemma. Do not invest in a finite printed case table until the relevant continuous scalar inequality is established and its scope is demonstrably reusable.
- If a candidate fails at a small physical model, record its failure and reformulate once. Do not create a growing succession of microgates to protect a false large claim.
- Once a mechanism is proved, build one **scope matrix of all 21 coarse parents**, marking which are literally covered and what *qualitatively different* exception remains. Only then perform original row-level joins for its remaining exceptions.
- Keep the original 20 six-body exterior rows as a **fallback acceptance table**, not the main discovery target. The four empty-central-face rows and unique-V A-only UU can be useful tests of a new mechanism, but completing them alone is not a research milestone of sufficient global leverage.
- In parallel, complete the downstream G4.2.c single-selection/true-degree/normal/physical-mask audit; a geometric lemma that cannot be applied to the original same certificate will not close anything.
- Exact equality at Q is a separate obligation. Never use a false subcritical strictness at equality. Once a global mechanism works, trace equality before opening unrelated pose classifications.
- Only tick a canonical fine/coarse ID after a complete original-domain hand proof; no new sub-gate denominators. Report “new original fine/coarse closures: zero” prominently while true.

**Hand-only contract:** no Lean/Lake run, no CI, no external script used to prove exclusions. Printed short rational comparisons and hand structural arguments are allowed. Exploratory computer tests may only challenge attack directions, and are never premises.

## 7. What counts as the *next* substantial result

A good next result is **not** a bound for one A-only endpoint. It is one of:

1. A direct annular/center capacity inequality with at least one nontrivial full nine-square physical caller, regardless of stress;
2. a branch/turn defect theorem valid for multiple cyclic-block orders, with a genuine actual-square budget rather than a purely graph-theoretic penalty;
3. a cut-wrench cone incompatibility valid for multiple two-block profiles with full actual means and circle loads.

Each can eliminate or sharply simplify a *structural class* containing several original coarse parents. If all three prove too ambitious or false, return to the 20-row explicit table, but explicitly acknowledge that this is a fallback exhaustive-proof program and not the primary conceptual route.

No present record asserts any of (1)–(3) has been proved. The established inputs (G), (G1), (W1), (W2) and the five-square counterexample are sound hand observations; (G1) is a new immediate corollary of an accepted hand source, and (W1)–(W2) follow by summing its existing physical equilibrium equations.

