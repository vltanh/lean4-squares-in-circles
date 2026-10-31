# PR #11 current continuation: cyclic three-port modules and sharp contact geometry

October 31, 2026. Branch: research/nine-tablefree-hand.
Input head: 8e8413d6abbb29663f70cf5511da45905b678763.
Substantive new commit: fdcbe2fd1aa7768fdd0f5d0d16077b1b3993d969.

**The unrestricted n=9 theorem remains OPEN. New original fine/coarse closures: zero.** Fixed coverage remains 37/58 coarse, 2373/2513 fine, and 18/38 six-body exterior. The new results are complete hand derivations with a self-check, not independent reviews or formal verification. No Lean, Lake, CI, numerical experiment, or mathematical proof script was used in this continuation.

## 1. Completed three-port cyclic-module theorem

Read:

    THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md

For any connected entirely unloaded actual module K in the target disk, with exactly three **full original positive cut edges** and exactly one independent internal cycle,

    |K|<=5.

This includes arbitrary external degrees, original means, orientations, repeated external terminal bodies and physical zero-weight boundary contacts. It does not depend on generic normal selection or on the remaining actual squares being unstressed.

The full topology is proved, not assumed: there are exactly three true-degree-three hubs, their reduced internal graph is a triangle, and each has one exit arm. Every channel has at most one genuine unloaded degree-two internal body. With t subdivided triangle edges and s subdivided exit arms, the only remaining pairs are

    (t,s)=(0,0),(0,1),(1,0),(1,1),(2,0).

In (1,1), the exit can be at an endpoint of the subdivided cycle edge or at the opposite hub. This is a necessary cover, not an existence assertion or a finished completion-capacity theorem.

The old uncommitted claim in the preceding conversation is superseded by this manuscript. The new bound is five, not merely the earlier cycle-rank estimate of six. Combining the existing three-port tree bound with the new theorem: any connected unloaded module of at least six bodies behind three full cut edges must have **at least two independent internal cycles**.

### Mechanism 1: parallel-channel rigidity

Two true unloaded degree-two channels between the same actual endpoint squares realize their exact set distance. The minimum displacement vector in the convex Minkowski difference is unique. Thus both channels have the same signed normal and width. A true-degree-three unloaded endpoint then makes its third force opposite to this normal. Actual support telescoping across that endpoint and one transmitter creates a gap of at least two at the other endpoint, forcing that endpoint loaded. Hence such a parallel pair cannot meet an unloaded degree-three hub.

This removes all one-/two-hub and multiple-edge unicyclic alternatives without shortening any original degree.

### Mechanism 2: a whole-module force concentration bound

This result is broader than the three-port theorem. For any connected reduced unloaded branching module, with at most one reduced exit channel at each branch, define:

- D: total direct internal channel magnitude;
- N: total subdivided internal channel magnitude;
- C: total exit magnitude;
- A: magnitude carried by subdivided exits;
- Delta=2(D+N)-C>=0, the full force-triangle deficit.

Then

    D>29N+30A+(31/2)Delta,
    N+A+Delta/2<C/60.

All original cyclic/chorded internal work is retained before these estimates. Thus over 29/30 of internal force is carried by direct channels, and subdivided exits carry less than 1/60 of the cut magnitude. No inference that every individual direction is close to another is made when a force can be arbitrarily small.

The three-cut force triangle prevents two exit arms from both being subdivided. The same budget excludes a triangle with all three edges subdivided. If two triangle edges are subdivided, its sole direct edge dominates their combined force by a factor exceeding 29; this then excludes every subdivided exit arm. These are complete exclusions of whole topology features, not sampled poses.

## 2. A sharp physical contact-radius theorem

Read:

    SHARP_CONTACT_RADIUS_AND_NEAR_LONG_ENDPOINT_LOAD_2026_10_31.md

For every actual shared point p of two disjoint-interior unit squares in D_R and every common supporting unit normal n,

    |p|^2+1+2|p.n|<=R^2,
    |p|<=sqrt(R^2-1).

The proof is short: p-n lies in the first square and p+n in the second; expand their two disk inequalities. Every side-interior point, original shared-side mean, endpoint, free point contact and zero-weight physical contact is covered. The bound is sharp, with the two-square equality geometry proved in the manuscript.

At Q, the sharp contact radius is sqrt(849)/16. The old 29/15 contact bound remains valid but is unnecessary for this new argument.

The new endpoint consequence replaces the old gap-two threshold by 39/20. If two actual squares A,B satisfy

    e.(c_B-c_A)-h_A(e)-h_B(e)>=39/20,

their outward dominant own sides are entirely contact-free. An actual positive inward force at either endpoint therefore forces positive circle load in that endpoint's full unchanged force equation. Endpoint degree and every other force are unrestricted. A geometric witness square need not be a positive neighbor. This theorem is independent of the nine-square count and of a generic certificate choice.

## 3. Preceding sharp paired-gap result remains available

Commit 8e8413d6 proves FOUR_SQUARE_PAIRED_GAP_HAND_COROLLARY_2026_10_31.md. For four actual distinct squares,

    46 g_e(M_L,M_R)+(27/2)g_e(B_L,B_R)
       <=211/2-119(r-R),   r=sqrt(1105)/16.

Gaps at least two and one give the sharp radius. For an actual four-chain with span excess G, every pair of the other five actual squares satisfies

    g_e(C,D)<=1-(92/27)G-(238/27)(r-R).

Their five projection intervals all meet a common interval of that length. These are conditional terminals, not a universal extraction of the paired gaps. The exact eight-square T/cross remains the relevant negative control for an unjustified extraction.

## 4. Broad scope and what is not closed

| Structural scope | Completed implication | Remaining issue |
| --- | --- | --- |
| Any physical contact in any sized unit-square packing | Sharp contact-radius and signed normal bound | Does not give a nine-square count |
| Any endpoint with gap at least 39/20 and a positive inward force | Positive circle load at arbitrary degree | Such gaps need not occur in every remaining core |
| Any one-exit-per-branch unloaded reduced module | Full force concentration inequality, with cycles/chords retained | Small positive forces cannot be discarded; no universal cycle elimination yet |
| Any three-cut unloaded tree or unicyclic module | At most three or five bodies, respectively | Higher cycle rank and the displayed small unicyclic survivors |
| Any actual four endpoint squares meeting the paired-gap thresholds | Sharp target radius | General extraction/joint T-shaped completion remains unproved |

The five unicyclic rows are not new canonical gate IDs. The original 58 coarse and 2513 fine denominators are unchanged. No original row is marked closed without its complete original-domain caller.

## 5. Continuation priorities

The useful new broad question is whether full force concentration, together with the near-long endpoint theorem and actual contact geometry, excludes the remaining cyclic modules or forces a sharp paired-gap terminal. A proof must handle arbitrarily small positive forces without deleting them. Do not restart a list of individual load masks merely because the necessary triangle profile table is finite.

The separate joint completion obstruction for a four-chain and five extras is still open. A T-shaped triple does not itself supply a parallel three-chain. The opposite-side capacity must be treated in the same argument.

Mixed-side articulation interfaces, circle-clear root neighbors, distant endblock loads, short/branching cores, global equality, and the G4.2.c prerequisite audit remain as in ADOPTION_PHYSICAL_CAP_AND_GLOBAL_CUT_THEOREMS_2026_10_31.md and N9_GLOBAL_PROOF_REORIENTATION_2026_10_31.md. The detailed local fallback and original open coarse IDs remain in HANDOFF_PR11_2026_10_30_PUSH_CURRENT.md. No new common-normal avoidance was introduced here.

## 6. Controls and verification record

The five-square cross has a four-edge cut at its central body, not the three-edge unicyclic premise. The eight-square cross has a four-cycle of unloaded central bodies with eight outgoing edges, so it also lies outside the new size theorem. The known sharp anchor stresses have no contradictory three-port six-body unloaded unicyclic module. The sharp two-square contact example explicitly retains equality at the new contact radius.

The hand self-check reconstructed the full degree sum, the nearest-displacement uniqueness argument, the work identity signs, the factor-29 inequality, the three-cut force triangle, the two-subdivided-edge exclusion, the inward unit segment at a support point, and all printed rational endpoint margins. There was no independent second reviewer and no kernel check. All new substantive manuscripts are attached to a branch commit, rather than left in an unattached Git tree.
