# Four-hub rank-two three-port module: exactly two diamond/exit topologies

Date: 2026-10-31. Hand-only original-graph structural lemma for PR #11.

**Status:** Hand-proved *necessary* finite graph-and-true-transmitter census; independent review pending. No physical exclusion of the two diamond families, original coarse parent, or unrestricted nine-square bound is claimed.

## Precise physical hypotheses

Fix the **same original planar selected positive body-pair stress** on nine actual unit squares in a disk with $R^2\le1105/256$. Let $K$ be a nonempty connected **selected-circle-unloaded** set with exactly three **original** positive cut edges and internal positive-graph cycle rank two. All full original positive degrees include cut incidences and any additional positive chords. There are exactly four true full-degree-at-least-three hubs, and all other vertices of $K$ have original full positive degree two.

No hypothesis restricts how the three exits are distributed. External terminal squares may repeat. A true-degree-two body on an exit arm is a real body, not an omitted original edge.

**Theorem.** Up to relabeling, the reduced internal hub graph is the simple diamond $K_4-e$. The original hub full-degree multiset is $(4,3,3,3)$, and precisely two distinct **hub/exit configurations** exist, distinguished by the missing diamond edge:

| Case | Missing reduced internal edge | Internal hub degrees | Three reduced original exit stubs |
|---|---|---|---|
| **D-peripheral** | $AH$, where $A$ is the unique true full-degree-4 hub and $H$ is one true-degree-3 hub | $A:2$, $H:2$, $B:3$, $C:3$ | **two** at $A$, **one** at $H$ |
| **D-central** | $BC$, between two of the true-degree-3 hubs | $A:3$, $B:2$, $C:2$, $H:3$ | **one each** at $A$, $B$, and $C$ |

Each of the **five reduced internal hub edges** and each of the **three reduced exit arms** contains zero or one *genuine* full-degree-two transmitter. There are at most **three transmitters total** among these eight slots, because $K$ has at most seven real bodies. Thus $(t,s)$, the number of transmitted internal links and transmitted exits, satisfies
\[
0\le t\le 3,\quad 0\le s\le3,\quad t+s\le3.
\]
The two displayed cases and these finite length constraints are **necessary**, not sufficient, for an original physical nine-square configuration. They retain every original force and moment equation; no virtual contracted contact is substituted for a transmitted edge.

## Complete hand proof

**1. Original degree excess.** The full original handshaking equation of [THREE_PORT_DEGREE_SIGNATURE_CENSUS_2026_10_31.md](THREE_PORT_DEGREE_SIGNATURE_CENSUS_2026_10_31.md) gives
\[
\sum_{v\in K}(d_{\rm full}(v)-2)=2b+p-2=5.
\]
With exactly four positive summands, the *only* partition of five into four positive integers is $2+1+1+1$. Thus the four full degrees are $4,3,3,3$, and there are no additional hubs hidden along an exit path.

**2. Reduced internal graph.** Suppress **only** original unloaded true-full-degree-two paths, recording the three original cut edges as distinct stubs with their unchanged physical terminals. The internal hub multigraph remains connected with cycle rank two, so it has $h-1+b=4-1+2=5$ edges. A returning loop cannot occur: a true-degree-two transmission loop would telescope strictly positive supported widths back to the same body. Distinct parallel reduced hub edges cannot have a true-full-degree-three unloaded endpoint: if both paths were direct, the original body-pair graph would duplicate an edge; if one were direct and the other transmitted, they would imply both zero and positive separation; if both were transmitted, the original two-parallel-channel/long-endpoint theorem forces that endpoint positively circle-loaded. These exact local facts were hand-proved in [THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md](THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md), Sections 2–3.

There is only one hub of true original degree greater than three. Therefore **every** potential pair of different hubs has at least one true-degree-three endpoint, so no parallel reduced pair survives. The internal reduced hub graph is a *simple* connected four-vertex graph with **five** edges. The complete four-vertex simple graph has six edges; removing exactly one yields $K_4-e$, with no other graph isomorphism type.

**3. The two actual original exit placements.** At a hub, its number of *reduced original exit arms* is exactly its original full degree minus its reduced internal degree. If the missing edge meets the unique full-degree-four hub $A$, label the other endpoint $H$. The two degree-three internal vertices then have degree three, while $A,H$ have internal degree two. The reduced exit counts are $4-2=2$, $3-2=1$, $3-3=0$, $3-3=0$: D-peripheral.

If the missing edge instead joins two full-degree-three hubs $B,C$, the full-degree-four hub $A$ and the remaining full-degree-three hub $H$ each have internal degree three, while $B,C$ have degree two. The reduced exit counts are $4-3=1$, $3-2=1$, $3-2=1$, $3-3=0$: D-central. This is exhaustive because every missing edge either meets $A$ or does not. It does **not** assume each true hub has at most one reduced exit, and specifically **retains** D-peripheral's two arms at $A$.

**4. True bodies and finite transmitter length.** Every reduced internal link or exit arm can contain **at most one** true original unloaded full-degree-two body by the original long-supported-endpoint theorem, as used in the same unicyclic source, Section 2. This argument applies to real transmitted exit arms as well as hub-to-hub channels. The stress component containing $K$ has at least two distinct positively circle-loaded actual squares **outside** $K$, so $|K|\le9-2=7$. With four actual hubs, there is room for at most three genuine transmitter bodies total. Consequently the number of transmitted reduced internal and exit channels obeys $t+s\le3$, as stated.

No orientations, physical junction ownership, contact application means, zero-corner coefficients, or actual completion squares have been eliminated.

## Open mathematical question, not silently checked

For **both** D-peripheral and D-central, excluding the actual all-direct and up-to-three-transmitted variants with **the full original three-cut force/torque and nine-square completion** remains open. The two diamonds are the *complete reduced hub/exit topology* at this scope, but a finite topology does **not** imply that every continuous square pose has been bounded.

This is an internally written hand proof, not a certified complete milestone M30 or an independently audited proof. It supplies a *smaller source-closed necessary classification* for an active task in the operative ledger.

No Lean/Lake, CI, enumeration programs, numerical pose exclusion scripts, or external mathematical certificates were used.
