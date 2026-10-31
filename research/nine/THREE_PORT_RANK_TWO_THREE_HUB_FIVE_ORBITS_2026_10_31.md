# Five distinct reduced-exit/side-transmitter patterns in the surviving three-hub rank-two module

Date: 2026-10-31. PR #11 hand-only finite case reduction.

**Status:** proved by an elementary hand symmetry argument, **conditionally** on the [previously written rank-two low-hub theorem](THREE_PORT_RANK_TWO_LOW_HUB_UNIFORM_EXCLUSION_2026_10_31.md) and its original planar selected-certificate hypotheses. Independent review pending. These five are necessary graph/true-transmitter **patterns**, not five realized nine-square packings or five physical exclusions.

## Exact scope

In the original nine physical squares with one unchanged planar positive contact-force certificate and squared disk radius at most $1105/256$, let $K$ be a connected selected-circle-unloaded set behind exactly three **original** positive cut edges, with induced cycle rank two and **exactly three original full-degree-at-least-three hubs**. All true degree-two transmitters, contact forces, physical means, original circle-corner masks, outside terminal identities and all nine physical squares remain.

The previously proved full-cut and true-channel lemmas show that any nonexcluded graph has true full hub degrees $4,4,3$. Denote the full-degree-four hubs $A,B$ and the full-degree-three hub $C$. The reduced internal graph consists of two parallel $A$--$B$ channels and single $A$--$C$, $B$--$C$ channels. There is **one reduced original exit arm** at each hub. Both $AB$ channels are transmitted, each by exactly one genuine actual degree-two body, and at least one of $AC,BC$ is transmitted. At most **two further** real degree-two bodies can occur across the other two internal edges and the three exit arms, because the unloaded set has at most seven bodies.

## The five necessary orbits

Use the relabeling symmetry $A\leftrightarrow B$, which exchanges $AC$ and $BC$; the two parallel $AB$ channels may also be interchanged. When exactly one of $AC,BC$ is transmitted, choose the label $AC$. The stabilizer of this marked edge fixes $A,B,C$ individually, so a transmitted exit at $A$, at $B$, and at $C$ are **genuinely different relative positions**. The full necessary table is:

| Label | Transmitted internal links besides the compulsory two $AB$ channels | Transmitted original exit arm | Actual $|K|$ |
|---|---|---|---:|
| **H1** | $AC$ | none | 6 |
| **H2** | $AC$ | at $A$ (the endpoint of the transmitted side link) | 7 |
| **H3** | $AC$ | at $B$ (the other degree-four hub) | 7 |
| **H4** | $AC$ | at $C$ (degree-three hub) | 7 |
| **H5** | $AC$ and $BC$ | none | 7 |

**Proof of exhaustiveness.** The first two genuine transmitters occupy the parallel $AB$ channels. The two remaining possible internal links $AC,BC$ may have one or two transmitted, but cannot have zero (that would make a literal embedded $K_{2,3}$ with intermediate squares $U_1,U_2,C$ and contradict the accepted occupied-cross exclusion). If exactly one is transmitted, the leftover allowed transmitter budget of one permits either no transmitted exit (H1) or exactly one at $A$, $B$, or $C$ (H2–H4). If both are transmitted, no real body remains available for a transmitted exit (H5). Each channel may contain at most one actual true-degree-two square by the original loaded-long-endpoint theorem. Every exit stub and original outside body remains unchanged during this abstract relabeling. The $A\leftrightarrow B$ symmetry identifies the transmitted-$BC$ alternatives with one of these five but cannot merge H2 and H3: an exit at the *same* degree-four hub as the transmitted $AC$ link is invariantly distinct from an exit at the *opposite* degree-four hub. Thus exactly five necessary relative placement types survive.

Their continuous original force/moment, support-owner and nine-unit-completion questions remain open. The three previous **count profiles** $(1,0),(1,1),(2,0)$ therefore expand into **five precise placement patterns**, not three verified physical cases. No old original fine/coarse or entire M29 flag is checked. This is a small structural statement suitable for tracking as source-written only in [the live ledger](gates/SESSION_CHECKPOINTS.md).

No Lean/Lake, CI, script enumeration, computational geometry exclusions, or numerical certificates were used.
