# Six necessary internal-transmitter patterns for the subcubic three-port \(K_{2,3}\)

Date: 2026-10-31. PR #11, hand-only case indexing.

**Status:** exact **finite hand orbit census** (necessary patterns only); independent review pending. No one of the six residual physical configurations is excluded. This complements [the earlier five-hub reduction](THREE_PORT_MULTICYCLE_SUBCUBIC_REDUCTION_2026_10_31.md) and [the accepted literal physical cross exclusion](GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md). It is not an original 58-cell closure.

## Physical scope and claim

Take one selected physical positive body-pair certificate on nine actual unit squares in \(R^2\le1105/256\). Let \(K\) be a connected entirely selected-circle-unloaded module with exactly **three original positive cut edges** and **two independent internal cycles**, every member of original full positive degree two or three, with **at most one reduced exit arm per branching hub**. All true full-degree-two bodies, including those on reduced exit arms, remain actual squares. Original normals, physical applications/means, force balance, torque, zero/positive circle masks and all nine squares are retained.

Assume the five-hub reduced **internal** graph is \(K_{2,3}\). Name its two full-internal-degree-three hubs \(A,B\), its three full-internal-degree-two hubs \(C,D,E\), and its six internal reduced edges
\[
 AC,\ AD,\ AE,\ BC,\ BD,\ BE.
\]
One reduced original exit arm leaves each of \(C,D,E\).

From the existing full-cut body bound, **at most two** genuine true-degree-two transmitters occur on these six internal edges **and the three exit arms combined**. Every reduced link/arm has at most one transmitter. The **literal internally unsubdivided** internal \(K_{2,3}\) (zero internal transmitters), with any zero, one or two *exit-arm* transmitters, is forbidden by the accepted actual embedded \(K_{2,3}\) cross theorem.

**Theorem (six necessary orbits).** Up to the genuine reduced graph/exit incidence symmetries exchanging \(A,B\) and permuting \(C,D,E\), the *remaining* choices for genuine internal/exit-arm transmitter locations are exactly:

| Case ID | Internal transmitter locations | Transmitted exit-arm locations | Total transmitters and \(|K|\) |
|---|---|---|---|
| **K1** | \(AC\) | none | 1, \(|K|=6\) |
| **K2** | \(AC\) | exit at \(C\) | 2, \(|K|=7\) |
| **K3** | \(AC\) | exit at \(D\) | 2, \(|K|=7\) |
| **K4** | \(AC,AD\) | none | 2, \(|K|=7\) |
| **K5** | \(AC,BC\) | none | 2, \(|K|=7\) |
| **K6** | \(AC,BD\) | none | 2, \(|K|=7\) |

Here a listed transmitted *internal* link means an original two-edge positive path with one actual genuine unloaded degree-two square. A listed transmitted *exit arm* means an original external cut reached through one genuine degree-two square in \(K\). It does not mean an edge was inserted from a hub to an external body. The table is a **necessary topological classification**, not proof of force/geometry feasibility or the sharp radius.

## Complete hand orbit proof

There are five hubs, so two distinct circle-loaded actual bodies in the same complete positive component outside \(K\) leave room for at most \(7-5=2\) further actual true-degree-two transmitters. The two-force transmitter and loaded-long-endpoint theorem limits each individual reduced internal or exit channel to one transmitter, irrespective of the external terminal-body identity. All three exits attach at the three \(C,D,E\) hubs.

Let \(t\) count transmitted internal edges, \(s\) transmitted exit arms. Then \(t+s\le2\); the physical \(K_{2,3}\) exclusion removes \(t=0\), so \(t\in\{1,2\}\).

If \(t=1\), exchange \(A,B\) and permute \(C,D,E\) to put the unique internal transmitter on \(AC\). For \(s=0\) this is **K1**. For \(s=1\), the transmitted exit arm either attaches to the same low-degree hub \(C\), giving **K2**, or to one of the other two low-degree hubs, equivalent by \(D\leftrightarrow E\), giving **K3**. There cannot be \(s=2\) because it would exceed two transmitters.

If \(t=2\), necessarily \(s=0\). Two distinct edges of the bipartite \(K_{2,3}\) either (i) share one of the two high-degree hubs, equivalent to \(\{AC,AD\}\), **K4**; (ii) share one of the three low-degree hubs, equivalent to \(\{AC,BC\}\), **K5**; or (iii) have disjoint endpoints, equivalent to \(\{AC,BD\}\), **K6**. This is exhaustive because a pair of distinct edges either shares one endpoint, which must be on the high or low side, or shares none. The three types are invariant under graph automorphisms, so none are equivalent.

Thus the table contains exactly the six **distinct necessary orbit types**, including transmitted exits. All actual cut edges and terminal incidences remain in the original physical problem; the combinatorial use of an automorphism merely relabels *internal* hubs and is not a rotation or relocation of actual squares. In particular, externally repeated terminal squares and different contact owners may give several original *physical* configurations inside one row. Every such physical variant remains open until excluded at original force/torque and nine-square-completion scope.

## Gate implications and bounds

This is a **small closed graph-theoretic hand gate** beneath [SESSION_CHECKPOINTS.md](gates/SESSION_CHECKPOINTS.md)'s subcubic \(K_{2,3}\) research track. It turns the previous broad residual K23 question into six *fixed topology/length categories*; it does **not** render the six physical exclusions easy or mark any original coarse parent, six-body exterior row, or fine gate checked. The older M23–M25 scope remains open.

Source dependencies: genuine-channel length/parallel argument in [THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md](THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md), exact body count and house/K23 dichotomy in [THREE_PORT_MULTICYCLE_SUBCUBIC_REDUCTION_2026_10_31.md](THREE_PORT_MULTICYCLE_SUBCUBIC_REDUCTION_2026_10_31.md), compatible selected-planar physical embedding in [PHYSICAL_BODY_GRAPH_UNCROSSING.md](PHYSICAL_BODY_GRAPH_UNCROSSING.md), and the accepted [occupied-cross nine-unit exclusion](GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md).

No Lean/Lake, CI, numerical pose exclusion, external computer-generated orbit enumeration, or script-based mathematical certificate was used.
