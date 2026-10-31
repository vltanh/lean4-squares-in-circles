# A single original-graph lemma eliminates all one- and two-hub rank-two three-port modules

Date: 2026-10-31. PR #11 hand-only continuation and roadmap audit.

**Status:** complete hand derivation **conditional only on the explicitly named existing physical selected-certificate, two-force channel, and occupied-$K_{2,3}$ theorems**. Self-checked; independent source-level review and final common-certificate audit are still pending. This is a whole *structural-family* exclusion, **not** a complete original nine-square coarse parent.

## Exact theorem and scope

Fix **one common selected planar physical positive body-pair certificate** as in [PHYSICAL_BODY_GRAPH_UNCROSSING.md](PHYSICAL_BODY_GRAPH_UNCROSSING.md); retain the nine real unit squares, all original pair contact means, full original positive degrees, zero/positive circle coefficients, and every additional edge. Work at $R^2\le Q=1105/256$.

Let $K$ be a **connected nonempty** set of *selected circle-unloaded* actual bodies. Require its **entire original positive edge cut** to consist of exactly $p=3$ edges and its **induced original positive graph** to have cycle rank $b=2$. An exit can terminate at the same outside body as another exit, can start after a genuine degree-two transmitter, and several reduced exits may originate at the same hub. **There is no one-exit-per-hub assumption and no subcubic assumption.**

A **hub** means a member of $K$ with original *full* positive degree at least three, including every edge in the original cut. A non-hub in $K$ has original full positive degree exactly two (one positive force alone cannot balance on an unloaded body).

**Theorem A (uniform 1–2 hub exclusion).** If $K$ has at most **two hubs**, it is impossible in a complete nine-unit packing at $R^2\le Q$.

**Theorem B (three-hub reduction).** If $K$ has exactly three hubs, its full-degree-excess signature $(3,1,1)$—the original full degrees $(5,3,3)$—is impossible. In the only other three-hub signature $(2,2,1)$ (degrees $(4,4,3)$), any surviving reduced internal topology consists of two parallel transmitter channels between its two degree-four hubs $A,B$, and one additional reduced channel each $A$--$C$ and $C$--$B$ to the degree-three hub $C$. Exactly **one original reduced exit arm leaves each hub**. The two parallel $A$--$B$ channels each contain exactly one actual degree-two transmitter. At least one of $A$--$C$ and $C$--$B$ must also have an actual internal degree-two transmitter. Thus, ignoring symmetry, the remaining **necessary** physical-transmission profiles are:

| Genuine transmitters on $AC,BC$ combined | Genuine transmitters on the three exit arms | Actual $|K|$ |
|---:|---:|---:|
| 1 | 0 | 6 |
| 1 | 1 | 7 |
| 2 | 0 | 7 |

The exit transmitter in the middle row can sit on any of the three original exit arms. The table is *necessary*, not an existence claim; the full physical geometry of these rows remains OPEN.

Together the theorems eliminate the complete original full-degree excess partitions $(5)$, $(4,1)$, $(3,2)$, and $(3,1,1)$; they also eliminate the direct-$AC$, direct-$BC$ subfamily of $(2,2,1)$. The remaining degree signatures $(2,2,1)$ with one or two transmitted side links, $(2,1,1,1)$ and $(1,1,1,1,1)$ are **not** eliminated.

## Proof: true-degree-two suppression retains the original cut

The exact original full-degree handshaking identity, proved independently in [THREE_PORT_DEGREE_SIGNATURE_CENSUS_2026_10_31.md](THREE_PORT_DEGREE_SIGNATURE_CENSUS_2026_10_31.md), gives
\[
  \sum_{v\in K}(d_{\mathrm{full}}(v)-2)
  =2b+p-2=5.                                           \tag{1}
\]
Thus the hub count is between one and five, and every hub's contribution is strictly positive. There are at least two distinct positively circle-loaded squares outside $K$, so $|K|\le7$.

Suppress only maximal paths of actual **unloaded, true full-degree-two** bodies, retaining their original normal, positive force, contact means, and actual physical length. Record the original $p=3$ exits as distinct cut stubs even if they terminate at the same outside body. The resulting internal *multigraph* on the $h$ genuine hubs is connected with unchanged cycle rank $b=2$, hence exactly
\[
                   e_{\mathrm{red}}=h+1                \tag{2}
\]
reduced internal edges, counted with multiplicity. There are no reduced internal components without a hub: such a component would be an isolated positive cycle of true-degree-two unloaded squares, incompatible with the original connectedness and full-force transmission.

Three previously established **local** hand facts apply without limiting higher hub degrees or reduced exit multiplicities:

1. **No reduced loop.** Along a returning genuine degree-two channel, the signed positive contact support gaps telescope from one hub center back to the **same** center; the resulting strictly positive projected displacement would equal zero. This is the original physical no-return argument in [THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md](THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md), Section 2.
2. **Each reduced channel incident to an unloaded hub has at most one internal real transmitter.** Two successive true-degree-two squares produce a long positive supported channel whose loaded-endpoint theorem would force a positive circle load at that hub. This holds for **internal** channels and transmitted **exit arms**; no exit is erased.
3. **Distinct parallel reduced channels must both be transmitted.** Two original direct edges joining the same pair are not distinct body-pair edges. A direct $AB$ contact cannot coexist with a transmitted $A$--$B$ route, because the former gives $\mathrm{dist}(A,B)=0$ and the latter gives a strictly positive separating distance. Thus, when two or more reduced channels join distinct hubs, **every one** contains **exactly one** genuine degree-two internal body. For this full scope, the argument is in the same unicyclic source, Sections 2–3.

As a result, any three reduced channels joining $A$ and $B$ create the six **original positive body-pair edges** of a literal embedded $K_{2,3}$ on the five distinct actual squares
\[
    A,\ B,\ U_1,\ U_2,\ U_3.
\]
There are no invented compressed contacts. The common physical planar selected certificate supplies the required embedding, by [PHYSICAL_BODY_GRAPH_UNCROSSING.md](PHYSICAL_BODY_GRAPH_UNCROSSING.md). The accepted [GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md](GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md), Section 7, excludes **any** such *actual embedded* $K_{2,3}$ at $R^2\le Q$ in a packing of all nine units, with all additional edges and physical squares retained. We call this the **literal occupied-cross exit**.

### Proof of A: one or two hubs

If $h=1$, equation (2) gives two reduced internal edges on the sole hub. Both must be loops, violating fact 1.

If $h=2$, equation (2) gives three reduced internal edges between the two hubs, because loops are forbidden and the reduced graph is connected. By facts 2–3 they are three actual distinct length-one-transmitter channels, giving a literal embedded $K_{2,3}$. The occupied-cross exit contradicts nine-square completion.

This proves Theorem A for **all** cut-attachment distributions, positive hub degrees, true-degree-two exit arms, zero contact multipliers and original shared means, without assuming one exit per hub.

By (1), exactly one hub corresponds to excess partition $(5)$, and exactly two hubs to partitions $(4,1)$ and $(3,2)$. Hence **all three partitions are excluded**. This closes the *entire literal scope* of session checkpoint **M28**.

### Proof of B: three hubs

Now $h=3$ and equation (2) gives **four** reduced internal edges. The excess partitions are necessarily $(3,1,1)$ or $(2,2,1)$.

We additionally use the previously proved **true-degree-three endpoint obstruction**: two distinct parallel reduced channels cannot have a common unloaded endpoint of original full positive degree **exactly three**. The original proof keeps its third original positive force and torque, then forces a long-gap positive inward endpoint to be circle-loaded (the unicyclic source, Section 3). It does **not** claim the obstruction for a high-degree endpoint.

In the $(3,1,1)$ branch only one hub has original full degree greater than three, so **every** pair of distinct hubs has a true-degree-three endpoint. All parallel pairs are forbidden, and loops are forbidden. A simple three-vertex graph has at most three internal edges, contradicting equation (2)'s four. This signature is eliminated.

For $(2,2,1)$, label the two degree-four hubs $A,B$ and the degree-three hub $C$. Any parallel edges can only join $A$ and $B$. Since a simple graph on three vertices has at most three edges, there are at least two parallel $AB$ links. The only possibilities compatible with connectedness and the degree-three endpoint obstruction are:

- $AB$ has three reduced edges and precisely one of $AC,BC$ is present. The three $AB$ channels each have one genuine transmitter, so the literal occupied-cross exit excludes this case.
- $AB$ has two reduced edges and both $AC,BC$ occur exactly once. Both $AB$ channels each contain one genuine transmitter. Their internal reduced degrees are $3,3,2$ at $A,B,C$. Since their full true degrees are $4,4,3$, the original three reduced exits occur **one per hub**. They may be transmitted, and are not omitted.

In the latter case, if both $AC$ and $BC$ were direct original positive edges, the three actual intermediate squares between $A$ and $B$ would be $U_1,U_2,C$, furnishing the literal embedded $K_{2,3}$; impossible. Therefore at least one of $AC,BC$ contains exactly one genuine full-degree-two square.

There are already two distinct $AB$ transmitters. The exact total nine-square physical budget has $|K|\le7$, so there can be **at most two more** genuine transmitters across the remaining $AC$, $BC$, and all three exit arms *combined*. At least one of $AC$ or $BC$ must be transmitted, and each channel/arm can carry at most one. This gives exactly the three necessary count profiles displayed in Theorem B. Nothing in the argument removes a positive contact from an original hub star or ignores a completion square. This proves B.

## Gate mapping and verification boundary

- **M28**: **fully closed at its stated scope**—all $(5)$, $(4,1)$, $(3,2)$ are excluded, including arbitrary cut arms, by one common proof. The original larger refined \`R-MODULE-TRICYCLE\` and all 21 original nine-square coarse parents remain OPEN.
- **M29**: **partially narrowed**, not checked. Signature $(3,1,1)$ and the unsubdivided-$(AC,BC)$ part of $(2,2,1)$ are eliminated, but the three necessary profiles above remain.
- **M30/M31/M32**: unchanged. In particular four-hub degree signature $(2,1,1,1)$ and all higher-rank cases are not silently covered. Nothing here implies M17–M25 are solved.

**Prerequisite integrity:** This relies on the one **common selected planar physical** certificate, original positive contact force/torque equations, and the previously accepted physical embedded $K_{2,3}$ exclusion. The local long-endpoint and parallel-channel arguments were originally self-checked but have not received a newly recorded independent audit during this continuation. This is therefore a **new self-checked hand proof**, not a kernel-certified theorem or a completed G4.2.c audit.

No Lean/Lake, CI, external enumeration program, numerical pose test, or script-assisted mathematical exclusion was used. The argument is handshaking, original-force channel transmission, finite cases on two or three hubs, and one named existing global physical geometry theorem.
