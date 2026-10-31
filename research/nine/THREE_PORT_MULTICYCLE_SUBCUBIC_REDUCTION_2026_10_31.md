# Three-port multi-cycle unloaded modules: a finite subcubic reduction

Date: 2026-10-31. PR #11 hand-only continuation.

**Status:** Hand-proved structural reduction within its exact hypotheses; independent audit and original nine-square caller assembly remain OPEN. This manuscript does not assert an unrestricted n=9 proof or a newly closed canonical fine/coarse row. It intentionally separates proved consequences from the unproved endpoint and completion exclusions.

## Scope

Let nine actual closed unit squares have pairwise disjoint open interiors in the disk of radius \(R\) centered at \(O\), with
\[
R^2\le Q=\frac{1105}{256}.
\]
Retain one **complete original** positive physical force-and-torque certificate (original positive body-pair graph, all true degrees, original contact applications/means, zero and positive circle corner coefficients). Let \(K\) be a connected set of physically real squares with **zero selected total circle load**, whose **full original positive edge cut has exactly three edges**. Allow the three external endpoint squares to repeat, arbitrary additional contacts of zero stress, and arbitrary degrees outside \(K\).

Assume the original **full positive degree** of each member of \(K\) is two or three. **Additional reduced-exit hypothesis:** suppress maximal genuine full-degree-two paths, including paths from branching hubs to the original three cut edges. Require each original true-degree-three branching hub to be incident to **at most one reduced exit arm**. This is stronger than merely requiring that each square has at most one *direct* cut edge: a true-degree-two square may lie on an exit arm, and two exit arms might otherwise reach the same hub. This one-exit-per-*hub* condition is essential; do not omit an original cut or a fourth positive force to invoke the theorem. Suppose the positive graph induced by \(K\) has cycle rank
\[
b=|E(K)|-|K|+1\ge2.
\]

**Theorem (finite three-port multi-cycle reduction).** Under these hypotheses:

1. \(b\in\{2,3\}\). Every member of \(K\) with full degree three is a branching hub; there are exactly \(2b+1\) such hubs. Every remaining member of \(K\) is a true unloaded degree-two transmitter. The **reduced internal hub graph** after suppressing genuine full-degree-two paths is simple (neither loops nor parallel edges); its reduced exit arms remain separate and retain the original actual terminal endpoints.
2. If \(b=2\), there are exactly five hubs and **at most two** true degree-two transmitters. The reduced internal hub graph is either the house (a theta with paths of lengths 1,2,3) or \(K_{2,3}\). Its three **reduced exit arms** leave the three reduced internal-degree-two hubs, and may each include a genuine transmitter. Every reduced internal edge and every exit arm retains its entire actual chain, terminal and original means.
3. If \(b=3\), \(K\) contains exactly seven squares, all with full degree three and with **no** suppressed transmitters. The other two of the original nine squares are both positively circle-loaded and belong to the same complete positive component as \(K\); there are no other squares or stressed components. The reduced graph has seven vertices, nine internal edges, and three distinct exit attachments.
4. In the \(b=2\) branch with **no transmitter subdividing an internal \(K_{2,3}\) edge** (though an exit arm may be subdivided), nine-square completion is impossible by the already accepted, arbitrary-degree **physical embedded \(K_{2,3}\) exclusion** in GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md, Section 7. This fourth assertion assumes the compatible physical embedding specified by that source, supplied by the common selected-certificate construction; it does not extend to a subdivided \(K_{2,3}\) without another argument.

The **remaining** \(b=2\) house shapes, subdivided \(K_{2,3}\) shapes, and \(b=3\) seven-hub shapes have NOT been excluded here. For the larger original modules with a degree at least four or a vertex with two positive cut edges, the theorem does not apply.

## Proof

### A. Full-degree excess and the nine-square count

At an unloaded square with positive degree one, its single positive pair force cannot sum to zero. Hence each vertex of \(K\) has full degree at least two as assumed. Let \(v=|K|\), \(e=|E(K)|\) and \(d_K(i)\) be the **original full positive degree**, counting cut incidences. The handshaking identity, with all three original cut edges retained, is
\[
\sum_{i\in K}(d_K(i)-2)
  =2e+3-2v=2(e-v+1)+1=2b+1. \tag{1}
\]
As \(d_K(i)\in\{2,3\}\), exactly \(2b+1\) vertices have full degree three. Call this set \(H\).

Every nonempty positive-stress connected component carries positive circle load on at least two *distinct* squares. This follows from the standard center-dot work identity and zero total radial-force sum in PHYSICAL_CONTACT_STRESS.md / PLANAR_STRESS_CORE.md; it does not use or remove completion squares. Since \(K\) is unloaded, its containing complete positive component contains at least two actual squares outside \(K\). Consequently
\[
  2b+1\le |K|\le 9-2=7,
\]
which gives \(b=2\) or \(b=3\). For \(b=2\), \(|K|\in\{5,6,7\}\); for \(b=3\), \(|K|=7\) and there are no degree-two members. In the latter case the two outside squares are precisely the two loaded bodies of the complete component. Because there are only nine actual squares, no additional positive component or zero-stress physical completion square is available. This proves the body-count assertions.

### B. Suppress true transmitters only

A true full-degree-two unloaded member has two equal opposite positive forces by its complete translational equation. Its full original torque equation implies its contact applications are aligned: its signed width in the transmitted normal is exactly \(1\) (own side normal) or \(\sqrt2\) (diagonal normal). This is the proved two-force classification in PHYSICAL_CONTACT_STRESS.md, Section 5.

Every maximal internal hub-to-hub path or exit arm through only such genuine transmitters propagates one signed normal and a positive total projection width. **No such reduced path can contain two consecutive internal transmitters:** the existing loaded-long-endpoint theorem, applied to the original supported gap of at least two and positive inward force at its hub endpoint, would force that endpoint to carry positive circle load, contrary to its membership in \(K\). This holds also for a hub-to-external-terminal exit arm. Consequently every reduced internal edge and every reduced exit arm has **zero or one** genuine transmitter. A closed returning path from a hub to itself would assert a strictly positive signed displacement in one direction from the hub to itself, impossible. Thus suppression creates no loop.

Suppose two different reduced paths joined the same two hubs \(A,B\). A direct \(AB\) contact and an internally subdivided \(AB\) path are incompatible: the direct contact makes \(\operatorname{dist}(A,B)=0\), while the transmitted path makes the distance its positive width. Two direct paths cannot be different edges of the original simple body-pair graph. If both paths contain transmitters, the unique minimum-length displacement vector between two disjoint compact convex squares forces both channels to transmit the same signed unit normal (each path achieves the exact distance between \(A,B\)). At an unloaded full-degree-three hub \(A\), its two positive outgoing forces are then parallel in that direction, and the remaining original third force is opposite. The actual third neighbor \(X\) gives a contact sequence \(X-A-U-B\), where \(U\) is the first genuine transmitter. Each of \(A,U\) has normal width at least one, so the actual projection gap of \(X,B\) is at least two. The existing loaded-long-endpoint theorem, SHARP_CONTACT_RADIUS_AND_NEAR_LONG_ENDPOINT_LOAD_2026_10_31.md, Section 4, applied to the real positive inward contact at \(B\), forces \(B\) to have positive circle load. This contradicts \(B\in K\). All three original hub forces are used; none is discarded. Therefore no parallel pair survives.

One may also appeal to Sections 2–4 of THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md for this exact whole-degree loop/parallel-edge argument. No unicyclic hypothesis is needed for those local sections.

### C. The two-cycle five-hub graph is house or \(K_{2,3}\)

Now \(b=2\). The reduced simple connected hub graph has five vertices and six edges: suppression preserves cycle rank. By the explicit reduced-exit hypothesis, the three full cut edges give three reduced exit arms at three **distinct** full-degree-three hubs (their original cut edges may instead be incident to the final true-degree-two square on an arm). Thus exactly these three hubs have **reduced internal** degree two. The other two hubs have internal degree three. Call the latter \(A,B\), and call the three internal-degree-two hubs \(C,D,E\).

If \(A\) and \(B\) are nonadjacent, both have three neighbors among precisely \(C,D,E\); thus every one of the six edges goes between \(\{A,B\}\) and \(\{C,D,E\}\). The graph is \(K_{2,3}\).

If \(AB\) is an edge, each of \(A,B\) has exactly two neighbors among \(C,D,E\). The lower-degree side has total degree six; the four high-low incidences leave exactly one low-low edge. Say it is \(DE\). Then \(C\), having no low-low edge, must meet both \(A\) and \(B\), while \(D\) and \(E\) each meet exactly one of \(A,B\). For the two high degrees to be three, the two latter neighbors must be different: up to relabeling \(AD\) and \(BE\). Hence the complete six-edge graph is
\[
AB,\quad AC,\quad BC,\quad AD,\quad DE,\quad EB.
\]
This is the house, equivalently a theta with \(A\)-to-\(B\) paths of lengths \(1,2,3\). This proof is exhaustive, including ties and all three original external cut-edge positions. Up to two true transmitters can subdivide its six edges, or those of the \(K_{2,3}\) skeleton, without changing the reduction.

### D. The literal \(K_{2,3}\) subfamily is impossible with nine physical squares

When no genuine degree-two transmitter subdivides any of the six **internal** reduced edges, the reduced \(K_{2,3}\) is the *literal* five-square positive subgraph in the original compatible physical embedding. GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md, Section 7, proves that any actual embedded positive \(K_{2,3}\) in a nine-square packing in \(D_{\sqrt Q}\) produces an occupied four-ring with an enclosed unit and therefore a five-square occupied cross. Its unconditional whole-square cross-capacity theorem gives **at most eight total squares**, contradicting the same original nine. The argument preserves every extra positive edge and all completion squares. This closes exactly the literal six-internal-edge \(K_{2,3}\) subfeature, including possible transmitters on separate exit arms; it does not cover subdivisions of the six internal edges or the entire parent coarse case.

## Extra quantitative restriction, not a completed exclusion

The existing reduced full-work inequality in THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md, Section 5, applies to this connected one-exit-per-hub multicycle as well. Denote the total exit magnitude by \(C>0\), the sum of internal direct-edge magnitudes by \(D\), the sum of subdivided internal-channel magnitudes by \(N\), the magnitudes of subdivided exit arms by \(A\), and \(\Delta=2(D+N)-C\ge0\). With original center bounds \(|c_i|<91/60\), it proves
\[
N+A+\frac{\Delta}{2}<\frac{C}{60},\qquad
D>29N+30A+\frac{31}{2}\Delta. \tag{2}
\]
For the present one-exit-per-hub module, exit arms may contain one genuine transmitter, so **do not set \(A=0\) without proving that those exit arms are direct**. Both subdivided internal channels (\(N\)) and subdivided exit arms (\(A\)) are quantitatively small relative to \(C\), but *small is not zero*. There is no legitimate removal of such an edge or transfer of a five-hub lemma to a reduced graph. The missing argument is a uniform physical obstruction to the residual small-force channels or a joint nine-square capacity that keeps them.

## Exact remaining original obligations

* \(b=2\): the three-exit house with zero to two genuine transmitters distributed over internal edges **and exit arms**; and the \(K_{2,3}\) with one or two transmitters on **internal links** (a literal six-internal-edge \(K_{2,3}\) is excluded even if its exit arms contain transmitters).
* \(b=3\): exactly seven unloaded trivalent squares plus exactly two circle-loaded external squares, in one nine-body positive component, retaining their true cut and all actual shared means.
* Any module with a genuine full-degree-four-or-higher vertex, a branching hub with two or more **reduced exit arms**, or four or more full cut edges is outside this theorem and remains open.

This is relevant to refined gate R-MODULE-TRICYCLE and potentially to multiple one-block and articulation parents, **only upon a verified full-original graph caller**. The original gate remains OPEN. The source does not give a universal sharp radius bound or equality classification.

## Verification boundary

Only hand degree arithmetic, finite graph classification and explicitly named pre-existing physical lemmas are used. No numerical pose search, mathematical exclusion script, Lean, Lake or CI was run. This new source has not received independent full-source review. Counts remain **37/58** original coarse, **2,373/2,513** canonical fine, and **18/38** six-body exterior, exactly as in PROGRESS.md.
