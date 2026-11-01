# Independent review: unloaded neighbor escape and full-cut degree bounds

Date: November 1, 2026 UTC. Reviewer: four_chain continuation.

**Decision: PASS all complete statements, including the universal-hub
exclusion and the six-body equality structure.**

The frozen target is
`UNLOADED_POSITIVE_NEIGHBOR_ESCAPE_AND_FULL_CUT_DEGREE_BOUNDS_2026_11_01.md`,
SHA-256 `bf840378a65bb9bbc3a1488b4b7dac887292b99c57bed1c2463c128c547401f7`.
I read the complete target and reconstructed its degree exhaustion,
cut count, equality case and all optional callers.

The two accepted geometric inputs remain at their declared scopes.
I checked the current occupied-cross Section 7 K2,3 statement directly
at `cb411042ad89d55d2f4c8d6e24682cec34677c89`, Git blob
`b8404306cba991afcc6b7cb7703f2f0ba6979acf`: arbitrary additional original
edges and forces are allowed. I rechecked the exact complete full-star
statement and Section 6 selection-free diamond corollary of the frozen
`UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md`,
SHA-256 `406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87`.
The target correctly uses that already reviewed selection-free kernel,
not an unsupported extension of a chosen-normal proof. This is a new
composition review, not a recursive re-audit of those accepted kernels.

## 1. Every original full degree is covered

Fix the actual positive HY with unloaded Y. Under the contrary
assumption, every other actual Y neighbor also touches H positively.
Degree one contradicts the full nonzero force. At degree two, the
complete original equations give opposite equal normals, collinear
applications and actual support gap equal to Y's width, at least one;
this contradicts the HX contact. Original side means are covered.
At degree three, H physically touches the two other neighbors, giving
two physical edges among the exact full unloaded three-force star's
neighbors; the accepted selection-free corollary excludes it.
At degree at least four, any three other neighbors give a literal
K2,3 with parts {H,Y} and those three distinct actual bodies.

The additional HY edge is permitted. H's degree and load never enter
the argument. Therefore a genuine original escape edge YZ with
Z outside N[H] exists. The conclusion is positive nonadjacency to H,
not physical disjointness. No triangle or reduced-channel premise is
needed, and no circle-zero coefficient is interpreted as physical
clearance.

## 2. Exact edge counting, including repeated outside terminals

For an entirely unloaded K, each of the d original internal H neighbors
needs an escape. There are exactly n-d-1 possible internal escape
vertices. Any one can meet at most two of those d neighbors, or it
and H with three neighbors would give the same actual K2,3.
Thus at most 2(n-d-1) neighbors can be served internally. Each remaining
one needs its own original cut edge, and none of these is incident
to H. Distinct neighbor bodies give distinct edges even when their
outside terminal body is the same. Hence

    d <= 2(n-d-1)+k-e_H,
    3d <= 2n+k-2-e_H.

This proof does not assume connectivity or distinct cut terminals.
For a universal H, no internal escape vertex exists and the stronger
count n-1 <= k-e_H follows directly. The equivalent cut bound on
N[H] uses the same distinct-edge argument and is also valid.

## 3. Whole universal-hub multicycle caller

For a connected full-three-cut region, universality gives n <= 4-e_H.
A simple graph on at most three vertices has cycle rank at most one.
Thus a multicycle caller requires n=4 and e_H=0. The original H star
is then genuinely full degree three. Rank at least two forces at least
two positive edges among those three actual neighbors, so the complete
selection-free diamond corollary applies. This excludes every stated
universal-hub multicycle feature without an enumeration.

The optional stronger cyclic statement uses precisely the already
reviewed distinct direct-exit-host conclusion. If n=4 and e_H=0,
all three other bodies carry one exit and are actual hubs. Their
internal degrees are therefore at least two. In addition to their
H edges, at least two edges join these three neighbors, giving the
same contradiction. The remaining cyclic universal possibility is
exactly the direct three-body triangle. This optional inference is
correctly separated from Theorem 3's smaller input boundary.

## 4. Six-body equality case

For n=6, k=3, distinct hosts and d=4 at a host H, its own cut count
is e_H=1. Its four internal neighbors have exactly one possible
internal escape target T, which can serve at most two of them.
The remaining two cut edges can serve at most two others. Since all
four need escape, both capacities attain equality and their served
neighbor sets are disjoint.

Thus the other two exit hosts must lie among H's neighbors and T has
no cut edge. The two neighbors without exits must both meet T.
Every possible other internal T neighbor would also be a positive
H neighbor; a third one would give K2,3. HT is absent by its definition.
Therefore T's entire original positive degree is exactly two and its
neighbors are exactly those two nonexit neighbors. This conclusion
retains all original forces and never substitutes a reduced degree.

The optional side-normal conclusion is a literal caller of
`UNIT_BYPASS_NORMAL_CHANNEL.md`: H is an actual unit touching both
ends of the genuine single-body T channel. Its width is consequently
one. No H--T physical contact or fixed application height is inferred.

## 5. Scope and verification

The result supplies uniform necessary graph conditions and a complete
universal-hub feature exclusion. It does not by itself close an entire
original coarse cell or all three-cut modules. All same-certificate,
radius and embedding prerequisites of the literal K2,3 input remain.
The new degree-three step needs no additional selection condition.
The proof and this review use hand reasoning only. Metadata hashing
does not certify a mathematical case. No mathematical script, Lean,
build, CI, frozen-source edit, ledger change or remote mutation was used.
