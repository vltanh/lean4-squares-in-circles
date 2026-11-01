# Every unloaded positive neighbor must escape its adjacent star

Date: November 1, 2026 UTC. Constructor: articulation continuation.

**Status: complete new hand proof, awaiting independent review.**
No original ledger, frozen source or remote object is changed.

## 1. Exact physical scope and inputs

Keep all nine actual closed unit squares, their disjoint open interiors,
the original disk and radius hypotheses, and the same complete selected
positive force-and-torque certificate. Every original pair magnitude,
normal, application or shared-side mean, true degree and individual circle
coefficient remains unchanged. Unloaded means zero selected circle load;
it does not mean physically circle-clear. A positive edge always means
an actual original body-pair edge, not a reduced channel or graph minor.

Use these two accepted geometric statements at their original scopes:

* `GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md`, Section 7: there is
  no literal positive K2,3 on five actual bodies in this same nine-unit
  packing, with arbitrary additional original edges, degrees and loads.
  The original compatible selected-certificate hypotheses remain premises.
* `UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md`,
  SHA256 `406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87`,
  Section 6: the three actual neighbors of a genuinely full-degree-three
  unloaded body cannot contain two physical contact edges. This is the
  complete selection-free diamond corollary, with all original means and
  arbitrary degrees and loads at the three neighbors.

Only the first imported theorem uses the nine-unit radius domain and its
compatible certificate. The elementary degree-one and degree-two facts
needed below are proved in place. No additional normal is selected.

Write N(H) for the set of original positive neighbors of an actual body H,
and N[H]=N(H) union {H} for its closed positive neighborhood. The notation
records positive force; absence from N(H) does not assert physical
disjointness from H.

## 2. The neighbor-escape theorem

**Theorem 1.** If HY is an original positive edge and Y is unloaded,
then Y has an original positive neighbor Z outside N[H]. In particular
Z differs from H and HZ is not a positive edge.

H may be loaded or unloaded, and may have any true degree. No positive
triangle, leaf, articulation, block, or small-degree hypothesis is made.

### Proof

Suppose that every positive neighbor of Y other than H also belongs
to N(H). Consider Y's actual full positive degree.

If it is one, its complete unloaded translation is one nonzero positive
force and cannot vanish.

If it is two, write its entire neighbor set as {H,X}. Complete translation
gives equal opposite pair forces. If n is the original direction from H
through Y toward X, and p_H,p_X are the original applications on Y,
complete torque gives det(p_X-p_H,n)=0. The support identity gives
n dot(p_X-p_H)=w, where w is the positive width of the actual Y in
direction n and w>=1. Therefore p_X-p_H=w n. The whole H and X lie
in the opposing support half-planes separated by w. In particular
their set distance is at least one. But X belongs to N(H) under the
assumption, so the original HX positive contact makes those actual
units touch. This is impossible, including all side means and endpoints.

If Y has full degree three, its complete neighbors are {H,X,W}.
The assumed original HX and HW edges give two physical contacts
among these three neighbors. The selection-free unloaded-diamond
corollary excludes precisely this full actual three-force star.

If Y has full degree at least four, choose three distinct neighbors
X1,X2,X3 other than H. The five distinct actual squares H,Y,X1,X2,X3
have all six original positive edges of K2,3 with parts {H,Y} and
{X1,X2,X3}. The extra HY edge and any other original forces are allowed
by the literal K2,3 theorem. This is again impossible.

These exhaust every possible actual degree. Thus an original neighbor
Z outside N[H] must exist. QED.

Equivalently, an unloaded vertex cannot have all of its positive
neighbors contained in the closed positive neighborhood of one of its
own positive neighbors. The statement is about the original full graph.
In particular it does not discard a weak force, erase a physical
zero-force contact, or declare H and Z physically disjoint.

## 3. Full-cut degree bound at every body of an unloaded region

Let K be any nonempty entirely unloaded set of n actual bodies. Its
FULL original positive cut has k edges. For H in K let

* d be its number of original positive neighbors inside K;
* e_H be its number of original positive cut edges to bodies outside K.

No cyclicity, connectedness, degree bound or terminal distinctness is
assumed in the following counting argument.

**Theorem 2.** At every H in K,

    3d <= 2n+k-2-e_H.                              (1)

If H is positive to every other member of K, the sharper form is

    n <= k+1-e_H.                                  (2)

### Proof

Apply Theorem 1 separately to every one of the d actual internal
neighbors Y of H. Each such Y is unloaded and needs an original
positive escape edge YZ with Z outside N[H].

There are exactly n-d-1 possible internal nonneighbors Z of H.
Any particular such Z can be positively adjacent to at most two
internal neighbors Y of H. If three existed, the actual H,Z and
those three Y bodies would form a literal positive K2,3. Thus at
most 2(n-d-1) of the d neighbors can have an internal escape.

Every remaining neighbor Y needs an original edge to outside K.
Different such Y bodies require different actual cut edges, regardless
of whether their outside terminal identities coincide. None of these
cut edges is incident to H. There are only k-e_H available cut edges.
Consequently

    d <= 2(n-d-1)+(k-e_H),

which is exactly (1). If H is universal in K, there is no internal
nonneighbor at all, so this same argument reads n-1<=k-e_H, proving
(2) directly. No full positive equation is shortened in this count.
QED.

An equivalent local cut formulation may be useful without an entirely
unloaded K: for any actual H, each unloaded member of N(H) requires a
different actual edge from N[H] to its complement. Thus the number of
unloaded positive neighbors of H is bounded above by the full cut of
its closed positive neighborhood. The cut may repeat outside bodies;
the original edges, not the distinct terminal labels, are counted.

## 4. Entire multicycle three-cut exclusion with a universal internal hub

**Theorem 3.** A connected entirely unloaded full-three-cut region K
of induced cycle rank at least two cannot have an internal universal
positive vertex.

### Proof

Suppose H is universal in K. Theorem 2 gives n<=4-e_H. A simple original
positive graph on at most three vertices has cycle rank at most one,
so n=4 and e_H=0 are necessary. H is then genuinely full degree three,
with its three neighbors equal to K minus {H} and no outside force.

The original internal star at H contributes three edges. Cycle rank
at least two on four connected vertices requires at least five edges,
so there are at least two actual positive edges among H's three
neighbors. The selection-free unloaded-diamond corollary at the full
three-force body H excludes these actual contacts. This contradiction
proves the whole theorem at every allowed rank and original degree.
QED.

This covers every multicycle wheel, fan, or other induced internal graph
with a universal vertex in an unloaded full-three-cut region. It is a
direct original-scope implication and does not rely on a table of small
skeletons. It does not exclude all multicycle three-cut regions.

If the separately accepted no-transmitted-exit theorem is also used,
the only cyclic universal-hub three-cut possibility is the three-body
direct triangle: at n=4,e_H=0 each of the other three bodies must carry
one exit and must have internal degree at least two, since all exit
hosts are actual hubs. Hence at least two edges join H's three neighbors,
and the same full-degree-three diamond contradiction applies. This
additional cyclic statement imports precisely
`CYCLIC_THREE_PORT_UNLOADED_MODULES_HAVE_NO_TRANSMITTED_EXIT_2026_10_31.md`;
Theorem 3 itself does not need that input.

## 5. Exact six-body equality structure at a degree-four exit host

Suppose now that n=6,k=3, all three original cut edges lie at distinct
actual hosts, and H is one such host with internal degree d=4. These
are the whole actual hypotheses; no reduced degree is substituted.
Let T be H's unique internal nonneighbor. Then:

1. The other two exit hosts are among H's four internal neighbors.
2. T is unloaded of genuine full degree two and has no outside edge.
3. Its two actual neighbors are exactly the two nonexit internal
   neighbors of H. In particular these two neighbors both touch H
   positively, and T connects them by an original true-two channel.

### Proof

Each of H's four internal neighbors requires an escape. The two cut
edges not incident to H can supply escapes for at most two different
ones. The sole possible internal escape terminal T can serve at most
two, by the literal K2,3 bound. All four bodies must be served, so both
counts attain equality and their served neighbor sets are disjoint.

In particular both other cut edges have their hosts among those four
neighbors; T has no cut edge. The two neighbors without exits must
both contact T positively. T cannot have a third internal neighbor:
all its possible internal neighbors lie among those same four positive
neighbors of H, and three would make a literal K2,3. Also HT is not
positive by definition. Thus T's entire positive star consists of
those exact two nonexit neighbors, proving every assertion. QED.

The original unit bypass H then makes this genuine T transmitter
side-normal of width one by `UNIT_BYPASS_NORMAL_CHANNEL.md`. That
last width conclusion is optional and uses that exact accepted input;
the equality graph statement has already been proved without it.
No contact between H and T is inferred. The actual original application
heights, shared-side means and all other hub forces remain free.

## 6. Verification and adoption boundary

The new arguments are the hand degree exhaustion and actual cut counts
printed above. They use no graph enumeration, numerical pose search,
computer interval proof, Lean, build, or CI. The geometric inputs keep
their already declared original hypotheses and complete physical scope.

These are uniform structural results and a full universal-hub multicycle
feature exclusion. A complete original coarse closure still requires a
literal caller proving its entire original graph and load domain lies
within these hypotheses. No such additional closure is declared here.
