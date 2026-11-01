# Cyclic three-port modules are biconnected; all four-hub and all at-most-five-body multicycle modules are excluded

Date: October 31, 2026. Separate hand continuation by module_universal.

**Status: complete proposed theorem, independent review pending.**
The earlier frozen proofs and all original status flags are unchanged.
No mathematical program, graph enumeration, numerical pose, Lean, build
or CI is used.

## 1. Same original scope and complete conclusions

Retain the original nine closed unit squares with pairwise disjoint
open interiors in the declared research window

\[
79/40\le R\le\sqrt{1105}/16.
\]

Use the same complete compatible physical contact-and-circle certificate,
including the strictly exposing original normal convention at point-only
vertex/vertex contacts. Retain the simultaneous selection required by the
accepted unloaded degree-three diamond and literal physical K23
exclusions. Every positive magnitude, original normal, actual application
or full shared-side mean, circle atom and individual coefficient remains.
Unloaded means zero selected circle load, not necessarily physically
circle-clear. Every other actual square stays in the same packing.

Let K be a connected entirely unloaded induced original positive region
whose FULL original positive cut has exactly three edges. Assume its
internal cycle rank b is positive. A hub is a member of original full
positive degree at least three. Suppress only paths of genuine original
full-degree-two unloaded bodies, solely as bookkeeping.

The complete new conclusions are:

1. **K is biconnected in its original positive graph.**
2. **K has at most six actual bodies.**
3. **If b>=2, K cannot have exactly four hubs**, at any original degrees
   or cycle rank.
4. **If b>=2, K cannot have at most five actual bodies.** Consequently
   every still-unexcluded multicycle three-port module has exactly six
   actual bodies and either five hubs with one genuine internal
   transmitter, or six hubs and no transmitter. Its cycle rank is at
   least three, and all three original exits are direct hub contacts.

The last alternative is a necessary remaining domain, not a realization
or a declared closure. In particular an arbitrary-degree six-body
multicycle module is not excluded by this source.

## 2. Exact accepted inputs

The operative inputs are the complete statements at their unchanged
same-certificate scopes:

- `THREE_PORT_CYCLIC_DISTINCT_EXITS_AND_FORCE_CONCENTRATION_2026_10_31.md`:
  three distinct reduced exit hubs; its Section 2 Fact B for a full
  two-terminal unloaded region with an unloaded endpoint; its complete
  common-point work obstruction.
- `CYCLIC_THREE_PORT_UNLOADED_MODULES_HAVE_NO_TRANSMITTED_EXIT_2026_10_31.md`:
  every cyclic three-port exit is an original direct hub contact. Its
  complete independent review is
  `reviews/2026-10-31/REVIEW_CYCLIC_THREE_PORT_NO_TRANSMITTED_EXIT_2026_10_31.md`.
- `THREE_PORT_RANK_TWO_AND_ALL_SUBCUBIC_MULTICYCLE_EXCLUSION_2026_10_31.md`:
  every rank-two three-port module is excluded; its unique direct
  exit-pair and physical terminal-triangle arguments apply at arbitrary
  cyclic rank and degrees.
- `THREE_HUB_ALL_RANK_AND_PARALLEL_TRANSMITTER_SIDE_TYPE_ADDENDUM_2026_10_31.md`:
  every three-hub rank-at-least-two three-port module is excluded.
- `TWO_LOAD_RECIPROCAL_RIGIDITY.md`, Sections 1--7, especially Corollary
  R.5: every positive component with exactly two loaded bodies has at
  most six total bodies in the research window, using the retained
  strict point-normal convention. The complete current source has Git
  blob `f10efa51418a4e1b68e6d31aa13f212d100d7d59` and was read through
  Section 9. Its printed force-polygon argument is the input; no
  supplementary regression or script is used.
- `NO_UNLOADED_DIAMOND_HUB.md`, Corollary 6.1: the three physical
  neighbors of an unloaded body of full positive degree three induce
  at most one physical pair contact. The neighbors may have arbitrary
  degrees and loads. Its unchanged compatible selection is retained.
- `GLOBAL_UNLOADED_CONNECTED_TERMINAL_CUT_AT_LEAST_FOUR_AND_COMPLETE_THREE_CUT_ALL_SIZE_PHYSICAL_PATH_EXCLUSION_2026_10_31.md`:
  a nonempty unloaded region with full positive cut of at most three
  cannot have a connected physical graph of distinct terminal squares.
  Its complete same-certificate and original full-cut scopes remain.
- `GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md`, Section 7: a literal
  original positive K23 is excluded in the same nine-square packing.

Every graph invoked below is the original positive graph or its explicit
genuine-transmitter bookkeeping. A contact between higher-degree hubs is
never replaced by a normal channel. No original force is discarded.

## 3. No articulation in a cyclic three-cut module

Suppose v is an articulation of the induced positive graph on K.
Every positive component of K minus v must carry at least one of the
three original external cut edges. Otherwise that component has a
nonempty full positive cut only to v, impossible by the common-point
work obstruction. There are at least two components and only three
external edges. Some component L therefore carries exactly one external
cut edge, say T--Z with Z outside K.

The FULL terminal set of L is precisely {v,Z}. It includes v by
connectedness, and Z by the chosen original edge. The endpoint v is
unloaded and the sole positive L-neighbor of Z is T. Fact B of the
distinct-exit source implies that the two actual terminal neighbor sets
inside L have a common body: if they were disjoint, full force/work
would give a terminal gap at least two and force v to be loaded.
The common body must be T, because the Z edge is unique. Thus v--T
is an original positive contact.

Remove T from L, merely to select further regions of the unchanged
equations. Every remaining nonempty positive component has a nonempty
full cut only to v and T. Those actual squares touch. Their common
point excludes such a component by the same full work sum, with any
cut multiplicity. Hence L={T}.

The complete original positive neighborhood of T is now exactly {v,Z}:
the external K-cut at T is unique, there are no further L bodies, and
K minus v separated L from all other K bodies. Thus T is a genuine
full-degree-two member carrying one original cut edge. This contradicts
the no-transmitted-exit theorem, whose conclusion places every original
cut edge directly at a true branching hub. Therefore v cannot exist.

Since K is connected and cyclic, it has at least three vertices. The
absence of an articulation is exactly the asserted biconnectivity.

## 4. The six-body bound from the full two-loaded component theorem

Let G be the complete original positive component containing K. Such a
component has at least two loaded bodies. To check this familiar fact
without omitting a force, sum all its original translation equations:
internal pair forces cancel, leaving the sum of its circle-load vectors
zero. A single loaded square has a nonzero circle-load vector, because
its positive circle atoms lie at one corner or two adjacent corners in
the research window, and their positive convex combination cannot be
zero. No loaded square is impossible as well: the complete center work
would be a strictly negative sum of internal support gaps on the
nontrivial connected positive component.

If K had seven or more bodies, all loaded bodies of G would be among
at most two actual squares outside K. The preceding argument would
force exactly two loaded bodies in G. Corollary R.5 of
`TWO_LOAD_RECIPROCAL_RIGIDITY.md` then bounds the entire component G
by six bodies. This is incompatible with K already having at least
seven. Thus

\[
|K|\le6.                                                   \tag{1}
\]

This use requires only the printed component-cardinality theorem. It
does not invoke the completion of four-, five- or six-body two-loaded
cores, a smaller auxiliary minimizer, or a weakened certificate.

## 5. Complete four-hub exclusion, at arbitrary cycle rank

Suppose K has exactly four hubs and b>=2. Rank two is already excluded,
so b>=3. The three distinct exit hubs are A,B,C and the sole other hub
is H. All exits are direct by the accepted theorem.

The direct positive graph on A,B,C must be precisely a two-edge path,
which we name A--B--C. Zero direct edges contradict force concentration;
one direct edge is excluded by the complete dominant-pair argument;
three direct edges are excluded by the physical three-terminal work
argument for b>=2. Thus there is no direct A--C contact in this graph.

The reduced internal multigraph has four vertices and therefore b+3
edges. A returning link is impossible. A direct pair cannot coexist
with another channel on the same endpoints: the direct contact has
set distance zero, while any genuine transmitted channel has positive
set distance. Every non-direct reduced link contains at least one
actual transmitter.

First suppose there is a reduced A--C channel. It is transmitted.
With at most six bodies and four hubs, there are at most two
transmitters in total. Every repeated reduced pair requires at least
two of them, so if A--C is present, all reduced pairs are simple except
possibly that pair alone. If A--C were repeated, it would use both
transmitters, with exactly one actual body U or V on each channel.
The literal K23 with parts {A,C} and {B,U,V} then excludes it. Hence
the entire reduced graph is simple whenever A--C is present, and has
at most six edges. Since b>=3 it has exactly six:
the complete reduced K4, with A--C transmitted and every other pair
present. The nonexit hub H then has full degree three. Take L to be
H together with ALL actual internal bodies on its three links to
A,B,C. Each such body is a genuine full-degree-two transmitter; the
three links are internally disjoint. Thus L has exactly three FULL
original cut edges, one to each of A,B,C, and no omitted contact to
the separate A--C channel. Its terminal squares form the physical
path A--B--C. The complete connected-terminal three-cut theorem
excludes L, including when L is the singleton H. This closes every
A--C-channel alternative at once, irrespective of which H-links are
direct or transmitted.

Now suppose A--C is absent even as a reduced link. All reduced edges
other than A--B,B--C join H to one of A,B,C. Their total multiplicity
is b+1>=4. Some H-pair is repeated. Three channels on a pair would
require at least three actual transmitters, contradicting (1), so its
multiplicity is at most two. The bound of at most two transmitters
means there is exactly one repeated H-pair, of multiplicity two; all other H-pairs
are single and direct. Four or more links among three possible pairs
therefore forces multiplicities (2,1,1).

If H--A or H--C is doubled, H--B is direct; the doubled pair has B as
a third original common neighbor in addition to its two transmitters.
If H--B is doubled, H--A is direct and A supplies that third original
common neighbor. Every case is a literal physical K23. Therefore the
entire alternative without an A--C channel is excluded as well. This
proves the complete four-hub claim at all b>=2.

## 6. Five hubs with five actual bodies: a complete exclusion

Suppose K has five hubs and five actual bodies, and b>=2. There are no
internal transmitters. Write A--B--C for the necessary direct exit-hub path, and
Y,Z for its two nonexit hubs. There are no other E--E edges.

If Y and Z are not adjacent, their full degrees at least three force
both to have all three positive neighbors A,B,C. This is a literal
K23 with parts {Y,Z} and {A,B,C}.

Otherwise Y--Z is direct. Each of Y,Z has at least two of A,B,C as
positive neighbors. If both have all three, the same K23 applies. If
one has all three and the other exactly two, the latter has full
degree three, with the other hub physically touching both of its E
neighbors. Its neighbor graph has two edges, contrary to the unloaded
diamond theorem.

It remains that each has exactly two E neighbors. Their two-element
neighbor sets intersect. If either is the adjacent pair {A,B} or
{B,C}, that full-degree-three hub has, among its neighbors, both the
E-pair contact and the other F-hub's contact to the intersection. This
again gives two neighbor edges and contradicts the diamond theorem.
Thus both E-neighbor sets must be {A,C}. The literal K23 now has parts
{A,C} and {B,Y,Z}. This exhausts every five-hub five-body graph, with
arbitrary initial cycle rank.

## 7. Whole small-module consequence and exact remaining domain

Distinct exits require at least three hubs. If b>=2 and K has at most
five actual bodies, three hubs are excluded by the accepted all-rank
three-hub theorem, four by Section 5, and five by Section 6. These are
all possibilities. Thus every multicycle module left by the combined
theorems has exactly six actual bodies, using (1), and at least five
hubs. The only remaining body/hub counts are

\[
(|K|,h,t)=(6,5,1)\quad\text{or}\quad(6,6,0),
\]

where t is the number of actual internal transmitter bodies. There
are no exit transmitters. The rank-two theorem separately forces
b>=3, and Section 3 makes the original six-body graph biconnected.

These are whole parameter-uniform exclusions and deductions, not a
numerical graph census. The full four-hub proof explicitly retains a
possible transmitted A--C link; concentration's direct exit path alone
does not remove that link. Every auxiliary cut was checked in the
unchanged original graph, including all channel bodies and all extra
positive contacts.

The two six-body higher-degree domains themselves remain open. This
source does not claim an arbitrary-degree multicycle theorem, an
original coarse-parent closure, or an equality classification. The
complete manuscript requires independent source-level review before
adoption; all original flags remain unchanged here.
