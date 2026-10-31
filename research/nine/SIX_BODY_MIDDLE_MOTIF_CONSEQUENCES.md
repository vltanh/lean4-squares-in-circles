# Exact six-body consequences of the unloaded triangle-hub obstruction

**Status: complete hand local-motif and load-family consequence; root and
separate independent full audits passed.** The geometric input is
UNLOADED_TRIANGLE_HUB_EXTERNAL_SEPARATION.md, whose full root and
separate independent scope audits have passed. This source does not
alter the authoritative six-body catalogue or close a coarse row.

Use the six-body component cover in SIX_BODY_CYCLIC_FRONTIER.md.
All three other physical squares remain in the original packing.
The positive graph is the entire selected connected component; additional
zero-weight physical contacts are retained separately.

## 1. Exhaustive positive graphs containing the local motif

Suppose A,D are adjacent unloaded exact-degree3 vertices, T is their
common exact-degree2 neighbor, and the other neighbors are B,C.
If B=C, the existing unloaded-diamond-hub theorem already excludes
the configuration, so no new consequence is counted here.

Take B,C distinct. The five fixed positive edges are
\[
                           AD,AT,DT,AB,DC.
\tag{1}
\]
Call the sixth vertex X. The degree assumptions leave no further
positive edge incident to A,D,T. Thus every remaining possible
positive edge is one of
\[
                              BC,\ BX,\ CX.
\tag{2}
\]
Connectivity requires at least one of BX,CX. Reflect the local
motif to exchange B,C if only one is present. The binary choices
in (2) give exactly four abstract positive graphs:

| Positive BC? | X neighbors | Complete positive graph | Existing six-body domain |
| --- | --- | --- | --- |
| No | B only | Triangle TAD, a length-two arm A--B--X and a leaf D--C | C1.3.b3, the two-root 2+1 chain layout |
| No | B and C | Exterior hexagon A--T--D--C--X--B--A with chord AD | C1.6.b0, one triangular ear |
| Yes | B only | House on A,D,T,B,C with a leaf at lower vertex B | C1.5.b1, house lower-vertex root |
| Yes | B and C | Two triangles TAD and XBC joined by AB and DC | C1.6.b0, two opposite triangular ears |

This is a hand degree argument, not an enumeration by software. Extra
positive edges cannot be inserted into any row without violating a
listed exact degree. Extra zero-weight physical contacts may still be
present, subject to the geometric theorem.

The table is exhaustive for this distinct local motif among the six
coarse profiles. It does not say that every six-body component contains
such a motif.

## 2. The two new full positive-load-family exclusions

### 2.1. A house block with a lower-vertex leaf

In the third row BC is positive and therefore physical. The uniform
obstruction immediately excludes the entire subfamily in which the
two degree3 house hubs A,D are both unloaded.

The roof T has exact degree2, the leaf X has exact degree1, the
attached lower body B has exact degree3, and C has degree2. No
degree2 equation is imposed on the bridge-attached B. The theorem
retains every B,C load possibility, both physical S/D leaf types,
all actual contact means and all three extra squares.

This is a complete zero-hub load-family exclusion within the house
lower-root type of C1.5.b1. It does not exclude that entire rooted
block type when one house hub is loaded. Roof-rooted and hub-rooted
house attachments do not satisfy the needed degree assumptions and
are not covered.

### 2.2. A six-body graph with two opposite triangular ears

In the fourth row, both T and X have exact positive degree2 with
touching neighbors, so both are loaded. Each triangle has at most
two physically circle-touching bodies. Therefore each pair {A,D}
and {B,C} has at most one loaded vertex.

Apply the new theorem first at A,D: since their external B,C edge
is positive, A,D cannot both be unloaded. Apply it again at B,C,
with roof X and external neighbors A,D: B,C cannot both be unloaded.
Consequently
\[
 |L\cap\{A,D\}|=|L\cap\{B,C\}|=1,\qquad T,X\in L.
\tag{3}
\]
Thus this entire graph must have exactly four loaded bodies. In
particular its complete three-load family is excluded, with every
physical mask, weight, contact owner and completion square retained.
This is a whole positive-load-class exit, not a small-angle subcase.

Each remaining zero-load hub is also physically circle-clear: its
triangle already contains its loaded mate and loaded roof, so a
zero-weight physical circle contact would create a boundary triangle.

There are exactly two remaining four-load orbits. Up to the graph
symmetries they are
\[
                      \{T,X,A,B\},\qquad \{T,X,A,C\}.
\tag{4}
\]
In the first the two selected hub loads are joined by a positive
edge; in the second they are not. Reflection exchanges A,D together
with B,C, and interchanging the two triangles gives all other
choices. Adjacency distinguishes the two displayed orbits.

In the exterior-hexagon labeling
\[
               0=A,\ 1=T,\ 2=D,\ 3=C,\ 4=X,\ 5=B,
\]
the two chords are02 and35. The remaining masks in (4) become
{0,1,4,5} and {0,1,3,4}. These full four-load families remain open;
no pressure or degree2 theorem is applied after deleting a hub force.

## 3. What the other two rows gain, and what they do not gain

In the first two rows BC is absent from the positive graph. The new
theorem still proves that B,C cannot have any zero-weight physical
contact when A,D are unloaded. It is a complete physical-noncontact
restriction over those local degree/load domains.

However the positive graph does not itself force such a contact.
Therefore neither the two-root triangle/bridge layout nor the
one-ear hexagon receives a whole positive-graph or positive-load-family
exclusion from this theorem alone. Their closed-disjoint B,C poses
remain in the metric/completion problem.

No new direct application occurs in the other listed four-body-block,
two-triangle-block or triangle/four-block attachment types: the
exhaustive degree argument of Section1 would have placed any qualifying
distinct motif in one of its four rows. Coincident-external-neighbor
cases are the older unloaded-diamond obstruction, not a new result.
The five pentagon/interior-body domains likewise receive no automatic
whole-graph closure from the new distinct motif.

## 4. Precise status

The newly closed six-body subfamilies are exactly the entire zero-hub
family of the house lower-leaf attachment and the entire three-load
family of the two-opposite-ear six-body graph. The latter's complete
remaining mask cover is (4). The other two positive graphs gain the
stated physical BC noncontact restriction only.

All six coarse six-body rows remain open, and no coarse closed-cell
count changes. Every statement retains the original containment,
nonoverlap, actual means, physical circle masks and all three extra
squares. The global local theorem's simultaneous prelisting is part
of the same necessary-certificate choice; no normal is changed after
extracting a stress. No numerical graph or pose search, Lean compilation
or CI is used.
