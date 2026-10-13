# A structural normal form for seven outer centers: one central stress cycle or a branching central force

**Research continuation, 2026-10-12. Status: conditional exact hand
structural theorem**, not a new sharp-radius lower bound.

Unlike side-cap threshold pruning, this theorem applies to the
**complete seven-outer actual-contact PATH/FORREST branch** of any
minimum-radius eight-square packing. It narrows the physical stress
architecture to a central branching case or one of just five
central-rooted cycle lengths. It does **not** discard the
genuine seven-outer actual-contact-cycle equality realization.

## Theorem

Let an attained minimum-radius packing of eight pairwise
interior-disjoint unit squares be contained in
\[
D_R,\qquad R^2\le9789/2500<4,
\]
and let C be its unique open origin-containing square.

Assume **exactly seven centers are outer**
(\(|p_i|\ge1\) for every exterior square) and
that their **actual-contact graph induced on
the seven outer squares is not the full
seven-outer cycle**. By
[HUMAN_OUTER_GRAPH_REDUCTION.md](HUMAN_OUTER_GRAPH_REDUCTION.md),
this outer-induced actual-contact graph is a
disjoint union of paths and isolated vertices.

Choose **any** normalized physical contact/circle
stress from HUMAN_CONTACT_EQUILIBRIUM.md, and write
\(G_+\) for its undirected graph of *positive*
square-square contact multipliers.

Then:

1. **The central square C belongs to the unique nontrivial
   positive-stress component.** In particular C has at
   least two distinct positive-stress square neighbors.
2. Every positive-stress outer--outer edge has **nonzero
   signed contact moment** about the disk origin and is
   contained in a directed positive-moment circulation
   cycle. Since the outer graph is a forest, **every such
   directed cycle includes C**.
3. If the central square has **exactly two** positive-stress
   neighbors, the **entire nontrivial positive-stress graph**
   is *exactly one simple cycle*
   \[
   \boxed{C-S_1-S_2-\cdots-S_m-C,\qquad
          3\le m\le7.}                          \tag{1}
   \]
   The outer vertices \(S_1,\ldots,S_m\) are consecutive
   in the cyclic order of all seven outer center rays.
   There are **no additional positive-stress outer
   tails, positive spokes, or a second stressed cycle**.
   All seven-minus-m exterior spectators have **zero
   circle multipliers and zero positive contact weights**
   for this stress, though they may have zero-weight
   actual contacts or touch the containing circle.
4. In the degree-two case the two positive C-contact
   normals are exactly **opposite**, their total positive
   normal force magnitudes are equal, and the two
   contact-neighbor squares \(S_1,S_m\) are separated
   by a *strict positive projection gap at least one*.
   Thus \(S_1,S_m\) cannot contact one another.
   Every positive-stress outer--outer edge on
   the cycle is nonradial, and the unique cycle
   carries a nonzero signed-moment circulation.
5. Modulo **cyclic indexing of the seven outer labels**,
   the degree-two graph support has only five
   integer length choices \(m=3,4,5,6,7\).
   With their current seven *fixed* circular labels,
   there are **exactly 35 combinatorially
   possible cycle supports**, seven per length,
   *before* geometric feasibility and stress-equilibrium
   inequalities are checked.

The remaining physically meaningful alternative is
\(\deg_{G_+}(C)\ge3\), the **central-branching
stress case**. The theorem does not eliminate it.

## Proof

### 1. The unique positive-stress component must contain C

A normalized physical stress exists at an attained
radius minimizer. In the relevant radius range
the theorem
[HUMAN_CONTACT_COMPONENTS.md](HUMAN_CONTACT_COMPONENTS.md)
proves that it has a **unique nontrivial
positive-stress component J**. Such a component
has a nonzero contact-moment circulation and
hence contains a directed contact-moment cycle
(the proof is from exact force/torque equilibrium).

If J avoided C, all its centers would be among the
seven outer centers. Its directed positive-moment
cycle would therefore induce an **all-outer
actual-contact cycle**, impossible by the
hypothesis that their actual induced graph is a
proper subgraph of the seven-cycle. Thus C is in J.

C has no circle contact: since zero belongs to
its open interior, each C vertex lies at distance
strictly less than the square diameter \(\sqrt2<R\).
Its circle multiplier sum is therefore zero.
The contact forces on C must balance to zero.
Since J contains C and at least one positive edge,
one nonzero contact force alone cannot balance.
Therefore C has at least **two distinct positive
neighbor labels**, proving claim 1.

### 2. All positive outer edges have nonzero contact moment

For an outer--outer positive-stress edge,
aggregate its positive contact multipliers
into a nonzero resultant normal force
\(\lambda n\), acting at a point \(z\) of the
actual common contact (for a segment contact
take the positive-weight average of the
contact points). Its signed moment is
\(m=\lambda(z\times n)\).

If \(m=0\), the contact point \(z\) would lie
on the radial line through its separating normal,
\(z=d n\). The elementary **radial contact**
lemma proved in section 2 of
[HUMAN_ACTUAL_BRIDGES.md](HUMAN_ACTUAL_BRIDGES.md)
applies to *any* such square-square radial
contact at \(R<2\): it forces the inner endpoint
of the contact to be C. This contradicts
both endpoints being outer/noncentral. Thus
every positive outer--outer edge has \(m\ne0\).

At each square, torque equilibrium makes the
signed edge moments a conserved antisymmetric
flow; active circle-vertex forces have zero
moment about zero. Orient every positive-moment
edge in its positive sign direction. A finite
nonnegative circulation decomposes into directed
cycles, so **each nonzero-moment outer edge
lies on such a cycle**. The outer-induced graph
is a forest, hence every such cycle must contain
C. This proves claim 2.

### 3. Exactly two C forces imply one simple stress cycle

Assume C has exactly two positive neighbors A and B.
If their total force magnitudes are \(\lambda_A,\lambda_B>0\)
and their outward normals from C are \(n_A,n_B\),
the force equilibrium of C reads
\[
\lambda_A n_A+\lambda_B n_B=0.
\]
Taking norms and directions forces
\[
\lambda_A=\lambda_B,\qquad n_B=-n_A=:-n.
\]
The full force normal can be aggregated for a
single pair even when its common contact is a point
with multiple supporting normals.

The same exact support calculation as in
HUMAN_CONTACT_COMPONENTS.md section 3 gives
\[
\min_{x\in A}n\cdot x-\max_{y\in B}n\cdot y
\ge2h_C(n)\ge1,                                \tag{2}
\]
where \(h_C(n)=(|n\cdot e_C|+|n\cdot f_C|)/2\)
is C's centered half-width. Thus A and B
are **strictly separated closed squares**,
and cannot have an actual contact (let alone
a positive one).

Because the positive component J contains a
nonzero-moment cycle, and the outer positive
subgraph is a forest, there is at least one
cycle through C. Since C has only the two
neighbors A and B, that cycle consists of
the two spokes C-A/C-B and a **unique outer
path** from A to B.

Now consider any other positive-stress edge
outside this unique cycle. No further C edge
exists. A positive outer--outer edge outside
this unique A--B path cannot lie on *any*
cycle: the outer graph is a forest and there
is only one C connection pair. But claim 2
says every positive outer edge has nonzero
moment and therefore lies on some directed
cycle. Contradiction. There are no such
extra positive edges. Uniqueness of J
rules out any second stressed component.
Thus the entire **nontrivial** positive
graph is exactly the simple C-rooted cycle.

By (2), A and B cannot be adjacent as actual
contact neighbors. Their outer positive path
therefore contains at least one intermediate
outer square: \(m\ge3\).
At most seven outer squares exist, so \(m\le7\).

Finally, the visibility theorem in
HUMAN_OUTER_GRAPH_REDUCTION.md says that an
outer square can actually contact an outer
square only if the two centers are circular
neighbors in the seven outer-ray order.
Hence the outer positive path consists of
**consecutive outer angular indices**.
This proves (1), claims 3 and 4, except
for the multiplier observation.

For an exterior square not on this cycle,
every positive contact multiplier is zero.
By the exact force/center stationarity
lemma in HUMAN_CONTACT_COMPONENTS.md section 1,
a square with zero resultant contact force
also has zero circle multiplier sum.
Thus spectator labels carry zero multipliers
for this stress, even if they have actual
zero-weight boundary contacts. The unique
cycle has nonzero moment flow because J's
moment circulation is nonzero.

### 4. Exhaustive discrete cyclic support count

In the fixed circular order of the seven
outer labels, any positive path of m consecutive
outer vertices has one of seven cyclic starting
positions, and exactly m-1 consecutive outer
edges. For m=3,4,5,6,7 these are different
edge sets and attachment pairs, giving
\(5\cdot7=35\) **labeled combinatorial supports**.

The companion
[verify_seven_outer_stress_cycle_graphs.py](verify_seven_outer_stress_cycle_graphs.py)
enumerates all 127 proper outer-edge subsets of
the seven-cycle and all 21 unordered pairs
of C spokes, uses the condition that **every
positive outer edge is on the unique C-cycle**,
and independently returns:

| Number m of outer members on stressed cycle | Labeled cyclic supports |
| --- | ---: |
| 2 (triangle) | 7, **excluded by opposite central normals (2)** |
| 3 | 7 |
| 4 | 7 |
| 5 | 7 |
| 6 | 7 |
| 7 | 7 |
| Total remaining | **35** |

The counting proof is the preceding paragraph,
not reliance on this finite enumeration.

## New global proof architecture and limitations

The **entire k=7 positive-stress problem** now
has the following legitimate branches:

* **Outer actual cycle:** all seven outer squares
  form a contact cycle (known exact equality
  construction belongs here). The present theorem
  makes **no impossibility claim** in this branch.
* **Outer actual paths, positive C stress degree 2:**
  a unique central-rooted stressed cycle of one
  of **five outer-vertex lengths**, m=3..7;
  other outer squares are zero-stress spectators.
* **Outer actual paths, positive C stress degree >=3:**
  unresolved *central branching force* case,
  potentially with several C-rooted moment cycles.

The reduction is **about real physical-stress edges,
not merely actual contacts**. Zero-stress actual edges,
isolated spectators, changes of square orientations,
and the case k<7 are not removed.

In particular 35 supports are *not* 35 complete
semialgebraic packing cases: positions, square
frames, circle-vertex multipliers, weight-zero
contacts and spectator placement remain
continuous. To prove \(R_8\ge\widehat R\),
the next step is to derive a **sharp radius lower
bound for the C-rooted stressed cycle plus all
spectators** and then handle the central
degree>=3 and outer-cycle branches.
No Lean 4 theorem, full equality classification,
or unrestricted optimum is claimed here.


## New complete macro-case elimination: m=7 cannot occur

**The 35-support enumeration above is now historical
*before* applying this geometric restriction.**

[HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md](HUMAN_OPPOSITE_CENTRAL_NEIGHBOR_ANGLE.md)
proves an independent full-orientation
**opposite central-support theorem**: if
the origin-containing C has two other genuine
squares wholly beyond its opposite signed
support lines, the two neighbor-center
rays are separated by
\[
\Delta>\pi/2+1/13.
\]
The proof uses the hand-proved one-square cap
envelope only for offsets \(\ge2/5\)
and the universal radial bound elsewhere,
with four exact rational offset bands;
it does **not** assume aligned frames.

[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md)
combines this with the six genuine
outer-outer contact gaps in the full
seven-outer C-rooted **stressed path**
m=7. Their independent universal outer-center
separation \(>\pi/4-1/500\)
forces the **missing** seventh center-ray
gap \(<\pi/2+3/250\), incompatible with
the opposite-spoke lower bound because
\[
1/13-3/250=211/3250>0.
\]
Thus the entire m=7 stress path support
is **impossible** for any minimum-radius
eight-square packing at \(q\le q_+\).

The corrected current degree-two, k7
actual-path stress queue is therefore:
\[
\boxed{m=3,4,5,6\quad
(\text{seven cyclic graph supports per }m,\
 28\text{ total}).}
\]
These 28 remain purely **combinatorial support
patterns**, not isolated realizable positions.

The real equality packing belongs to
the **actual seven-outer contact-cycle**
root, not to the missing-edge outer
path root, and remains admitted.
No unrestricted \(R_8\ge\widehat R\)
proof is asserted.


## Sharpened actual-contact graph conclusion when C has only two actual neighbors

The original 35-support count, followed by the
m=7 path exclusion to 28 **positive
stress** supports, is now complemented
by a stronger *actual-contact* graph
result:

[HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md](HUMAN_B2_PURE_CENTRAL_CONTACT_ISOLATES_SPECTATORS.md)
proves that if the chosen *minimum-contact*
radius minimizer has **exactly two
actual C neighbors**, equal to its
two positive-stress C neighbors,
**every remaining exterior spectator
is actually isolated from all other
squares**. Otherwise a nonempty
proper set of extra outer-ray
neighbor edges would produce an
actual-degree-one *noncentral*
spectator, violating the exact
actual-leaf theorem. Thus
**all positive-stress edges are
exactly all actual square contact
edges in the nontrivial component**.

An exact graph-only audit now
eliminates **364 of the 392**
possible proper *actual outer-contact
supergraphs* of m3..6 stressed paths,
leaving only the 28 bare stressed
actual graph supports (seven per m).
This is a stronger claim about
**true contacts**, not a new
numerical assertion about the
number of positive cycle supports.

The contact-minimal transmitter
theorems then force **both**
central stressed path endpoints
to have true disk-circle vertices.
The internal stressed-path
vertex-cover theorem forces
additional circle-contact
outer square labels. Minimum
stressed-path circle-touching
label counts for m3,m4,m5,m6
are **2,3,3,4** respectively.

[HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md](HUMAN_ISOLATED_OUTER_CIRCLE_FREE_NORMALIZATION.md)
allows the actual isolated outer
spectators to be repositioned
slightly radially inward, retaining
their true frames, center outer
classes, zero actual contacts and
the least radius, until **all
their disk vertices are strict**.
The spectators must still appear
as real whole unit squares in
every sharp packing inequality.

The **entire m6 root with extra
actual C contacts** is separately
classified by
[HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md](HUMAN_M6_SPECTATOR_CONTACT_TRICHOTOMY.md):
the sole spectator T is either
actually isolated, a central
leaf with true circle contacts,
or a C--T--S1/S6 actual triangle
with a true circle contact.
Diagonal two-stress central mode
still requires two-sided
tangential actual bracing
and internal C chords.

These are new complete graph
and actual-contact *subcase
exclusions*, not the sharp
global inequality
\(R_8\ge\widehat R\).
The legitimate full seven-outer
actual-contact equality ring
remains outside the outer-path
hypotheses and is preserved.
