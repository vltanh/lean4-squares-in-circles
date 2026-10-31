# Two complete chorded-hexagon load families have the same radius-free obstruction

Date: October 28, 2026 UTC. Author: pentagon continuation.
Read base: `c31ecd109097dde3c8faa1db11a84655575e87ab`.

**Status: complete proposed original-family joins, submitted for full root and
separate independent review.** The local theorem is already present in
`UNLOADED_TRIANGLE_HUB_CHANNEL_BYPASS_EXCLUSION.md`. The present result
identifies two additional complete original callers. Neither a graph parent
nor the whole six-body cell is declared closed here. No original checkbox is
changed by this source.

## 1. One radius-free local obstruction, with arbitrary degrees at the bypass

The complete local theorem has the following exact hypotheses. An actual
unit square U has zero total circle force and exactly three positive pair
neighbors X,T,V. The physical units X and T touch. The edge UV begins an
actual normal channel with one or more true unloaded positive-degree-two
internal units and final endpoint Q. The actual units X and Q touch.
Every displayed unit is distinct. Every positive force at U and at every
internal channel unit is retained.

The theorem excludes this configuration for interior-disjoint closed unit
squares. It has no containing-radius premise and no force, load or degree
premise at X,T,Q. In particular X may have four, five, or more positive
pair forces. Both extra physical contacts XT and XQ may have zero stress;
using original positive contacts for them is sufficient.

For clarity, this is the complete mechanism of the local proof, rather
than an appeal to a house graph that silently removes another force.
The full equations of the internal channel give a fixed unit direction n
and actual strip reserve w at least one. If h=h_U(n), then

    U lies in n.x <= h,       Q lies in n.x >= h+w.        (1)

Every original channel mean is retained in the force/torque telescoping.
For an actual unit W, a minimum-m support point P, and m.k<0, its positive
k-span from P is strictly less than one. This holds at a vertex because
one of the two inward-axis k-components is strictly negative, and at a
side-interior point because only a tangent component of absolute value
strictly less than one can contribute a positive span.

Let n0 be the unchanged U-to-X normal at p0. If n0.n<0, the span fact
applied to X contradicts an actual q in X intersect Q: equation (1) gives
n.(q-p0)>=w>=1. Thus n0.n>=0. If n0 were an own axis of U, the actual
triangle UXT would also give n0.m>=0 for the U-to-T normal m. Indeed an
obtuse own-axis triangle would put T strictly short of X's supporting
half-plane by the same span fact. The full positive U force sum dotted
with n0 is then positive. Consequently n0 is a strict vertex normal.

Normalize U=[0,1]^2, p0=(1,1), n0=(a,b), a,b>0. The span fact and actual
XT contact exclude a strict southwest T port, and the owned-axis triangle
fact excludes negative-axis T normals. The inequality n0.n>=0 excludes
the same southwest and negative-axis alternatives at the channel port.
Thus the other two normals must be strict northwest and southeast, to
balance both positive coordinates of the n0 force. Write their actual
applications and normals as

    pB=(0,1), nB=(-c,d),       pC=(1,0), nC=(e,-f),
    c,d,e,f>0, c^2+d^2=e^2+f^2=1.

Every side-owned and shared-side alternative was included in the preceding
feature cover; these strict vertex applications are conclusions, not
choices of original side means. The full U torque about p0 gives
muB*d=muC*e. Its two full force coordinates then give

    mu0*a=muB*(c-d)>0,       mu0*b=muC*(f-e)>0.

Hence c>d, f>e, and c,f>1/sqrt(2). If the channel uses nC, the actual XQ
contact requires nC.(q-p0)>=w+f>1+1/sqrt(2)>sqrt(2). If it uses nB,
it requires nB.(q-p0)>=w+c>sqrt(2). Both contradict the width bound
sqrt(2) for the one original unit X containing p0 and q.

This covers both channel roles, all original owners, actual means and
endpoints, every original positive force and every zero circle weight.
The complete local source includes all normal-channel and support-span
proofs; no normal reselection or generic-normal avoidance is needed.
The full U3 hypothesis is essential. No U4 is substituted into it.

## 2. First complete original family: chords 02,03 and loads 125

The same nine actual unit squares remain in the original radius domain

    79/40 <= R <= sqrt(1105)/16.

The original six-body positive component has outer rim

    0--1--2--3--4--5--0

and exactly the positive chords 02 and 03. Its positive circle-load set
is exactly {1,2,5}. All three other physical units remain arbitrary.
The complete adjacency, degree, and circle-load table is:

| Actual unit | Entire positive pair-neighbor set | Degree | Total circle load |
| --- | --- | ---: | --- |
| 0 | 1,2,3,5 | 4 | Zero |
| 1 | 0,2 | 2 | Positive |
| 2 | 0,1,3 | 3 | Positive |
| 3 | 0,2,4 | 3 | Zero |
| 4 | 3,5 | 2 | Zero |
| 5 | 0,4 | 2 | Positive |

Take the exact local roles

    U=3, X=0, T=2, V=4, Q=5.

The actual triangle UXT has edges 30,32,02. The real unloaded channel
is 3--4--5, with its single internal unit 4 of true positive degree two.
The actual bypass contact XQ is the unchanged rim edge 05. Thus every
hypothesis of Section 1 is literal in the original graph.

Only the complete unloaded equations at 3 and 4 are used. Unit 0 keeps
all four forces 01,02,03,05. Unit 2 keeps all three forces 20,21,23 and
its original circle-force system. In particular neither the bypass 0
nor the triangle neighbor 2 is assigned a smaller-degree equation.
The direct contradiction occurs in this original core, so no completion
square needs to be moved, deleted, or given a capacity assumption.

The whole family, including every graph-preserving image of its load set,
is excluded. The graph with chords {02,03} has no nontrivial dihedral
stabilizer: its unique degree-four rim vertex is 0; the reflection fixing
0 would send 02 to 04. Nevertheless any rotation or reflection of the
entire displayed physical configuration simply carries all five roles,
actual means, force equations and contacts together, and the same theorem
still applies. No physical frame is selected by that relabeling.

This is the entire existing fine family

    M6.B6.HEXAGON.D0203.L125.

It is not a claim about the distinct L124 or L1245 sets, where 4 is loaded
and cannot be used as an unloaded channel unit.

## 3. Second complete original family: chords 02,04 and loads 125

Keep the actual six rim edges and precisely the positive chords 02,04.
The complete original load set is again {1,2,5}. The entire degree table is:

| Actual unit | Entire positive pair-neighbor set | Degree | Total circle load |
| --- | --- | ---: | --- |
| 0 | 1,2,4,5 | 4 | Zero |
| 1 | 0,2 | 2 | Positive |
| 2 | 0,1,3 | 3 | Positive |
| 3 | 2,4 | 2 | Zero |
| 4 | 0,3,5 | 3 | Zero |
| 5 | 0,4 | 2 | Positive |

Now take

    U=4, X=0, T=5, V=3, Q=2.

The real triangle UXT is 4--0--5--4. The real unloaded channel is
4--3--2, with the original true unloaded degree-two internal unit 3.
Its actual bypass XQ is the positive chord 02. This is the same complete
local obstruction with every original force and unit unchanged.

Again the bypass 0 has true degree four. It is used only as the one
actual square containing the U0 support point and a point of contact
with Q. No force equation at 0,2,5 is simplified. All three arbitrary
completion squares remain, and all actual masks, normal owners and side
mean intervals are retained.

The dihedral stabilizer of the displayed chord graph consists of the
identity and the reflection i -> -i modulo six. The unique degree-four
vertex 0 must be fixed; that reflection interchanges 2 and 4, and 1 and
5. It sends the representative load set 125 to 145. Applying it to the
whole original configuration gives the corresponding local roles
U=2, X=0, T=1, V=3, Q=4. The real triangle is 2--0--1--2, the channel is
2--3--4, and the bypass is 04. This explicitly covers both original
load representatives without creating a second gate.

Thus the entire existing fine family

    M6.B6.HEXAGON.D0204.L125

is excluded, including its full graph-preserving orbit. Other original
load sets in this chord graph are not removed by this join.

## 4. Hand audit of the full outer-hexagon table for this exact motif

This section checks whether the same local theorem has further
unconditional callers among the existing nine exterior-hexagon graph
rows. It is a graph adjacency audit of the already proved hand cover,
not a sampled configuration or a new computational certificate.

The generic U must be an unloaded vertex of true positive degree three.
Two of its actual neighbors must touch, and the remaining direction
must begin with a true unloaded degree-two body. A path cannot be
extended through a loaded body or a higher-degree hub. These conditions
make the following short audit exhaustive for contacts already supplied
by the positive graph.

| Chord row | Complete possible triangular unloaded U roles | Why there is no further direct caller |
| --- | --- | --- |
| None | None | No triangle among a rim vertex and two of its neighbors. |
| 02 | 0 or 2 | At U=2 the triangular neighbors are 0,1 and the only channel direction is 3. The only retained load sets with both 2 and 3 unloaded are 014, 145, and 0145; 145 is the image of representative 134 under i -> 2-i. In all three, the first endpoint is the loaded 4, and neither 0 nor 1 has a graph edge to 4. The reflected argument covers U=0. |
| 03 | None | The two degree-three hubs have no touching pair among their three graph neighbors. |
| 02,03 | 3 | Vertices 1,2 are forced loaded, and 0 has degree four. An unloaded 3 has loads 124,125, or 1245. Only 125 makes the first channel unit 4 unloaded. The exact caller is Section 2. |
| 02,04 | 2 or 4 | The respective first channel unit is 3. It is unloaded only in L125, its reflected image, or L1245; in L1245 both degree-three candidates 2,4 are loaded. Thus only Section 3 applies. |
| 02,35 | 0,2,3,5 as their permitted loads allow | The third neighbor outside either loaded-tip triangle is another true degree-three hub. No channel starts with a degree-two unit. |
| 02,03,04 | None | The only unloaded vertex is 0 of degree five. |
| 02,03,35 | None | The only unloaded vertices are 0,3, both of degree four. |
| 02,04,24 | None | Every potential unloaded hub has degree four; all three degree-two tips are loaded. |

For the two-chord row 02,04, the retained list is exactly
125,135,0135,1235,1245,12345. In the middle three listed sets the required
internal channel unit 3 is loaded. In the last set every degree-three
vertex is loaded. These checks include all graph-preserving images.

Additional physical zero-stress contacts are still allowed. Their
presence can create additional local applications, which the generic
theorem also excludes, but a missing positive graph edge does not prove
physical noncontact. Accordingly this table claims only that the two
joins above are the complete *unconditional* applications furnished by
the existing positive graph/load table. It makes no assertion that
other physical subdomains satisfy no further restriction.

The remaining inner-pentagon masks do not acquire a caller by treating
the interior hub as a transmitter. In H3 the hub has true degree three,
and in H4_D0 it has degree four. In the currently open masks, each
potential channel across a missing spoke stops first at a loaded rim
body; all these forces remain. Their open statuses are unchanged.

## 5. Full retained original contract and exact credit

Both whole original families are ruled out by an actual-core
contradiction. All nine original physical squares stay present. The
argument is radius-free, so it covers the entire original closed radius
interval and any earlier strict, critical, or high-radius subdivision
without a new scalar certificate.

The generic U and V are unloaded in the sense of zero total circle
force. They may physically touch the circle with zero multipliers;
physical clearance is not inferred or used. Every positive channel
force, selected normal, actual side-interior or endpoint mean, free or
owned singleton, shared-side alternative, individual zero corner weight,
and additional physical zero-weight contact remains covered by the
local theorem's complete proof. There is no unknown mean replacement,
no physical perturbation, no new normal selection, and no deletion of
any additional force at X,T,Q.

At the read base both literal fine checkboxes are open. After complete
root and separate independent review, this source supports exactly two
new fine closures:

- `M6.B6.HEXAGON.D0203.L125`;
- `M6.B6.HEXAGON.D0204.L125`.

It supplies no coarse closure, no complete hexagon graph-parent closure,
and no change to the 58- or 2,513-identifier inventories. It does not
close a whole remaining pentagon mask, the unrestricted sharp inequality,
the equality classification, any still-open global prerequisite, or Lean
integration. The proof adds zero computational certificates.

## 6. Exact current source pins

| Complete operative source | SHA-256 |
| --- | --- |
| `UNLOADED_TRIANGLE_HUB_CHANNEL_BYPASS_EXCLUSION.md` | `824aa9fe810ca4049a2d6a583a3a15cb9934841c03fa0aee5a6cabbf9337956e` |
| `SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md` | `cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1` |
| Original `DEEP_GATED_ROADMAP.md` at the read base | `5314712845d5e3cbba01a2f25c645ee9b6d4476f607a83063578fe5db4a2d812` |
| Existing complete local-theorem independent review `REVIEW_UNLOADED_TRIANGLE_HUB_CHANNEL_BYPASS_AND_HOUSE_JOINS_INDEPENDENT_703_2026_10_28.md` | `6c2340d0fc820f615aa72a98a592c6f4644a176b2a041aca5824cf5b8863b207` |

The source's local theorem is elementary and radius-free. Its prior
house callers do not serve as premises of the present joins; the full
local hypotheses have been checked directly against each actual
hexagon graph above. New original-family adoption still requires its
separate complete reviews. No remote write, ledger edit, Lean build,
compilation, CI, or workflow dispatch is performed by this artifact.
