# Rank-two and all subcubic multicycle three-port unloaded modules are impossible

Date: October 31, 2026. Complete hand-proof composition; independent review pending.

## 1. Original scope and theorem

Keep nine actual interior-disjoint unit squares in the same disk, with
\(R^2\le Q=1105/256\), and one unchanged complete physical positive
force-and-torque certificate. All original body-pair edges, true degrees,
applications or shared-side means, circle coefficients and all nine
physical squares remain. Where the physical embedded \(K_{2,3}\)
exclusion is used, retain the same compatible selected planar certificate
required by that input.

Let \(K\) be connected and entirely selected-circle-unloaded, with
exactly three edges in its FULL original positive cut. Write
\(b=|E(K)|-|K|+1\) for its induced original positive cycle rank.

**Theorem. No such K exists either (i) at b=2 with arbitrary full degrees,
or (ii) at b>=2 with every original full degree at most three.**

This covers H1–H5, both four-hub diamonds with every allowed transmitted
link and exit, all houses and internally subdivided K23 shapes, and all
subcubic higher-rank modules. External terminals may repeat and have
arbitrary degrees. Physical zero-weight contacts remain. Arbitrary-degree
rank at least three and cuts of four or more are not thereby excluded.

## 2. Exact inputs

The new prerequisites are
`THREE_PORT_CYCLIC_DISTINCT_EXITS_AND_FORCE_CONCENTRATION_2026_10_31.md`
and `DOMINANT_UNLOADED_CONTACT_PAIR_IS_CENTRAL_2026_10_31.md`.
The former prints the complete common-point and two-terminal one-layer
arguments and proves that every cyclic three-port module has three
DISTINCT reduced exit hubs. The latter proves: an original unloaded
direct pair of magnitude d, one distinguished exit at each endpoint,
and all other original incident magnitudes totaling r_A+r_B < 2d/29,
has its original shared application p at |p|<15/16. Every actual unit Z
then has dist(p,Z)<469/240<2.

The inherited geometric inputs are the genuine full-degree-two torque
classification in `PHYSICAL_CONTACT_STRESS.md`; the loaded endpoint
theorem at supported gap at least two in
`SHARP_CONTACT_RADIUS_AND_NEAR_LONG_ENDPOINT_LOAD_2026_10_31.md`;
and the literal physical embedded K23 exclusion in
`GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md`, Section 7.

One existing full-cut theorem is needed only in the final four-hub case:
`GLOBAL_UNLOADED_CONNECTED_TERMINAL_CUT_AT_LEAST_FOUR_AND_COMPLETE_THREE_CUT_ALL_SIZE_PHYSICAL_PATH_EXCLUSION_2026_10_31.md`.
It excludes a connected unloaded region with at most three full original
cut edges when its distinct actual terminal squares have a connected
physical contact graph. Its entire recovered source and complete review
are preserved unchanged alongside this manuscript. No claim about cuts
of four or more is imported from it.

The two-cut reduction and three-touching-terminal result used below
are rederived here. No new normal, force, application or physical packing
is selected.

## 3. One direct exit-hub edge excludes the entire module

Suppress only genuine unloaded true-full-degree-two paths. Each reduced
link or exit arm contains zero or one transmitter: two successive
transmitters would force its unloaded hub endpoint loaded. There is no
returning link, since positive signed widths cannot telescope back to
the same endpoint. The three exit hubs E are distinct by the first new
input; F denotes all other hubs.

Let S_EE,S_EF,S_FF be the sums of internal channel magnitudes by endpoint
classes; N the total magnitude of transmitted internal channels; N_EE
its exit-to-exit part; A the magnitude sum of transmitted exit arms;
and C>0 the magnitude sum of all exits. The complete work bounds are

\[
S_{EF}+2S_{FF}+2N+2A<C/30,\qquad
D_E>29C/60+S_{FF}+(N-N_{EE})+A,                 \tag{1}
\]

where D_E=S_EE-N_EE is the magnitude sum of DIRECT original contacts
between exit hubs. In particular the direct graph on E is nonempty.

Suppose it has just one edge AB, of magnitude d=D_E. At A and B
distinguish their unique exit-arm forces, acting at their actual first
neighbors. Every other incident original force remains in r_A,r_B.
Other exit-to-exit channels are all transmitted, so

\[
r_A+r_B\le S_{EF}+2N<C/30,
\qquad d>29C/60,
\qquad (r_A+r_B)/d<2/29.                        \tag{2}
\]

The dominant-pair input applies to the ORIGINAL common application
p of AB. It gives dist(p,Z)<2 for every actual unit square Z.

Let H be the third exit hub. Remove A,B and the internal degree-two
bodies of their two exit arms. A remaining positive component not
containing H has nonempty full cut only to A,B. These two terminals
contain p, so common-point work excludes that component. Thus all
remaining members form one connected unloaded L containing H and its
entire exit arm. Its full cut consists of arbitrary edges to A,B and
exactly the original third edge to an actual outside square Z.

Write the latter edge's magnitude z>0, normal u from its actual host
T in L to Z. If H's exit is direct, T=H; otherwise T is its genuine
degree-two exit transmitter. T has no positive contact to A or B:
in the first case that would be another direct edge on E, and in
the second it would be an extra force at a true-degree-two body.

Let W be ALL members of L positively adjacent to A or B. The full
force from L toward A,B is -zu. Since T is not in W, summing all
translations over W gives vector sum zu across W to L-W. Their
magnitude sum is at least z. Therefore the whole internal work obeys

\[
I_L\ge z.                                         \tag{3}
\]

Dot all full translations on L with c_i-p. A cut to A or B gives
n.(c_i-p)<=-h_i(n), because p lies in its actual terminal. Insert
the support identity at the unique cut T-Z. The exact full work gives

\[
z(\min_Zu\cdot x-u\cdot p)
\ge I_L+\sum_{\rm full\ cut}\mu h_{\rm internal}(n)
\ge I_L+C_L/2.                                    \tag{4}
\]

The magnitude sum toward A,B is at least z, so C_L>=2z. Equations
(3)-(4) yield u.(x-p)>=2 for every x in Z, and dist(p,Z)>=2.
This contradicts the dominant-pair conclusion. Thus the whole
unique-direct-exit-edge alternative is impossible at arbitrary degrees,
cycle rank, applications and transmitted exits.

## 4. A direct triangle of exit hubs also excludes b>=2

Three pairwise touching unit squares have a disk of radius strictly
below 1/2 meeting all three. To prove this, choose their three actual
pair contact points. Each side of the resulting triangle belongs to
one terminal by convexity and has length at most sqrt(2). If the
triangle is nondegenerate with semiperimeter s, Heron and AM-GM give
area^2<=s^4/27. Its incircle therefore has radius

\[
r=\operatorname{area}/s\le s/(3\sqrt3)
\le1/\sqrt6<1/2.
\]

It meets all three terminal squares. In the collinear case the median
of the three points lies on all three pair segments and in every
terminal, giving a radius-zero hitting disk.

For any unloaded region with a nonempty full cut to these terminals
or a subset, center-dot work about the hitting-disk center gives
I+H<=rC, while H>=C/2. This is impossible. The argument permits any
number of original cut edges.

If all three exit-hub pairs are direct, remove those hubs and their
exit-arm internal bodies. Every remaining positive component has a
nonempty full cut to the three touching hubs and is impossible by
the preceding result. A direct contact cannot coexist with a
transmitted channel joining its same two endpoints: it would assert
both zero and positive set distance. Thus the entire reduced internal
graph is the three-edge triangle, of rank one. It is outside b>=2.

## 5. Complete two-cut reduction

For R<5/2, an unloaded connected region with exactly two original
positive cut edges has only one actual degree-two body or two adjacent
actual degree-two bodies. Here is the complete graph argument.

Write its cut xA,yB. A=B is impossible by common-point work. Its two
magnitudes agree, say mu, and its normals are opposite. Multiply each
full projected translation by graph distance from x and sum over the
region. The distance changes by at most one on every internal edge;
this gives I>=mu dist_graph(x,y). Terminal-ball work with the midpoint
of nearest terminal points then gives

\[
\operatorname{dist}(A,B)\ge1+\operatorname{dist}_{\rm graph}(x,y).
\]

Since the radius-1/2 center disks lie in D_R, |c_A|,|c_B|<=R-1/2,
and dist(A,B)<=|c_A-c_B|-1<=2R-2<3. Hence the integer graph distance
is zero or one. If x=y, any remainder component has just x as its
terminal and is impossible. If x,y are adjacent, any remainder
component has terminals inside the physically touching pair x,y
and is impossible. The only bodies left are x or x,y, respectively;
their unchanged original full degrees are exactly two. No cycle or
branch was deleted in order to apply a path argument.

## 6. Uniform subcubic multicycle exclusion

If all full degrees are at most three, every hub has full degree
three. Full handshaking gives exactly 2b+1 hubs. Thus b>=2 gives
at least two nonexit hubs F.

The direct graph on the three exit hubs has at least one edge by
(1); one edge is excluded by Section 3 and three by Section 4. The
only remaining graph is the two-edge path A-B-C.

The middle hub B has its two direct internal forces and one exit,
exhausting full degree three. Each end hub A,C has precisely one
remaining reduced internal incidence. If these two incidences form
an AC channel, every exit hub has exhausted its internal degree,
and no nonexit hub could be connected, a contradiction.

Otherwise the region of all nonexit hubs, all transmitters between
them, and all transmitters on their incident links to A,C has exactly
two original cut edges. Each component must meet both A and C,
since a one-terminal component is impossible. Thus there is exactly
one component. Section 5 says all its members have original full
degree two, contradicting its retained degree-three hubs.

This excludes EVERY subcubic b>=2. It does not need a separate house,
subdivided K23, or seven-hub orbit enumeration.

## 7. Every remaining arbitrary-degree rank-two signature

For b=2 the full degree excess is five. Distinct exits require at
least three hubs, and five positive excess units allow at most five.
Five hubs all have degree three and were handled by Section 6.

### Three hubs

All three are exit hubs and their reduced internal multigraph has
four edges. There are no loops. Two parallel reduced channels must
both be transmitted, since one direct contact would force distance
zero. Their signed directions agree by uniqueness of the nearest
displacement between two disjoint convex squares. A full-degree-three
unloaded endpoint of such a pair would have its only remaining force
opposite the two parallel ones; adjoining that actual neighbor gives
a supported gap at least two through this hub and a true transmitter,
forcing the opposite endpoint loaded. Thus a parallel pair has only
full-degree-at-least-four endpoints.

Each of the three hubs has internal degree at least two, because it
has full degree at least three and one exit. The three pair
multiplicities sum to four. If a pair were absent, the two others
would each be at least two, yielding a full-degree-three endpoint
of a parallel pair. Therefore all three pairs occur and their
multiplicities are (2,1,1).

Label the doubled pair AB, with its actual single transmitters U,V,
and the third hub H. If both AH and BH are direct, the ACTUAL five
squares A,B,U,V,H contain the literal positive K23 with parts
{A,B} and {U,V,H}. The accepted physical occupied-cross theorem
excludes it within the same nine squares. Otherwise at least one
of AH,BH is transmitted. AB supplies no direct edge, so the direct
exit-hub graph has zero or one edge and Section 3 excludes it.
This handles H1-H5 and their entire exit-arm scope together.

### Four hubs

The full degrees are (4,3,3,3). Every potential parallel pair has
a degree-three endpoint and is impossible. The reduced graph is
therefore simple with four vertices and five edges: the diamond.

The distinct-exit theorem excludes the D-peripheral placement with
two exits at its degree-four hub. The remaining D-central placement
has exit hubs A,B,C, with A of degree four, and nonexit hub H.
Its internal reduced links are AB,AC,AH,BH,CH.

The only possible direct exit-hub edges are AB and AC. At most one
direct is excluded by Section 3. If both are direct, H and all
genuine transmitters on HA,HB,HC form an actual unloaded region L
with exactly three FULL original cut edges. Its terminals A,B,C
form the physical path B-A-C. The complete connected-terminal
three-cut theorem listed in Section 2 applies literally and excludes
L. Every transmitter on any exit arm remains outside L with its
actual original forces; the terminal hubs themselves are not deleted.

Three, four and five hubs exhaust the rank-two degree signatures.
This proves the theorem.

## 8. A whole unicyclic row is also excluded

The argument of Section 3 applies to every cyclic three-port module
whose exit-hub direct graph has exactly one edge. It uses only b>=1,
not the stronger b>=2 hypothesis of the main theorem.

In the complete corrected unicyclic classification
`THREE_PORT_UNICYCLIC_UNLOADED_MODULES_AT_MOST_FIVE_WITH_COMPLETE_INTERNAL_ENDPOINT_SCOPE_CORRECTED_2026_10_31.md`,
the row (t,s)=(2,0) has three genuine full-degree-three exit hubs,
exactly two transmitted internal triangle links, one direct internal
triangle edge, and no transmitted exit. It therefore meets Section 3
literally. The remaining connected region retains the third exit hub
and both actual internal transmitters; its full cut and unique outside
terminal are exactly those used in (3)-(6).

**Corollary. Every original three-port unicyclic (t,s)=(2,0) module is
impossible.** Its arbitrary original applications, actual terminal
identities and all nine physical squares remain.

The necessary unicyclic table is consequently reduced to (0,0),
(0,1), (1,0), and (1,1). Both original inequivalent exit positions
in the last row remain. This closes one whole force-concentration
topology at the scope requested by R-MODULE-SMALL_FORCE; it does not
close the full R-MODULE-SMALL_UNI obligation or an original canonical
nine-square parent.

## 9. Exact remaining domain and verification boundary

For arbitrary degrees and rank at least three, Sections 3-4 still
force a two-edge path as the direct graph on the three distinct
exit hubs. The remaining nonexit region can have four or more
original cut edges. Such edges cannot be omitted to invoke Section
5 or the connected-terminal three-cut theorem. This is an explicit
unresolved domain, alongside cut sizes four and higher.

The theorem does not show that every original open coarse parent
contains a forbidden module. Same-nine caller extraction, all
remaining geometric parents, equality and the final common-certificate
audit remain separate. No original canonical coarse/fine flag is
changed by this manuscript alone.

All new mathematics is a printed hand argument. No pose search,
numerical test, mathematical exclusion script, Lean, Lake or CI was
used. The complete composition requires independent reconstruction
before its evidence state is promoted.
