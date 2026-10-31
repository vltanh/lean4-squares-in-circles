# Mixed shared blocks and the complete common-frame short-C7 exclusion

Date: October 30, 2026. Author: joint-pockets continuation.
Input mathematical tree: `3132896f3c306faecfdd69daafb0b577bf7d70a1`.

**Status: complete proposed uniform hand theorem and whole-family exit,
awaiting separate independent review.** There are two results.

1. In any compatible positive simple cycle with at least three loaded
   bodies, a maximal shared-side block incident to a surviving free
   vertex/vertex edge must contain a body with at least two positive
   circle-corner coefficients. Internal unloaded bodies, including
   physically boundary ones with zero coefficients, are allowed.
2. No original nine-square packing in the project window has a selected
   positive short seven-cycle whose seven bodies all have one common
   side frame. Every actual circle mask, shared mean, and additional
   zero-weight physical contact is retained. The two completing squares
   need not share that frame and are not moved.

The second theorem allows both genuine shared sides and free singleton
contacts at entry. It is therefore stronger than assuming every positive
cycle contact shared. The first theorem is not restricted to a common
frame for the whole cycle; only each actual shared block has its own
parallel frame, as forced by sharing.

No claimed block translation is a feasible physical motion. These are
virtual-work identities in the full original equations, followed by
proved generic nonidentity and a separate exact radius contradiction.

## 1. Full physical and generic domain

Work in the unchanged closed window

\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
                                                                  \tag{1.1}
\]

Use the common physical certificate selected before any local argument:
genuine strict free vertex/vertex normals, the matched parameter at
each four-square junction, physically compatible uncrossing, and the
common algebraically independent choice over fixed physical geometry.
In the final supported embedding at most one of the two opposite
singleton pairs is positive at a four-square junction. No normal,
circle mask or actual application is changed after extraction.

Let an entire positive component be a simple cycle with at least
three loaded bodies. Every member has full positive pair degree two.
`SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md` gives the exact common nonzero
origin moment

\[
                      \mu_e\det(p_e,n_e)=H\ne0              \tag{1.2}
\]

on every consistently directed original edge. It applies to mixed
cycles, not only all-boundary cycles, and includes physical two-corner
bodies and every zero circle coefficient.

The generic two-port theorem in
`GENERIC_TWO_AND_THREE_PORT_CUT_RULES_FOR_ARBITRARY_UNLOADED_BODY_MODULES_2026_10_30.md`,
applied to a singleton unloaded body, says that neither of its two
positive edges can have a free vertex/vertex normal. Hence

\[
           \text{every supported free vertex/vertex edge
                         joins two loaded bodies.}         \tag{1.3}
\]

Both those bodies physically touch the circle. This fact concerns the
free edge only. Other bodies inside a shared block may be unloaded and
physically circle-clear.

## 2. A free boundary-pair vertex is not radial to an actual circle corner

We need a small geometric fact in its literal local scope. If p is a
vertex of a physically boundary square S and is also contained in a
different physically boundary square T, then p is not collinear with
any physical circle corner z of S.

Choose S's own axes so `S=[a-1,a] x [b-1,b]` and `z=(a,b)`,
where `a,b>=1/2` and `a^2+b^2=R^2`. A containing-circle point
cannot be shared by two contained squares, so `p!=z`. The adjacent
vertices have nonzero determinants with z. The opposite vertex can
be collinear only when

\[
       a=b=R/\sqrt2,\qquad
       p=(1-\sqrt2/R)z,\qquad |p|=R-\sqrt2>0.              \tag{2.1}
\]

But every point of a boundary unit has norm at least `R-sqrt(2)`.
For any circle corner `z_T` of T, equality in

\[
 R=|z_T|\le |p|+|z_T-p|\le(R-\sqrt2)+\sqrt2=R
\]

would force `z_T=Rp/|p|=z`. The two squares would share a circle
point, a contradiction. Thus

\[
                                \det(p,z)\ne0.              \tag{2.2}
\]

The no-shared-circle-point assertion is elementary: if z is a circle
corner and `u,v` are the square's orthogonal inward unit edges, then
containment of `z+u,z+v` gives `z dot u,z dot v<=-1/2`.
The short inward radial segment from z therefore lies in its open
interior. Two contained squares sharing z would overlap openly.

## 3. A mean-preserving translation field on a mixed shared block

Let `S_1,...,S_s` be a maximal path of positive edges whose actual
physical intersections have positive length. Choose its first external
edge to be a free vertex/vertex edge at the fixed actual point p.
By (1.3), `S_1` is loaded. All frames inside the shared path are
parallel. Every internal normal is a signed common axis.

Suppose, for a contradiction to the intended block theorem, that
each body of this path has at most one positive circle atom. At each
loaded body choose its actual positive corner z; its circle resultant
is a positive multiple of z. Unloaded members have zero circle
resultant, irrespective of their physical mask. Every coordinate of
a physical circle corner in this common frame has absolute value at
least `1/2`. Consequently, for every common unit axis e,

\[
                               e\cdot Jz\ne0.              \tag{3.1}
\]

We construct fixed pure-translation velocities w on all path members.
Set

\[
                                 w_1=Jz_1.                 \tag{3.2}
\]

At each later loaded member use a velocity `w= kappa Jz`, choosing
kappa to preserve the normal component across the incoming shared
channel. More explicitly, if successive loaded members along the path
are i,j and their intervening shared channel has direction e, set

\[
          \kappa_j=\kappa_i
                  \frac{e\cdot Jz_i}{e\cdot Jz_j}.          \tag{3.3}
\]

All denominators and all kappas are nonzero. Any intervening unloaded
members have equal, opposite original forces, so their incoming and
outgoing directed normals agree. Assign each such member any velocity
with the preserved e component, for example

\[
                         w=(e\cdot w_i)e.                  \tag{3.4}
\]

If the path ends with one or more unloaded members, apply the same
construction from its last loaded member to that end. If its two
external contacts coincide because the path consists of a singleton,
(3.2) still supplies its velocity. A final unloaded endpoint can have
only a fixed-normal external contact by (1.3); its complete two-force
equation makes that normal the continuation of its internal axis.

The resulting field has exactly the needed two properties:

\[
 \begin{split}
 &m_i\cdot w_i=0\quad\hbox{for every path member},\\
 &e_i\cdot(w_{i+1}-w_i)=0\quad\hbox{on every internal edge}.
 \end{split}                                                \tag{3.5}
\]

At a loaded member the first statement is orthogonality to its chosen
circle corner; at an unloaded member it uses its actual zero load.
The second statement concerns the same relative translation at every
point of the complete shared side. Hence it preserves its virtual
work for the original application mean, including both endpoint cases.
No mean is selected or treated as fixed data.

The construction depends only on the physical block, its designated
one-atom-or-zero load mask, chosen actual circle corners and internal
axis directions. It does not depend on the external free normals,
unknown magnitudes, or shared means.

## 4. Two exact external virtual-work equations

Let the block's two external contacts be at the fixed actual points
p,q, with outward normals n,m from the block and positive magnitudes
mu,nu. Both contacts are physical singletons, by maximality of the
shared path. The point at q may involve an unloaded endpoint or an
unloaded outside neighbor; no boundary assumption there is inserted.

Sum the full original force equations against the pure translations
in Section 3. Every circle term and internal pair contribution vanishes
by (3.5). Therefore

\[
                        \mu(n\cdot w_1)+\nu(m\cdot w_s)=0. \tag{4.1}
\]

Also sum the full origin-moment equations over the block, or use rigid
rotation of the entire block about the circle origin as a virtual
velocity field. Each circle force is radial, and internal pair forces
have the same application on both bodies. Hence

\[
                      \mu\det(p,n)+\nu\det(q,m)=0.          \tag{4.2}
\]

These are identities in the actual certificate, not proposed finite
motions. Eliminating the two positive magnitudes gives

\[
 D(n,m):=\det(p,n)(m\cdot w_s)
                  -\det(q,m)(n\cdot w_1)=0.                \tag{4.3}
\]

Every internal magnitude, every internal mean and every individual
circle coefficient have been eliminated without replacing their values.

## 5. Complete nonidentity, including the closing edge

### 5.1 Distinct external physical edges

For a fixed value of m, write

\[
 D(n,m)=n\cdot W(m),\qquad
 W(m)=(m\cdot w_s)Jp-\det(q,m)w_1.                         \tag{5.1}
\]

Whenever `det(q,m)!=0`, the vector W(m) is nonzero: otherwise
`w_1=Jz_1` would be parallel to Jp, contradicting (2.2). That
geometric fact applies because the designated free edge at p joins
two loaded, hence physically boundary, bodies by (1.3).

If m is geometrically fixed and `det(q,m)=0`, the proposed positive
cycle is already impossible by its common nonzero moment (1.2).
If m is fixed and its moment is nonzero, (5.1) is a nonzero linear
condition on n and cannot vanish on its genuine open normal interval.

If m is free, its parameter is independent of that of n in the
final supported physical graph. The sole possible coupling would
be the two opposite pairs at one four-square junction, which cannot
both be positive after the stipulated physical uncrossing. A zero
point `q=0` is again excluded by (1.2). For `q!=0`, the open
interval for m contains a value with nonzero moment. At that value
(5.1) proves D nonidentically zero as n varies. Thus D is a proper
nonzero factor on the full genuine product of external parameters.

This includes two distinct external edges at one geometric point
when their parameters are independent. It does not identify independent
edges merely because their applications happen to coincide.

### 5.2 One physical edge closes the entire shared path

If the shared path contains all bodies of the cycle, the two external
incidences are the same closing free edge. Then `p=q` and `m=-n`.
Both endpoint bodies are loaded by (1.3), so the constructed endpoint
velocities have the forms `Jz_1` and `kappa_s Jz_s`. Equation (4.3)
becomes

\[
                    \det(p,n)\,n\cdot(w_1-w_s)=0.           \tag{5.2}
\]

The vector `w_1-w_s` is nonzero. If it vanished, `z_1=kappa_s z_s`.
Their common norm R would give identical or antipodal circle corners.
Identical corners cannot belong to the two different contained squares.
Antipodal corners are impossible for these touching endpoints, since

\[
                  2R=|z_1-z_s|
                        \le |z_1-p|+|p-z_s|\le2\sqrt2<2R.
\]

Also `p!=0`, since it lies in a boundary square and `R>sqrt(2)`.
The two factors in (5.2) are therefore nonzero linear functions of
the free unit normal. Their product is not identically zero on any
open interval. This proves the closing-edge nonidentity without
pretending its two incidences are independent parameters.

## 6. One legitimate common selection covers every mixed block

Before extraction one can prelist every actual path of physical
shared-side pairs, every possible designation of its members as
zero-load or one-positive-corner, each actual corner choice, and
its two external physical point contacts. The list is finite for
the fixed original packing. Include only the necessary internal
straight-normal condition at a designated unloaded member; a final
unloaded member necessarily satisfies it by its full force equation.
Endpoint candidates forbidden by the already imposed two-port rule
cannot occur in the final support.

The velocities (3.2)--(3.4) and their legitimate denominators are
fixed physical geometric data. Under rational unit-circle charts,
every nonidentity in Section 5 is a nonzero rational function over
the fixed countable geometry field. The common algebraically
independent normal tuple therefore avoids all of them simultaneously.
Equivalently, their finitely many nonzero numerators can be avoided
inside the already established nonempty normal domain. No force
weight or unknown mean is adjoined as a fixed coefficient.

Uncrossing preserves surviving point normals and adds only already
available shared-side atoms. Initial minimum-support selection may
delete circle or endpoint atoms before local callers freeze means.
Every resulting maximal shared block and every resulting zero-or-one
positive-corner mask was prelisted. Thus those operations do not create
an unexamined final block. No post-extraction normal change is made.

**Theorem 6.1 (mixed shared-block selection).** In the selected compatible
positive simple cycle, every maximal shared-side block incident to a
free vertex/vertex edge contains a body with at least two positive
circle-corner coefficients. This holds with any number of internal
unloaded bodies and all their physical masks.

**Corollary 6.2.** If every cycle body has at most one positive circle
atom, no positive free vertex/vertex edge survives. In particular this
holds when all loaded bodies have one physical circle corner, regardless
of whether the unloaded bodies physically touch the circle.

These statements extend the virtual-work argument of
`C7_SHARED_SIDE_BLOCK_GENERIC_SELECTION.md`. Its old all-boundary
hypothesis was used to supply circle corners at all internal members
and nonradiality at both external contacts. Here the explicit unloaded
velocity propagation and the whole-cycle nonzero moment replace those
uses. Its stronger radial-endpoint classification is not imported or
claimed for mixed blocks.

## 7. A common-frame short cycle has no physically radial loaded body

For the rest of the source, let the cycle have seven bodies, with
isolated unloaded vertices, and assume all seven actual body frames
are parallel. No assertion about their positive normal directions is
made at entry.

Two parallel axis-aligned unit squares whose interiors are disjoint
and whose closed sets touch have either a positive shared segment,
or a singleton with both coordinate center gaps equal to one in
absolute value. In the latter case it is a vertex/vertex contact
with a genuine open interval of strict common normals. Thus the
two-port rule makes both edges of every unloaded body genuinely
shared sides. In particular every unloaded transmitter is side normal
of width one. Its isolated neighbors are loaded boundary bodies.

Suppose some loaded S has two physical circle corners. A contained
common-frame square has two farthest corners precisely when one
center coordinate is zero. Both coordinates cannot be zero here,
since then physical boundary equality would require `R^2=1/2`.
After a common rotation and reflection write

\[
 S=[d,d+1]\times[-1/2,1/2],\qquad
 T=d+1=\sqrt{R^2-1/4}.                                    \tag{7.1}
\]

The project window implies

\[
              \frac9{10}<d<\frac{61}{60},\quad
              |d-1|<\frac1{10},\quad R-\sqrt2>\frac{11}{20}.
                                                                  \tag{7.2}
\]

For example `T>19/10` and `T<121/60` follow by squaring at
the endpoints, and `sqrt(2)<57/40` gives the last bound.

### 7.1 No adjacent isolated transmitter is possible

Every such positive contact has an own-axis normal. The outer radial
axis is impossible because its support T exceeds `R-1` and a unit
neighbor has width at least one. If the normal is the inward radial
axis, its original application is `(d,t)`, `|t|<=1/2`. Across the
actual width-one transmitter, the other loaded application would be
`(d-1,t)`, of squared norm strictly less than

\[
                       \frac1{100}+\frac14=\frac{13}{50}
                                      <\left(\frac{11}{20}\right)^2.
\]

This is impossible for a point of a boundary unit, whose norm is at
least `R-sqrt(2)`. Finally a tangential own-axis normal has support
`1/2` at S. The far loaded application has projection `3/2` along
that normal; its entire square lies beyond that support and its
width at least one gives a point of projection at least `5/2>R`.
Thus no own-axis channel through an isolated transmitter can leave S.
All means and both individual circle-weight endpoints are included.

### 7.2 Two loaded neighbors would give parallel forces

Both positive neighbors of S must therefore be loaded and physically
boundary. An outer radial contact is still impossible. Any parallel
square on the inner side that touches S has x interval `[d-1,d]`
and center height of absolute value at most one. This includes the
two singleton inner-diagonal contacts. Every one of its corners has
squared norm at most

\[
                       d^2+\frac94
                              <d^2+2d+\frac54=R^2,         \tag{7.3}
\]

because `d>1/2` and `|d-1|<d`. Such a neighbor is physically
circle-clear, a contradiction. An outer-corner singleton would share
an actual circle point and is impossible as well.

Hence every parallel boundary neighbor of S must share one of its
two tangential sides. Both of its positive normals are then parallel
to the tangential axis. But the entire simple-cycle nonparallel theorem,
retained in the force-polygon input, applies at every loaded vertex.
This contradiction excludes S.

We have proved, rather than assumed,

\[
       \text{every loaded body of a common-frame short C7
                    has one physical circle corner.}      \tag{7.4}
\]

## 8. Complete common-frame short-C7 exclusion

By (7.4), every body of this cycle has at most one positive circle
atom. Corollary 6.2 excludes every positive free vertex/vertex edge.
In a common frame, Section 7's exact pairwise contact classification
then makes every positive cycle contact a genuine shared segment.

The complete theorem in
`ALL_SHARED_SHORT_SEVEN_CYCLES_FORCE_RADIUS_BELOW_TWO_2026_10_30.md`
now applies literally. It retains all physical masks and original
means and forces

\[
                         R^2=\frac{2257}{576}<4.
\]

The same nine original squares satisfy the independent lower theorem
`R>2`, already retained in that source's whole-nine conclusion. This
is a contradiction.

**Theorem 8.1 (entire common-frame short-C7 family excluded).** In the
closed project window, no original nine-square packing has a selected
positive simple seven-cycle with isolated unloaded vertices and parallel
frames on its seven core bodies. Its positive contacts may initially
be shared or singleton; its loaded bodies may initially have either
physical circle mask; its unloaded bodies may physically touch the
circle with zero coefficients. Every original additional physical
contact and both completing squares remain unrestricted.

This excludes all four-, five-, and six-load short-C7 arrangements in
this common-frame family at once. It does not place the two additional
squares in the common frame and does not impose row stratification.
The known record-radius packings with long unloaded runs are outside
the short-run premise and remain intact.

Cycles with genuinely different core frames are not assigned a common
frame by this theorem. They still receive the uniform mixed-block
conclusion of Theorem 6.1, with its actual two-positive-corner block
alternative retained.

## 9. Direct inputs and verification boundary

The following direct sources were read in full at the stated identities.
The full mixed-block construction, nonidentity, common-frame circle-mask
exclusion and final literal join are proved in this source.

| Direct source | SHA-256 | Exact use |
| --- | --- | --- |
| `GENERIC_MINIMAL_PHYSICAL_STRESSES_HAVE_RATIONAL_WEIGHTS_AND_SHARED_MEANS_2026_10_30.md` | `fa459e3713c3dc244111528ed65be230dd718a00f388f38f13b6519bb85fa049` | One algebraically independent choice over fixed physical geometry, with initial physically compatible support selection. Only the fixed-geometry generic interface is needed here. |
| `GENERIC_TWO_AND_THREE_PORT_CUT_RULES_FOR_ARBITRARY_UNLOADED_BODY_MODULES_2026_10_30.md` | `f6b12507086fd284e99b637748ef3b40c994c56aba44264a2c3a408338181251` | Theorem 3.1 at a singleton unloaded true-degree-two body; its full positive cut has exactly two edges. |
| `SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md` | `5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635` | Nonparallel loaded stars and nonzero common moment for the entire mixed simple cycle with at least three loads. |
| `ALL_SHARED_SHORT_SEVEN_CYCLES_FORCE_RADIUS_BELOW_TWO_2026_10_30.md` | `af037e1ef7f9fe1a26d662f4b226d3bb446bd8e93cb48b0d7a32e78d141047cb` | Complete all-shared short-C7 exclusion with full reflection work and unchanged same-nine lower-radius dependency. |

`GENERAL_FIXED_TIP_NORMAL_SELECTION.md` was also read completely. Its
distinct-fixed-application result remains a valid earlier local theorem;
the present block theorem handles genuinely variable internal shared
means and does not replace them by fixed endpoints. The old all-boundary
block and pinned-profile sources were read for scope and are not imported
outside their physical-boundary hypotheses.

No original fine or coarse ledger flag is changed by this proposed
source. No numerical search, mesh, certificate computation, Lean/Lake
invocation, CI dispatch, metadata mutation, remote edit, or deletion
of a physical body is used.
