# n=9: exact small-tree stress cores and complete star exclusion

**Status:** hand necessary-condition and exclusion theorems for the
physical positive-stress graph, with the radius window stated explicitly.
No global nine-square lower bound, independent audit, Lean build, CI run,
or remote write is claimed.

## 1. Current source synchronization and prior inputs

The initial read base of this continuation was
`a6b37a74769908a64cef5835550f0ec04191eb98`. During this work the research
branch advanced to `028a63b4fc963eb78d776a7f42ff3606e651e816`, which adds
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`. That file already proves the
radial bridge law and loaded-leaf classification. **Those are credited
as existing inputs here, not counted again as new closure.**

Use the physical force/torque stress of `PHYSICAL_CONTACT_STRESS.md`,
aggregated to one force at an actual shared point per positive body pair.
The prior radial-bridge manuscript supplies these exact facts:

1. Every positive body-pair graph bridge has a force line passing through
   the disk center; each cut side carries positive circle load.
2. At `q <= Q` and `R > sqrt(2)`, every bridge has an incident square
   that is geometrically circle-clear. In particular, a bridge cannot
   join two circle-loaded bodies.
3. The physical certificate can be selected so that every off-origin,
   point-only vertex/vertex positive edge lies on a cycle. Such an edge
   is not a bridge. This is an **existence of a suitable certificate**,
   not an assertion about every arbitrary normal choice.
4. A circle-loaded leaf has exactly one of these two forms, for a unit
   radial vector \(e\), with \(T=\sqrt{R^2-1/4}\):

\[
\begin{array}{c|c|c}
\text{type}&\text{center}&\text{inward contact point}\\\hline
S\ (\text{side normal})&(T-1/2)e&(T-1)e\\
D\ (\text{diagonal})&(R-1/\sqrt2)e&(R-\sqrt2)e.
\end{array}                                                   \tag{1}
\]

An S leaf has two equally weighted outer circle vertices. A D leaf has
one loaded circle vertex and its opposite vertex at the bridge. Under
the normal selection in item 3, a D leaf contacts the **relative interior
of a side of its neighbor**: its off-origin vertex/vertex alternative
cannot be a bridge. Therefore its force normal is an axis of the
neighbor's own square frame.

The existing discrete-transmitter theorem also says an unloaded,
degree-two square transmits across opposite sides (width 1) or opposite
vertices (width \(\sqrt2\)). At \(q\le Q\), a square-ended path of such
internal bodies has total reserve only \(0,1,\sqrt2,2\).

The graph in this manuscript is the **positive aggregated body-pair
graph**, not the full contact graph and not the separate planar incidence
graph. Unstressed squares remain physical packing obstacles.

## 2. A tree with exactly two loaded bodies has one possible radius in the n=9 window

The following theorem states its radius window explicitly:

\[
                        79/40\le R\le\sqrt{1105}/16.        \tag{2}
\]

The repository's established n=8 result supplies such a coarse lower
window for a nine-square packing by deleting one square. **That earlier
n=8 proof has computational dependencies on the current main branch.**
The theorem below is a hand implication under (2); this document does
not silently import the n=8 theorem into a supposedly independent
unrestricted table-free n=9 proof. A separate elementary lower-window
argument or a declared dependency is needed when assembling the final
unrestricted theorem.

**Theorem 1 (two-loaded tree normal form).** Let a connected positive
physical-stress component be a tree with exactly two circle-loaded
square bodies. Under (2), its squared radius is necessarily

\[
                               R^2=17/4.                   \tag{3}
\]

It consists of four squares in a straight horizontal projection chain,
after rotating the whole configuration:

\[
 (-3/2,0),\quad(-1/2,\tau_1),\quad(1/2,\tau_2),\quad(3/2,0),
 \qquad |\tau_1|,|\tau_2|\le1/2.                            \tag{4}
\]

All four side frames are aligned with the displayed coordinates.
Only the outer two squares are circle-loaded. The two middle centers
may slide vertically; the theorem does **not** set them equal to zero.

*Proof.* Every graph leaf is loaded, since an unloaded one-force body
cannot balance forces. A finite tree with exactly two loaded nodes
therefore has exactly two leaves and is a path, with the loaded bodies
at its endpoints and all internal bodies unloaded of degree two.

By `PHYSICAL_CONTACT_STRESS.md`, the internal transmitters have widths
\(1\) or \(\sqrt2\) along a common force direction, and the square-ended
path reserve \(W\) at \(q\le Q\) is one of

\[
                             0,\ 1,\ \sqrt2,\ 2.           \tag{5}
\]

The radial bridge theorem makes every contact force line radial. Force
balance propagates the same line and magnitude along the path, and the
loaded-leaf dichotomy puts the two leaves on opposite radial rays. Let their inward-contact radii be

\[
             a_S=\sqrt{R^2-1/4}-1,
       \qquad a_D=R-\sqrt2.
\]

Both are positive under (2). The physical shared-point gaps telescope
along the path, giving exactly

\[
                  W=a_X+a_Y,\qquad X,Y\in\{S,D\}.           \tag{6}
\]

There are three unordered endpoint-type cases, which can be handled
without enumerating the internal poses.

- **D–D:** \(W=2R-2\sqrt2\). Under (2),
  \(1<W<\sqrt2\). The lower bound follows from
  \(\sqrt2<59/40\); the upper from \(R^2\le Q<9/2\).
  None of (5) lies in this interval.
- **S–D:** \(W=R+\sqrt{R^2-1/4}-1-\sqrt2\).
  Since \(\sqrt{R^2-1/4}>19/10\), the lower bound
  \(R+\sqrt{R^2-1/4}>31/8>1+2\sqrt2\) gives \(W>\sqrt2\).
  Since \(R<17/8\), the upper bound
  \(R+\sqrt{R^2-1/4}<17/4<3+\sqrt2\) gives \(W<2\).
  Again no value in (5) is possible.
- **S–S:** \(W=2\sqrt{R^2-1/4}-2>9/5>\sqrt2\).
  The only remaining value in (5) is \(W=2\), so
  \(\sqrt{R^2-1/4}=2\), proving (3).

A reserve of two consists of exactly two side-normal internal squares.
The S-leaf centers are at \(\pm3e/2\), and the force points run from
\(-e\) to zero to \(e\). The two internal squares consequently have
centers \(-e/2+\tau_1Je\) and \(e/2+\tau_2Je\), with
\(|\tau_i|\le1/2\) so the force line meets their opposite sides.
This is precisely (4). QED.


## 3. Exclude every positive star component in the same radius window

**Theorem 2 (no positive star core).** Use the physical certificate with
the nonradial off-origin vertex/vertex normal choice above. Under

\[
                          79/40\le R\le\sqrt Q,
\]

no connected positive body-pair component can be a star with one hub
and two or more leaves. A two-body, one-edge component is also impossible.
This holds regardless of the orientations and placements of any other
unstressed squares.

*Proof.* Every positive graph leaf is circle-loaded: one nonzero contact
force cannot balance on an unloaded body. The bridge circle-clear
property consequently makes the hub circle-clear and unloaded. It
also immediately excludes a component consisting of just two loaded
bodies joined by one bridge.

Set

\[
        A=\sqrt{R^2-1/4}-1,\qquad B=R-\sqrt2.
\]

All S-leaf contacts on the hub have the form \(p=Ae\); all D-leaf
contacts have the form \(p=Be\). The corresponding forces on the hub
are positive multiples of \(e\). In the stated window,

\[
          A>9/10,\qquad 1/2<B<7/10,
          \qquad A^2-B^2>1/4,\qquad A>\sqrt2 B.             \tag{7}
\]

Here \(\sqrt{R^2-1/4}>19/10\) follows by substitution at \(79/40\).
The lower bound for B follows from \(\sqrt2<59/40\), and its upper
bound from \(R<21/10\) and \(\sqrt2>7/5\). Thus
\(A^2-B^2>81/100-49/100=8/25>1/4\).
For the last comparison, put \(T=\sqrt{R^2-1/4}\). The exact identity

\[
 T^2-(\sqrt2R-1)^2=\frac34-(R-\sqrt2)^2
                        =\frac34-B^2>0
\]

gives \(T>\sqrt2R-1\), hence \(A>\sqrt2 B\).

Fix coordinates along the **hub's** two side axes.
Every D leaf contacts the relative interior of a hub side, by the
chosen normal certificate. Its radial vector e is therefore one of
\(\pm e_x,\pm e_y\). Two D leaves with the same e would have the
same center and square, which physical nonoverlap forbids. Two D leaves
with opposite e would require the distance between two opposite hub
sides to be \(2B\), hence \(2B=1\), contrary to (7).
There can therefore be **at most two D leaves**, and if there are two
their normals are adjacent perpendicular directions.

There are exactly three cases.

### No D leaves

Every contact point on the hub has norm A, and hub force balance is
\(\sum_j\mu_j p_j/A=0\), with \(\mu_j>0\).
Normalize the weights to sum to one. If c is the hub center, every
contact point lies in the hub square and so has
\(\|p_j-c\|^2\le1/2\). But their weighted mean is zero, whence

\[
       \sum_j w_j\|p_j-c\|^2=A^2+\|c\|^2>1/2,
\]

a contradiction. This treats any number of S leaves without a graph
or angle table.

### Exactly one D leaf

Rotate/sign the hub axes so that this contact is \((B,0)\), on its
right side. The hub's horizontal interval is \([B-1,B]\).
Because \(B>1/2\), every hub point satisfies \(|x|\le B\).
Every S contact has norm A, so (7) gives

\[
                     |y|\ge\sqrt{A^2-B^2}>1/2.
\]

The D force has zero vertical component. Positive hub force balance
therefore requires S contacts with both signs of y (or it already
fails). Two such points differ vertically by more than one, impossible
inside a unit square whose sides are the chosen coordinate axes.

### Exactly two D leaves

Their normals are adjacent; use sign choices so the two contacts are
\((B,0)\) and \((0,B)\), on the hub's right and top sides. The entire
hub lies in \([B-1,B]^2\), so every point has norm at most
\(\sqrt2B<A\). It cannot contain an S contact at all.
The only remaining two force vectors have positive coefficients in
perpendicular directions and cannot sum to zero. Contradiction.

These three cases exhaust the star. QED.

The radius window matters: the standard five-square plus packing at
\(q=5/2\) has an unloaded central hub and four side-radial loaded
leaves. It is a valid positive star **below** the window, not a
counterexample to the theorem.

## 4. Completion capacity and remaining tree/cycle cases

Theorem 1's two-loaded path can involve only four of the nine physical
squares. Its five remaining squares cannot be discarded because their
stress weights are zero.

The subcase \(\tau_1=\tau_2=0\) is now excluded completely: it is a
solid four-square row, so `SOLID_FOUR_ROW_UNRESTRICTED_NINE.md` forces
any nine-square completion to have \(q=Q>17/4\), contradicting the
path's radius.

For arbitrary \(\tau_1,\tau_2\in[-1/2,1/2]\), the four-square union
is staggered rather than a solid rectangle. Its free squares can use
oblique separators even against a row square. The full five-square
completion obstruction remains open.

Theorem 2 excludes **all star components**, rather than one radius
or angle perturbation of a star. It does not exclude trees with several
branching bodies, or a hub connected to leaves through nontrivial
transmission paths. Cyclic components likewise require further work.
The remaining global gate is an exhaustive sharp bound for every
realizable core **together with every physical completion to nine**.