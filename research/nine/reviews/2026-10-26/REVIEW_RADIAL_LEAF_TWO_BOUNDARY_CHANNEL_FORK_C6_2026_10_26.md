# Independent review of the radial-leaf two-boundary-channel fork

Date: October 26, 2026.

**Result: PASS, for the entire stated physical domain and the two exact
original C5 load-23 gates.** This is an independent source and scope
audit of `RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md`.
The review does not assert any additional coarse graph gate, and uses
neither a pose sample nor an interval certificate.

The reviewer read the whole source, the genuine-leaf root and channel
lemmas in `FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`, the complete geometric
statement and proof in `CENTERED_INNER_ARC.md`, and the original
`M6.B5L.RETAINED_CONTRACT` and C5 load-23 entries in
`DEEP_GATED_ROADMAP.md`.

## 1. Common premises and the original channel directions

The root is physically clear and has its true three positive forces:
the genuine radial leaf and the two actual channels. Thus the displayed
force equation is complete. Its leaf application is radial, so its
origin torque is zero; changing the torque origin to that application
retains all other terms.

Each true unloaded degree-two internal body supplies the original
normal channel, with its real application means and reserve at least
one. The far endpoints are not assigned degree-two equations. The
center estimate follows from the farthest-corner inequality, and the
minimum directional halfwidth of a unit square is one half. These facts
give each root support at most \(\delta=d-1\).

The inherited genuine-leaf root lemma is independent of the root's
other forces and retains both full leaf types. If \(\delta<0\), it puts
the origin in the closed root square, contradicting the negative
channel-support bounds. Consequently the proof may use
\(0\le\delta<1/60\). No positive-force edge or physical body is removed.

## 2. D and tilted-S root domains

The D root has the full open side-interior slider. Both horizontal
support distances exceed one quarter, while the vertical interval
contains zero. Thus each channel has horizontal component smaller
than \(1/15\) in absolute value and vertical component greater than
\(14/15\) in absolute value. The complete vertical force equation
requires opposite signs. Their two supports then have sum greater
than \(14/15\), contradicting the upper bound \(2\delta<1/30\).
This argument needs containment of the far endpoints, but does not
need their boundary contact.

For a tilted S root, the inward orthonormal coordinate choice covers
both reflected families and every tilt. The support formula includes
every face. The two support exclusions correctly remove
\(x\le0,y\ge0\) and \(0<x\le y\). The five remaining rows of the moment
table are exhaustive, including the complete side-mean intervals and
their endpoints. Every retained moment about the actual leaf
application is nonpositive. The full second coordinate of force
balance requires at least one strictly positive \(y\), whose moment
is strictly negative. The determinant orientation of the chosen frame
multiplies every moment by the same nonzero sign, so it does not affect
the contradiction.

The explicitly stated arbitrary-root-degree extensions for D and
tilted S also follow. For D, the complete force equation supplies an
oppositely directed pair among the channels. For tilted S, the moment
table sums over every actual channel. The source correctly does not
extend the aligned-S two-force identities to an arbitrary number of
channels.

## 3. Aligned S roots and the force/torque identities

The aligned domain retains both endpoint sliders. If a channel has
nonnegative horizontal component, the weighted components can indeed
be written \((X,v)\) and \((-Y,-v)\), with
\(X\ge0\), \(v>0\), and \(Y=X+\lambda>X\). The support applications are
the stated upper support mean \((\xi,a)\) and lower-left vertex
\((\delta,-b)\); when \(X=0\), the whole interval
\(\delta\le\xi\le d\) remains.

Taking moments about \((d,0)\) gives exactly

\[
 v(\xi-\delta)=aX+bY=X+b\lambda.
\]

Since \(\xi-\delta\le1\), both inequalities \(v\ge X\) and
\(v\ge bY\) are justified. The resulting upper bound on \(a\), lower
bound on \(b\), and lower bound on the second support produce the
strict contradiction displayed in the source. This covers vertical
channels as well as channels pointing strictly right.

After excluding these cases, both channels point strictly westward.
If one vertical component is zero, the complete force equation makes
both zero. Otherwise their actual support applications are the two
left vertices. Directly re-expanding force and torque gives

\[
 \mu_1\sin\phi=\mu_2\sin\psi,
 \qquad
 a\mu_1\cos\phi=b\mu_2\cos\psi.
\]

They imply the stated formula for \(a\), including the necessity
that both \(a,b\) are positive in this branch. Choosing the larger
angle yields \(\sin\phi,\sin\psi<1/15\). The exact triple-angle
comparison implies \(\phi,\psi<\pi/36\). The west-parallel branch
is retained with both angles zero.

## 4. Actual endpoint centers and the angular contradiction

The point \((\delta,0)\) belongs to every aligned root in its full
slider domain. Therefore every root support is at least
\(-\delta\). The actual reserve and endpoint halfwidth give projection
greater than \(89/60\), whereas the endpoint center norm is smaller
than \(91/60\). Thus each endpoint center lies within \(15\) degrees
of its own channel direction.

Combining the strict \(5\)-degree channel bound and strict
\(15\)-degree projection bound puts both centers within \(20\) degrees
of west. Their mutual minor angular separation is strictly less than
\(40\) degrees. The directly checked `CENTERED_INNER_ARC.md` theorem
applies to every physically circle-touching unit square, regardless of
its individual or total circle-force weights. It requires only disk
containment and disjoint open interiors, and gives separation strictly
greater than \(40\) degrees. Its use here is therefore valid for all
the stated masks and zero-weight contacts.

For completeness, the following fixed rational comparisons in the
source were reproduced exactly:

\[
\begin{aligned}
 (121/60)^2-(1105/256-1/4)&=31/57600,\\
 (57/40)^2-2&=49/1600,\\
 (25/12)^2-1105/256&=55/2304,\\
 1-(61/60)(3/4)&=19/80,\\
 (19/80-1/60)(2/3)&=53/360,\\
 -1/60+(2/3)(29/30)^2&=1637/2700,\\
 16\cdot89^2-15\cdot91^2&=2521.
\end{aligned}
\]

These are transparent arithmetic checks of displayed constants, not
a finite sign grid substituting for an interval proof.

## 5. Exact join to the original C5 load-23 obligations

The original rooted cycle is \(0-1-2-3-4-0\), with its genuine leaf
at root \(0\). In block-load representative \(23\), vertices \(1\)
and \(4\) are actual unloaded degree-two transmitters. The clear root
has true degree three, with all three original forces retained. Its
two channels are precisely \(0-1-2\) and \(0-4-3\), whose distinct
far endpoints are loaded and hence physically boundary. The root
reflection exchanges these two channels and leaves the complete
load orbit included.

The proof therefore closes exactly these two pre-existing whole
families under `M6.B5L.RETAINED_CONTRACT`:

| Original gate | Full exit verified |
| --- | --- |
| `M6.B5L.C5.L23.S` | Every aligned and tilted genuine S-root pose and mean |
| `M6.B5L.C5.L23.D` | The full genuine D side-interior root slider |

The three arbitrary additional physical squares are retained: the
contradiction already occurs in the unchanged core. The result does
not require any completion-capacity certificate. It neither replaces
the distinct earlier load-12/load-14 exits nor closes the other rooted
C5 load orbits or the whole five-body-block-with-leaf parent.

**Accepted conclusion.** The entire stated fork theorem, its precise
D/tilted-S degree extension, and both original load-23 S/D joins are
sound. No Lean compilation or CI was used in this review.

## 6. Independent audit of the size-independent propagation addition

The subsequently added Section 8 also passes for the original
nine-square selected-certificate setting. The component is exactly a
simple cycle with one genuine leaf; it has no additional chord or
attachment. The clear root consequently retains true degree three,
and every other cycle vertex retains true degree two.

The component has at least two positive circle loads by the basic
component force and virial identities. A single loaded body's circle
resultant is nonzero, since its physical circle corners lie in one
open hemisphere and their nonnegative weights have positive total;
it cannot supply a zero total component force. Zero circle loads
contradict the positive internal-force virial. The directly re-read
`TREE_AND_TWO_LOAD_COMPLETION.md`, Corollary TL, excludes exactly two
loads while retaining all nine squares. Thus there are at least three
loads. The genuine leaf accounts for one and the physically clear
root accounts for none, so at least two distinct nonroot cycle
vertices are positively loaded.

Cutting the simple cycle at its root gives a linear order of all
nonroot cycle vertices. If both immediate neighbors were unloaded,
the first and last loaded vertices in this order would be different.
The two paths to them consist entirely of unchanged unloaded
degree-two internal bodies. Their actual force and torque equations
therefore give the two normal channels, each with reserve at least
one, required by the fork theorem. Possible physical zero-weight
circle contacts along a path do not affect those exact unloaded
equations. The endpoint loads imply physical boundary contact. No
endpoint equation or internal force is deleted.

It follows that at least one immediate cycle neighbor of the leaf
root must carry positive circle load. The same proof simultaneously
excludes the whole both-neighbors-unloaded family for C5, C6, C7,
and C8 with one genuine leaf, whose actual component sizes are
respectively six, seven, eight, and nine and whose retained numbers
of other physical units are three, two, one, and zero.

This propagation uses the existing two-load completion theorem in
the stated nine-square problem; it makes no claim about packings
with an arbitrary total number of squares. It does not close a
whole larger cycle-leaf graph or infer a channel through a vertex
with an additional positive force. The source's stated limitation
and absence of additional roadmap counts are correct.
