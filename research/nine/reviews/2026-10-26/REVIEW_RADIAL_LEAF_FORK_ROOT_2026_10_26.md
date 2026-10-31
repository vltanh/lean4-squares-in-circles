# Root review: radial-leaf channel fork and simultaneous cycle-leaf propagation

Date: October 26, 2026.

**Result: PASS for the full two-boundary-channel fork theorem, both
original C5 load-23 leaf alternatives, the stated D/tilted-S extension,
and the exact simple-cycle-plus-one-leaf corollary.**

Root independently read the complete saved
RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md, its actual
leaf/root and channel prerequisites, the complete
CENTERED_INNER_ARC.md geometric theorem, the original C5
graph/load cover and the two pre-existing roadmap entries.
The separate complete review is
REVIEW_RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_C6_2026_10_26.md.

## 1. No force or degree is lost at the root

The full theorem assumes a genuinely circle-clear root of true
positive degree three: one actual radial-leaf force and two
unchanged normal-channel forces. Its outward-force signs,
positive magnitudes and original moments are correct. A leaf
application is radial, so its moment about the circle origin is
zero; taking moments about the actual leaf application also
retains its zero moment. The root has no hidden fourth force.

The far-endpoint halfwidth and sharp center bound give the
channel support \(h_i\le d-1=\delta\) for every true reserve
at least one. The genuine radial-leaf root distance bound gives
an immediate contradiction if \(\delta<0\). Thus all subsequent
uses of \(d\ge1\) and \(0\le\delta<1/60\) are justified
original-domain reductions.

## 2. D root: full slider and opposite-sign supports

The complete D root has its origin in the open rectangle and
horizontal half-support distances both greater than \(1/4\).
The support bound therefore forces
\(|n_x|<1/15\), \(|n_y|>14/15\). The original vertical
force equation requires opposite vertical signs. The two
supports then sum to more than \(14/15\), because the two
vertical side distances sum to one, while each support is at
most \(\delta\). This contradicts \(2\delta<1/30\).

No endpoint boundary mask or force equation is needed in this
part. Every D root-slider value remains.

## 3. Tilted S root: complete actual support-face moment cover

The inward own-axis representation covers both tilted families
after a possible orientation reversal. That reversal multiplies
every own-frame moment by the same nonzero determinant and does
not affect the zero-torque condition.

The support formula in equation (14) is exact. The two excluded
quadrant regions follow from the stated positive coefficient
bounds. Every remaining normal is in one of the five rows of
the moment table. I checked the vertex rows and both owned-axis
rows with their complete closed mean intervals. Every moment
is nonpositive. The unchanged second-component force equation
has positive right side \(\lambda b\), forcing a normal in the
strictly negative-moment row. The full torque sum is therefore
strictly negative, a contradiction.

The endpoint means are included in the two axis rows. There is
no implicit replacement of a shared-side mean by a chosen vertex.

## 4. Aligned S root: complete force, torque and angular argument

If a channel has nonnegative horizontal component, reflection
and the actual two-channel balance give weighted forces
\((X,v)\), \((-Y,-v)\), with \(Y=X+\lambda>X\).
Their true support applications give exactly
\[
 v(\xi-\delta)=aX+bY=X+b\lambda.
\]
This retains the upper-side mean interval when \(X=0\).
It implies both \(v\ge X\) and \(v\ge bY\).
The successive inequalities \(a<1/30\), \(b>29/30\) and
the contradiction \(h_2>1637/2700>\delta\) follow with the
correct strict signs. Both aligned slider endpoints are covered.

When both normals point strictly westward, the original vertical
force and torque equations give the displayed ratio
\(a=\tan\phi/(\tan\phi+\tan\psi)\). The larger channel angle
has the corresponding vertical root distance at least \(1/2\).
Its support bound gives \(\sin\phi,\sin\psi<1/15\).
The exact triple-angle comparison proves both angles below
\(\pi/36\), including the separate west-parallel case.

The actual root point \((\delta,0)\) yields
\[
 n_i\cdot c_{Q_i}>89/60,\qquad |c_{Q_i}|<91/60.
\]
Hence each endpoint center lies within \(\pi/12\) of its
channel direction. I independently checked the fixed cosine
comparison, the rational torque bound, and all displayed
arithmetic reserves.

Both center directions are consequently within \(\pi/9\) of
west, so their mutual minor angle is less than \(2\pi/9\).
The full centered-inner-arc source proves a strict greater-than
\(2\pi/9\) separation for any two distinct physical boundary
squares in the entire radius window. I checked its actual
physical-circle premise, strict interior arc, cubic remainder
estimate and pair consequence; it needs no positive weight at
the endpoint square. The contradiction is therefore valid for
both physical circle masks and zero individual weights.

## 5. Original C5 gates and the exact larger-cycle consequence

For C5 order \(0,1,2,3,4\) and genuine leaf at 0, the exact
load word 23 makes 1 and 4 true unloaded degree-two bodies.
The channels are 0--1--2 and 0--4--3, and both distinct far
endpoints are physical boundary squares. Root 0 has exactly
the three positive edges used in the theorem. All three other
physical squares remain arbitrary.

This excludes exactly the two originally unchecked labels
M6.B5L.C5.L23.S and M6.B5L.C5.L23.D, over their full
retained contract. The earlier 12/14 exits are different
orbits. The other C5 load words remain open.

For an exact simple cycle plus one genuine leaf, the root
still has degree three and every other cycle vertex degree
two. The nontrivial positive component has at least three
positively loaded bodies: the elementary force/virial
exclusions handle zero or one, and
TREE_AND_TWO_LOAD_COMPLETION.md excludes exactly two.
The loaded leaf and clear root thus leave at least two cycle
loads. If both immediate cycle neighbors were unloaded, the
two unchanged degree-two paths from the root reach the first
and last loaded vertices in the cut-cycle order. They are
distinct, and both paths have reserve at least one. The fork
theorem applies with no force deleted.

This proves the immediate-neighbor load restriction simultaneously
for the exact C5/C6/C7/C8-plus-leaf graphs, with respectively
3/2/1/0 other original physical units. No full larger coarse
cell is inferred, and chords or additional attachments require
new degree checks.

## 6. Precisely limited degree-free extension

For D roots, arbitrary many actual nonleaf channels still force
at least one upward and one downward channel; the contradiction
uses their two support bounds without deleting the other
forces from the equation that supplied them. For tilted S
roots, all channel moments are nonpositive and the full sum
of second force components makes one strict. These two
extensions are valid without any boundary premise at the
far endpoints.

The aligned-S argument uses exactly two channels. The source
correctly keeps the true degree-three premise for the full
S/D theorem and does not assign its pair identities to a
higher-degree root.

No new gate, coefficient certificate, numerical proof premise,
Lean compilation, CI or workflow action is introduced. The
unrestricted radius theorem, equality classification and older
full prerequisite audit remain open.
