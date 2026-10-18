# Entire radial SS interface of the smallest k=7/B3 branching core is impossible

**Structural research, 2026-10-13. Complete conditional global
stress subbranch exclusion.** This is a genuine whole **positive
contact-graph contradiction** independent of any numeric local
cap-cutoff tuning.

The proof combines two previously established inputs:

* an all-orientation hand exclusion of the **all-C-side-normal**
  SS triangle,
  [HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md](HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md),
  which uses only the purely analytic lower bound
  \(R>\sqrt2+1/2\);
* the sharper *complete* two-sign SS side-plus-corner
  normal form
  [HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md](HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md),
  which uses the project's **independently exact computer-certified**
  global lower bound \(R_8^2>19/5\), recorded in
  GLOBAL_LOWER_BOUND.md.

**The second dependency is explicit.** The final XY
contact contradiction is a short hand proof and does
not use the computer verifier itself.

## Theorem

Assume eight genuine, interior-disjoint unit squares
attain the minimum containing radius
\[
19/5<R^2\le9789/2500,\qquad R<2,
\]
with the unique origin-containing C, **seven outer**
exterior center labels, and outer actual-contact
graph a proper subgraph of the seven-center ray cycle.

Suppose a normalized physical stress has its
unique positive component consisting of the smallest
branching core
\[
C-X-Y-C\quad\text{plus positive radial bridge }C-Z.
\]

Then the radial bridge **C--Z C-side/Z-side interface
SS is impossible**:
\[
\boxed{\text{no such stress may have radial
side-to-side bridge C--Z}.}                    \tag{1}
\]

This conclusion is independent of C's number of extra
zero-positive-stress *actual* contact neighbors,
the four spectator squares' frames/contacts, and
any unconstrained X/Y frame rotations. The real
equality-bearing **full outer seven-contact ring**
belongs to a different global root and remains valid.

Consequently the only two **genuine radial bridge interfaces**
still not excluded in this **minimal B3 component** are
\[
\boxed{\text{CS: C radial corner / Z true side},
\qquad
\text{SD: C true side / Z inward diagonal corner}.}       \tag{2}
\]
In a contact-minimal radius minimizer, both require
additional actual zero-stress spectator bracing.

## 1. The exact surviving SS side-plus-corner normal form

Suppose for contradiction C--Z has radial SS mode,
with positive bridge normal n and t=Jn.
Because C and Z share n as a true side normal,
Z is frame-parallel to C and contacts its
radial positive side at \(z_Z=bn\).

The prior complete hand normal form
[HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md](HUMAN_B3_SS_SIDE_CORNER_DICHOTOMY.md)
uses positive C force/torque balance,
the exact high radial leaf cap,
a near-origin true-square diameter bound,
and the separately certified lower
radius \(R^2>19/5\) to prove:

* C's transverse center displacement
  \(d:=t\cdot p_C\) is **nonzero**;
* if d>0, then, after naming the
  upper and lower stressed triangle
  squares X,Y,
  \[
  \begin{aligned}
  z_X&=-k n+(d+\tfrac12)t,&
  n_X&=-c n+s t,\quad c,s>0,\ c^2+s^2=1,\\
  n_Y&=-t,&
  Y&\subseteq
       \{w:t\cdot w\le d-\tfrac12\};
  \end{aligned}                                  \tag{3}
  \]
  the point z_X is C's actual
  **top-left corner**, and is a
  **true inner support-face contact point of X**;
* if d<0, the frame-reflected
  statements hold: Y contacts C
  at the **bottom-left corner**
  with normal \(-c n-s t\), while
  X contacts C with normal +t
  and lies wholly **above**
  \(t\cdot w=d+\tfrac12\).

The present theorem only needs
the geometric support statements (3);
it does not otherwise use their
quantitative derivation.

## 2. A corner-to-side true-square vertical separation lemma

**Lemma.** Let \(X\) be a genuine unit square of
**arbitrary independent orientation**, with an
actual inward supporting side contact at a point
\(z\) and unit outward-from-contact normal
\[
m=-c n+s t,\qquad c,s>0,\quad c^2+s^2=1.
\]
In the coordinates of true frame \(m,Jm\),
the whole square X is a unit-width slab with
its **inner m-support face passing through z**.

Every point \(w\in X\) has a representation
\[
w=z+u m+v Jm,\quad
0\le u\le1,\quad v\in[a,a+1]
\]
for some \(a\in[-1,0]\), because z belongs
to the inner face of X.
Since
\[
t\cdot m=s>0,\qquad
t\cdot Jm=-c<0,
\]
every actual point of X satisfies
\[
t\cdot w=t\cdot z+us-vc
\ge t\cdot z-c.
\]
Because \(s>0\), we have \(c<1\), so
\[
\boxed{X\subseteq
 \{w:t\cdot w>t\cdot z-1\}.}                  \tag{4}
\]

This is an **exact full-square support separation**,
not an inference from center signs or a sampled
frame angle. Equality at the line
\(t\cdot z-1\) is impossible because c<1.

## 3. The positive X--Y triangle contact is impossible

Take first d>0 and use (3). The genuine
C-corner-to-X contact point has
\[
t\cdot z_X=d+\tfrac12.
\]
By (4), **every actual point of X** satisfies
\[
t\cdot w>d+\tfrac12-1=d-\tfrac12.
\]
But by its true C bottom-side
contact normal -t, the **entire
different square Y** satisfies
\[
Y\subseteq\{w:t\cdot w\le d-\tfrac12\}.
\]
Thus X and Y have a strict positive
one-dimensional separating gap:
\[
\boxed{\inf_{w\in X}t\cdot w
      -\sup_{v\in Y}t\cdot v
      \ge1-c>0.}                               \tag{5}
\]
In particular **their closed squares do not touch**,
whereas the positive-stress core
\(C-X-Y-C\) requires a *genuine
positive X--Y actual contact*.
Contradiction.

If d<0, reflect the geometry across the
n direction. The lower corner-contact
square lies strictly **below** the upper
pure-transverse-side square, with exactly
the same positive gap \(1-c\).
Thus the required positive X--Y contact
is impossible in either reflected case.

These two cases exhaust SS by the
previous proved complete dichotomy.
Therefore the entire radial SS bridge
interface is impossible, proving (1). QED.

## 4. Current remaining B3 normal forms and precise status

The **minimal four-square positive B3 branching component**
has, after this theorem, only two genuine
radial bridge interfaces:

* **CS:** radial contact at a true C corner,
  Z side-oriented, two equally weighted
  disk-circle vertices, high radial cap
  \(b=\sqrt{R^2-1/4}-1>4/5\).
  The X/Y positive C contact normals
  have nonzero **opposite transverse
  projections**. In contact-minimal
  representatives the CS radial stress leaf
  must have an extra **true zero-weight
  spectator contact**.
* **SD:** contact along a true C side to
  Z's **inward diagonal corner**, with Z's
  single positive true circle vertex at
  \(R n\), offset \(b=R-\sqrt2\).
  Its actual radial leaf likewise requires
  additional zero-weight spectator bracing.
  Do **not** import the CS high-cap
  exclusivity into this lower-offset mode.

If C has exactly its three positive
*actual* neighbors X,Y,Z, the
[HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md](HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md)
theorem forces either a **complete
Y-Z spectator path or a complete
Z-X spectator path** in both CS and SD.
The no-extra-spectator-edge case is
impossible because the radial Z square
would then be an unbraced actual leaf.

The additional circle-or-transmitter
anchors along those full spectator paths
are proved in
[HUMAN_B3_AUXILIARY_ARC_BOUNDARY_COVER.md](HUMAN_B3_AUXILIARY_ARC_BOUNDARY_COVER.md).
This is a finite actual-contact
structural queue, **not** a certified
feasible packing list or the
sharp global lower bound.

**Proof dependency guard:** the full
SS interface exclusion currently
depends on the project’s exact
integer-interval certificate
\(R_8^2>19/5\).
That older computational lower bound
has not been replaced by an entirely
pen-and-paper proof within the present
continuation. If one requires a fully
human-only global proof, either
formal verification of the certificate
or a separate analytic radius bound
above the needed coarse threshold
must eventually be supplied.

The full seven-outer actual ring A
remains a genuine sharp equality
configuration. The unrestricted
\(R_8\ge\widehat R\),
global equality classification,
and Lean theorem remain OPEN.
