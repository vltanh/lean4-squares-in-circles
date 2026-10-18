# Coarse global radius certificate forces an exact transverse-side/corner SS branching scaffold

**Structural research, 2026-10-13.** This is a hand
geometric implication with one **explicit separately
computer-certified premise**: the already recorded
unrestricted lower bound \(R_8^2>19/5\) from
[GLOBAL_LOWER_BOUND.md](GLOBAL_LOWER_BOUND.md),
whose certificate is the exact integer interval
verifier in verify_sharp_exterior_markers.cpp.
The new deductions below use only elementary
square geometry, true SAT owners, positive stress
forces and rational inequalities. They are
**not** an independent, computer-free proof
of the \(19/5\) lower bound or the sharp optimum.

## Theorem: only two signed SS triangle contact patterns survive

Assume the smallest k7 central-branching positive
stress component is
\[
C-X-Y-C\quad\text{plus positive radial bridge }C-Z,
\]
with **SS side-to-side radial leaf interface**:
its normal is a true C/Z side normal n,
\[
Z=\{\,bn+u n+v t:0\le u\le1,\ |v|\le1/2\,\},
\quad t=Jn,\quad
b=\rho-1,\quad \rho=\sqrt{R^2-1/4}.
\]
The containing radius obeys the **separately
exact-certified** global bounds
\[
19/5<R^2\le9789/2500.
\]
Orient n horizontally and write C's center
\[
p_C=(b-1/2,d),\qquad |d|<1/2.
\]
Let X and Y have the two positively stressed
C-contact outward normals with strict,
opposite t projections, as proved in
[HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md]
(HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md).
Relabel such that
\(n_X\cdot t>0>n_Y\cdot t\).

Then **the central transverse displacement d
cannot vanish**, and the normal/contact geometry
belongs to exactly one of two mirror-image
necessary patterns:

* **d>0:**
  \[
  \boxed{n_Y=-t,\quad
  n_X\cdot n<0<n_X\cdot t.}
  \]
  Y contacts C along its **bottom transverse
  side** \(t\cdot z=d-1/2\in(-1/2,0)\),
  while X's positive contact is the
  **true top-left C corner**
  \[
  z_X=(b-1)n+(d+1/2)t
  \quad\text{with }d+1/2>1/2.
  \]
* **d<0:**
  \[
  \boxed{n_X=+t,\quad
  n_Y\cdot n<0,\quad n_Y\cdot t<0.}
  \]
  X contacts C along its **top transverse
  side** \(t\cdot z=d+1/2\in(0,1/2)\),
  while Y's positive contact is the
  **true bottom-left C corner**
  \[
  z_Y=(b-1)n+(d-1/2)t
  \quad\text{with }d-1/2<-1/2.
  \]

In particular **both-oblique left-corner
SS triangles, both pure transverse-side
SS triangles, and the d=0 centered SS
triangle are all impossible** under these
exact hypotheses. At least one of X/Y
has a true C **side-normal** contact
and the other a true C **opposite corner**
contact.

This is **not** a global exclusion of both
mirror-image patterns, and does not
prove \(R_8\ge\widehat R\).

## 1. A strict near-origin C-corner exclusion from the independently certified radius bound

Set \(k=1-b=2-\rho\). The already certified
\(R^2>19/5\) gives
\[
\rho^2=R^2-1/4>71/20>(47/25)^2,
\qquad
\boxed{0<k<3/25}.
\]
The k>0 bound uses R<2.

Let Q be **any genuine unit square of any
orientation containing a contact point**
\[
z=-k n+\tau t,\qquad |\tau|\le1/2.
\]
Every true vertex v of Q has \(|v-z|\le\sqrt2\),
because the **diameter of a unit square is
\(\sqrt2\)**. Therefore
\[
\begin{aligned}
|v|
&\le|z|+\sqrt2\\
&<\sqrt{(3/25)^2+1/4}+\sqrt2\\
&<13/25+71/50
=97/50\\
&<\sqrt{19/5}<R.                         \tag{1}
\end{aligned}
\]
Every displayed rational radical comparison is
strict and checked by squaring:
\[
(13/25)^2-((3/25)^2+1/4)=3/500>0,
\]
\[
(71/50)^2>2,\qquad
19/5-(97/50)^2=91/2500>0.
\]
Thus **Q is strictly circle-free** if it
even contains one contact point at such a
near-origin central opposite corner.

Both positive triangle squares X and Y
must have **strictly positive physical
circle-vertex multipliers** by
HUMAN_POSITIVE_TRIANGLE_FORCES_CIRCLE_WEIGHTS.md.
Consequently **neither** can contact
C at a left corner \(z=-k n+\tau t\)
with \(|\tau|\le1/2\).

Notice this exclusion does **not**
require Q to be wholly beyond
a particular signed C cap. It uses
only that the contact point belongs
to the true unit square, its diameter,
and the coarse globally certified radius.

## 2. True Z-interior overlap forbids a near-contact C right corner

The radial side leaf Z occupies the
closed slab
\[
b\le n\cdot w\le b+1,\qquad
-1/2\le t\cdot w\le1/2.
\]
Its **open interior** occupies strict
inequalities in both coordinates.

Consider any different unit square Q
with a genuine positive C-contact
normal m satisfying
\[
m\cdot n>0,\quad m\cdot t\ne0.
\]
Because m has both nonzero components
in the true C side frame, the C support
face exposed by m is the **single
right-hand C corner**
\[
z=bn+\tau t,\quad
\tau=d+\tfrac12\operatorname{sgn}(m\cdot t).
\]
Suppose \(|\tau|<1/2\).
Since m is **not** a C side normal,
the true separating-axis theorem
forces m to be an **actual Q side normal**.
The point z belongs to Q's inward
m-support side. Moving a sufficiently
small distance into Q along m, and
if z is a support-side endpoint adding
a still smaller inward tangential
displacement, gives genuine **interior
points of Q** with
\[
n\cdot w>b,\qquad |t\cdot w|<1/2.
\]
Those points are also in the **interior
of Z**, because n·w can be chosen
below b+1. This contradicts the
disjoint open square interiors.

Thus **no positively C-contacting square**
can have \(m\cdot n>0,\ m\cdot t\ne0\)
at a C right corner whose true radial
transverse coordinate has \(|\tau|<1/2\).
The special m=+n case was already
ruled out by the high-cap two-square
capacity theorem because Z occupies
the high +n whole cap.

## 3. Force balance leaves only a pure transverse contact near the radial line

The earlier exact SS force-balance theorem
requires strictly opposite transverse
positive C contact normals:
\[
n_X\cdot t>0,\qquad n_Y\cdot t<0.
\]
By true C support geometry their
contact transverse coordinates are
\[
\tau_X=d+1/2>0,\qquad
\tau_Y=d-1/2<0.
\]

If d>0, the **lower** Y contact obeys
\(-1/2<\tau_Y<0\).
It cannot have \(n_Y\cdot n<0\),
because then it would occur at the
left C corner \((-k,\tau_Y)\),
which is circle-free by section 1,
contradicting \(m_Y>0\).
It cannot have \(n_Y\cdot n>0\),
by the true Z-interior overlap
obstruction in section 2.
Therefore \(n_Y\cdot n=0\).
Since n_Y is a **unit** normal
and \(n_Y\cdot t<0\), it is exactly
\[
n_Y=-t.
\]
Now the n component of C force
balance reads
\[
\lambda_Z+\lambda_X(n_X\cdot n)=0,
\]
so \(n_X\cdot n<0\).
Combined with \(n_X\cdot t>0\),
the exposed C face is precisely
the **top-left C corner**
\((b-1,d+1/2)\).
This proves the d>0 mode.

If d<0, the upper X contact has
\(0<\tau_X<1/2\), and the same two
obstructions force \(n_X\cdot n=0\),
hence \(n_X=+t\). The other Y normal
has negative n component from C force
balance and negative t component by
SS transverse normal polarization.
It therefore exposes the true
bottom-left C corner. This proves
the reflected mode.

If d=0, **both** positive C triangle
contact points have \(|\tau|=1/2\).
The n component of central positive
force balance
\[
\lambda_Z+\lambda_X(n_X\cdot n)
+\lambda_Y(n_Y\cdot n)=0
\]
forces at least one of the two n
components to be strictly negative.
That positive contact therefore
occurs at a *left C corner*
\((-k,\pm1/2)\). Section 1 makes
its entire true unit square
strictly circle-free, contradicting
its positive circle multiplier.
Thus d=0 is impossible.

The alternatives d>0 and d<0 are
complete and mutually exclusive.
This proves the theorem. QED.

## 4. Certification dependency and remaining problem

The new **geometric implication** is
a written finite hand proof, with
arbitrary true square orientations
and genuine C side/contact points.
Its stronger near-origin corner
radius estimate uses the previously
recorded **full-domain exact
computer-certified** inequality
\(R_8^2>19/5\) from GLOBAL_LOWER_BOUND.md.
The fully hand-derived lower bound
\(R_8>\sqrt2+1/2\) **alone** does
not supply the simple diameter
reserve (1). A future completely
human-only sharp proof would need
an analytical substitute or a
separate exact formal verification
of the marker certificate.

This theorem does **not** eliminate
the remaining **two reflected
side-plus-corner SS triangle**
cases; they still require true
X--Y pair contact geometry,
positive disk-circle forces and
the four full spectator squares.

CS/SD bridge interfaces remain open
with mandatory actual spectator bracing.
The full outer-contact-ring equality
case A is explicitly preserved.
The unrestricted sharp \(R_8\ge\widehat R\)
and Lean 4 formalization remain OPEN.
