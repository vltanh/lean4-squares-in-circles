# A diagonally stressed central square needs two tangentially opposing zero-stress contacts

**2026-10-12. Exact full-orientation structural hand theorem.**
This is a *strict, global contact-graph pruning* in the B2 root,
not a cap-offset estimate. It strengthens
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md)
and applies to every minimum-radius eight-square packing chosen
with **the fewest actual square-square contacts**.

## Theorem (two-sided tangential bracing)

Consider an attained least-radius packing of eight genuine
unit squares in \(D_R\), with all square interiors disjoint,
and choose **among all radius minimizers** one having
the fewest actual contacting pairs. Suppose its central
square C contains the disk origin in its open interior
and a normalized physical stress has **exactly two
positive-stress C-neighbor labels**, A and B.

Let the two equal/opposite positive resultant C-contact
forces use the **diagonal** normal
\[
n=\frac{e_C+f_C}{\sqrt2}
\quad\text{or}\quad
n=\frac{e_C-f_C}{\sqrt2},
\]
up to signs, where \(e_C,f_C\) are C's unit side frame.
Let \(t=Jn\) be the unit tangent perpendicular to n.

For each **additional actual C-contact neighbor** T
(other than A,B), choose **any one genuine contact
separating normal** \(m_T\) directed *outward from C toward T*,
i.e. a signed side normal of C or T with a supporting
equality at the common contact.

Then **every such choice of normals must include**
\[
\boxed{
\exists T_+,T_-\ \text{distinct additional C contacts}:
\quad m_{T_+}\cdot t>0,\quad
m_{T_-}\cdot t<0.}                               \tag{1}
\]

Consequently:

1. C has at least **four distinct actual square-contact neighbors**;
2. at least **two** of those actual neighbors are
   *positive-stress-weight-zero C pairs*;
3. an isolated pair of opposite-corner stressed
   contacts, or that pair plus only one extra
   actual C contact, **cannot** occur in a
   contact-minimal radius minimizer.

The true equality-bearing seven-outer contact ring is not
excluded: the result is conditional on C having **exactly
two positive stress neighbors** in **diagonal** mode.

## Proof: rotate away both diagonal contacts and shear away any one-sided braces

### 1. The central square has strict circle clearance

Because zero lies in the open interior of a unit
square C, every point of C has norm strictly less
than its diameter \(\sqrt2\) measured from zero
(the vertex bound is strict, by compactness).
The established eight-square radius lower bound
gives \(R>\sqrt2+1/2>\sqrt2\).
Thus C lies **strictly inside** the containing
disk. Any sufficiently small translation or
rotation of C continues to fit in the same
closed disk.

### 2. A small rotation opens the two opposite diagonal contacts

The prior
[HUMAN_TWO_CENTRAL_FORCE_AXES.md](HUMAN_TWO_CENTRAL_FORCE_AXES.md)
and true force/torque equilibrium put the
A/B contact points at the two **opposite
vertices of C**, with outward normals ±n.

For any centered square with side frame e,f,
the support half-width along a unit m is
\[
H_C(m)=\frac12\big(|m\cdot e|+|m\cdot f|\big).
\]
Let \(C_\theta\) be C rotated through an angle
\(\theta\) *about its own center*,
keeping the center fixed for now.
For \(0<|\theta|<\pi/4\), because n is a
square-diagonal normal,
\[
\boxed{H_{C_\theta}(\pm n)
       =\frac{\cos\theta}{\sqrt2}
       <\frac1{\sqrt2}
       =H_C(\pm n).}                             \tag{2}
\]
The originally tight *actual* C/A and C/B
supporting-line gaps along ±n therefore
become **strictly positive** for every
small nonzero θ. The centers of A,B and
their frames remain fixed, and no tangent
translation of C changes these two
gaps because n·t=0.

### 3. Every other contact normal has a uniformly controlled response

Choose an actual contact normal \(m_T\) for
each additional contacting square T. Let
\[
g_T(\theta,s)=m_T\cdot(p_T-p_C-s t)
    -H_{C_\theta}(m_T)-H_T(m_T),
\]
where \(s\) is a signed translation of C
along the fixed unit tangent t.
Because m_T is a genuine contact support
normal at the original packing,
\[
g_T(0,0)=0.
\]

For all m and all θ the elementary
rotation estimate for unit vectors gives
\[
\left|H_{C_\theta}(m)-H_C(m)\right|
\le|\theta|.
\]
Indeed each of the two rotated side
unit vectors moves by Euclidean norm
at most |θ|, and the two absolute
support projections carry coefficients 1/2.
Therefore
\[
\boxed{g_T(\theta,s)
       \ge -s(m_T\cdot t)-|\theta|.}            \tag{3}
\]
If \(m_T\cdot t=0\), then
\(m_T=\pm n\), and (2) gives the
stronger *exact* strict support gap
\[
g_T(\theta,s)=\frac{1-\cos\theta}{\sqrt2}>0
\]
for every s (since s t is perpendicular to n).

### 4. Lack of braces on one tangent side allows all contacts to disappear

Suppose the assertion (1) fails for some
choice of one genuine separating normal
at each additional C contact. Then the
**nonzero** real numbers
\(m_T\cdot t\) are all of one sign
(or no such nonzero values exist).

If they are all positive, choose
\[
s=-K|\theta|,
\]
with a fixed finite K sufficiently large
that \(K(m_T\cdot t)>1\) for **every**
one of the finitely many positive
projections. Equation (3) makes **all
these contact gaps strictly positive**.

If they are all negative, choose
\(s=+K|\theta|\) with an analogous K.
If there are no nonzero projections,
take s=0.

Every zero-projection additional contact
opens automatically by the exact diagonal
formula (2), and the two original
positive-stress A/B contacts open by (2)
in **all three choices** of s.

Thus, for every sufficiently small
nonzero θ, **every previous actual C
contact is strictly separated from C**
along one genuine supporting direction.
An arbitrarily small motion also preserves
the **strictly positive distances of all
original C noncontact pairs**, and preserves
the strict disk slack of C. All other
squares remain fixed, so their contacts
and nonoverlap relations are unchanged.

We have thereby constructed a new
eight-square packing in the same disk
of radius R, with **strictly fewer
actual square-square contacting pairs**.
Because R was already the least
possible radius, the new packing is
another radius minimizer. This
contradicts the choice of the original
minimizer as having the *fewest*
actual contacts.

Therefore every selection of genuine
additional-contact normals must have
at least one positive and one negative
tangential projection. That requires
at least **two distinct additional
actual C neighbors**, which cannot
be positive-stress neighbors because
C has exactly A and B with positive
weights. The theorem follows. QED.

## Consequence: a finite, genuine B2 structural mode split

The **central positive degree-two**
minimizer root now splits into exactly:

* **Side-stressed mode:** positive normals
  along C's own side-frame axes, with the
  same central tangential contact coordinate
  at both opposite faces. The actual C
  degree may be 2 or more.
* **Diagonal-stressed braced mode:**
  positive contacts at **opposite C
  vertices**, **at least four actual C
  neighbors**, and at least two additional
  zero-positive-stress C contact normals
  with **opposing projections along the
  diagonal tangent**.

In particular a purported pure
two-spoke **diagonal C stress core with
zero or one extra C contact is impossible**,
not just numerically disfavored. The
corner-stressed mode is not ruled out
when it has the necessary two-sided
additional bracing.

The same reasoning is a structural
rigidity principle for any strictly
circle-free unit square in a
*contact-minimal* radius minimizer,
whenever it has exactly two positive
opposite-diagonal contacts and no
other positive neighbor. It must not
be transferred to a merely
contact-*maximal* representative, or
to C positive degree three or more,
without re-proving its hypotheses.

The sharp unrestricted bound
\(R_8\ge\widehat R\), equality
classification and Lean 4 handoff
remain OPEN.
