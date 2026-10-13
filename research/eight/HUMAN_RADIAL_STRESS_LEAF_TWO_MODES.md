# Radial positive-stress leaves have only two exact square-frame modes

**Structural research, 2026-10-13.** This is a full-orientation,
force-and-vertex theorem. It applies to a positive-stress **leaf
edge attached to the origin-containing square**, even if its outer
endpoint has other **zero-weight actual contacts**.

It does **not** assert that the central and leaf square frames are
always parallel. A central corner contact can have a radial direction
not aligned with either central side or central diagonal.

## Theorem (side or diagonal leaf, no third mode)

Let C and Z be distinct interior-disjoint genuine unit squares
contained in the disk \(D_R\), with
\[
\sqrt2+1/2<R<2.
\]
Suppose the disk origin is in the open interior of C, Z has
**exactly one positively stressed square-contact neighbor**, C,
and a valid physical stress has positive C--Z resultant force
\(\lambda n\) **on Z**, \(\lambda>0,\ |n|=1\), applied at
an actual combined contact point \(z\in C\cap Z\).

Suppose C--Z is a **positive-stress bridge**, so that its
combined contact point is radial by the physical moment theorem:
\[
z=b n,\qquad b>0.
\]
(The sign is outward from C to Z; b is the positive C support
distance along n.)

The physical force equation at Z is
\[
\lambda n=2\sum_{v\in \mathrm{Vert}(Z)\cap\partial D_R}
   \mu_v v,\qquad \mu_v\ge0,\qquad \sum\mu_v>0.
\tag{F}
\]

Then **exactly one** of the following geometric modes occurs:

**S — radial side mode.** With
\(\rho=\sqrt{R^2-\tfrac14}\), we have
\[
\boxed{b=\rho-1,\quad
p_Z=(\rho-\tfrac12)n,\quad
n\text{ is an actual side normal of }Z.}
\]
The contact \(z=b n\) is the **midpoint of Z's inner side**.
The entire opposite outer side has endpoints
\[
v_\pm=\rho n\pm\tfrac12 Jn,
\]
**both on the circle with equal positive multipliers**:
\[
\mu_+=\mu_->0.
\]
The contact force magnitude is
\(\lambda=4\mu_+\rho\).

**D — radial diagonal mode.** We have
\[
\boxed{b=R-\sqrt2,\quad
p_Z=(R-\tfrac1{\sqrt2})n,\quad
n\text{ is an actual diagonal direction of }Z.}
\]
The contact point \(z=b n\) is **Z's inward vertex** and
the opposite vertex
\[
v=R n
\]
is the **unique** disk-circle vertex of Z. It has
positive multiplier \(\mu>0\), and
\(\lambda=2\mu R\).

The classification is **about Z's true frame** and uses its
physical circle multipliers; it does not require Z's
*actual* square-contact degree to equal one.

## Proof

**The contact line and active vertices.**
Since C contains zero in its open interior, its outward
support is strictly positive. The radial bridge contact
is \(z=b n\) with \(b>0\), and z realizes the **minimum**
n-support of Z: every \(w\in Z\) obeys \(n\cdot w\ge b\).

The positive resultant \(\lambda n\) and equation (F)
imply \(\sum\mu_v>0\). A circle-contact vertex of a
unit square must maximize its squared vertex norm.
Writing the true frame as e,f, the four vertex squared
norms are
\[
|p_Z|^2+\tfrac12
 +(\pm p_Z\cdot e)\ +(\pm p_Z\cdot f).
\]
Because Z is exterior to C and zero is in the open
interior of C, \(p_Z\ne0\). Hence there are at most
**two** maximally distant square vertices; if there
are two, they are adjacent endpoints of one true side.

**Case 1: exactly one circle vertex has positive weight.**
Let that vertex be v. Equation (F) forces \(v=R n\)
and \(\lambda=2\mu_vR\).
Because all of Z is in the closed radius-R disk,
every \(w\in Z\) has \(n\cdot w\le|w|\le R\).
Equality requires \(w=Rn=v\). Therefore the entire
maximal n-support face of Z is the **single vertex v**,
and its minimal support face is also a single vertex,
opposite v. Thus z is that opposite true vertex.
Since \(v-z=(R-b)n\) joins two opposite vertices of
one unit square, it has length \(\sqrt2\)
and points along a true diagonal. Therefore
\(R-b=\sqrt2\), \(n\) is a diagonal direction and
\(p_Z=(v+z)/2=(R-1/\sqrt2)n\).
This is mode D.

Note that if a second vertex happened also to lie on
the containing circle with **zero** multiplier, it
would lie on the same outer side of Z as v. In that
situation, n must still be the actual diagonal
by the preceding argument, and a diagonal n gives
a *unique* farthest vertex for \(p_Z\ne0\).
Hence there is indeed only one circle vertex in mode D.

**Case 2: both vertices of one circle side carry weight.**
Let the two adjacent equal-radius vertices be
\[
v_\pm=\rho d\pm\tfrac12 t,\quad
\rho=\sqrt{R^2-\tfrac14}>1,\quad |d|=|t|=1,\ d\perp t.
\]
Their midpoint is radial by equality of their norms,
and the genuine square is
\[
Z=\{a d+b' t:
      \rho-1\le a\le\rho,\ -\tfrac12\le b'\le\tfrac12\},
\]
with center \(p_Z=(\rho-\tfrac12)d\).
Here d points outward, because the square is contained
in \(D_R\) and \(\rho>1\).

Its positive circle reaction barycenter is
\[
w=\frac{\mu_+ v_++\mu_- v_-}{\mu_++\mu_-}
 =\rho d+\zeta t,\qquad -\tfrac12\le\zeta\le\tfrac12.
\]
By (F), \(n\parallel w\) with positive scalar, so
\(n\cdot d>0\) and \(n\cdot t\) has the same sign as
\(\zeta\).

If \(\zeta\ne0\), the **unique** minimizer of
n-projection on Z is the inner corner
\[
z_*=(\rho-1)d-\frac12\operatorname{sgn}(\zeta)t.
\]
Its t component has sign **opposite** to
\(n\cdot t\). But the radial contact point
\(z=b n\), \(b>0\), must have its t component
of the **same** sign as \(n\cdot t\).
This is a contradiction. Therefore \(\zeta=0\).

It follows that \(n=d\), \(\mu_+=\mu_->0\),
and Z's **minimum n-support face** is its inner side
\(n\cdot w=\rho-1\). The radial contact on that
face is its midpoint \(z=(\rho-1)n\);
hence \(b=\rho-1\), proving mode S.
Equation (F) gives
\(\lambda=2\mu(v_++v_-)\cdot n=4\mu\rho\).
The two modes exhaust the true maximal-circle-vertex
possibilities. QED.

## Global consequences for the minimal B3 branching core

[HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md](HUMAN_B3_THREE_OUTER_TRIANGLE_LEAF_NORMAL_FORM.md)
proves that the smallest k=7 central-branching
positive stress component is the true contact
triangle \(C-X-Y-C\) plus one **positive radial
stress bridge** \(C-Z\). Z has exactly one
positively stressed neighbor and a positive circle
multiplier. Hence **the theorem applies verbatim**.

The formerly generic radial Z bridge is thus **one of
two exact leaf frame/vertex scaffolds**, without any
actual-leaf assumption:

* Side mode: \(b=\sqrt{R^2-1/4}-1\) and a true
  **two-circle-vertex side**, equal positive
  multipliers, inner-side midpoint radial contact.
  At \(R>\sqrt2+1/2\), \(b>4/5\).
  The existing high-cap capacity theorem consequently
  forbids any **second entire unit square** beyond
  this same C-owned radial supporting line.
* Diagonal mode: \(b=R-\sqrt2\), Z is a
  **corner-to-corner radial rod of length \(\sqrt2\)**,
  with its outward vertex on the circle and its
  inward vertex contacting C. The vertex multiplier
  is unique and positive.

The C-contact point is either a C side point or a
C vertex radial from the origin. A radial **C corner**
need not be a diagonal direction of C when C is
off-center; it is therefore *incorrect* to infer
C and Z have parallel frames from the bridge alone.

This reduces one continuous leaf-orientation variable
to **two explicit true-square geometries**.
The remaining B3 triangle, stress force polygon, four
other spectator units and the sharp radius bound are
still OPEN. The real equality-bearing outer ring is
unaffected. The theorem is not a Lean proof.
