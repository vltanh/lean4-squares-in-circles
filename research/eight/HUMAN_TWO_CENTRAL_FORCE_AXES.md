# Two positive central forces have only four possible axes

**2026-10-12. Exact all-orientation, global stress structural theorem.**
Unlike the generic outer-center angular bounds, this **discretizes the
central square's positive-stress contact direction**, and is independent
of the numeric cap cutoffs. It is a strict strengthening of the
opposite-contact-normal result for the B2 root.

## Theorem

Let C be a genuine unit square of any position/orientation, with
orthonormal side frame \(e,f\) and center \(p_C\), in an attained
minimum-radius eight-square packing. Assume C lies strictly inside
the containing circle (in our problem this follows because
zero lies in C's open interior and \(R>\sqrt2\)).

Suppose a normalized physical stress has **exactly two distinct
positive-stress neighbor labels** A and B at C. Let their true
positive pair-contact resultant forces have equal magnitude
\(\lambda>0\) and opposite outward-from-C unit normals \(n,-n\);
write their aggregated actual contact points as \(z_A,z_B\in C\).
The opposite-force statement is the earlier two-force equilibrium
theorem in HUMAN_CONTACT_COMPONENTS.md.

Then the normal n **must lie on one of just four
unoriented central-frame axes**:
\[
\boxed{
n\parallel e,\quad n\parallel f,\quad
n\parallel(e+f),\quad n\parallel(e-f).
}                                                       \tag{1}
\]
Equivalently, there are eight possible **signed** central-frame
directions \(\pm e,\pm f,\pm(e+f)/\sqrt2,
\pm(e-f)/\sqrt2\).

Furthermore the actual C--A and C--B contact points obey
the precise geometric alternatives:

* **Side mode.** If \(n\parallel e\) (or f), the contact
  points lie on *opposite C side segments*, with **exactly
  equal transverse side-frame coordinates**. For \(n=e\),
  \[
  z_A=p_C+e/2+t f,\quad
  z_B=p_C-e/2+t f,\qquad -1/2\le t\le1/2.
  \]
  Thus \(z_A-z_B=e\), a straight central width-one
  force chord (not necessarily through the origin).
* **Diagonal mode.** If \(n\parallel(e\pm f)\), the two
  actual contacts are precisely the *opposite vertices*
  \[
  z_A=p_C+\frac{e\pm f}{2},\qquad
  z_B=p_C-\frac{e\pm f}{2}
  \]
  up to reversing the signed direction n.
  Their contact-to-contact chord is a
  **central square diagonal of length \(\sqrt2\)**.

There is **no continuously oblique third possibility**.
This is about the *positive physical contact forces*, not about
all actual contact normals or all central neighbors, which may
include contacts carrying zero stress.

## Proof

The two resultant forces on C are \(-\lambda n\)
at z_A and \(+\lambda n\) at z_B.
C has **no circle multipliers**, because it is
strictly inside the containing disk. Its torque
balance about the disk origin therefore reads
\[
-\lambda(z_A\times n)+\lambda(z_B\times n)=0,
\]
hence
\[
\boxed{(z_A-z_B)\times n=0.}                    \tag{2}
\]

The two actual contact points lie on C's opposite
support faces in directions n and -n. In C's own
frame, write \(a=n\cdot e,\ b=n\cdot f\).
There are two exhaustive geometric possibilities:

**(i) a and b are both nonzero.** The unique maximizer
of \(n\cdot z\) over the closed square C is the vertex
\(p_C+(\operatorname{sgn}a\,e+
\operatorname{sgn}b\,f)/2\); the unique minimizer is
the opposite vertex. Hence the *only possible*
aggregated contact points are these two true vertices,
and
\[
z_A-z_B=\operatorname{sgn}a\,e+
        \operatorname{sgn}b\,f.
\]
The torque condition (2) makes this vector parallel
to n. Therefore
\[
(a,b)=\pm(1/\sqrt2,1/\sqrt2)
\quad\text{or}\quad
(a,b)=\pm(1/\sqrt2,-1/\sqrt2).
\]
Thus n is a signed central diagonal normal,
and the diagonal contact-pair statement follows.

**(ii) a=0 or b=0.** Since n is unit,
n is a signed side-frame normal ±e or ±f.
For n=e, the two opposite C support faces
are the sides \(p_C\pm e/2+[-1/2,1/2]f\).
Write \(z_A=p_C+e/2+t_A f\) and
\(z_B=p_C-e/2+t_B f\).
Then \(z_A-z_B=e+(t_A-t_B)f\).
The torque condition (2), with n=e, forces
\(t_A=t_B=:t\), giving the stated side-mode
aligned transverse coordinate.
Other signed side directions follow by
symmetry.

Both cases exhaust the unit-circle normals n
and prove (1). QED.

## Significance and limitations

A computer search for global B2 contact patterns
can now branch over **only four relative
central-force axes**, not a free central
force angle: two central sides or two
central diagonals. This reduction is
exact even when A,B have arbitrary independent
frames and the central square has extra
zero-weight *actual* contacts.

It does **not** force central side mode:
the diagonal corner-force option remains
until additional actual-contact rigidity
is invoked. Nor does central positive
stress degree two imply the central square
has actual contact degree two. The next
[HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md](HUMAN_DIAGONAL_CENTRAL_TANGENTIAL_BRACING.md)
proves that diagonal positive mode in a
contact-minimal representative requires
at least two extra **zero-weight actual
central contacts with opposing tangential
contact normals**.

The exact five-corner candidate's legitimate
seven-outer actual contact-ring equality
branch is unaffected.
The unrestricted \(R_8\ge\widehat R\)
remains OPEN.
