# A C-corner radial bridge cannot have two collinear opposite triangle normals

**Structural research, 2026-10-13.** This is an exact
force/torque/circulation exclusion in the k=7 minimal
branching core. It applies to the genuine **CS** bridge
interface (C radial corner, Z radial side), without any
frame alignment of its X/Y triangle squares.

## Theorem

Suppose the normalized positive-stress component is
\[
C-X-Y-C\quad\text{plus positive radial bridge }C-Z,
\]
where zero lies in the open interior of the genuine unit
square C, the bridge force has positive magnitude
\(\lambda_Z>0\) and unit normal n directed outward from C
toward Z, and its actual combined radial contact point
is \(b n\), \(b>0\).

Assume n is **not** a side normal of C, so it exposes a
*single true C corner* (the CS interface, with Z a genuine
radial side-leaf square by SAT ownership).

Let the two other positive C-contact resultant normals
be \(n_X,n_Y\) with magnitudes \(\lambda_X,\lambda_Y>0\).
Then their transverse components are necessarily
**strictly nonzero and of opposite signs**:
\[
\boxed{(n_X\cdot Jn)(n_Y\cdot Jn)<0.}           \tag{1}
\]
In particular, the tempting case
\[
n_X=n_Y=-n
\]
is **fully impossible**, not merely numerically disfavored.

## Proof

Physical force equilibrium at the circle-free central
square gives
\[
\lambda_Z n+\lambda_X n_X+\lambda_Y n_Y=0.
\]
Dot with \(t=Jn\):
\[
\lambda_X(n_X\cdot t)+
\lambda_Y(n_Y\cdot t)=0.                        \tag{2}
\]
If one transverse component vanished, both would vanish
because the \(\lambda\)'s are positive. Both normals would
therefore belong to \(\{+n,-n\}\).

But +n is the radial bridge direction and exposes the
unique C corner \(v=b n\), occupied by the positive
C--Z contact. If X or Y also had outward C-normal +n,
its whole square would share that same C support point
\(v\) with Z. This is an actual triple-square contact at v
and need not alone contradict disjoint interiors; thus
we use the force equation instead.

Taking the n component, a sum of three nonzero positive
multiples of ±n can vanish only if at least one of
\(n_X,n_Y\) equals -n. Because each true C +n contact
would put an additional full square in the same
**high side cap** as the radial side leaf Z
(\(b=\sqrt{R^2-1/4}-1>4/5\)), the exact two-square
high-cap capacity theorem forbids +n on either
triangle contact. Hence
\[
n_X=n_Y=-n.
\]

Since n is not a C side normal, the \(-n\) support face
of C is a **unique opposite C corner**, say w.
The two actual combined positive contact points
of C--X and C--Y must both be exactly w.

At C, the bridge force acts at \(b n\), so contributes
zero moment about the disk origin. The other two
force vectors sum to a nonzero multiple of n
and act at the **same** point w. Central torque
balance therefore gives
\[
(\lambda_X+\lambda_Y)(w\times n)=0,
\]
so \(w\times n=0\): w also lies on the radial line.

Thus the **positive contact-moment contribution**
of each of the three C incident edges is zero:
C--Z is radial; C--X and C--Y both have normal
parallel to their radial contact point w.

The only other positive edge in the entire component
is X--Y. Signed contact-moment conservation at X
(or Y), because true circle-vertex forces are radial
about the origin, forces the X--Y edge moment also
to vanish. Every positive edge in the component
therefore has zero signed moment.

But the exact
[HUMAN_CONTACT_COMPONENTS.md](HUMAN_CONTACT_COMPONENTS.md)
nonradial-component theorem proves that **every**
nontrivial positive-stress component of an eight-square
radius minimizer in
\(\sqrt2+1/2<R<2\) has **nonzero contact-moment
circulation**. Contradiction.

Therefore neither transverse projection may vanish
in (2); since the positive coefficients sum them to
zero, their signs are strictly opposite. This proves
(1). QED.

## Important scope

The high-cap exclusion of a C +n contact is valid
in **CS mode** because Z is a radial side-leaf
square with b>4/5. It is **not** valid in the SD
corner-leaf interface where b=R-\sqrt2 is smaller.

Together with
[HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md](HUMAN_B3_SS_TRANSVERSE_CORNER_FORCING.md),
we now know that **both radial side-leaf interfaces
SS and CS** force the X/Y triangle positive C normals
to have *nonzero, opposite* components transverse
to the bridge. In SS this was deduced using
the stronger circle-free opposite-face exclusion;
in CS it follows from radial corner torque
and the nonzero moment-cycle theorem.

This does not eliminate every CS bridge with genuinely
transverse contact normals, the SD bridge, the larger B3
cores, or the sharp global eight-square bound.
