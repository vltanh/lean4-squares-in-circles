# Radial SS branching leaves force a transverse central two-side/corner scaffold

**Structural research, 2026-10-13.** This is a stronger
normal-form theorem for the **remaining** minimal B3
SS (C-side/Z-side radial leaf) positive-stress bridge
cases. It builds on the complete all-C-side
subcase exclusion in
[HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md]
(HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md).

No square frames are assumed parallel beyond the genuine
C/Z side-frame agreement. The theorem uses positive force
balance and *true C support faces*, not a cap-offset sweep.

## Theorem

Assume the k=7, no-outer-full-actual-ring
smallest branching positive core
\[
C-X-Y-C \quad\text{plus radial bridge }C-Z,
\]
with the actual positive C--Z bridge in the
**SS interface**: C and Z are parallel, its outward
normal is n and the radial contact point is
\(z_Z=b n\) on C's true +n side, with
\(b=\sqrt{R^2-1/4}-1>4/5\).

Let t=Jn and denote the actual positive
outward C--X and C--Y unit contact normals
by \(n_X,n_Y\), with strictly positive force
magnitudes \(\lambda_X,\lambda_Y\).

Then after swapping X,Y if necessary:

1. Their true contact normals have **opposite,
   strictly nonzero transverse components**:
   \[
   \boxed{n_X\cdot t>0>n_Y\cdot t.}              \tag{1}
   \]
   Neither triangle C contact normal is
   parallel to n.
2. Their true combined C contact points
   \(z_X,z_Y\in C\) lie on the **opposite
   transverse central sides**:
   \[
   \boxed{t\cdot z_X=t\cdot p_C+\tfrac12>0,\qquad
          t\cdot z_Y=t\cdot p_C-\tfrac12<0,}
   \tag{2}
   \]
   because \(|t\cdot p_C|<1/2\) (zero is in the
   open interior of C). Consequently
   \[
   (t\cdot z_X)-(t\cdot z_Y)=1
   \quad\text{and}\quad
   \min\{|t\cdot z_X|,|t\cdot z_Y|\}<1/2.
   \]
3. **At least one** of the positive triangle
   C contacts is at a **true C corner on
   the side opposite Z**:
   \[
   \boxed{\exists Q\in\{X,Y\}:
      n_Q\cdot n<0,\ n_Q\cdot t\ne0,\quad
      z_Q=p_C-\tfrac12n
              \pm\tfrac12t.}                  \tag{3}
   \]
   Thus the surviving SS triangle necessarily
   includes a genuine opposite C **corner**
   support contact. In particular there is
   no all-three-C-side-normal positive
   SS stress configuration at this radius.

These are whole-geometry support properties,
not a complete B3 case exclusion.

## Proof

Because the side-mode radial leaf Z occupies the
high whole cap
\[
Z\subseteq\{x:n\cdot x\ge b\},
\qquad b>4/5,
\]
the exact high-cap capacity theorem excludes
**any different square** wholly beyond this same
C +n support line. Thus neither X nor Y
can have outward C-contact normal **+n**.

At C, the positive contact force equilibrium reads
\[
\lambda_X n_X+\lambda_Y n_Y+\lambda_Z n=0,
\quad\lambda_Z>0.
\]
Taking the t component yields
\[
\lambda_X(n_X\cdot t)+
\lambda_Y(n_Y\cdot t)=0.                       \tag{4}
\]

Suppose one transverse component vanished.
The other must also vanish by (4), because
both \(\lambda_X,\lambda_Y\) are positive.
Then \(n_X,n_Y\in\{+n,-n\}\).
Neither can be +n by the high-cap exclusivity,
so both are -n. But the full all-C-side
SS configuration with both X,Y opposite -n
was **completely excluded** by
HUMAN_B3_SS_OPPOSITE_SIDE_EXCLUDED.md:
physical torque gives contact points straddling
the radial line, one within tangential distance
1/2, and the opposite-face rotated-square bound
then forces one positively circle-stressed
triangle square to be strictly circle-free.
Hence both t components in (4) are nonzero
and strictly opposite. Relabel to obtain (1).

For any genuine unit square C with side-frame
unit normals n and t, a normal \(m\) with
\(m\cdot t>0\) attains its maximum on C at
the **top transverse side** \(t\cdot x=
t\cdot p_C+1/2\). If \(m\cdot t<0\), it
attains its maximum at the bottom
transverse side. Therefore the two
true C-contact points have the
coordinates in (2).

The actual radial C--Z contact point bn lies
on C's +n side and has t coordinate zero.
Since zero is in C's open interior,
\(|t\cdot p_C|<1/2\).
So the two signed values in (2)
straddle zero, and their difference
is exactly 1.

Finally take the n component of the
positive force balance:
\[
\lambda_X(n_X\cdot n)+
\lambda_Y(n_Y\cdot n)=-\lambda_Z<0.
\]
At least one of \(n_X\cdot n,n_Y\cdot n\)
must therefore be **strictly negative**.
Its t component is nonzero by (1).
Such a normal exposes exactly the
**negative-n, signed-t C corner**,
with coordinates \(p_C-n/2\pm t/2\).
The actual positive pair-contact
point lies at this unique exposed
corner. This proves (3). QED.

## Remaining exact SS branch

The SS radial bridge now has two mutually
exclusive cases at the minimal B3 core:

* **All triangle C contacts side-normal:** fully
  eliminated by the opposite-face true-vertex
  and positive-circle-force obstruction.
* **At least one triangle C contact C-corner-owned:**
  necessary, with transverse opposite C-face signs
  and at least one *negative-n* central corner.
  Square frames X,Y and their genuine X--Y positive
  contact still need a sharp global inequality.

For CS or SD radial bridge mode, independent
zero-positive-stress spectator bracing is required
by the contact-minimal leaf theorem; the full
spectator arcs are classified in
[HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md]
(HUMAN_B3_COMPLETE_SPECTATOR_ARCS.md) **only when**
C has exactly its three positive actual neighbor
labels.

All of root A full outer ring,
the B2 m4/m5/m6 path roots,
larger B3 positive components,
low-k roots and the exterior X root
remain OPEN, as does the unrestricted
\(R_8\ge\widehat R\) theorem.
