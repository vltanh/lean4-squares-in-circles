# Sharp seven-square contact-cycle obstruction with independent rotations

**Theorem (seven whole squares; conditional directed-axis topology).**
Let seven interior-disjoint unit squares
`A,B,T,D,E,H,G` fit in a disk of radius R
centered at zero. Suppose **only A and E**
have sides parallel to one common orthonormal
frame (a,b); the other five squares may
have completely independent orientations.

Assume there exists an angle `0<=t<=pi/4`
and `e=cos(t)*a+sin(t)*b`,
`f=-sin(t)*a+cos(t)*b`,
for which the seven **directed full-square
separating projections** hold:

    b dot(p_B-p_A) >= h_B(b)+h_A(b),
    a dot(p_B-p_T) >= h_B(a)+h_T(a),
    a dot(p_T-p_D) >= h_T(a)+h_D(a),
    b dot(p_D-p_E) >= h_D(b)+h_E(b),

    e dot(p_A-p_G) >= h_A(e)+h_G(e),
    e dot(p_G-p_H) >= h_G(e)+h_H(e),
    f dot(p_E-p_H) >= h_E(f)+h_H(f).                (1)

Each h is a centered square support function,
and **each direction in (1) must actually
be justified by its stated separating
projection**. The existence of some
different separator for a pair does not
imply the desired inequality.

Then

    R >= R_hat,                                       (2)

where R_hat is the exact least five-corner
radius selected by HUMAN_FAMILY_CLOSURE.md.

This lower bound is **sharp already for
seven squares**: the seven exterior units
A,B,T,D,E,H,G of
ANALYTIC_SHARP_SEVEN_OUTER_CONSTRUCTION.md
attain radius exactly R_hat and satisfy
all seven separators.

## Hand proof of the lower bound

Add the second and third inequalities of
(1). Their sum gives

    a dot(p_B-p_D)
      >=h_B(a)+2*h_T(a)+h_D(a)
      >=h_B(a)+1+h_D(a),                           (3)

because every unit square has projected
half-width `h_T(a)>=1/2`, regardless
of its orientation.

The first and fourth inequalities
of (1) give precisely the two vertical
outer-end constraints of
HUMAN_TWO_ALIGNED_ENDS.md. The last
three inequalities of (1) give
precisely its oblique e,e,f constraints.

Thus (1), together with (3), meets
**all six explicit geometric hypotheses**
of that theorem with aligned ends
A,E and freely rotated middle/tilted
square frames. Its proven canonical
point construction produces five
genuine disk points satisfying the
sharp projected five-corner inequalities.
Their previously proved exact optimum
gives (2).

No central square, force stress,
contact graph minimality or shared
orientation of B,T,D,G,H has been
assumed or used. This completes
the seven-square conditional proof.

## Equality reconstructs all seven side frames

Suppose now R=R_hat. By
HUMAN_TWO_END_EQUALITY_RIGIDITY.md,
all five extracted disk witness points
must lie on the circle and all
five projected inequalities must be
equalities. Moreover B,D align with
A,E, while G,H align with e,f.
The five points and the centers
of A,B,D,E,H are uniquely reconstructed
from the stationary exact family,
up to rigid circle symmetries.

Equality of the middle span in (3)
also forces

    h_T(a)=1/2,

so T has the a,b frame. Equality of
each of the two nonnegative
separator residuals in (3) gives

    a dot(p_B-p_T)=1,
    a dot(p_T-p_D)=1.

In the exact family `p_B.x=U-1/2`,
`p_D.x=U-5/2`, hence T has
fixed horizontal center coordinate

    a dot p_T=U-3/2.                               (4)

Its other center coordinate remains
subject to the disk and pair nonoverlap
constraints and can slide.

Likewise G and H share the e,f
frame; equality of their e separator
gives

    p_G=p_H+e+eta*f,                              (5)

where eta is a free transverse
parameter within its allowed
containment and separation interval.

All seven frames are therefore
forced at equality, even though
**five of them were arbitrarily
rotated in the theorem's hypotheses**.
Equations (4)--(5) leave genuine
one-dimensional T and G slider freedoms;
the actual sharp construction provides
nontrivial intervals.

The theorem does not claim that all
permitted real slider values give
nonoverlapping seven-square packings:
each actual value must satisfy the
remaining disk and pair inequalities.
Nor does equality of projected
support lines automatically imply
the corresponding physical contact
faces intersect.

## Critical unrestricted gap

The exact sharp eight-square construction
admits a seven-outer **actual-contact
cycle**, so it would be incorrect to
exclude all such cycles below or at
R_hat. The theorem above identifies
one *complete seven-edge directed
separator pattern* for which the
sharp lower bound and its frame
equality conditions can be proved by
hand. An arbitrary seven-outer
contact ring has not been shown to
admit this pattern or two aligned
end squares. Other center populations
and central-path attachments also
remain.

Therefore this conditional seven-square
theorem does NOT establish
unrestricted `R8>=R_hat`.
