# Independent full review of the H4 owned-end height and opposite-owner reduction

Date: October 28, 2026 UTC. Reviewer: shared_s continuation.

**Result: PASS of the entire frozen necessary-domain source,
including every HC sign and C feature, both full side intervals,
and the complete original H4 identity. No whole original gate
is closed by this review.**

Reviewed in full:

    INNER_PENTAGON_OWNED_END_RETURN_HEIGHT_AND_OPPOSITE_END_OWNER_REDUCTION.md
    SHA256 23bb6edea9c4988b64636070ebe53acca5ca6617ddf7f595054948fdb8453c4b

I also read and independently checked the complete new geometric input:

    PHYSICAL_SIDE_GAP_CLOSED_BY_TOUCHING_NEIGHBORS_EXCLUDES_UNIT.md
    SHA256 f209207b7aed6ae2bbf8c6fb92dc81d855721173c88060f08a00fb69fdf81492

The complete fixed-opposite-return input at bc1b08bc and the
general fixed-axis selector at d5e02f31 were read previously
in full; I independently reviewed the latter with its whole
literal H4 call. Their actual points, full D3 vectors and
external side intervals are preserved here.

## 1. Force-free side-gap input

I checked the complete convexity and area argument. The sides
of the actual S,T,Z triangle lie in H,B,C. Physical interior
disjointness therefore makes the open D interior avoid that
entire triangle boundary. A segment from its actual relative
base-interior point P to any interior D point starts strictly
inside the contact triangle. Connectedness, or direct segment
crossing, confines the whole D interior to the triangle's
interior. Closure then gives containment of the whole unit D.

Its area is one, but the actual B diameter bounds the
triangle height by sqrt(2), so the triangle area is at most
sqrt(2)/2<1. No selected contact, force, circle radius,
graph embedding or endpoint displacement enters this proof.

The two normal support inequalities indeed place every
physical BC point strictly above the H side, including
the permitted horizontal-axis endpoints when the stated
literal corner incidences hold.

For the H4 caller, the opposite strict-corner and four
owned-axis exclusions leave only Northwest and Southeast
HB. Northwest supplies precisely the two side endpoints
and the actual exterior D required by the force-free
theorem. Thus Southeast HB and the strict whole-B
height/width conclusions used in the target are justified.

## 2. Complete C feature cover

I rederived the coordinates of S-R in the actual C
frame (n,Jn):

    U=(qX-eta-gamma b)/N_C,
    V=-(qY_C+eta)/N_C.

The identities aX+bY_C=eta+gamma b and
aY_C-bX=-eta are exact consequences of the unchanged
D3 force table. S in C gives U>=0, while q<1 and
eta+gamma b>0 give U<1. The formula
qY_C+eta=eta[1+q(b-a)]+q gamma b^2 is strictly positive,
so V<0<ell_C+1.

These strict actual coordinate bounds force both own
components of the original minimum-C normal at S to
be nonnegative. Every possible sign is then covered.

For Y_C>=0, its n component is positive. If its Jn
component were also positive, S would be the actual
corner with both inward y components nonnegative,
putting all of C at y>=1. That contradicts the real
BC contact with max_B y<1. Thus the normal is n,
Y_C is strictly positive, and S lies on the same
actual C side as R. Both points are strict side
interior, so qX=eta+gamma b and |S-R|<1.

For Y_C<0, Jn has two positive world components.
Its normal coefficient is positive, fixing V=ell_C.
The positive n-component alternative is exactly the
free HC corner; its zero-component alternative is
exactly the perpendicular C-owned side, with its
whole original interior coordinate 0<U<1. No side
position or zero-component feature is omitted.

## 3. Whole E height for every sign and both HC types

At Y_E>0, the actual minimum-support span in the
downward direction is strictly below one, giving
min_E y>a>0. At Y_E=0 the full vertical span is at
most one and the same positive conclusion follows.

At Y_E<0, the original D3 formulas force b>a and
Y_C>gamma>0. The prior East-HC inequality Y_C<=0
therefore places this entire case in the Northeast
branch. The complete C cover just checked gives
q<2a from its real side chord and
q(a+b)-1=gamma b^2/X>0. Hence
a>1/(2(a+b))>=1/(2sqrt(2))>1/3.

The original E normal and strict side-interior
application retain a full tangent interval of
length one. Its downward span is strictly below
(X+|Y_E|)/sqrt(X^2+Y_E^2). I checked the exact
ratio comparison

    0<|Y_E|/X<(b-a)/(a+b)<1;

cross multiplication leaves the positive reserve
gamma a. The monotone span function therefore gives
the strict upper bound sqrt(2)b. Finally
(1+a)^2-2b^2=(3a-1)(a+1)>0, proving the whole E
lies above y=0. Every sign and original HC mean
is covered without an E2 equation.

## 4. Opposite-end ownership and full H4

The actual AB and AE contacts supply a point of A
with positive x and a point with positive y. If
the original HA point (0,0) were an A vertex with
Southwest minimum support, an inward axis with
positive x would have negative y, and a different
axis with positive y would have negative x. Their
dot product would be strictly negative, contrary
to orthogonality. The point is therefore an actual
A side-interior point and A owns HA.

The square formula

    A=[0,1]n_A+[-kappa,1-kappa]j_A, 0<kappa<1

retains the original physical side position. Its
two positive coordinate maxima are exactly
(1-kappa)v_A and kappa u_A, so the asserted
full-side extent identity is correct.

I independently rederived the entire H4 equation
and moment at (0,0). They give

    y=s-r+p gamma,
    U_A=x+r,
    V_A=r+q gamma.

All four actual forces and applications are
present. Neither C nor E nor the opposite A
is assigned an unloaded or two-force surrogate.

## 5. Literal scope and acceptance

Both original H4_D0 load rows retain the same
actual H4, unloaded D3 and their full remaining
stars. L124 admits the stated graph-preserving
reflection; L0124's loaded opposite end is never
made unloaded. The source remains radius-free
and does not normalize its H-side height to the
circle center.

These are necessary domains, not exclusions of
the two complete families. All original nine
units, physical masks, zero weights, circle and
full side intervals remain. No edit to either
reviewed mathematical source was requested.

This was a complete proof and scope review,
with no Lean compilation, CI, numerical pose,
angle mesh, bookkeeping edit or remote action.
