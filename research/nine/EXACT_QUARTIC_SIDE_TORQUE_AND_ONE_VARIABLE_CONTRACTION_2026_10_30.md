# Exact quartic side torque and a sound one-variable contraction rule

Date: October 30, 2026. **Complete proposed algebraic theorem and interval
soundness lemma.** These statements do not claim that an original D02 row has
been excluded. They eliminate a radical from the *whole* original two-endpoint
side-torque equation, give at most four possible side directions for fixed
endpoint data, and justify the contractor used in a complete parameter cover.
No matrix determinant is inverted, and no singular endpoint is discarded.

## 1. Full original torque and the exact coordinates

Use the actual both-unique side domain of
`TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md`,
Sections 4--6, or any other caller supplying those literal two endpoint
torque equations. All original full forces, actual applications and physical
side means remain. N is the actual unloaded true-degree-two side transmitter.
For a generic caller the statement concerns the unchanged endpoint data;
it does not convert a higher-degree star to degree two.

In the fixed actual orthonormal frame write

    b=(-a0,-b0), c=(-cX,cY),
    wB=(-b0,a0), wC=(-cY,-cX),
    a0>b0>0, cY>cX>0,
    a0^2+b0^2=cX^2+cY^2=1,
    sigma=b.wC=c.wB=a0*cY+b0*cX>0,
    Atilde=Delta.c-sigma>0,
    Btilde=Delta.b-sigma>0,
    PB>0, PC>0.

The actual unit side direction has

    d=(-1,w)/h, h=sqrt(1+w^2)>0,
    (a0-b0)/(a0+b0)<w<(cY-cX)/(cY+cX).

The original vector return gives the exact genuine offsets

    xB=(d.c-Atilde)/sigma,
    xC=(d.b-Btilde)/sigma,
    0<xB,xC<1.

Put kB=d.(wB-b)>0 and kC=d.(wC-c)>0. The two *complete original* endpoint
torques, with the same positive original bridge magnitude gamma, are

    PB*xB=gamma*kB,
    PC*xC=gamma*kC.

Their exact elimination is

    E1=PB*xB*kC-PC*xC*kB=0.                            (1)

This theorem retains every separate original circle, radius, support and
containment equation. It only rewrites (1); it does not replace the full
physical system by (1).

## 2. One quadratic and one linear polynomial replace the repeated radicals

Define four linear polynomials in the **one** direction variable w:

    U(w)=cX+cY*w,
    V(w)=a0-b0*w,
    KB(w)=(b0-a0)+(a0+b0)*w,
    KC(w)=(cY-cX)-(cY+cX)*w.

Then

    d.c=U/h, d.b=V/h, kB=KB/h, kC=KC/h.

Consequently multiplication by the positive factor sigma*h^2 gives exactly

    sigma*h^2*E1 = Q(w)+h*L(w),                       (2)
    Q(w)=PB*U(w)*KC(w)-PC*V(w)*KB(w),
    L(w)=-PB*Atilde*KC(w)+PC*Btilde*KB(w).

Q has degree at most two; L has degree one. Every coefficient depends only
on the fixed endpoint data, not on w. In the D02 three-variable reduction,
the unique original hub root u depends only on the two roof angles, so it
also remains constant during this one-variable differentiation or contraction.

For direct coefficient computation, write Q=q0+q1*w+q2*w^2 and L=l0+l1*w:

    q0=PB*cX*(cY-cX)+PC*a0*(a0-b0),
    q1=PB*(cY^2-2*cX*cY-cX^2)
         -PC*(a0^2+2*a0*b0-b0^2),
    q2=-PB*cY*(cY+cX)+PC*b0*(a0+b0),
    l0=-PB*Atilde*(cY-cX)-PC*Btilde*(a0-b0)<0,
    l1= PB*Atilde*(cY+cX)+PC*Btilde*(a0+b0)>0.          (3)

These are polynomial identities after the fixed actual axes have been
specified. They can be checked by a single ring normalization, with no
trigonometric approximation or floating-point root calculation.

## 3. A quartic plus one sign is exactly equivalent, including L=0

Define

    P(w)=Q(w)^2-(1+w^2)*L(w)^2.

Since h>0 and h^2=1+w^2, for every real w one has the exact equivalence

    Q(w)+h*L(w)=0
      iff P(w)=0 and Q(w)*L(w)<=0.                    (4)

The forward direction follows by substitution. Conversely, if L(w)=0,
P(w)=0 gives Q(w)^2=0 and hence Q(w)=0. If L(w)>0, the product sign gives
Q(w)<=0; the squared identity and positive h give Q(w)=-h*L(w). If L(w)<0,
the product sign gives Q(w)>=0 and the same equality follows. Thus squaring
loses no information when the one product-sign condition is retained.

The exact coefficients of the polynomial P are

    p0=q0^2-l0^2,
    p1=2*(q0*q1-l0*l1),
    p2=q1^2+2*q0*q2-l0^2-l1^2,
    p3=2*(q1*q2-l0*l1),
    p4=q2^2-l1^2.                                     (5)

In particular P is **not identically zero** throughout the actual strict
both-unique domain. Suppose all five coefficients vanished. From p1=p3=0,
q0*q1=q1*q2=l0*l1, and l0*l1<0 by (3). Thus q1 is nonzero and q0=q2.
The equations p0=p4=0 then give q0^2=l0^2=l1^2. Substitution into p2=0
gives q1^2=0, a contradiction.

It follows that there are **at most four real w values** satisfying the
original two-endpoint torque for fixed original endpoint data. The physical
sector, the exact product sign in (4), the positive offsets, both actual
circle equations and all remaining physical constraints may remove further
roots. No assertion that any of the at most four candidates is realizable
is made. This is a uniform finite-direction reduction, not a new normal
selection or a force-free replacement of the original contact star.

## 4. Interval mean-value contraction in w is sound without a root oracle

Let I=[l,r] be a closed direction interval, let w0 be any chosen point of I,
and hold one actual endpoint-data tuple fixed. Define

    F(w)=Q(w)+sqrt(1+w^2)*L(w).

The function is continuously differentiable on all real w. Its exact derivative
is

    F'(w)=Q'(w)+[L'(w)*(1+w^2)+w*L(w)]/sqrt(1+w^2)
         =q1+2*q2*w
             +(l1+l0*w+2*l1*w^2)/sqrt(1+w^2).          (6)

Suppose exact interval arithmetic supplies

    F(w0) in J,
    F'(w) in D for every w in I,
    0 notin D.

If an actual root w* belongs to I, the mean value theorem gives a point xi
between w0 and w* with

    0=F(w*)=F(w0)+F'(xi)*(w*-w0).

Since F'(xi) is nonzero,

    w* in I intersect (w0-J/D).                         (7)

Here J/D is the full interval quotient, enclosing every numerator in J and
every denominator in D. This is not an approximate Newton step: (7) is a
necessary enclosure of **every** actual root in I, proved by the mean value
theorem. It requires no existence, uniqueness, convergence, derivative sign
outside I, matrix inverse or external root solver.

If the derivative enclosure D contains zero, this rule gives no contraction
and must not be used to exclude the cell. If the intersection in (7) is empty,
then the cell contains no root. If it is nonempty, replacing the w interval
by any certified superset of that intersection preserves every actual root.
Closed endpoints remain part of the enclosure.

### 4.1. One rule covers an entire two-angle box

For a parameter box of roof angles, each actual angle pair has its own
coefficients q0,q1,q2,l0,l1 and its own unique u. Suppose J encloses F(w0)
for **every** such original angle pair, and D encloses F'(w) for every such
pair and every w in I. Apply the preceding mean-value proof separately to
each fixed actual pair. The same interval (7) then contains all original
solutions in the whole three-variable box.

The numerical midpoint w0 is a rational proof parameter, not a physical
contact point. It does not need to satisfy any original force or circle
equation. All actual endpoint data and their entire uncertainty are retained
in the interval coefficient enclosures.

## 5. What a complete finite certificate must record

The contractor is a valid proof-tree node only when replay establishes its
premises and its output enclosure. In particular a checker must:

1. Recompute the angle-only coefficient intervals and the original sector,
   using the same sound unique-u enclosure and positive denominators.
2. Verify w0 belongs to the current closed w interval, enclose F(w0) and
   F'(I) using (2),(3),(6), and verify that the derivative interval excludes
   zero before dividing.
3. Check that the child's interval contains I intersect (w0-J/D); if the
   intersection is empty, record an actual contradiction leaf.
4. Keep both children of every ordinary split and retain the original full
   root box. A necessary-sector contraction must likewise record that every
   original solution lies in its new interval.
5. Terminate every surviving leaf in either a proved scalar contradiction
   or a complete physical capacity theorem for all nine squares. Unresolved
   boxes and a node limit never constitute a proof.

Exact quartic interval or Bernstein sign tests may be used alongside the
unsquared mean-value rule. Equation (4) specifies precisely which extra sign
must accompany quartic roots; no positive denominator or physical boundary
may be discarded when passing between the two forms.

The algebra and the contraction soundness are complete at their stated
scope. A finished global D02 parameter cover, compilation of its generic
checker, the original load-row union and independent-kernel replay remain
separate obligations.
