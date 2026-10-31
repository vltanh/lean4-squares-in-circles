# A boundary-contact moment has the sign of the actual circular traversal

Date: October 28, 2026. Author: hexagon.

**Status: complete force-free local theorem, frozen for full
independent review.** The result holds for arbitrary degrees,
selected contact owners and actual shared-side means. No force
equation or concurrence is a premise.

## 1. Complete physical statement

Let A,B be two actual contained unit squares with disjoint open
interiors, both physically touching the original circle of center O,
in the window

    79/40<=R<=sqrt(1105)/16.

Let p be any point in their actual common support face and n any
unit common supporting normal directed from A into B. Let c_A,c_B
be their actual centers. Then

    det(p-O,n) and det(c_A-O,c_B-O)
    are both nonzero and have the same sign.          (1)

Equivalently, the origin moment of the actual directed A-to-B
normal is positive precisely when the actual minor center traversal
from A to B is counterclockwise. The minor arc has length less than
72 degrees, so the orientation in this statement is unambiguous.

If A,B carry any nonzero nonnegative weights on their respective
physical circle corners, with full resultants F_A,F_B, then also

    sign det(p-O,n)=sign det(F_A,F_B).                (2)

Individual corner weights may vanish. The additional assertion
does not require translation or torque equilibrium at either body.
The other seven packing units, when present, remain arbitrary.

## 2. Physical angular and support bounds

The complete physical angular-order theorem gives, for this actual
touching pair, the minor center gap

    pi/5<gamma<2pi/5.                                (3)

The one-square calculation in Section 1 of
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md gives that every physical
circle corner is within pi/12 of its own center direction. The
same holds for every nonzero nonnegative circle resultant. This
one-square statement does not require that source's four-body
balance premise. Both physical radial masks and all weight endpoints
are included.

In particular the minor angular gap of any chosen circle corners
z_A,z_B is strictly less than

                   2pi/5+2(pi/12)=17pi/30.           (4)

This follows from the triangle inequality for angular distance on
the circle and does not presuppose either orientation.

Translate only the coordinate chart to O and rotate it so n=East.
Write the original application as p=(h,y). Then

    A subset {x<=h}, B subset {x>=h}.

Both actual units have width at least one in this normal direction.
Their containment gives

                       1-R<=h<=R-1.                 (5)

If y=0 and h>=0, choose a physical circle corner z of A. Its
x coordinate is at most h, so

    |z-p|^2=R^2-2h z_x+h^2
           >=R^2-h^2>=2R-1>2.

This contradicts the unit diameter. If h<=0 use a circle corner
of B instead. Thus y is nonzero, proving the nonzero contact
moment without a stress equation.

## 3. The upper application with nonnegative support

Assume first y>0 and h>=0. Every physical circle corner z_A of A
has positive y coordinate. Otherwise

    |z_A-p|^2
       =R^2+h^2+y^2-2h(z_A)_x-2y(z_A)_y
       >=R^2-h^2+y^2>=2R-1+y^2>2,

again contradicting the diameter. Choose its angular representative
theta_A in (0,pi). A circle corner z_B of B has x coordinate at
least h>=0, so choose theta_B in [-pi/2,pi/2]. Their actual
support ordering gives

    cos(theta_A)<=h/R<=cos(theta_B)
                              =cos(|theta_B|).

Cosine is decreasing on [0,pi]. Hence theta_A>=|theta_B| and

                         L=theta_A-theta_B>0.        (6)

The only possible equality in (6) would be a common physical circle
point, which contained units with disjoint interiors cannot share.
Indeed containment at a circle corner z makes both inward unit side
directions w satisfy z dot w<=-1/2, so a short inward radial segment
lies in the open square. Two units sharing z would overlap there.

The actual diameter also gives

    (z_A)_x>=h-sqrt(2)>=-sqrt(2).

Since R>=79/40>sqrt(8/3), this implies

    cos(theta_A)>=-sqrt(2)/R>-sqrt(3)/2,
    theta_A<5pi/6,
    L<5pi/6+pi/2=4pi/3.                            (7)

If L>=pi, its minor circular gap would be 2pi-L>2pi/3.
That contradicts (4), because 17pi/30<2pi/3. Therefore

                         0<L<pi,
                         L<17pi/30.                 (8)

Thus these two real circle corners are ordered clockwise from
A to B. To transfer this orientation to the centers without a
hidden lift assumption, choose their center angles alpha_A,alpha_B
within pi/12 of theta_A,theta_B. Equations (8) give

    -pi/6<alpha_A-alpha_B<11pi/15<pi.

If this difference were nonpositive, its absolute value would be
less than pi/6, contradicting the strict lower center gap pi/5 in
(3). Hence it is positive and less than pi. It follows that

    det(c_A,c_B)<0,             det(p,n)=-y<0.

Both determinants are strictly negative. This proves
(1) for y>0,h>=0. Every support-side endpoint and every original
normal-cone endpoint was included; no strict side ownership was used.

## 4. All support and application signs

For y>0,h<0, reflect the chart by x->-x and exchange A,B. The
new directed normal is again East, its support is -h>0, and its
application still has positive y. Section 3 applies. Reflection
and exchange each reverse the center determinant, so their combined
operation preserves it:

    det(reflect(c_B),reflect(c_A))=det(c_A,c_B).

The new application moment is still -y. Thus the original center
determinant and moment are both negative in this entire row too.

For y<0 reflect vertically without exchanging A,B. The normal
remains East, the application is above the horizontal axis, and
both determinants reverse sign. They are therefore both positive
in the original chart. The zero value y=0 was already excluded
in Section 2. These cases exhaust every actual common support line
and establish the full statement (1).

## 5. Full circle-resultant version and precise limitations

By (3), the directed minor center gap has absolute value strictly
between pi/5 and 2pi/5. Each nonzero nonnegative circle resultant
has angular deviation less than pi/12 from its own center.
Consequently the corresponding directed resultant gap has the same
orientation and absolute value strictly between

                         pi/30 and 17pi/30.

It lies strictly between zero and pi. Its determinant therefore
has the same sign as the center determinant. This proves (2),
including a single positive corner on a physical two-corner unit.

The theorem determines only a sign. It does not give proper
concurrence, place a concurrence point inside a body, replace a
full higher-degree star, fix a mean, or assert any force balance.
It may be used at a boundary pair of arbitrary actual degrees
precisely because the proof is physical and force-free.

The exact direct inputs are

| Source | SHA-256 | Scope |
| --- | --- | --- |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | 2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449 | Physical center gaps, touching-pair order, and impossibility of a shared circle point |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708 | Section 1 one-square corner and resultant angle only |

For the two additional radius comparisons used above,

    79/40-3/2=19/40>0,
    (79/40)^2-8/3=5923/4800>0.

The angular reserves are 2pi/3-17pi/30=pi/10 and
pi/5-pi/6=pi/30. All are strict over the complete stated window.
No sampled pose, circle-weight restriction, new normal selection,
force deletion, motion, Lean compilation, CI, remote mutation, or
shared metadata edit is used.
