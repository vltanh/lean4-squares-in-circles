# Opposite central-side neighbors are separated by more than ninety degrees

## Theorem: an arbitrary-frame three-square angular obstruction

Let unit squares C,A,B have pairwise disjoint open interiors in
a disk centered at zero with

    R^2 <= 98/25.

Suppose C contains zero in its open interior, and that A and B
are separated from C on **opposite sides of the same side-normal
direction n of C**. Explicitly, with centered support h_S,

    n dot(p_A-p_C) >= h_A(n)+h_C(n),
    n dot(p_C-p_B) >= h_C(n)+h_B(n).                 (1)

Then their centers have **strictly negative dot product**:

    p_A dot p_B < 0.                                   (2)

Thus the smaller angle between their two nonzero center rays is
**strictly greater than pi/2**. Neither A nor B is assumed
axis-aligned, and they need not touch C. The separator axes (1)
are genuine whole-square hypotheses, not assignments based
only on center location.

This strengthens HUMAN_OPPOSITE_CENTRAL_ANGLE.md, whose
general-support estimate gave a gap just below pi/2,
in the important branch where n is a central **side**
normal. The new ingredient is the sharp arbitrary-frame
one-square cap envelope of HUMAN_ONE_SQUARE_CAP_ENVELOPE.md.

## 1. Signed coordinates and the global center bound

Rotate coordinates to n=(1,0), write p_C=(t,u),
p_A=(a,v), p_B=(b,w). Because C is an open central square,
its signed side coordinate satisfies

    -1/2<t<1/2.                                       (3)

The two support inequalities and the fact that the
minimum unit-square half-width in any direction is
1/2 give

    a >= t+1>0,       b <=t-1<0.                    (4)

Every packed unit square center p satisfies

    |p|^2+|p|+1/2<=R^2<=98/25,

by the exact farthest-vertex formula.
Consequently

    |p|^2<101/50.                                      (5)

Indeed, if |p|^2>=101/50 then
|p|>7/5, since 101/50>49/25, and
the left side in the preceding inequality would
strictly exceed

    101/50+7/5+1/2 = 98/25,

a contradiction.

## 2. If the central side is offset at least 1/10

Assume |t|>=1/10. Equation (4) gives

    a^2+b^2 >=(1+t)^2+(1-t)^2
             =2+2t^2 >=101/50.                    (6)

Put M^2=101/50. By (5), a^2+v^2<M^2 and
b^2+w^2<M^2. Hence

    |v*w|<sqrt((M^2-a^2)*(M^2-b^2))
          < |a*b|,                                 (7)

where the last strict comparison follows by
squaring nonnegative quantities and using

    a^2+b^2 >=M^2:

    a^2*b^2-(M^2-a^2)*(M^2-b^2)
       =M^2*(a^2+b^2-M^2)>=0.

The first strict inequality in (7) handles the
boundary case a^2+b^2=M^2 as well.
Since a>0>b,

    p_A dot p_B = a*b+v*w <0.                     (8)

This proves the theorem for |t|>=1/10 without
using any orientation information about A or B.

## 3. If the central side is nearly centered

Now assume |t|<1/10. The two supporting lines of C
have signed x coordinates

    h_plus=1/2+t>2/5,
    h_minus=1/2-t>2/5.

The entire square A lies in {x>=h_plus}
and the entire square B lies in {x<=-h_minus},
by (1). Apply the orientation-free one-square
cap theorem HUMAN_ONE_SQUARE_CAP_ENVELOPE.md
to A and the horizontally reflected B.
It yields

    (h_plus+1)^2+(|v|+1/2)^2<=R^2,
    (h_minus+1)^2+(|w|+1/2)^2<=R^2.                (9)

Since both h thresholds exceed 2/5 and
R^2<=98/25, each transverse coordinate satisfies

    |v|,|w| <= sqrt(98/25-(7/5)^2)-1/2
             = sqrt(49/25)-1/2
             =9/10.                                  (10)

Equation (4) also gives, using a>0>b,

    a*b <=(t+1)*(t-1)=t^2-1<-99/100.             (11)

Therefore

    p_A dot p_B=a*b+v*w
        <-99/100+81/100=-9/50<0.                 (12)

This proves the near-centered side case,
and the two cases exhaust (3). QED.

## 4. A direct contact-cycle consequence at the sharp search radius

Suppose an eight-square packing at squared radius at most
98/25 contains a full actual-contact cycle on the seven
squares whose center norms are at least one. The private-ray
theorem HUMAN_OUTER_CENTER_VISIBILITY.md orders them
circularly and says that its edges connect precisely
consecutive outer center directions.

If two distinct cycle squares A,B lie beyond opposite
side-normal separators of the central square C, the
present theorem gives center-angle gap >pi/2.
But any two **touching outer squares** have
center-angle gap <=pi/2: a common contact point
lies within each square's radius-1/sqrt(2)
circumdisk, so their center distance is at most
sqrt(2); if both center norms are >=1, the cosine
law forces their angular separation <=pi/2.
This is also HUMAN_CONTACT_ANGLE_UPPER.md.

Thus A and B **cannot be adjacent on that full
outer contact cycle**. Each of the two circular arcs
from A to B contains at least one other outer square.

In particular, for the important branch where C
has actual degree exactly two in a minimum-contact
radius minimizer, its two contact normals are
opposite **central side normals**, by
HUMAN_CYCLE_ANALYSIS.md section 8. If both of its
neighbors belong to the seven-outer actual-contact
cycle, they must be nonconsecutive on it. The sharp
candidate realizes this pattern with a third square
T between the two central neighbors B and D.

This is a rigorous structural restriction, not the
five-corner chain. Central degree >=3, corner-owned
separators and alternative global contact patterns
still require a sharp radius argument. No conclusion
R8>=Rhat is claimed here.
