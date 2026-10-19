# A distant central side has one compulsory transverse lane

## Theorem (arbitrary unit-square frames)

Let unit squares be packed in a disk D_R centered
at zero, with

    q=R^2 <=9789/2500 <2257/576.

Fix an outward side of the unique central square
C at signed distance h from zero, where

    17/24 <= h <1.

Then:

1. At most **one** exterior whole square S can lie
   beyond that central supporting line.
2. If such an S exists and its center is p_S,
   and n is the outward side normal while m=Jn,
   then its transverse center coordinate satisfies

       |m dot p_S| <1/2.                               (1)

3. The line through zero in direction n
   (the perpendicular diameter of the central
   side) crosses the **open interior** of S.
4. S cannot also lie beyond either of C's
   two perpendicular central sides. Thus its
   12-status label is necessarily the
   **single-side** label of that distant side.

These assertions apply to every independent
orientation of S and require no actual circle
or square contact. Merely locating the center
beyond the central side is not sufficient;
the **whole square** must be in the cap.

## Hand proof

Rotate coordinates so the side normal n=(1,0),
its perpendicular m=(0,1), and S lies wholly
in the cap x>=h.

If two distinct unit squares lay in the
cap, the exact arbitrary-frame two-square
capacity theorem HUMAN_EXTENDED_TWO_SQUARE_CAP.md
would require

    q >=(h+1)^2+1
      >=(41/24)^2+1
       =2257/576 >9789/2500,                       (2)

a contradiction. This proves the capacity one.

For the transverse coordinate, invoke the sharp
orientation-free **single-square** disk cap envelope
HUMAN_ONE_SQUARE_CAP_ENVELOPE.md. Its hypotheses
h>=2/5 and q<=98/25 are met, and it gives

    (h+1)^2+(|p_S.y|+1/2)^2 <=q.

Using (2)'s numerical comparison without its
second-square premise yields

    (|p_S.y|+1/2)^2
       <=q-(h+1)^2
       < 2257/576-(41/24)^2
       =1.

The left square root is positive, so

    |p_S.y|+1/2<1,      |p_S.y|<1/2,                (3)

proving (1).

Every unit square, of any orientation, has vertical
projected half-width

    L/2=(|cos theta|+|sin theta|)/2 >=1/2.

Equation (3) places zero **strictly inside**
the open vertical projection interval of S,
which is exactly the set of ordinates achieved
by points of its open interior. Thus the line
y=0 intersects int(S). Since S is wholly
in x>=h>0, this intersection is on the
positive radial half-line from the disk
origin, giving assertion 3.

Finally, suppose S were also beyond a
perpendicular side of C, whose signed distance
h_perp is necessarily positive because C
contains the origin openly. The sharp
two-coordinate corner cap theorem
HUMAN_SHARP_DOUBLE_CORNER_CAP.md would give

    q >=(1+h)^2+(1+h_perp)^2
       >(41/24)^2+1
       =2257/576,

contradiction. Therefore S has no other
central-owned side separator, proving (4). QED.

## Concrete consequence for the surviving 3+1 occupancy class

If three whole squares lie beyond the
**right** central side, the sharp
three-square cap theorem forces its
offset h_R<7/24. The opposite left
side has offset h_L=1-h_R>17/24.
Thus the left side can serve at most
one square; if a single square exists
there, it must have:

* **only L** among its available
  central-owned side separators;
* center y-coordinate strictly in
  (-1/2,1/2) of the central frame; and
* an open-interior intersection with
  the horizontal diameter through zero.

Reflection and rotation give the
corresponding statement for every
3+1 profile. This is a geometric
placement restriction *within* a
surviving pattern, not its exclusion.

The result narrows the remaining
central-side branch analysis without
assuming parallelism or contact
equilibrium. It does not yet imply
the coherent five-corner projected
inequalities or the unrestricted
R8>=Rhat.
