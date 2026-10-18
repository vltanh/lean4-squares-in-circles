# The fully single-side S1 pattern cannot have seven outer centers

## Theorem (exact global macro-case rejection)

Let eight unit squares of arbitrary, independently chosen
orientations have disjoint open interiors in a disk with

    q=R^2 <=9789/2500.

Let C denote the unique origin-containing central square,
and suppose the other seven squares have **exactly one**
central-owned whole-square side-separator status apiece.
If their opposite-side occupancy type is

    S1=(3+0,3+1),

then **at least one noncentral square center has norm <1**.
Equivalently, the S1/k=7 intersection of the two
exhaustive global classification systems is **impossible**:

    **S1 => k<=6.**                                  (1)

This conclusion has no central-center offset caveat.
It includes the tiny-offset S1 survivors
of HUMAN_PERPENDICULAR_TRIPLES_SHARP_LANE.md.
No contact graph, frame, circle-touching or stress
hypothesis is assumed.

## 1. A universal exact radial ceiling for square centers

Any contained unit square with center p satisfies

    R^2 >= |p|^2+|p|+1/2,

by the exact farthest-vertex formula and
|p dot e|+|p dot f|>=|p|.
Consequently every center satisfies

    |p|<283/200.                                    (2)

Indeed at r=283/200 the right side equals

    (283/200)^2+283/200+1/2
       =156689/40000
       >156624/40000=9789/2500,

and the expression strictly increases with r>=0.

HUMAN_STABLE_OUTER_ANGLE.md proves the
whole-orientation hand inequality

    angular gap of any two distinct outer centers
       > delta0 :=pi/4-1/500.                     (3)

An outer center has norm >=1.
The source theorem applies without actual contact.

## 2. Normalize the S1 whole-square side populations

Use central-frame reflections and an axis swap
so the triple with opposite singleton is

    U: three whole squares,
    D: one other whole square,

and the perpendicular opposite pair is

    R: three whole squares,
    L: zero whole squares.

Because all seven statuses are **single-side**,
these labels are distinct. Write h=h_U>0
for the upper side's signed offset. The
orientation-free three-square cap theorem gives

    h<7/24,              h_D=1-h>17/24.             (4)

The D-singleton square lies wholly in y<=-h_D.
Its center p_D=(x_D,y_D) therefore satisfies

    y_D<-(h_D+1/2)<-29/24,                         (5)

and the sharp one-square cap center envelope
HUMAN_ONE_SQUARE_CAP_ENVELOPE.md yields

    |x_D|<1/2.                                       (6)

Thus, using the usual polar angle in (-pi,pi],

    angle(p_D)>-pi/2-atan(12/29),
    angle(p_D)<-pi/2+atan(12/29).                  (7)

Every R-side member has p_x>1/2>0,
so its center-ray angle lies in
(-pi/2,pi/2). Every U-side member has
p_y>1/2>0, so its angle lies in (0,pi).

We now improve the **upper bound** on U
center-ray angles and the **lower bound**
on D's center-ray angle. There are two
exhaustive cases for the upper triple offset h.

## 3. Upper triple offset h>=7/50

Every U-cap square center satisfies

    p_y>=h+1/2>=16/25.

Together with (2) this gives

    sin(angle(p))>= (16/25)/(283/200)
                     =128/283.

Its angle in (0,pi) therefore obeys

    angle(p) <=pi-asin(128/283)
              <pi-atan(9/20).                      (8)

For the final strict comparison, both positive
arguments lie in (0,pi/2), and

    sin(atan(9/20))=9/sqrt(481)
                        <128/283,

which follows on squaring from

    128^2*481=7880704
        >6487209=9^2*283^2.

Put A=atan(9/20), D=atan(12/29).
The positive tangent difference identity gives

    A-D=atan(21/688),                              (9)

since (9/20-12/29)/(1+(9/20)*(12/29))=21/688.

For every 0<x<1, atan(x)>x/2,
e.g. by integrating 1/(1+t^2)>1/2 on [0,x].
Hence

    A-D>21/1376>3/250=6/500.                    (10)

By (7)--(10), **all seven** center-ray angles
from the R, U and D populations lie in an
ordinary (nonwrapping) interval with lower
endpoint -pi/2-D and upper endpoint pi-A,
of width

    W<3*pi/2-(A-D)
      <3*pi/2-6/500
      =6*(pi/4-1/500)=6*delta0.                  (11)

## 4. Upper triple offset 0<h<7/50

The opposite D side has offset

    h_D=1-h>43/50.

The sharp one-square center-height cap envelope
therefore gives the **stronger** transverse bound

    |x_D|<9/50,                                    (12)

as proved in section 5 of
HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md.
Combining (12) with (5) strengthened to
y_D<-(43/50+1/2)=-34/25 gives

    angle(p_D)>-pi/2-atan(9/68).                 (13)

Every U-square still has p_y>1/2.
Equation (2) now gives

    angle(p_U)<pi-asin(100/283)
              <pi-atan(1/3),                       (14)

because

    sin(atan(1/3))=1/sqrt(10)<100/283,

which on squaring reduces to
100000>80089=283^2.

Also 9/68<1/7 because 63<68, so
atan(9/68)<atan(1/7).
The exact arctangent subtraction identity yields

    atan(1/3)-atan(1/7)=atan(2/11).             (15)

Again atan(x)>x/2 for 0<x<1 gives

    atan(2/11)>1/11>3/250=6/500.                (16)

Thus by (13)--(16), all seven center rays
belong to a nonwrapping arc with width

    W<3*pi/2-[atan(1/3)-atan(1/7)]
      <3*pi/2-6/500=6*delta0.                  (17)

The R rays lie in (-pi/2,pi/2) and the U
rays lie in (0,pi), so they are certainly
included between the displayed D lower
endpoint and U upper endpoint.

## 5. Six angular gaps give the contradiction

Suppose contrary to (1) that **all seven**
exterior square centers have norm >=1.

In either section 3 or section 4,
their seven distinct polar angles lie
in a single linear interval of width
W<6*delta0. Sort those seven angles

    theta_1<theta_2<...<theta_7.

By the already proved pairwise outer-center
angular separation theorem (3), each
successive difference satisfies

    theta_(i+1)-theta_i >delta0,  i=1,...,6.

Indeed if a linear difference is <=pi,
it is exactly the smaller angular separation
and obeys (3); if it exceeds pi, it is
automatically >delta0. Adding gives

    theta_7-theta_1>6*delta0,

contradicting the enclosing interval
W<6*delta0. Therefore at least one
noncentral square center has norm <1,
so k<=6. QED.

## 6. Place in the sharp n=8 roadmap

This removes **the entire S1/k=7 macro-case**,
not just a sampled central-position region.
It is independent of the new perpendicular
triple overlap theorem, though it reuses its
exact far-singleton transverse lane proof.

Combined with the other recent hand results:

* S1/k=7 is **globally impossible**.
* S1/k=3,4 requires a triple offset <7/50.
* S1/k=5,6 survives only with at least
  one triple offset <7/50, and every 3+1
  opposite singleton in such a narrow
  branch obeys the transverse lane
  |z|<9/50 if its triple side is tiny.

The other all-single-side cases S2,S3,S4,
the corner-only and double-side branches,
and general outer-path attachments remain.
In particular S4 contains the exactly
realized candidate, so the unrestricted
radius lower bound R8>=Rhat is still OPEN.
