# A sharp center-height bound for one arbitrarily rotated square in an outer disk cap

## Theorem (whole orientation range, pure hand proof)

Let a unit square S with any side frame lie in

    D_R intersect {x>=h},     R^2<=98/25, h>=2/5,

where the containing disk is centered at the origin.
Write its center as (x,y). Then

    (h+1)^2+(|y|+1/2)^2 <=R^2.                     (1)

In particular |y|<=sqrt(R^2-(h+1)^2)-1/2, exactly the
upper center-height bound attained by the axis-parallel
square [h,h+1] x [y-1/2,y+1/2]. **No orientation of S
is assumed in the lower bound.**

Equality in (1), if attainable, forces S to be
axis-parallel, its left edge on x=h, and one of
its two farthest right corners on the containing
circle. This is a sharp single-square cap theorem.

This supplies a quantitative arbitrary-frame
ingredient for two-opposite-central-side geometry;
it does not itself imply the unrestricted n=8 optimum.

## 1. A simple global linear bound h+|y|<7/5

Reflect across the x axis to assume y>=0. Take
the frame angle modulo quarter turns and reflection
to be either +theta or -theta, 0<=theta<=pi/4.
Write

    c=cos(theta), s=sin(theta),
    L=c+s, D=c-s.

Its horizontal half-width is L/2, so its center
has x>=h+L/2. The centered square's support in
direction (1,1) is exactly c, regardless of
the sign of the frame angle. Consequently

    max_(z in S)(z_x+z_y)=x+y+c
       >=h+y+(3c+s)/2
       >=h+y+sqrt(2).                                 (2)

For the final bound, 3c+s is positive and strictly
concave in theta on [0,pi/4], so its minimum is
at an endpoint. The endpoint values are 3
and 2*sqrt(2), whose minimum is 2*sqrt(2).

Disk containment gives max(z_x+z_y)<=sqrt(2)*R
<=14/5. Therefore

    2/5<=h,  0<=y,  h+y<=14/5-sqrt(2)<7/5.          (3)

The last strict inequality is sqrt(2)>7/5,
verified by the square comparison 2>49/25.
This is a *necessary bound from the actual
rotated square*, not a circular use of (1).

## 2. Reduce to one fixed horizontal center coordinate

The center has x>=h+L/2. Moving it to x=h+L/2
only decreases the squared norms of the
vertices used below: each has positive x
coordinate, because h>=2/5. It therefore
suffices to show that at least one of these
selected vertices at the minimal abscissa
has squared norm at least

    q_axis=(h+1)^2+(y+1/2)^2.                         (4)

The square has exactly one of the two frame
signs. We treat them separately and do not
infer parallelism or select a fictitious
corner from two independent support faces.

## 3. Negative frame angle: a concave-vertex proof

Take e=(c,-s), f=(s,c). The actual rightmost
vertex p+(e+f)/2, evaluated at the minimal
center abscissa, is

    V_-=(h+L,y+D/2).

Its squared norm is

    Q_-(theta)=(h+L)^2+(y+D/2)^2.                   (5)

Direct differentiation, using L'=D and
D'=-L, gives the strict concavity identity

    Q_-''(theta)=-2*h*L-6*c*s-y*D<0                (6)

for 0<theta<pi/4, since h>=2/5 and y>=0.

At theta=0, Q_-(0)=q_axis. At theta=pi/4,

    Q_-(pi/4)-q_axis
      =2*h*(sqrt(2)-1)+3/4-y
      >=(2*sqrt(2)-1)*h-13/20
      >=(16*sqrt(2)-21)/20>0.                      (7)

We used (3), h>=2/5, and sqrt(2)>7/5.
Strict concavity places Q_-(theta) at least
the lesser endpoint value, namely q_axis.
It is strictly larger for theta>0.
Thus (4) holds for every negative frame
angle, including the diagonal endpoint.

## 4. Positive frame angle: one rational polynomial identity

Now take e=(c,s), f=(-s,c). Two **actual**
vertices at the minimal center abscissa are

    V_top=(h+c,y+L/2),
    V_right=(h+L,y-D/2).

Put

    Q_top=(h+c)^2+(y+L/2)^2,
    Q_right=(h+L)^2+(y-D/2)^2.

The farthest vertex norm squared is at
least max(Q_top,Q_right), hence also
at least c^2 Q_top+s^2 Q_right.

Set z=tan(theta/2). Then
c=(1-z^2)/(1+z^2), s=2z/(1+z^2), and
0<=z<=sqrt(2)-1<1.
A direct expansion gives the exact identity

    c^2 Q_top+s^2 Q_right-q_axis
      = z*(1-z)*P_(h,y)(z)/(1+z^2)^4,              (8)

where the following is an **affine expression
in h and y**, with polynomial coefficients
entirely rational:

    P_(h,y)(z)
      = h*(4z^6+4z^5+16z^4+12z^2-4z)
        +y*(2z^6-2z^4-8z^3-2z^2-8z+2)
        +(z^5+5z^4+14z^3+6z^2-3z+1).             (9)

We prove P_(h,y)(z)>0 throughout (3), without
sampling or any floating-point bound.

## 5. A three-vertex positivity certificate

For fixed z, expression (9) is affine
in h,y. The closed triangle

    h>=2/5, y>=0, h+y<=7/5

has vertices (2/5,0), (7/5,0), (2/5,1).
A linear function attains its minimum
there at a vertex. At these vertices
the three polynomials 5P are exactly

    P_A=8z^6+13z^5+57z^4+70z^3+54z^2-23z+5,
    P_B=28z^6+33z^5+137z^4+70z^3+114z^2-43z+5,
    P_C=18z^6+13z^5+47z^4+30z^3+44z^2-63z+15. (10)

The first is positive for every z>=0:
its low-degree part 54z^2-23z+5 has
discriminant 23^2-4*54*5=-551<0
and positive leading coefficient;
all remaining monomials are nonnegative.
The second likewise uses
114z^2-43z+5, whose discriminant is
43^2-4*114*5=-431<0.

For the third, note that P_C''(z)>0
for every z>=0: its second derivative
is 540z^4+260z^3+564z^2+180z+88,
all nonnegative except for the
strictly positive constant.
At the exact rational point a=79/200,
straight integer expansion yields

    P_C'(a)=761606023/80000000000>0,
    P_C(a)-a*P_C'(a)
       =1041716561351/6400000000000>0.          (11)

Convexity and its elementary tangent inequality
therefore give, for all z>=0,

    P_C(z)>=P_C(a)+P_C'(a)*(z-a)
           =[P_C(a)-a P_C'(a)]+P_C'(a)*z>0.      (12)

Thus all three triangle-vertex polynomials
in (10) are strictly positive. Affinity
in (h,y) proves P_(h,y)(z)>0 throughout
the triangle, in particular throughout (3).

For theta>0, z*(1-z)>0, so (8) is strict:
the weighted combination of two actual
vertex norms exceeds q_axis. At theta=0
the top vertex already has norm squared
exactly q_axis. This completes the
positive-frame case.

## 6. Disk containment and equality

Sections 3--5 prove that for every
orientation, at least one actual square
vertex at x=h+L/2 has squared norm
at least q_axis. If the actual center
has x>h+L/2, the selected vertex
squared norms only increase because
the selected vertex x coordinates
are positive. Therefore the square's
greatest vertex squared norm is at least

    (h+1)^2+(y+1/2)^2,

with **strict inequality** if the frame
is nonparallel or x>h+1/2.

Every square vertex is in D_R, so (1)
follows. Reflecting the y coordinate
establishes the statement for either sign.

At equality the frame must be
horizontal/vertical, x=h+1/2 and the
top-right (or bottom-right) vertex
lies on the containing circle.
Conversely that standard square
achieves equality whenever it is
contained in the disk.

## 7. Exact role in the eight-square proof

For every center-containing square C
in an eight-square packing at q<=98/25,
a neighbor separated beyond a central
side at signed threshold h>=2/5
now has a rigorous, orientation-free
bound on its center's transverse
coordinate. This is stronger than
the universal center-radius estimate,
and allows opposite-side neighbors
to be compared by actual coordinate
geometry without assuming they have
common frames.

It is a **whole-square cap** theorem:
centers on one side of a line do
not suffice; the entire square must
lie beyond x=h. Corner-separated
neighbors remain a separate branch.
No unrestricted conclusion R8>=Rhat
is asserted in this note.
