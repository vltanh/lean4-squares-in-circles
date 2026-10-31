# A long physical channel gives a straight-line barrier for every completion

**Date:** October 30, 2026 UTC. **Status:** complete proposed hand
derivation, awaiting independent full review. No original case flag is
changed by this manuscript alone.

The first result is force-free and applies to any two actual squares
separated by a support gap of two. The second uses actual force and
moment balance at the two internal bodies of a four-square channel.
It places every remaining original square wholly on one side of the
channel's original force line. Endpoints can have arbitrary degrees,
circle masks, other contacts and tilts, and all completing squares keep
their independent orientations.

## 1. Setup and the existing coupled endpoint estimate

Let a packing of actual unit squares have pairwise disjoint open
interiors and lie in the disk about the origin with squared radius

    R^2 <= Q = 1105/256.

For a square S of center c and orthonormal side axes u,v, put

    h_S(n)=(|n.u|+|n.v|)/2

for its halfwidth in the unit direction n. Every actual center obeys

    |c|<M=91/60.                                         (1)

Indeed its largest squared corner norm is
`|c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2`, and the right
side at M exceeds Q by `31/57600`. Distinct unit centers have distance
at least one, by disjointness of their open radius-half incircles.

Suppose two actual squares A,B have one signed support direction n with

    n.(c_B-c_A) >= 2+h_A(n)+h_B(n).                       (2)

Choose n as the x direction, with origin still the disk center. Write

    c_A=(-X_A,y_A), c_B=(X_B,y_B).

The two endpoints satisfy

    89/60 < X_A,X_B < 91/60,
    |y_A|+|y_B| <= 1/8.                                  (3)

The horizontal bounds follow from (1),(2), using `h_A,h_B>=1/2`.
The height estimate is the complete coupled-height result (12) of

`TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md`,

frozen SHA256
`78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6`.
That estimate includes all actual endpoint tilt signs and does not
assume that either endpoint touches the containing circle. More
precisely it gives

    |y_A|+|y_B| <= 1/8-E+(320/39)E^2 <= 1/8,
    0<=E<1/30,

where E is half the sum of their horizontal width excesses. Only the
last inequality is needed here.

## 2. No other actual square enters either outer vertical strip

**Theorem 1 (outer-strip exclusion).** Under (2), A is the only actual
square that can meet the closed halfplane `x<=-119/60`, and B is the
only actual square that can meet `x>=119/60`. In particular every
square other than A,B is contained in the open strip

    -119/60 < x < 119/60.                                (4)

**Proof.** Suppose an actual square C different from A contains a point
p with `p_x<=-119/60`. Every point of C is at distance at most
`1/sqrt(2)<71/100` from its center c. Thus

    c_x <= p_x+1/sqrt(2) < -119/60+71/100 = -191/150.

By (1), also `c_x>-M` and

    c_y^2 < M^2-(191/150)^2
          =6789/10000 < 25/36.                           (5)

Consequently `|c_y|<5/6`. Both c_x and the x coordinate of c_A lie
strictly between `-M` and `-191/150`. Equations (3),(5) give

    |c_x-(c_A)_x| < M-191/150=73/300<1/4,
    |c_y-y_A| < 5/6+1/8=23/24.

It follows that

    |c-c_A|^2 < (1/4)^2+(23/24)^2=565/576<1,

contradicting the incircle center separation. This includes a point p
on the boundary of C or of the closed halfplane. Reflection proves the
right-hand assertion with B. QED.

No contact relation between C and either endpoint is used. In
particular the exclusion covers all unstressed, noncontacting and
otherwise unclassified units of the original packing.

## 3. The actual force line of a true two-transmitter channel

Consider four distinct actual squares

    A -- U -- V -- B

joined by three actual positive contacts. Let the actual application
points be q_0,q_1,q_2 respectively, each belonging to both incident
squares and to their supporting faces. Suppose U and V have exactly
these two incident positive pair contacts and zero other external
force and moment. This holds for true degree-two unloaded bodies of
the original full positive physical stress. Their force and torque
equations refer to these actual means, including the endpoints of
their permitted contact segments.

Translational balance at U,V makes the signed normals of all three
edges equal to one unit direction n, and all three positive weights
equal. Angular balance at U then gives

    (q_1-q_0) cross n=0,

and at V gives `(q_2-q_1) cross n=0`. Opposite supporting-face
equalities fix the positive signed differences. Hence q_0,q_1,q_2
are on one line in direction n and

    q_1-q_0=2*h_U(n)*n,
    q_2-q_1=2*h_V(n)*n.                                 (6)

For completeness, a unit square admitting opposite support points
whose difference is parallel to n has width exactly 1 or sqrt(2).
If one component of n in the square frame is zero, its support faces
are opposite sides and (6) forces equal transverse coordinates, with
difference n. If both components are nonzero, the support points are
the two uniquely exposed opposite vertices. Their difference has
components of absolute value one in the square frame. Parallelism
therefore forces the two components of n to have equal absolute value,
so the width is sqrt(2). This argument includes endpoint means on a
side support face and assumes no generic orientation.

Support telescoping gives

    n.(c_B-c_A)=h_A(n)+2*h_U(n)+2*h_V(n)+h_B(n).          (7)

If either internal width were sqrt(2), the right side would be at
least `2+sqrt(2)>2M=91/30`, contradicting (1). For example the
strict comparison follows from `sqrt(2)>31/30`, since
`2>(31/30)^2`. Both U and V are therefore side-normal transmitters,
and

    q_1-q_0=q_2-q_1=n.                                  (8)

In particular (2) holds with equality, and Theorem 1 applies to the
actual endpoints without changing their poses or contact points.

## 4. Every inward normal chord of a unit square has length at least one

**Lemma 2.** Let q belong to the maximum-n supporting face of a unit
square S. Then

    q-t*n belongs to S for every 0<=t<=1.                (9)

The reflected assertion holds for a minimum supporting face.

**Proof.** Use the square's own orthonormal axes. If a component
`n.u` is nonzero, the corresponding coordinate of q is the exposed
endpoint `sign(n.u)/2`. Subtraction of `t*n` moves that coordinate
inwards by `t*|n.u|<=1`, so it remains in the closed interval
`[-1/2,1/2]`. If the component is zero, the coordinate stays at its
original admissible value. Apply this independently to both axes.
The argument applies to an arbitrary support mean and to a vertex.
QED.

Combining (8),(9), the actual four-square union contains the complete
closed force-line segment

    [q_1-2*n, q_1+2*n].                                 (10)

The two internal pieces are actual opposite-support chords of U and
V, while the outer pieces are actual chords of A and B. Their common
endpoints are precisely the original contact means. The segment is
not obtained by aligning, translating or otherwise replacing a unit.

## 5. Global straight-line separation and the sharp height bound

Write `q_1=(s,t)` in the n-horizontal disk frame. From (7),(8),

    (c_A)_x=s-1-h_A(n),
    (c_B)_x=s+1+h_B(n).

Together with (1) and `h_A,h_B>=1/2`, these imply

    -1/60 < s < 1/60.                                   (11)

Therefore the segment (10) starts strictly left of `-119/60` and
ends strictly right of `119/60`.

**Theorem 3 (straight-line barrier).** Every actual square C outside
the four-square channel is contained wholly in one of the two closed
halfplanes

    y>=t  or  y<=t.                                     (12)

Its open interior is contained wholly in the corresponding open
halfplane. The common force-line height also satisfies

    (2+|s|)^2+t^2 <= R^2 <= Q,
    |t| <= 9/16.                                        (13)

**Proof.** Theorem 1 says that C cannot meet either outer strip. All
points of the line y=t between those strips belong to the actual
channel union by (10),(11). The open interior of C cannot meet the
closed union of the four other squares: if an interior point belonged
to one of those closed squares, nearby interior points of that square
would also lie in the open interior of C, a contradiction.

Thus the open convex interior of C misses the entire line y=t. It
lies in one of the two open halfplanes, and taking its closure gives
(12). This proves separation also when the force line lies on a side
or vertex of one or more channel squares. The force line need not
pass through the interior of a channel body.

The two actual points `(s-2,t)` and `(s+2,t)` in (10) lie in the
containing disk. The larger of their squared norms is exactly
`(2+|s|)^2+t^2`. This proves (13), since `Q-4=81/256`. QED.

The constant 9/16 is sharp already for the local four-square geometry.
Take four aligned squares with centers

    (-3/2,1/16), (-1/2,1/16), (1/2,1/16), (3/2,1/16),

and actual contact means `(-1,9/16),(0,9/16),(1,9/16)`.
They lie in the disk of squared radius Q, with the two extreme top
vertices on that circle. Equal horizontal contact forces have zero
force and moment on each internal unit, including at these endpoint
means. Their force line has t=9/16 and s=0. No full endpoint stress
balance is asserted by this local sharpness witness.

## 6. Completion-count consequences and scope

In a nine-unit packing there are five actual units outside this
four-square channel. Theorem 3 assigns them to the two force-line
halfplanes, so at least three lie on one side. All five units are
retained, with arbitrary orientations and arbitrary mutual contacts.

This consequence does not assert which side has three units or move
the force line. In particular the existence of a four-square channel
alone is not declared impossible by the present theorem. Applying an
independent sharp three-square cap theorem requires its actual floor
or ceiling hypothesis, which (13) by itself does not supply.

Theorem 1 is entirely force-free. Theorem 3 additionally uses angular
balance on the two internal units to obtain one physical straight
force line. Merely translational balance supplies the same normals
and the endpoint gap but does not justify (6) or replace the actual
application means. Endpoints may carry arbitrarily many other forces;
their full equations, masks and physical means are retained. Nothing
here assumes a selected plane embedding or closes the unrestricted
n=9 theorem. No original fine/coarse flag, Lean file, CI state or
repository metadata was changed.
