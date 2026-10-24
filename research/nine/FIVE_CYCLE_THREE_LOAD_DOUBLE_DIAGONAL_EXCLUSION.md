# Two diagonal transmitters are impossible in the three-load five-cycle

**Status: complete conditional hand exclusion; root and independent full hand audits passed.**
In the usual window

\[
                 79/40\le R\le\sqrt{1105}/16,
\tag{1}
\]
consider the full three-load C5 orbit

\[
                         T-U-B-C-V-T,
\]
with precisely T,B,C loaded. Choose the necessary certificate with the
compatible diagonal avoidance at point-only vertex/vertex contacts
in PHYSICAL_BODY_GRAPH_UNCROSSING.md, Section2. Then **U and V
cannot both be diagonal transmitters**. All four extra units and
all actual application means remain.

The parallel pair-force alternative at T was independently excluded
in FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md. The present theorem
covers the entire remaining double-diagonal width chart, not a
prescribed pair of orientations. The three-load C5 still permits
side/side or one side/one diagonal at this stage.

## 1. Each diagonal transmitter forces its endpoint frames to agree

At an unloaded degree-two diagonal transmitter, the two actual
applications are its opposite vertices. Every selected pair normal
at a point-only vertex/vertex intersection avoids both incident
squares' diagonal directions. Thus such a transmitter cannot have
a vertex/vertex endpoint in the selected certificate.

Both of its endpoints therefore lie in relative interiors of sides
of its neighboring squares. Their unique common normal, parallel
to the transmitter diagonal, is an actual side axis of each neighbor.
Consequently both endpoint neighbors have the same square frame,
with one side axis along that channel.

These choices are made before multiplier extraction, simultaneously
with the preceding finite strict/generic choices. Uncrossing keeps
surviving point normals; thinning only deletes atoms. There is no
change of a force normal after a stress has been obtained, and no
shared-side mean is constrained by the avoidance.

Apply the statement first to U, then to V. If both are diagonal,
T,B,C all have the same square frame. Both actual pair normals
at T are side axes of that frame. They cannot be parallel by the
complete parallel-T theorem. Hence they are perpendicular.

## 2. Exact coordinate cover, including the physical two-corner mask

Orient the two side axes of T so its pair normals point in the
negative x and negative y directions. Force balance gives a strictly
positive coordinate in each direction for its circle resultant.
Thus one of T's physical circle corners lies in the positive own
coordinate quadrant and can be denoted by (alpha,beta), with

\[
          \alpha,\beta\ge1/2,\qquad \alpha^2+\beta^2=R^2,
          \qquad T=[\alpha-1,\alpha]\times[\beta-1,\beta].
\tag{2}
\]

This also covers two physical circle corners with arbitrary
nonnegative individual weights: the coordinate perpendicular to
the radial axis can have either sign before the axis choice, and
the chosen corner has that signed coordinate equal to1/2. A zero
coordinate of the resultant is impossible here because both
perpendicular pair forces have strictly positive magnitudes.

Relabel U,V and B,C if needed so U carries the leftward channel
from T to B, while V carries the downward channel from T to C.
Each diagonal has reserve sqrt(2). Since B,C are aligned with T,
their supporting intervals satisfy exactly

\[
 \begin{split}
 B_x&=[\alpha-2-\sqrt2,\ \alpha-1-\sqrt2],\\
 C_y&=[\beta-2-\sqrt2,\ \beta-1-\sqrt2].
 \end{split}
\tag{3}
\]

Their other interval positions remain arbitrary. These equations
follow from actual support gaps, not from centered application means.
The actual positive BC edge requires their physical rectangles to
touch. In particular, writing y_B for B's lower side coordinate,

\[
                         y_B\le\beta-1-\sqrt2.
\tag{4}
\]

The right side of (4) is strictly negative because beta<=R<21/10
and 1+sqrt(2)>12/5. Likewise alpha-2-sqrt(2)<0.

## 3. The touching condition forces a radius above the target

B has its lower-left vertex at (alpha-2-sqrt(2),y_B). Equations
(3)--(4), their negative signs, and disk containment give

\[
 R^2\ge(2+\sqrt2-\alpha)^2+(1+\sqrt2-\beta)^2.
\tag{5}
\]

Put A=2+sqrt(2), D=1+sqrt(2). Subtracting alpha^2+beta^2=R^2
from (5) yields

\[
                 A\alpha+D\beta\ge\frac{A^2+D^2}{2}.
\]

Cauchy's inequality now gives

\[
 R\sqrt{A^2+D^2}\ge\frac{A^2+D^2}{2},
 \qquad
 R^2\ge\frac{A^2+D^2}{4}
       =\frac{9+6\sqrt2}{4}
       >\frac{87}{20}>\frac{1105}{256}.
\tag{6}
\]

The penultimate inequality uses sqrt(2)>7/5. The final rational
comparison is22272>22100 after multiplying by5120. This contradicts
(1), completing the full double-diagonal exclusion.

The proof uses only exact frame consequences, actual channel widths,
one necessary BC intersection inequality and an all-coordinate
Cauchy bound. It retains every side-application endpoint allowed by
the selected physical convention, every circle-corner weight mask
and all four arbitrary extras. It uses no secondary-minimizer
premise, numerical pose search, Lean compilation or CI.
