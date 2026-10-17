# The exact optimum for eight parallel unit squares

## Theorem

For eight unit squares with a common side frame, pairwise disjoint open
interiors, and containment in a disk of radius R,

    R^2 >= 2257/576.

Equality is attained. No assumption about their contact graph, columns,
center positions, or contact with the circle is made in the lower bound.

The argument uses the already analytical central-square theorem at
q<=98/25 and otherwise only coordinate order and convexity of the disk.
It reduces the entire parallel problem to two occupancy patterns and one
four-point inequality. It is not a proof that a general packing can be
made parallel: the sharp tilted construction has smaller radius.

## 1. The four-point inequality

Suppose four points L+,L-,R+,R- belong to a disk centered at zero, with

    (L+ - L-)_y >= 3,      (R+ - R-)_y >= 2,
    (R+ - L+)_x >= 3,      (R- - L-)_x >= 3.             (1)

Reflect in the horizontal axis and exchange the + and - labels on each
side. Average each old point with its reflected partner. Convexity of the
disk and linearity of (1) preserve containment and all four inequalities.
The new four points have the form

    (a,h), (a,-h), (b,k), (b,-k),
    h>=3/2, k>=1, b-a>=3.

Writing q=R^2, containment implies

    3 <= b-a <= sqrt(q-1)+sqrt(q-9/4).                   (2)

The right side strictly increases on q>=9/4. At q0=2257/576 its two
summands are 41/24 and 31/24, whose sum is three. Hence (2) implies
q>=q0. Rotation through a right angle gives the same conclusion when
horizontal and vertical requirements in (1) are interchanged.

The points in this lemma need not be vertices of a rectangle. Their
unconstrained coordinates may differ; averaging, not an assumed alignment,
is what removes those differences.

## 2. The complete occupancy alternatives

For the lower bound suppose, towards a contradiction, that R^2<q0.
In particular R<2 and q0<98/25. Choose coordinates centered at the disk
origin with the squares' common horizontal and vertical side frame.
By HUMAN_GLOBAL_GEOMETRY_CLOSURE.md there is exactly one square C whose
open interior contains zero.

Every square center (x,y) satisfies

    -3/2 < x,y < 3/2,                                   (3)

because its extremal horizontal and vertical coordinates have absolute
values |x|+1/2 and |y|+1/2 and are at most R<2. Two such parallel squares
have disjoint open interiors precisely when

    |x_i-x_j|>=1 or |y_i-y_j|>=1.                       (4)

Classify the seven centers other than C as follows:

* Horizontal straddlers: |y|<1/2 and |x|>=1/2.
* Vertical straddlers: |x|<1/2 and |y|>=1/2.
* Quadrant squares: |x|>=1/2 and |y|>=1/2.

This is exhaustive: a center with both absolute coordinates less than
1/2 would give a second open square through zero. The weak inequalities
place every possible coordinate-boundary case in exactly one class.

There is at most one horizontal straddler on each side of zero. Two on
the right, for example, have x coordinates in [1/2,3/2) and y coordinates
in (-1/2,1/2). Both differences are strictly below one, contradicting (4).
Reflection gives the left side. Likewise there is at most one vertical
straddler above and one below zero. Each of the four quadrants holds at
most one quadrant square, by the same two coordinate-width bounds.

Let H,V,Q be the numbers in these three classes. Thus

    H<=2, V<=2, Q<=4, H+V+Q=7.

There are exactly two alternatives, up to a quarter turn:

    Case I:  H=1, V=2, Q=4;
    Case II: H=2, V=2, Q=3.                             (5)

No finer geometric classification is being assumed.

A repeated ordering fact will be used below. Any two centers in the same
positive horizontal band x>=1/2, or the same negative horizontal band
x<=-1/2, have horizontal difference less than one, by (3). They must
therefore have vertical difference at least one. Similarly, two centers
in the same upper or lower band must have horizontal difference at least
one. When their other coordinates are ordered by the class definitions,
the sign of that difference is determined as well.

## 3. Case I: one horizontal and two vertical straddlers

Reflect horizontally so that the one horizontal straddler is on the left.
Denote its center by E. Name the two vertical straddler centers T and G
(top and bottom). Name the four quadrant centers B,D,J,K in the northeast,
northwest, southwest, and southeast quadrants, respectively.

The left-band ordering gives

    D_y-E_y>=1,       E_y-J_y>=1,
    D_y-J_y>=2.                                         (6)

The right-band ordering gives

    B_y-K_y>=1.                                         (7)

In the upper band, T lies horizontally between D and B, so

    T_x-D_x>=1,       B_x-T_x>=1,
    B_x-D_x>=2.                                         (8)

The lower band similarly gives

    K_x-J_x>=2,                                         (9)

using the intervening center G.

Select the following actual square vertices:

    L+ = D+(-1/2, 1/2),   L- = J+(-1/2,-1/2),
    R+ = B+( 1/2, 1/2),   R- = K+( 1/2,-1/2).

All four lie in the disk. Equations (6)--(9) give exactly (1): their
left vertical span is at least three, right vertical span at least two,
and both horizontal spans are at least three. Section 1 gives q>=q0,
the desired contradiction.

## 4. Case II: both horizontal and both vertical straddlers

Use reflections to put the missing quadrant in the southeast. Let A,E
be the right and left horizontal straddler centers, T,G the top and bottom
vertical straddler centers, and B,D,J the northeast, northwest, and
southwest quadrant centers.

The band orderings give

    B_y-A_y>=1,
    D_y-E_y>=1,       E_y-J_y>=1,
    B_x-T_x>=1,       T_x-D_x>=1,
    G_x-J_x>=1.                                         (10)

The signs of the two coordinate differences between A and G are positive:

    A_x>G_x,       A_y>G_y.

By their disjointness (4), at least one of the following is true:

    A_x-G_x>=1,       A_y-G_y>=1.                       (11)

These are the only further alternatives needed.

### 4.1 The horizontal alternative

If A_x-G_x>=1, equations (10)--(11) give

    D_y-J_y>=2,       B_y-A_y>=1,
    B_x-D_x>=2,       A_x-J_x>=2.

Choose

    L+ = D+(-1/2, 1/2),   L- = J+(-1/2,-1/2),
    R+ = B+( 1/2, 1/2),   R- = A+( 1/2,-1/2).

These disk vertices satisfy (1), again giving q>=q0.

### 4.2 The vertical alternative

If A_y-G_y>=1, the same equations give

    B_y-G_y>=2,       D_y-J_y>=2,
    B_x-D_x>=2,       G_x-J_x>=1.

Take the outer vertices of B,D,J,G: add (+1/2,+1/2) to B,
(-1/2,+1/2) to D, (-1/2,-1/2) to J, and (+1/2,-1/2) to G.
The upper horizontal span is at least three, the lower horizontal span
at least two, and both vertical spans are at least three. This is the
right-angle rotation of the four-point lemma. It too implies q>=q0.

Cases (5) and (11) exhaust the packing, contradicting q<q0 in every
case. The lower-bound proof is complete.

## 5. A matching eight-square construction

Take three vertical columns of standard unit squares, with centers

    (-19/24,-1), (-19/24,0), (-19/24,1),
    (  5/24,-1), (  5/24,0), (  5/24,1),
    ( 29/24,-1/2), (29/24,1/2).

Consecutive column abscissas differ by one; centers in a column differ
vertically by at least one. Thus every pair satisfies (4).
For a standard unit square centered at (x,y), its farthest vertex norm
squared is (|x|+1/2)^2+(|y|+1/2)^2. The largest values in the left,
middle, and right columns are, respectively,

    (31/24)^2+(3/2)^2 = 2257/576,
    (17/24)^2+(3/2)^2 = 1585/576,
    (41/24)^2+1       = 2257/576.

Hence all eight squares fit in D_(sqrt(2257)/24), completing equality
and the theorem.

## 6. Relation to the unrestricted target

The sharp tilted construction is strictly below sqrt(2257)/24. Therefore
an unrestricted lower-bound proof cannot normalize all eight frames to be
parallel. This note instead gives a fully proved endpoint case for a
future orientation-dependent argument.

Its two-case occupancy proof uses (4) in an essential way. For rotated
squares, centers in a common band need not be separated by one in the
other coordinate; a separator may belong to a rotated frame. Likewise,
the four selected outer vertices need not have the displayed offsets.
Those facts cannot be assumed when importing this argument into the
unrestricted problem. The final oblique five-corner constraints remain
an independent proof obligation.
