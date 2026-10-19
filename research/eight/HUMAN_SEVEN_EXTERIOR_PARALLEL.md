# Seven exterior squares parallel: exact lower bound without orienting the central square

## Theorem

Suppose eight unit squares with pairwise disjoint open interiors fit a
closed disk D_R centered at the origin. If **seven of the eight** have
one common square side frame and the **eighth** contains the disk origin
in its open interior, then

    R^2 >= 2257/576.                                      (1)

The eighth square may have *any orientation*. It may touch some of the
other seven squares, and neither its center nor its frame is prescribed.

The bound is sharp even with the eighth square unrestricted: the three
parallel columns of HUMAN_PARALLEL_EIGHT_OPTIMUM.md attain equality.

In an arbitrary eight-square packing satisfying R^2<2257/576, the
analytic central-square theorem supplies a unique square C containing
zero in its open interior. Consequently **at least two of the seven
exterior squares must have different orientations**. In particular
the candidate with two tilted exterior squares lies on the permitted
side of this theorem.

The proof below is independent of the central square's geometry:
the central square is used *only* to certify that the seven other
parallel squares do not contain zero. No central-to-exterior
separator, common frame with C, stress, or contact graph is assumed.

## 1. Four disk points give the exact bound

We first prove a point lemma, with no square assumption.
Suppose four points L+,L-,R+,R- lie in D_R and obey

    (L+-L-).y>=3,    (R+-R-).y>=2,
    (R+-L+).x>=3,    (R--L-).x>=3.                        (2)

Reflect the four points across the x axis, exchange the plus
and minus labels in both columns, and average corresponding old and
reflected points. Convexity of D_R preserves the averaged points
inside D_R; the linear inequalities (2) are preserved as well.
The resulting points have the form

    (a,h), (a,-h), (b,k), (b,-k)

with h>=3/2, k>=1, and b-a>=3. Containment gives

    a>=-sqrt(R^2-9/4),     b<=sqrt(R^2-1),

so

    3<=sqrt(R^2-9/4)+sqrt(R^2-1).                        (3)

The right side is strictly increasing in R^2 on its domain.
At q0=2257/576 its two radicals are 31/24 and 41/24,
which sum to 3. Therefore (3) implies R^2>=q0.

The same conclusion holds with x,y interchanged in (2).

## 2. Seven parallel squares: exhaustive center classes

If R^2>=q0 there is nothing to prove. Suppose for contradiction
that R^2<q0. Then R<2 and q0<98/25.
The analytically proved central-square theorem at radius
sqrt(98/25) supplies a unique square C containing zero in
its open interior.

By hypothesis the *other seven* have a common side frame.
Rotate coordinates to make their sides horizontal/vertical;
**do not rotate or otherwise normalize C's frame**.
Each of those seven centers (x,y) satisfies

    -3/2<x,y<3/2,                                         (4)

because its x,y-extent lies inside D_R and R<2.
Any two of the seven squares have disjoint open interiors exactly
when

    |x_i-x_j|>=1  or  |y_i-y_j|>=1.                       (5)

No one of their centers can have simultaneously
|x|<1/2 and |y|<1/2: such a parallel square would
also contain zero in its open interior, contradicting C.
**This argument uses no information about C's orientation.**

Partition their seven centers into the following disjoint classes:

* H: horizontal straddlers, |y|<1/2 and |x|>=1/2;
* V: vertical straddlers, |x|<1/2 and |y|>=1/2;
* Q: quadrant centers, |x|>=1/2 and |y|>=1/2.

There is at most one H center on each of the left and right sides,
at most one V center on each of the top and bottom sides,
and at most one Q center in each quadrant. Indeed two centers
in any of these same cells have both coordinate differences
strictly less than one by (4); (5) forbids them.
Therefore

    H<=2, V<=2, Q<=4, H+V+Q=7.

Up to exchanging x and y and reflecting axes there are
only two occupancy cases:

    Case I:   H=1, V=2, Q=4;
    Case II:  H=2, V=2, Q=3.                            (6)

An elementary ordering fact will be used: two centers in
the same outer x band [1/2,3/2) (or (-3/2,-1/2])
must have y coordinates differing by at least one;
similarly two centers in one upper or lower y band
must have x coordinates differing by at least one.
In these comparisons the coordinate classes determine
which center comes first, so the signed inequalities follow.

## 3. Case I: one horizontal, two vertical, four quadrant centers

By reflection place the one horizontal straddler E on the left.
Write B,D,J,K for the northeast, northwest, southwest,
and southeast quadrant centers; let T,G be the top and
bottom vertical straddlers.

The left-band ordering D,E,J yields

    D_y-E_y>=1,    E_y-J_y>=1,
    D_y-J_y>=2.                                           (7)

The right band B,K gives B_y-K_y>=1.
The upper band D,T,B gives B_x-D_x>=2;
the lower band J,G,K gives K_x-J_x>=2.

Choose **actual vertices of the seven parallel squares**

    L+=D+(-1/2,1/2),    L-=J+(-1/2,-1/2),
    R+=B+(1/2,1/2),     R-=K+(1/2,-1/2).

The four vertices lie in D_R.
Their vertical spans are at least 3 and 2,
and both horizontal cross-spans are at least 3,
by (7) and the preceding two band comparisons.
They satisfy (2). Section 1 gives R^2>=q0,
contradicting the assumption.

## 4. Case II: two horizontal, two vertical, three quadrant centers

Reflect so the *missing* quadrant is southeast.
Denote the right and left H centers by A,E,
the top and bottom V centers by T,G,
and the northeast, northwest, southwest Q centers by B,D,J.

The band orderings force

    B_y-A_y>=1,    D_y-E_y>=1,    E_y-J_y>=1,
    B_x-T_x>=1,    T_x-D_x>=1,    G_x-J_x>=1.             (8)

Since A lies on the positive x side with |A_y|<1/2,
while G lies on the lower y side with |G_x|<1/2,
we have A_x>G_x and A_y>G_y.
Their disjointness (5) therefore supplies a
**complete two-branch disjunction**:

    A_x-G_x>=1   or   A_y-G_y>=1.                       (9)

In the first branch (8)--(9) give

    D_y-J_y>=2, B_y-A_y>=1,
    B_x-D_x>=2, A_x-J_x>=2.

Take

    L+=D+(-1/2,1/2),    L-=J+(-1/2,-1/2),
    R+=B+(1/2,1/2),     R-=A+(1/2,-1/2).

These satisfy (2), so R^2>=q0.

In the second branch (8)--(9) give

    B_y-G_y>=2,  D_y-J_y>=2,
    B_x-D_x>=2,  G_x-J_x>=1.

Take instead the upper vertices of D,B and
the lower vertices of J,G:

    L+=D+(-1/2,1/2),    R+=B+(1/2,1/2),
    L-=J+(-1/2,-1/2),   R-=G+(1/2,-1/2).

Their upper and lower horizontal spans are
at least 3 and 2, while both vertical
cross-spans are at least 3. This is the
coordinate-swapped version of (2), so again
R^2>=q0.

The two alternatives in (9) exhaust Case II.
This completes the proof of (1).

## 5. Sharpness, application, and limitation

The all-parallel centers

    (-19/24,-1),(-19/24,0),(-19/24,1),
    (5/24,-1),(5/24,0),(5/24,1),
    (29/24,-1/2),(29/24,1/2)

form a packing whose maximum vertex norm squared
is exactly 2257/576. The center square
among them contains zero in its open interior,
so the equality construction belongs to
the theorem's larger class.

For a genuine eight-square packing at radius
R<=Rhat, the exact construction has
Rhat^2<2257/576. Hence at least two
of its **seven exterior squares** must fail
to share one common frame. This is not
the assertion that at least two exterior
squares have different angles from *some
fixed arbitrarily chosen axis*: no orientation
has been singled out; rather, the collection
of all seven exterior squares cannot have
only one common orientation.

The theorem does not classify arrangements
with one or more rotated exterior squares,
does not force two specific tilted squares
to be adjacent, and does not derive the
sharp unrestricted bound R8>=Rhat.
