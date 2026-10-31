# Four-square junction capacity eight with a one-fifteenth coordinate margin

Date: October 30, 2026 UTC.

**Status: complete proposed force-free extension, awaiting independent
review. The previously frozen one-sixtieth source is unchanged.**

The larger margin permits a two-long-channel application using only
translational force balance: the normals need only be close to the
junction's common axes, without torque equations forcing exact axes.

## 1. Statement

Let actual unit squares have pairwise disjoint open interiors and lie
in the disk centered at O of squared radius at most Q=1105/256.
Suppose four of the actual squares meet at one point p. Their common
orthonormal square frame gives coordinates satisfying

    |p_x|<=1/15, |p_y|<=1/15.                              (1)

Then there are at most eight units in the whole packing. All other
units have arbitrary independent orientations, contacts and masks.

At a common point of four interior-disjoint squares, the four local
interior angles must all be pi/2 and fill the four quadrants. Thus
the four actual squares form an aligned two-by-two block with union

    B=[p_x-1,p_x+1] x [p_y-1,p_y+1].                     (2)

No selected contact graph or stress premise is used.

## 2. Center clearance from the entire actual block

Every actual center c has norm less than M=91/60. Indeed the actual
farthest-corner expression is at least |c|^2+|c|+1/2, and

    M^2+M+1/2-Q=31/57600>0.                              (3)

Distinct unit centers have distance at least one, by disjointness of
their open radius-1/2 incircles. For any unit outside the four-square
block, its incircle misses int(B); therefore

    dist(c,B)>=1/2.                                      (4)

An alleged open overlap with B contains a point off the block's
internal edges and overlaps one actual block-square interior. If the
nearest point in B is a boundary point at distance less than 1/2,
nearby interior points of B also lie in the incircle. This justifies
(4) at all closed boundary cases.

## 3. Four center caps cover every additional square

Set

    a=14/15, b=43/30.                                    (5)

A center in both coordinate intervals of B contradicts (4). A center
outside only its horizontal interval has |c_x-p_x|>=3/2 and hence
|c_x|>=b. The vertical-only case gives |c_y|>=b.

A center outside both intervals can be written

    |c_x-p_x|=1+s, |c_y-p_y|=1+t,
    s,t>0, s^2+t^2>=1/4.

By (1), |c_x|>=a+s and |c_y|>=a+t. Since s+t>=1/2,

    |c|^2>=2*a^2+2*a*(s+t)+s^2+t^2
          >=2*a^2+a+1/4
          =2633/900
          =M^2+2251/3600>M^2,                            (6)

contradicting (3). Thus every additional actual center belongs to
one of the four caps

    x>=b, x<=-b, y>=b, y<=-b,
    x^2+y^2<=M^2.                                       (7)

Each cap has diameter strictly below one. For example in the eastern
cap b<=x<=M and |y|<=sqrt(M^2-b^2), so the squared distance between
any two points is at most

    (M-b)^2+4*(M^2-b^2)=713/720<1.                        (8)

The exact reserve is 7/720. Reflection and swapping coordinates
give the other caps. At most one actual unit center belongs to each
cap, so there are at most four additional units and at most eight
units in total. The caps need not be assigned by an arbitrary tie;
adjacent caps are in fact disjoint since 2*b^2>M^2.

## 4. The one-thirtieth corollary used for near-axis normal inversion

The theorem includes |p_x|,|p_y|<=1/30. If this sharper hypothesis
is used directly in Sections 2--3, the exact constants become

    a=29/30, b=22/15,
    2*a^2+a+1/4-M^2=2827/3600,
    (M-b)^2+4*(M^2-b^2)=719/1200<1.                      (9)

In particular, any two actual unit centers in the same directional
cap n.c>=22/15 are impossible under (3), independently of a
four-square-junction hypothesis. Rotate the center coordinates so
n is horizontal and apply the final diameter estimate in (9).
This explicit one-cap consequence is available for excluding two
long-channel normals near the same common junction axis.

## 5. Scope and retained witness

The eight-square packing consisting of the four central centers
(+-1/2,+-1/2) and the four outer centers (+-3/2,0),(0,+-3/2), all
axis-aligned, lies in the smaller disk of squared radius 17/4 and
attains the count eight. Thus the ninth original unit remains
essential to the contradiction.

No claim is made about a four-square junction at an arbitrary
translation: the coordinate hypothesis (1) is essential to this
proof. A caller must separately establish it in the actual common
square frame. The source does not move a square, replace its mean,
select a new stress, run a numerical pose search, compile Lean,
trigger CI or change any original ledger flag.
