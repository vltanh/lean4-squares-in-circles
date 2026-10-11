# The interior capacity of a directed exterior contact cycle

## Theorem

Let unit squares with pairwise disjoint open interiors lie in D_R, where
R<2. Suppose a directed positive-contact-moment cycle consists of k distinct
squares, all of whose closed sets omit the origin. The meaning of its
orientation is that at every edge the separating normal n points from the
source square to the target and its actual contact point z satisfies
`z cross n>0`.

Join the two contact points in each cycle square by its straight chord.
For a square not in the cycle, let w_S be the winding number of this closed
polygonal path about any point of its open interior. It is independent of
that point. Then w_S is a nonnegative integer and

    sum_(S outside the cycle) w_S
      <= k max(C_k, 2C_k-1/2),
    C_k = (1/4) cot(pi/k).                                (1)

In particular the following capacity bounds hold:

| Number k of cycle squares | Total possible winding multiplicity of other unit squares |
| --- | --- |
| 3 | 0 |
| 4 | at most 1 |
| 5 | at most 1 |
| 6 | at most 2 |
| 7 | at most 3 |

No simplicity or planarity of the polygonal path is assumed. Repeated
contact points, overlapping boundary segments, and self-contacts of the
path are allowed. A square of winding zero is not bounded by this theorem:
it can lie outside the selected cycle and must still be accounted for in
the eight-square proof.

## 1. A sharp area cost for a chord of a unit square

Let a chord between two boundary points of a unit square have length d.
Each side of its supporting line cuts off area at least

    a(d) = (1/2) sqrt((d^2-1)_+),
    x_+ = max(x,0).                                      (2)

For d<=1 this states only nonnegativity. Suppose 1<d<=sqrt(2).
The endpoints cannot be on the same side of the square, and the chord
crosses its open interior.

If it joins adjacent sides, let r,s in [0,1] be the distances of its
endpoints from the common corner. Its length obeys `d^2=r^2+s^2`.
Since

    (1-r^2)(1-s^2)>=0,

we have `r^2 s^2>=d^2-1`. The corner triangle has area `rs/2`, at least
the quantity in (2). The complementary piece has area at least 1/2,
which also bounds (2), because `d^2<=2`.

If it joins opposite sides, choose coordinates giving endpoints
`(0,r),(1,s)`, with r,s in [0,1]. Then `d^2=1+(s-r)^2`, and the smaller
cut trapezoid has area

    min(r+s, 2-r-s)/2 >= |s-r|/2 = a(d).

This proves (2), including endpoint degeneracies. It is sharp for every
1<=d<=sqrt(2), using a chord from a corner to the opposite side.
It also implies the weaker bound used in the four-cycle note:

    a(d) >= (d^2-1)_+/2,                                 (3)

because sqrt(x)>=x for 0<=x<=1.

## 2. Angular monotonicity makes every winding number nonnegative

For each exterior square S, let v be its nearest point to zero. Convexity
of the square and the minimizing property of v give

    v dot z >= |v|^2>0       for every z in S.

All point arguments in S therefore have a common lift into the open
interval `(arg(v)-pi/2,arg(v)+pi/2)`.
HUMAN_GLOBAL_CYCLE_CLOSURE.md, section 3, proves that its incoming
positive-moment contact precedes arg(v), and its outgoing contact follows
arg(v), in this lift. In particular, the argument increment from the
incoming point to the outgoing point is in [0,pi).

The argument along the chord between these contacts is nondecreasing.
For a nonradial chord this follows directly from

    d/dt arg(a+t(b-a)) = (a cross b)/|a+t(b-a)|^2 > 0;

for a radial chord the argument is constant. The chord avoids zero because
it lies in the exterior square. Thus the whole polygonal path has a
nondecreasing lifted argument.

Here is why this implies more than a nonnegative winding number about zero.
Choose a ray from zero whose angle avoids the finitely many vertex angles
and angles of radial edges. Every intersection of this ray with the path
crosses the ray in the positive angular direction. For a point p on the
ray and off the path, its winding number is the number of path crossings
on the part of the ray beyond p. Indeed the winding number is zero at
infinity and increases by one at each positive crossing when the base
point moves inward along the ray. It is therefore nonnegative.

Every connected component of the complement of the path contains points
on such generic rays. The winding number is constant on each component,
so it is nonnegative everywhere off the path. Denote this integer-valued
function by w(p).

The open interior of any square not in the cycle avoids every closed cycle
square. To check the boundary issue, an open set containing a point of a
closed square also contains interior points of that square; such a point
would contradict pairwise interior disjointness. Thus the open interior
of the other square avoids the path. It is connected, so w is constant
there. This justifies the number w_S in the theorem.

If a central square contains zero in its open interior, the positive
winding theorem in HUMAN_GLOBAL_CYCLE_CLOSURE.md makes its w_S positive.
Replacing each two-segment nearest-point path there by its chord is a
homotopy inside the corresponding convex cycle square, avoiding the entire
open central square, so it preserves that winding number.

## 3. Count the inward pieces with winding multiplicity

Write d_i for the chord length of cycle square S_i. If d_i>1, that chord
crosses the open interior of S_i and cuts it into two open connected
pieces. No other chord can enter either piece: each other chord lies in
a different closed square. The winding number is constant on each cut
piece. Across the oriented chord its value on the left exceeds its value
on the right by one. Since all winding numbers are nonnegative, its value
on the left cut piece is at least one.

This jump calculation takes place at an interior point of S_i. No other
edge of the path passes through that point, so coincident boundary chords
elsewhere do not affect it. The left piece has area at least a(d_i) by
(2). If d_i<=1, its assigned lower area cost is zero and no jump argument
is needed.

These cut pieces have disjoint interiors. They are also disjoint from the
open interiors of all squares not on the cycle. Since a unit square has
area one, integrating the nonnegative winding function gives

    sum_(S outside the cycle) w_S + sum_i a(d_i)
        <= integral_(plane) w(p) dp
         = (1/2) sum_i z_i cross z_(i+1).                (4)

Here z_i are the cyclic contact points. The last equality is the signed
shoelace formula with winding multiplicity. One elementary justification
is to cut the polygonal path at its finitely many intersections and apply
the ordinary area formula to the resulting faces, with their integer
winding coefficients. Alternatively triangulating the oriented path from
one auxiliary point gives the same identity by cancellation of internal
edges. Boundaries and the path itself have area zero.

The nonnegativity of w is what permits (4) for a nonsimple path. Taking
only the unsigned area of an assumed Jordan polygon would not justify
this step.

## 4. A polygonal area inequality with its proof

For any closed polygonal path with k vertices and consecutive side lengths
d_1,...,d_k, its signed area A satisfies

    A <= C_k sum_i d_i^2,
    C_k = (1/4) cot(pi/k).                               (5)

This does not require the path to be simple or convex. Here is a direct
finite Fourier proof. Identify the plane with the complex numbers. Write

    z_j = sum_(l=0)^(k-1) b_l exp(2pi i l j/k),
    b_l = (1/k) sum_(j=0)^(k-1) z_j exp(-2pi i l j/k).

The finite geometric-series identity makes the exponentials orthogonal.
Expansion followed by that identity gives

    A = (k/2) sum_l |b_l|^2 sin(2pi l/k),
    sum_j |z_(j+1)-z_j|^2
      = 4k sum_l |b_l|^2 sin^2(pi l/k).

The l=0 terms vanish in both expressions. For 1<=l<=k-1, the ratio of
the area coefficient to the squared-edge coefficient is

    (1/4) cot(pi l/k) <= (1/4) cot(pi/k),

because cotangent decreases on (0,pi). Summing the coefficient inequalities
with the nonnegative weights |b_l|^2 proves (5). Thus no unproved extremal
polygon assertion is being imported.

## 5. Complete the capacity estimate

Combine (3)--(5), and put x_i=d_i^2 in [0,2]. Then

    sum_(S outside the cycle) w_S
       <= sum_i [C_k x_i - (x_i-1)_+/2].                 (6)

The summand is piecewise affine on [0,1] and [1,2]. Its maximum is
`max(C_k,2C_k-1/2)`, attained at one of x=1 or x=2.
This proves (1). Keeping the sharp square-root cost instead yields the
stronger unmaximized inequality

    sum_(S outside the cycle) w_S
       <= sum_i [C_k d_i^2 - sqrt((d_i^2-1)_+)/2],       (7)

which can be useful when actual chord lengths are known.

Here are exact comparisons giving the integer table.
For k=3,4,6 the constants C_k are respectively
`1/(4sqrt(3)), 1/4, sqrt(3)/4`; all are below 1/2. Their total bounds
are `sqrt(3)/4<1`, `1`, and `3sqrt(3)/2<3`.

For k=5, use `tan x >= x+x^3/3` on [0,pi/2). This follows by integrating
`tan'(x)=1+tan(x)^2>=1+x^2`, after first noting tan(x)>=x.
As `pi/5>3/5`,

    tan(pi/5)>84/125>5/8.

Hence `cot(pi/5)<8/5`, so `C_5<2/5<1/2` and `5C_5<2`.

For k=7, `pi/7>4/9` and the same tangent inequality give

    tan(pi/7)>4/9+(4/9)^3/3=1036/2187>7/15.

Thus `C_7<15/28`. Both `C_7` and `2C_7-1/2` are strictly below 4/7,
so their sevenfold maximum is strictly below 4. Integrality and
nonnegativity of the winding numbers give the stated table.

## 6. What this forces in an eight-square packing

An exterior directed cycle surrounds the entire open central square, with
positive winding. Consequently:

* For a five-square cycle, the central square has winding exactly one and
  both of the other two squares have winding zero. Neither additional
  square can be hidden inside the cycle.
* For a six-square cycle, the one additional square besides the central
  square either has winding zero or one. If it has winding one, the
  central square also has winding one.
* For a seven-square cycle there is only the central square outside the
  cycle's vertex set. The bound alone does not exclude this case, as it
  must not: it includes the candidate's exterior ring.

These are rigorous placement alternatives, not a radius lower bound at
R_dagger. The next step must control the winding-zero squares in the
five- and six-cycle cases, and derive the sharp projected obstruction for
the surviving long cycles. Cycles through the central square also remain
a separate case. No global closure is inferred solely from (1).
