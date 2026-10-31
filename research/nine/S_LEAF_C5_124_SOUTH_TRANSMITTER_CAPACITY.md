# The C5 S124 south-side transmitter leaves room for at most two extras

Date: October 27, 2026.

**Status: complete hand exclusion of one exhaustive ordered attachment
domain, submitted for full root and separate independent review.**
The complementary ordered attachment remains explicit in Section 6.
This manuscript does not claim the entire original S124 gate closed.

## 1. Original graph and exact remaining domain

Retain the same nine actual interior-disjoint unit squares and the
original compatible certificate. The complete positive component is

    H--B_1--B_2--X--B_4--H,       H--L,

where L is the genuine S leaf, B_1,B_2,B_4 have their original
positive boundary loads, and X is the actual unloaded degree-two
transmitter. The true degrees are H3, all four cycle neighbors2,
and L1. All three completion units remain arbitrary and present.

This is the original C5 load124 graph, with the additional
hypothesis that B_4 is the last root neighbor in the actual
counterclockwise root-boundary order cut at the real leaf.
Thus X is adjacent to the last, rather than the first, root
neighbor. This condition refers to the actual embedding; it is
not imposed by changing the loaded labels.

The complete accepted reduction
S_LEAF_C5_124_ORDERED_ROOT_DOMAIN.md leaves, in the tilted high
case under consideration, the actual chart

    R<=sqrt(1105)/16,       d=sqrt(R^2−1/4)−1,
    1<d<61/60,
    H=[U−1,U] times [V−1,V],
    77/100<U<4/5,       3/5<V<2/3,
    U^2+V^2=d^2,
    P=(U,V),       e=P/d,
    L=P+[0,1]e+[-1/2,1/2]Je.                            (1)

Allowing U=4/5 in the physical argument below is harmless.
The original last normal and application are exactly one of

    South, at (qU/d,V−1),       0<q<=d;
    strict Southeast, at (U,V−1).                       (2)

Every application in (2) is its actual original application.
The original transmitter X keeps its actual width, normal,
both means, frame, force and torque. None will be deleted or
replaced by a hypothetical contact B_2--B_4.

We prove that these six actual units have room for at most
two additional units in the original circle.

## 2. A unit with center radius at most five sixths stays strictly west

The following lemma is purely physical.

**Lemma.** For an actual unit E interior-disjoint from H in (1),
if |c_E|<=5/6, every point of E has x<1/20.

Use the complete separating-axis theorem for the two actual
squares. There is a separating axis normal to an own side of
H or of E, including equality and all shared-point limits.

For an H side axis, the east alternative would force the
center's x coordinate to be at least U+1/2>5/6. The north
alternative similarly forces its y coordinate above V+1/2>5/6.
The south alternative forces

    (c_E)_y<=V−1−1/2<−5/6,

because V<2/3. All are impossible. The west alternative
already puts every E point at x<=U−1<=−1/5<1/20.

It remains to use an actual E side axis n directed from H
toward E. Its original physical separating inequality is

    c_E dot n>=h_H(n)+1/2.                              (3)

Since |c_E|<=5/6, this gives h_H(n)<=1/3.
If n_x>=0, the actual H support is strictly greater than
1/3: in the northeast cone use U>77/100 and V>3/5;
in the southeast cone use U>77/100 and 1−V>1/3.
Thus necessarily

    n=(-a,b) or (-a,-b),       a>0, b>=0, a^2+b^2=1.

The actual root supports give

    h_H(n)>=a/5+b/3,

strictly when b>0. Put

    K=5/6,       S=1/2+a/5+b/3.

Equations (3) and |c_E|<=K imply S<=K. For b>0 this
also gives 3a+5b<5, hence

    b<8/17,       a>15/17.                              (4)

Indeed 3a<5(1−b); square and divide by 1−b>0.
For b=0 the west conclusion is immediate, so assume b>0.

For a center of norm at most K and projection onto n at
least S, its largest possible x coordinate is bounded by

    (c_E)_x<=−aS+b sqrt(K^2−S^2).

This follows by resolving the center along n and its
perpendicular axis: the expression
−at+b sqrt(K^2−t^2) decreases for t>=S>0.
The actual x halfwidth of E is (a+b)/2. Therefore

    max_E x
      <=−a^2/5−ab/3+b/2+b sqrt(K^2−S^2).               (5)

Here S>=23/34+b/3, by (4). Consequently

    K^2−S^2<=2K(K−S)<=40/153−5b/9.

The one-variable cubic has the exact global bound

    b^2(40/153−5b/9)
      <=10240/1193859<1/100,                            (6)

on the interval where the right side is nonnegative.
Its maximum is at b=16/51. Thus the final radical term
in (5) is strictly less than 1/10.

On the other hand, (4) gives

    1/20+a^2/5+ab/3−b/2
      >=1/20+45/289−(7/34)b
      >=37/340>1/10.                                   (7)

Equations (5)--(7) imply max_E x<1/20. This proves the
lemma at every separating-axis and center-norm endpoint.
The exact reserve in (6) is 169859/119385900.

## 3. Every point of the actual last boundary neighbor is east of one twentieth

Write C=B_4 and sigma=1/sqrt(2)<71/100.
The real contact in (2) always has height V−1 in (−2/5,−1/3).
Its distance to the actual center of C is at most sigma.
Thus

    |(c_C)_y|<2/5+71/100=111/100.                       (8)

The center's x coordinate is positive. For a strict Southeast
root normal, the actual point has x=U>77/100>sigma, so this
is immediate.

For the South normal, the actual top support of C is V−1,
and its actual application has x=qU/d>0. Apply the complete
physical top-support lemma in
FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md, Section 3:
a unit with top height in [-1/2,0], with a positive-x top
point and center x<=0, has every corner norm squared at
most 9/4+sqrt(2). That is strictly less than R^2 here.
Since C physically touches the circle, its center cannot
have x<=0. The lemma includes aligned sides and all actual
side means; no degree-two equation is imported into C.

Every actual high-radius boundary center has norm greater
than 27/20. Together with (8) this gives

    (c_C)_x^2
      >(27/20)^2−(111/100)^2
      >(19/25)^2,

with final reserve 8/625. Since its sign is positive,

    min_C x>19/25−71/100=1/20.                          (9)

The real X--C contact and the lemma of Section 2 now force

    |c_X|>5/6.                                         (10)

Otherwise all points of X would have x<1/20 while every
point of C has x>1/20, contradicting that actual contact.
No application or force on X has been adjusted to obtain
(10); it is a consequence of the actual physical units.

## 4. The complete real path spans more than one hundred degrees

The root H contains the closed central disk D_(1/5).
Every other actual unit therefore avoids its open interior,
has distance from the origin at least 1/5, and has actual
center norm at least 7/10>2/3.

Apply MIXED_BOUNDARY_CONTACT_CENTER_GAP.md to the real
path B_1--B_2--X--B_4, using (10).
Its first edge is a boundary--boundary contact; its other
two are actual boundary--X contacts. Every other nonroot
center, including the real leaf and all three completion
units, is excluded from each closed minor edge arc.

The complete path consequently traverses one circular
orientation and, cut at the real leaf direction e, has
strictly ordered center lifts

    0<beta_1<beta_2<beta_X<beta_4<2pi.                  (11)

All contact arcs are the original minor arcs. Their sum
is less than 2pi, and their exact strict lower bounds are

    beta_2−beta_1>2pi/9,
    beta_X−beta_2>pi/6,
    beta_4−beta_X>pi/6.

In particular

    beta_4−beta_1>5pi/9.                                (12)

The two root-boundary endpoints both lie within 5pi/9 of
the real leaf direction. This is the complete force-free
physical estimate of
S_LEAF_C5_CENTRAL_ROOT_BOUNDARY_PATH_CAPACITY.md,
Section 3, whose premises (1) hold literally here.
For completeness its ingredients are: every actual
root-boundary port p has |P−p|<21/20, hence
|c_B−P|<9/5; |c_B|>27/20 and |P|=d>1 then give
cos(angle(c_B,P))>−1/6>cos(5pi/9).
Its four-side proof retains every root corner and actual mean.

Thus beta_1 and beta_4 each belong to

    (0,5pi/9) union (13pi/9,2pi).

They cannot both belong to the same component, because
(12) exceeds that component's length. Their order in (11)
therefore gives

    beta_1<5pi/9,       beta_4>13pi/9.                 (13)

Every completion center lies outside the whole interval
[beta_1,beta_4], by the three actual contact-gap exclusions.
This conclusion includes physically clear completion units.

## 5. The original leaf leaves only two forty-degree slots

Every nonroot unit has distance at least 1/5 from the
origin. The accepted force-free theorem
FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md
therefore gives each one a single connected open arc on
the radius-9/8 circle, longer than 2pi/9, containing the
circle point in its actual center direction.

The real S leaf's closed intersection with that circle
has exact halfwidth

    alpha=min(arccos(8d/9),arcsin(4/9))>pi/9.

This is the unchanged actual-leaf computation in Section 5
of the central-root/path theorem. The outer radial side is
inactive, and both strict angular inequalities hold for
the entire d<61/60 range.

A completion unit whose center is before beta_1 has its
whole connected open arc in (alpha,beta_1); one after
beta_4 has its whole arc in (beta_4,2pi−alpha).
Otherwise its connected arc would cross either the
closed occupied leaf arc or an endpoint unit's actual
interior circle point. Actual disjoint interiors forbid
either crossing, including weak arc endpoints.

By (13), both intervals have length strictly less than

    5pi/9−pi/9=4pi/9.

Each completion unit supplies a disjoint open arc longer
than 2pi/9. Hence at most one completion unit fits in
each interval. There are at most two completion units,
whereas the original nine-square packing contains three.
This contradiction excludes the entire domain of Section 1.

## 6. Exact remaining original obligations

This proof closes the complete high tilted S124 ordered
attachment in which the actual unloaded transmitter
touches the last South-or-Southeast root neighbor.

It does not relabel the other embedding into this one.
When the actual transmitter instead touches the first
West-or-Northwest root neighbor, Section 3 does not
supply (10) for that transmitter. That complete ordered
attachment remains a separate obligation.

The aligned strict-low root domain recorded in
S_LEAF_C5_124_ORDERED_ROOT_DOMAIN.md also remains separate.
All other root domains were already excluded there.

The proof retains the original true H3/X2 degrees, every
positive force and origin moment, both actual X means,
all physical circle masks and zero individual weights,
and all nine original squares. Its geometric capacity
argument changes none of them. No numerical pose,
compilation, CI, shared metadata or remote change is
a premise or an output.

