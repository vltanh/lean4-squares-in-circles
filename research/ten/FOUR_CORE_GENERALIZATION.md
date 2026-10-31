# Parallel four-inner-square cores: a projection-graph normal form

**Status:** independently reviewed structural hand reduction (2026-10-29).

Four parallel unit squares whose centers lie in the **open** unit disk have
one of two types of arrangement: a coordinate line separates two whole
squares from the other two, or the centers have the pinwheel order described
below. The pinwheel alternative occurs even with two center norms below
`13/20` and the other two strictly between `9/10` and `1`.

This is a structural reduction for parallel cores only. It is not a
completion bound, does not normalize the core to two exact rows, and does
not constrain the orientations of additional squares. The exact example
in Section 3 leaves six available abstract outer arcs, so its physical
completion remains an additional obligation.

## 1. The only projection graphs are two disjoint edges and a four-vertex path

Rotate coordinates to the core's common edge directions. Let `G_x` join
two centers when their horizontal coordinate difference is strictly less
than one. Thus an edge means that the open horizontal projections of the
two unit squares overlap. Define `G_y` similarly. Packing implies that
`G_x` and `G_y` have disjoint edge sets.

Neither graph has a triangle. For instance, three pairwise overlapping
horizontal projections would force all three vertical center differences
to be at least one. Their vertical span would be at least two, contrary
to all centers lying in the open unit disk. Neither graph has an
independent set of three: three horizontal center coordinates with all
pairwise differences at least one likewise span at least two.

A triangle-free graph on four vertices with no independent triple has
maximum degree at most two: three neighbors of a vertex would have to be
pairwise nonadjacent. A four-cycle is impossible for an interval graph.
For completeness, choose in a proposed induced four-cycle the interval
with smallest right endpoint. Its two neighbors both extend to that
endpoint and start before it, so they overlap each other, giving a
triangle. The graph is consequently a union of paths. The absence of an
independent triple leaves exactly

```text
P4: a path on four vertices, or
2K2: two disjoint edges.
```

All statements use open projection intervals, so contacts at coordinate
difference exactly one are handled without an implicit strict-separation
assumption.

## 2. The dichotomy and the pinwheel order

If, say, `G_x=2K2`, the two connected components occupy disjoint horizontal
projection intervals. A vertical line between them separates the two
whole squares of one component from the two of the other. The horizontal
version follows when `G_y=2K2`. This gives a line separating two pairs,
not equal row heights or touching squares within a pair.

Otherwise both graphs are `P4`. Number the centers in increasing horizontal
order as `A,B,C,D`. The path edges in `G_x` are precisely `AB,BC,CD`.
Indeed an edge skipping an intermediate center would give a triangle,
and the connected graph must join each successive pair. Thus

```text
x_A < x_B < x_C < x_D,
x_B-x_A<1, x_C-x_B<1, x_D-x_C<1,
x_C-x_A>=1, x_D-x_B>=1.
```

The complement of this path is the path with edges `AC,AD,BD`. Since
`G_y` has three edges and is disjoint from `G_x`, it is exactly that
complement. After a vertical reflection its order is therefore

```text
y_C < y_A < y_D < y_B,
y_A-y_C<1, y_D-y_A<1, y_B-y_D<1,
y_D-y_C>=1, y_B-y_A>=1.
```

These inequalities are also sufficient for pairwise disjointness of the
four axis-parallel squares: `AB,BC,CD` separate vertically, while
`AC,AD,BD` separate horizontally. They describe the complete pinwheel
alternative in the open-unit-disk setting.

## 3. An exact localized pinwheel with abstract gap capacity six

Take the four axis-parallel unit squares centered at

```text
A=(-3/4,-13/25),       B=(-9/40,11/20),
C=(1/4,-11/20),       D=(31/40,23/50).
```

Their squared center norms and farthest squared vertex norms are

| Square | Center norm squared | Farthest vertex norm squared |
| --- | --- | --- |
| A | `8329/10000` | `26029/10000` |
| B | `113/320` | `521/320` |
| C | `73/200` | `333/200` |
| D | `32489/40000` | `101889/40000` |

Every center is strictly inside the unit disk, `B,C` have norm below
`13/20`, and `A,D` have norm above `9/10`. Every square lies well inside
the containing disk of squared radius `9/2`.

The six separation checks are

```text
AB: y_B-y_A=107/100,   BC: y_B-y_C=11/10,
CD: y_D-y_C=101/100,
AC: x_C-x_A=1,         BD: x_D-x_B=1,
AD: x_D-x_A=61/40.
```

The successive horizontal differences are `21/40,19/40,21/40`, while
`y_D-y_A=49/50<1`. Both projection graphs are therefore `P4`, exactly as
in Section 2. All four horizontal coordinates and all four vertical
coordinates are distinct. In particular this core is not any of the
exact common-frame two-row cores in the existing completion theorems.

Put `r=sqrt(1+1/sqrt(2))`. The squares B and C lie wholly inside the test
circle, since their farthest squared vertex norms are below `17/10<r^2`.
The traces of D and A are respectively

```text
[alpha_D,beta_D],       [pi+alpha_A,pi+beta_A],
alpha_D=acos((51/40)/r), beta_D=asin((24/25)/r),
alpha_A=acos((5/4)/r),  beta_A=asin((51/50)/r).
```

Their outward corners are outside the test circle, and their other three
corners are inside; this also verifies that these are their complete
traces. The following strict bounds suffice:

```text
pi/16 < alpha_A,alpha_D < pi/4,
pi/4 < beta_A,beta_D < 5pi/16.
```

Here `r^2>17/10` and `cos(pi/8)>23/25` give

```text
r^2 cos^2(pi/16) > (17/10)(24/25)=204/125>(51/40)^2,
```

proving the lower alpha bound. The cosine estimate follows by squaring
and using `sqrt(2)>7/5`. Also `sin(pi/8)>3/8`, by squaring and using
`sqrt(2)<23/16`, gives

```text
r^2 sin^2(5pi/16) > (17/10)(11/16)=187/160>(51/50)^2,
```

proving the upper beta bound. The two middle bounds follow from
`r^2<7/4`: both outward x-coordinates exceed `1>r/sqrt(2)`, and
both outward y-coordinates are at least `24/25>r/sqrt(2)`.

The complementary gaps thus have lengths

```text
pi+alpha_A-beta_D,       pi+alpha_D-beta_A,
```

and each lies strictly between `3pi/4` and `pi`. Each can accommodate
three disjoint abstract arcs of length `pi/4`, with positive clearance,
and neither can accommodate four. The abstract gap capacity is exactly
six.

As in the earlier [localized gap obstruction](LOCALIZED_FOUR_CORE_GAP_OBSTRUCTION.md),
this is a four-square core, not a ten-square packing. It shows that a
proof for parallel four-inner cores must handle both the line-separated
and pinwheel alternatives and use more than the minimum outer-arc length.

## 4. A general narrow-channel filling lemma

The following exact geometric rule makes part of the virtual-obstacle
idea rigorous. Let `0<w<1`, and suppose the two horizontal segments

```text
[L,U] x {a},       [L,U] x {a+w}
```

belong to the union of fixed closed unit squares. Let S be another unit
square, with arbitrary orientation and interior disjoint from all fixed
squares. If `U-L>w`, then S's interior is disjoint from the closed
rectangle

```text
J=[L+w/2,U-w/2] x [a,a+w].                         (1)
```

Thus J may be added as a virtual obstacle without excluding any actual
additional square. No containing-circle hypothesis is needed.

To prove this, recall first that no interior point of S can belong even
to the boundary of a fixed square: a neighborhood of such a point would
meet that fixed square's interior. Suppose that an interior point p of S
lay in the open channel `(L,U) x (a,a+w)`, and let c be S's center. If
`L<c_x<U`, the segment from p to c forbids c from lying above or below
the channel: its first crossing of one of the two fixed segments would
be an interior point of S. But c cannot lie inside the channel either,
because S's open inscribed disk has radius `1/2` and `w<1`; a vertical
line through c then crosses one of the fixed segments in S's interior.
Consequently `c_x<=L` or `c_x>=U`.

Suppose `c_x<=L`; the other case is the horizontal reflection. For every
`x` strictly between L and `p_x`, the segment cp supplies an interior
point of S at that horizontal coordinate. Its vertical section lies
wholly between a and `a+w`: any connected section extending beyond one
of these heights would cross a fixed segment in S's interior. The
section length is therefore at most w.

For an axis-parallel unit square every nonempty interior vertical
section has length one, immediately a contradiction. Otherwise choose
`c_0>=s_0>0`, `c_0^2+s_0^2=1`, for the absolute direction cosines of its
edges, and put `h=(c_0+s_0)/2`. At a horizontal coordinate to the right
of its center the section length is

```text
min(1/c_0, (c_x+h-x)/(c_0 s_0)).
```

Since `w<1<=1/c_0`, its being at most w implies

```text
max_x(S)=c_x+h <= x+c_0 s_0 w <= x+w/2.
```

Letting x decrease to L proves `max_x(S)<=L+w/2`. Every interior point
of S has strictly smaller horizontal coordinate than this maximum. Hence
an interior point p in the channel must have `p_x<L+w/2`. Reflection
gives `p_x>U-w/2` for a center beyond the other end. Both exclude the
rectangle (1), including its vertical sides. Its horizontal sides
already belong to the fixed obstacles. This proves the lemma.

For the pinwheel in Section 3, the whole top segment

```text
[-29/40,3/4] x {1/20}
```

belongs to B or D, and the whole bottom segment with height `-1/20`
belongs to A or C. Taking `w=1/10` gives the valid virtual obstacle

```text
[-27/40,7/10] x [-1/20,1/20].                     (2)
```

Every additional unit square avoids the interior of (2), indeed its
interior avoids the entire closed rectangle. This joins the two core
rows across their narrow central channel. It does not fill the much
larger exposed corner regions, so the existing solid-block completion
theorem cannot yet be applied. A capacity bound using this filled core
remains open.
