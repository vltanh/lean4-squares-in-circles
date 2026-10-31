# Robust physical capacity near the opposite-return side configuration

Date: October 30, 2026. Author: pocket_capacity continuation.

**Status: complete conditional geometric theorem with exact rational finite
data.** The six-core theorem below excludes even a seventh square throughout
an explicit neighborhood of the listed twenty-four actual vertices. It does
not yet assert that the entire opposite-return, side-N branch enters that
neighborhood. The original branch ledger is unchanged. No compiled Lean or
independent kernel replay is claimed.

The argument uses actual square interiors, their actual vertices, and the
original containing disk. It is independent of contact graphs, endpoint
degrees, physical circle masks, selected normals, force magnitudes, and side
means. Consequently the same conditional theorem applies to these six units
inside any larger positive component, with every additional unit retained.
All coordinates are in one original disk-centered orthonormal frame. Applying
one orthogonal map fixing that center to the entire actual configuration and
the reference/cap data transports the theorem, including whole-data reflection.

## 1. A general core-capacity theorem

Let distinct actual unit squares have pairwise disjoint interiors and lie in
the disk about the original origin with squared radius at most

    Q = 1105/256.

Select k of those actual squares as cores, retaining all other units. For each
core, name its four actual vertices in an order paired with four rational
reference points. The rational reference points need not themselves form an
exact unit square. Suppose each actual vertex is at Euclidean distance at
most epsilon from its paired reference, where 0<epsilon<1/2.

Set M=91/60. Suppose a finite closed-box subdivision of [-M,M]^2 has leaves
of the following three kinds:

1. Every point of the leaf has squared norm at least M^2.
2. Every point of the leaf is at distance strictly less than 1/2-epsilon
   from a specified convex combination of the four reference points of one
   core square.
3. The whole leaf lies in one of j fixed closed disks, each of radius
   strictly less than 1/2.

Then the entire packing has at most k+j squares. In particular j=0 excludes
any additional square at all.

### 1.1. The center bound and physical exclusions

For the center x of any unit square with orthonormal side directions e,f,
the largest squared norm of its four corners is

    |x|^2 + 1/2 + |x dot e| + |x dot f|
       >= |x|^2 + |x| + 1/2.

The inequality is the elementary comparison between the sum of the absolute
coordinates and their Euclidean norm. Since

    M^2 + M + 1/2 - Q = 31/57600 > 0,

every actual square center has |x|<M. Thus no center lies in a leaf of the
first kind, including a leaf whose minimum squared norm is exactly M^2.

Two distinct square centers have distance at least one: their open
incircles of radius 1/2 lie in their respective square interiors. Also, if
y is **any actual point of a closed core square** and x is the center of
another square, then

    |x-y| >= 1/2.                                           (1)

If the distance were smaller, y would be in the other square's open
incircle. A small neighborhood of y in that incircle contains an interior
point of the core, even when y is on a side or vertex of the core. The two
actual interiors would meet. This proves (1) without asserting that a
boundary vertex itself is an interior point.

A convex combination of paired actual vertices lies in the actual closed
core square. Its distance from the same convex combination of reference
points is at most epsilon, by the triangle inequality and the nonnegative
weights summing to one. A leaf of the second kind therefore puts any
purported additional center at distance strictly less than 1/2 from an
actual core point, contradicting (1). The strict leaf comparison is what
preserves every closed perturbation endpoint.

All remaining centers lie in the union of the j disks. Each disk has
diameter strictly less than one and therefore contains at most one of
these centers. Assigning each center to any disk containing it gives at
most j additional centers. This proves the general theorem.

## 2. An exact six-core neighborhood with zero remaining capacity

The data file

    certificates/physical_two_opposite_side_six_core_capacity.json

lists the six cores V,A,D,B,C,N, their four rational reference points each,
and the exact error bound

    epsilon = 2/25.

Every reference coordinate is the displayed integer in the data file divided
by 10^7. Their discovery was suggested by an exploratory six-square pose of
the opposite-D-vertex return with side N. That numerical pose is not used as
a theorem, root certificate, or exhaustive description of the branch. Only
the rational data and the explicit actual-vertex neighborhood enter this
result.

The finite exact cover has the following dimensions:

| Item | Exact value |
| --- | ---: |
| Core squares | 6 |
| Vertex neighborhood radius | 2/25 |
| Witness grid denominator | 16 |
| Total tree nodes | 289 |
| Closed-box split nodes | 72 |
| Core-exclusion leaves | 140 |
| Outside-center-disk leaves | 77 |
| Capacity disks | 0 |
| Maximum depth | 8 |
| Minimum core squared reserve | 103504826267363/230400000000000000 |

Each core witness uses the exact weights

    (1-i/16)(1-j/16), (i/16)(1-j/16),
    (i/16)(j/16),     (1-i/16)(j/16),

for named integers 0<=i,j<=16. They are nonnegative and sum to one. Each
core leaf has maximum squared distance to its witness strictly smaller than

    (1/2 - 2/25)^2 = (21/50)^2.

The displayed positive reserve is the smallest difference over all those
leaves. The entire center disk is therefore excluded for every additional
square, with no residual capacity region. By Section 1 the whole packing
has at most **six** squares in this neighborhood.

In particular this excludes nine actual squares, with all three completing
units arbitrary. It even excludes any attempt to append just one further
unit to the six named squares. No equation on B or C is shortened or omitted
to claim their original stars; their stars are simply unnecessary to this
physical capacity conclusion.

## 3. Exact replay and direct coordinate-interval entry

The separate generic checker and generator are

    ../../scripts/n9_core_capacity_family.py.

They retain all four closed children at every split, reject repeated or
unreachable tree nodes, check every leaf by integer/rational arithmetic,
and validate the actual number and strict diameters of the residual disks.
An empty residual-disk list is allowed and is the certificate in Section 2.
The claimed total is checked to equal the number of cores plus the number
of residual disks. The proof checker performs no floating-point operation,
sampled sign decision, or numerical optimization.

Replay and all-rational regeneration are respectively:

    python scripts/n9_core_capacity_family.py \
      research/nine/certificates/physical_two_opposite_side_six_core_capacity.json

    python scripts/n9_core_capacity_family.py \
      research/nine/certificates/physical_two_opposite_side_six_core_capacity.json \
      --regenerate

For algebraic parameter boxes, the function
`verify_actual_vertex_dyadic_boxes(data, vertex_boxes, precision_bits=44)`
can replace the uniform Euclidean neighborhood premise by direct actual
coordinate intervals. Its input shape is

    [number of cores][four vertices][x or y][lower or upper].

Each raw integer z denotes z/2^precision_bits. The caller must establish
that the actual vertices lie in those closed intervals. The function does
not establish this entry premise, nor does it assert uniqueness of an
algebraic solution.

For a core leaf [a,b] x [c,d], the exact convex combination of actual-vertex
intervals gives a witness box [l,h] x [m,n]. The direct sufficient predicate
is

    max(|a-h|,|b-l|)^2 + max(|c-n|,|d-m|)^2 < 1/4.        (2)

It puts every leaf point at distance strictly less than 1/2 from the same
actual convex witness, uniformly over the full coordinate box. After
multiplying all coordinates by a common positive integer D, the hot-loop
test is the equivalent integer inequality

    D^2 - 4*(dx^2+dy^2) > 0.

Thus a successful direct check implies the same capacity theorem without
requiring each entire coordinate interval to fit a prescribed error ball.
An unsuccessful check means only that this input box has not been proved
by this particular finite cover. It is not a feasibility assertion.

## 4. Remaining original entry obligation

The original opposite-return side-N branch is wider than the particular
neighborhood certified here. A whole-branch application must supply a
complete original-domain cover whose surviving cells satisfy one of these
actual-vertex entry predicates, or prove a stronger geometric enclosure
uniformly. The full force, torque, circle, singleton-owner and side-N
relations are available for that task. This source does not replace that
remaining obligation by a sampled pose or a fitted numerical region.

## 5. A five-core theorem independent of the actual N placement

The second completed certificate

    certificates/physical_two_opposite_side_five_core_capacity.json

uses just the first five listed cores V,A,D,B,C, with the same reference
coordinates, grid denominator 16, and closed vertex-error radius 2/25. It
does not place N. Instead all centers of remaining units, including the
actual N and all three additional units of a nine-square packing, must lie
in the following three rational disks:

| Disk | Center | Radius |
| --- | --- | --- |
| 0 | (-829/1000,236/1000) | 49/100 |
| 1 | (-1336/1000,23/1000) | 49/100 |
| 2 | (-1287/1000,547/1000) | 49/100 |

Every disk has squared diameter 2401/2500<1. The exact cover has 269 nodes,
67 split nodes, 115 core-exclusion leaves, 67 outside-disk leaves, and 20
capacity-disk leaves. Its maximum depth is 8. Its smallest core squared
reserve is again 103504826267363/230400000000000000, strictly positive.

The general theorem therefore gives at most 5+3=8 total squares. This
version is weaker in the number of allowed squares but has the more useful
entry premise: it requires only the twenty actual V,A,D,B,C vertices and is
uniform over every possible physical placement, side mean, direction,
orientation, and original force at N and the three completing units.

The same generic replay and direct dyadic-coordinate interface apply by
supplying this data file. It is a separate proved conditional neighborhood;
its use for an entire original branch still requires the complete entry
obligation in Section 4.

## 6. Three profiles for the lower-radius loaded-endpoint family

Three further completed five-core certificates use a new common rational
reference, suggested by a necessary loaded-endpoint geometry with B--C
distance one. The discovery parameters were approximately
s=0.1699739799331104, b=0.33044391304347825, d=0.9351929160060206; the
suggested squared radius was approximately 3.99497162216. These floats are
not part of any proof predicate and do not assert the existence of a full
original stressed realization. The complete exact reference vertices are
the twenty integer pairs in each data file, divided by 10^7.

All three reference lists have order V,A,D,B,C. In these files the B and C
reference vertices have the order produced by

    center + se*own_axis + sw*transverse_axis,
    (se,sw) = (-1/2,-1/2), (1/2,-1/2),
              (1/2,1/2), (-1/2,1/2).

An algebraic caller must pair the corresponding actual vertices with this
order, or reorder its complete actual vertex boxes accordingly. No force
direction is reselected by such a relabeling of the four corners.

| Data file in `certificates/` | Radius premise | Vertex error | Nodes | Leaves | Depth |
| --- | --- | ---: | ---: | ---: | ---: |
| `physical_two_opposite_side_loaded_low_five_core_capacity.json` | R^2<=1105/256 | 1/25 | 229 | 172 | 8 |
| `physical_two_opposite_side_loaded_radius_two_five_core_capacity.json` | R^2<=4 | 2/25 | 181 | 136 | 7 |
| `physical_two_opposite_side_loaded_radius_two_wide_five_core_capacity.json` | R^2<=4 | 3/25 | 261 | 196 | 9 |

The first profile uses M=91/60 as before. The other two use the stronger
exact center bound M=36/25. Section 1.1 applies verbatim because

    (36/25)^2 + 36/25 + 1/2 - 4 = 17/1250 > 0.

Thus these two profiles require the **additional actual radius premise
R<=2**; they cannot be invoked solely from the original larger Q bound.
The exact checker validates this arithmetic from each file's rational
`radius_squared_upper` and `center_bound` fields. Its direct vertex-box
interface does not establish the radius premise on the caller's behalf.

For the widest profile, the three exact disk centers are

    (-1331/1000,256/1000),
    (521/1000,1336/1000),
    (-692/1000,72/1000),

and each disk radius is 499/1000. Their squared diameters are
249001/250000<1. The cover has 65 split nodes, 112 core leaves, 45
outside-center-disk leaves, and 39 disk-capacity leaves. Its least core
squared reserve is 47299528959/100000000000000, strictly positive.

The narrower radius-two profile has least reserve
27257143/195312500000. The original-radius profile has least reserve
35190659680391/230400000000000000. Both use three disks of radius 49/100,
whose squared diameters are 2401/2500<1.

Each profile therefore excludes nine actual squares using only the twenty
actual V,A,D,B,C vertices and its explicit radius premise. The remaining
four squares, including N, are arbitrary. The generic exact replay and
direct coordinate-interval checker apply without any sampled geometric
oracle. As with the preceding profiles, a complete original parameter cover
is still needed to establish entry on the whole feature.
