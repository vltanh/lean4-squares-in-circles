# Double-side bundles can be consolidated without increasing the packing radius

**Status:** reviewed local hand argument; root and independent full review
passed on 2026-10-30. This is a normalization of a minimizing packing together with its
physical stress. It is not a new catalog or a claim that an arbitrary
unchanged packing has no double-side bundle.

Use a physical stress satisfying the strict point-only VV convention and
the side-bundle geometry in
[BRANCHING_COMPONENT_SKELETON_DRAFT.md](BRANCHING_COMPONENT_SKELETON_DRAFT.md).
Suppose two different unloaded degree-two side transmitters U,V connect
the same retained endpoint bodies A,B. Their two paths form a double-S
bundle, of width one. The endpoints may be loaded or unloaded and may
have arbitrary other positive contacts.

**Local theorem.** One can move at most one of U,V within the containing
disk, then replace the two positive paths by one positive side-transmitter
path, with all the following properties:

* Every other square stays fixed, and all ten squares remain present and
  interior-disjoint.
* The force and torque applied to A and B by the bundle are unchanged.
  All other positive forces outside the bundle and all circle loads are
  unchanged.
* Exactly one previously active unloaded body becomes entirely unstressed.
  The other remains a balanced, unloaded, degree-two side transmitter.
* Every surviving positive point-only VV pair, its geometry and normal,
  is unchanged. In particular strictness, nonradiality, and incident
  diagonal avoidance survive.
* The positive graph is obtained by deleting one of the two subdivided
  paths. Component connectivity and each component's loaded bodies are
  unchanged, after omitting the now isolated unstressed body.

The theorem applies simultaneously to all loaded and unloaded retained
counts. Its consequence is that a minimum-active-body certificate can
be chosen without any double-S bundle. The exact certificate-selection
scope of that statement is specified in Section 5.

## 1. Parallel frames give an enclosed rectangular gap

The reviewed bundle reduction makes both endpoint supports sides and fixes
their frames parallel to the transmitters. Use local Cartesian coordinates
(a translation is allowed here) in which

```text
A=[-1,0] x I_A,       B=[1,2] x I_B,
U=[0,1] x [a,a+1],    V=[0,1] x [b,b+1],
b>=a+1,
```

where I_A and I_B are closed intervals of length one. The two transmitter
intervals have disjoint interiors. Each overlaps each endpoint interval
in positive length: a singleton intersection would be a point-only VV
contact carrying a side normal, forbidden by the selected convention.

Consequently, if `g=b-a-1>0`, both endpoint intervals contain `[a+1,b]`
in their relative interiors. Their length one gives `0<g<1`. The open
rectangle

```text
G=(0,1) x (a+1,b)                                   (1)
```

has its left, right, lower, and upper boundary sides in A,B,U,V,
respectively.

No other physical square meets G. Indeed the interior of any other square
is disjoint from the four closed obstacle squares: an interior point in
one of their boundaries would already force an overlap of interiors.
If its connected interior met G, it could not leave G without crossing
the occupied boundary. The entire square would therefore lie in the
closure of G. But every unit square, with arbitrary orientation, has
vertical projection length at least one, whereas G has height g<1.
This is impossible. Since a square is the closure of its interior, even
a boundary-only intersection with the open set G is impossible.

If g=0 there is no gap and no motion through it will be needed.

## 2. The two endpoint wrenches determine one common height

Let the two path force magnitudes be mu,nu>0. Force and torque balance on
each side transmitter makes its two horizontal endpoint forces have the
same height. Call these heights y_U and y_V. Thus

```text
y_U in [a,a+1] intersection I_A intersection I_B,
y_V in [b,b+1] intersection I_A intersection I_B,
y_U<=a+1<=b<=y_V.
```

The bundle's aggregate forces at A and B have magnitude mu+nu and the
common transverse application coordinate

```text
m=(mu*y_U+nu*y_V)/(mu+nu).                           (2)
```

Replacing the two forces at either endpoint by that total force at m
preserves its force and torque about the original disk center. If the two
heights differ, m is strictly between them and hence in the relative
interior of both I_A and I_B. If they agree, then g=0 and both original
paths already use that same height.

## 3. A transmitter can be placed at the aggregate height

If m belongs to either existing transmitter interval, retain that
transmitter at its present position. Otherwise m belongs to the gap
`(a+1,b)`. Move U upward by

```text
h=m-(a+1)+epsilon,
0<epsilon<min{b-m,1}.
```

Then `0<h<g`, and the moved square

```text
U_h=[0,1] x [a+h,a+h+1]
```

contains m in the relative interior of both vertical sides. Its newly
occupied strip lies in the empty rectangle G, apart from its boundary;
therefore it creates no overlap with any other square. Its old overlap
with U's position causes no problem because U is the body being moved.

The new square also remains in the containing disk. For each point u of
the old U, the point `u+(0,b-a)` belongs to V. Since
`0<h<b-a`, the corresponding point `u+(0,h)` is a strict convex
combination of those two points. Convexity of the disk gives containment
of every point of U_h. This argument uses the actual containing disk,
so translating the local coordinate frame in Section 1 has no effect.

The unused square V remains fixed. The same proof with vertical reflection
permits a downward motion of V if desired. In particular, when m is at
one endpoint of a nonempty gap, a sufficiently small motion into the gap
can place m in the retained transmitter side's relative interior too.
When g=0 and m is the common boundary height, either existing transmitter
may simply be used without motion.

Every selected endpoint pair still has positive-length shared sides. When
the original heights differ, m is in the interiors of I_A,I_B; a unit
transmitter interval containing m therefore has positive overlap with
both endpoint intervals, even if m is one of its endpoints. When the
heights agree, retain one original path and its original positive-length
overlaps. No point-only VV contact with a boundary normal is introduced.

## 4. Transfer the forces and preserve the physical certificate

Remove both original path stresses. On the retained, possibly moved,
transmitter, put horizontal opposite forces of magnitude mu+nu at height
m on its two vertical sides. They have zero resultant and zero torque.
Put the opposite forces at the same physical contacts on A and B.
Equation (2) preserves each endpoint's previous resultant and torque.
Keep every other positive contact force and every circle weight unchanged.

The unused transmitter now has no positive contact or circle force. It
remains a physical square in the packing. The retained transmitter remains
unloaded; if it moved, no circle force had to be transported because its
original circle weights were zero. All equilibrium and normalization
equations therefore remain valid.

Every positive pair in the removed and retained bundle is SS. No positive
point-only VV pair is moved, created, or assigned a different normal.
The selected strict/nonradial/nondiagonal conventions at those pairs
survive exactly.

Abstractly, the positive graph loses one degree-two path and retains the
other, with the same endpoint bodies. If the path chosen after motion was
the other original path, this is just the corresponding alternative
deletion. Thus connectivity of the component is preserved. Every loaded
body is unchanged, and a mixed component remains mixed because one of the
two unloaded transmitters remains active. No entirely loaded component is
created. Other components are unchanged.

A planar embedding with its loaded boundary order remains available by
deleting the unused path from the earlier embedding. No assertion that
this embedding must use the new force points as its edge routes is needed;
the selected planar theorem likewise uses the graph embedding. Its loaded
body order and exposed circle vertices are unchanged.

The stronger geometric condition behind the physical planar construction
is preserved as well: at every four-square junction, at most one of its
two opposite-quarter point-only VV pairs is positive. A newly created
junction must involve the moved transmitter. That transmitter has only
positive SS contacts, so its own opposite-quarter pair is not positive;
at most the other opposite pair can be positive. Junctions among unmoved
bodies were already present and retain the condition, and deletion of
positive edges cannot spoil it. Thus the physical contact routing and its
cyclic force-normal order can be reconstructed for the new packing by the
same planar construction. This preserves more than abstract graph
planarity and allows subsequent arguments using that physical order.

## 5. A precise minimum-active-body normalization

Begin with any radius-minimizing packing and the jointly selected physical
certificate from the preceding research. In particular, after
[SEVEN_RING_COMPLETE_CAPACITY.md](SEVEN_RING_COMPLETE_CAPACITY.md), it
has no entirely loaded positive component. Keep the following properties
as the normalization class:

```text
the same minimizing radius and ten physical squares;
normalized nonnegative physical force and torque balance;
strict, nonradial, nondiagonal surviving positive point-only VV normals;
a planar positive graph with the loaded vertices in their boundary order;
at most one positive opposite-quarter VV pair at each four-square junction;
no entirely loaded positive component.
```

This class is nonempty by the reviewed selection and seven-ring theorems.
Among all packing/certificate pairs in it, minimize the integer number of
active bodies, where a body is active if it has a positive contact force
or a positive circle weight. Such a minimum exists because the possible
numbers form a nonempty subset of `{1,...,10}`; no compactness of the
certificate subclass is being asserted.

If this minimum pair had a double-S bundle, Sections 1--4 would give
another pair in the same class with one fewer active body. This is a
contradiction. Therefore a certificate in this normalization class has
no double-S bundle, for every possible loaded/unloaded retained count.

As a consequence, every unloaded retained vertex has at least three
distinct retained neighbors. The only possible two-neighbor pattern in
the reviewed skeleton reduction was direct plus double-S. Also the
remaining parallel-bundle possibility is double-SS; diagonal bundles had
already been excluded by the original geometric reduction.

There is an important limit to this formulation. Motion can change
endpoints of unused geometric shared-side contacts. Thus this note does
not claim that every nonzero generic-selection polynomial written for the
old geometric packing remains nonzero after the motion. The explicitly
listed positive-normal, junction, and graph properties are the ones preserved.
Results requiring additional certificate properties must have their
compatibility checked before being applied to this normalized pair.
In particular, the no-entirely-loaded conclusion is retained here by
component preservation, not by silently rerunning the old polynomials.
