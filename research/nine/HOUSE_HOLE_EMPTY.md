# Every positive five-body house has empty bounded completion regions

**Status: complete hand region theorem; root and independent full hand audits passed.**
Work in the selected physical certificate and the declared window
\[
                 79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Let the positive component be the house graph, labeled by the edges
\[
                 13,\quad14,\quad15,\quad24,\quad25,\quad35.
\tag{2}
\]
Its roof triangle is 1--3--5--1; its four-cycle is
1--4--2--5--1. All additional physical squares and all actual shared
application means are retained.

**Theorem.** Neither bounded region of this house can contain another
unit square. Thus all four completion squares in the house branch of
C1.5.b0 must be exterior. This holds for every positive-load mask and
all zero-weight physical circle contacts. The joint exterior capacity
and the parent coarse cell remain open.

## 1. The complete equality consequence for any four-square ring

Sections1--2 of FOUR_CYCLE_LEAF_HOLE_EMPTY.md prove the following
geometric implication, before using any leaf or load condition:

> If a selected physical four-cycle encloses an interior-disjoint unit
> square, the four ring bodies form the aligned cross around that unit.
> Their four actual cycle contacts are point-only vertex/vertex contacts.

To identify exactly which input is being used, choose the four actual
cycle applications p_i and chord lengths ell_i<=sqrt(2). The winding
and area proof, including arbitrarily small physical routing at shared
junctions, gives
\[
 1\le A(P)-\frac12\sum_i\sqrt{\max(\ell_i^2-1,0)}
 \le\sum_i\left(\frac{\ell_i^2}{4}
              -\frac12\sqrt{\max(\ell_i^2-1,0)}\right)\le1.
\tag{3}
\]
Opposite coincident vertices give zero winding; consecutive coincident
vertices give a triangle of area at most sqrt(3)/2<1. Thus neither
case hides an inner unit. Equality in (3) gives every ell_i=1 and a
unit contact polygon P. Its chords must be full outward sides of the
ring bodies, since any inward occupied area would make (3) strict.
This is exactly the aligned cross. The argument uses no absence of
additional positive edges at the ring vertices.

After a rigid motion, write that cross as
\[
\begin{aligned}
 E&=[1/2,3/2]\times[-1/2,1/2],\\
 N&=[-1/2,1/2]\times[1/2,3/2],\\
 W&=[-3/2,-1/2]\times[-1/2,1/2],\\
 S&=[-1/2,1/2]\times[-3/2,-1/2].
\end{aligned}
\tag{4}
\]
The selected normals from E to N and S have strictly negative first
coordinate: the two contacts are vertices of both squares, and the
retained point-normal convention strictly exposes those vertices.

## 2. A third neighbor touching an adjacent cross body cannot balance E

Suppose E has zero circle load and exact positive degree three. Its
neighbors are N,S and another unit square V, where V physically
touches at least one of N or S. The V contact may have any owner and
may be a shared side with an arbitrary actual mean.

Let m be the actual outward unit normal from E toward V. We claim
\[
                                  m_x\le0.
\tag{5}
\]
If m_x>0, every maximum-m support point q of E has q_x=3/2.
Choose the actual EV application q. It is simultaneously a minimum-m
support point of V. The support-span lemma from
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Section1, with u=-e_x,
gives
\[
                    \max_{v\in V}(-e_x)\cdot(v-q)<1,
\]
because m dot(-e_x)<0. Consequently every point of V satisfies
\[
                                  v_x>1/2.
\tag{6}
\]
But both N and S have maximum first coordinate exactly1/2. Equation(6)
prevents V from physically touching either, a contradiction. This
proves (5), including every shared or endpoint application.

Both other positive E reactions have strictly negative first
coordinate. The positive weighted sum of the three pair normals
therefore has negative first coordinate, whereas zero circle load
requires that sum to vanish. This contradiction proves a radius-free
local cross obstruction. No force or degree condition at V,N,S was
used.

The same assertion holds at any of the four cross bodies by rotation.
It is distinct from the unloaded-diamond-hub theorem: V needs to touch
only one adjacent ring neighbor, and the complete cross geometry is
essential here.

## 3. One house hub is always an unloaded degree-three cross body

The roof vertex3 has positive degree two and its two neighbors1,5
physically touch. It must carry positive circle load: an unloaded
degree-two transmission square cannot have touching endpoint bodies.
This is the degree-two triangle input in
FIVE_BODY_BICONNECTED_REDUCTION.md, Section1.

The physical triangle1--3--5 cannot consist of three circle-touching
squares, by CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md and
ACUTE_LOADED_CONTACT_GRAPH.md. Since3 physically touches the circle,
at least one of the two hubs1,5 is physically circle-clear and hence
has zero circle load.

Suppose a unit completion square lay on the bounded side of the
four-cycle1--4--2--5--1. Section1 would force its aligned cross.
The chosen clear hub has exact positive degree three. Its two ring
neighbors are adjacent cross bodies, and its third positive neighbor
is the roof3. That roof physically touches the other hub, which is
one of the two adjacent ring neighbors. Section2 applies and gives a
contradiction.

Therefore the house four-cycle has unit-square capacity zero,
uniformly over all its load masks, contact normals and additional
zero-stress contacts.

## 4. Exterior routing and precise remaining scope

The roof triangle has capacity zero by CONTACT_RING_HOLE_AREA.md.
The loaded roof3 is on the unbounded face of the selected physical
embedding, so it cannot be enclosed on the bounded side of the
four-cycle. The house has its usual bounded triangular and
quadrilateral faces, with the full shared-junction routing interpreted
as in Section1. A completion square in a bounded face would contradict
one of the two capacity-zero results. Every completion square is
therefore exterior to the house core.

This proves the stated whole-house region theorem. It does not prove
that the core is impossible or that its exterior has capacity at most
three. The complete exterior problem still retains all three
reflection classes of load masks, every contact owner, every physical
circle mask and all four independently oriented extras.

The same cross argument also records two reusable sufficient exits for
any selected four-cycle: an unloaded exact degree-two ring vertex
excludes the cross by the strict-normal transmission argument in
FOUR_CYCLE_LEAF_HOLE_EMPTY.md, Section3; an unloaded exact degree-three
ring vertex whose third neighbor touches either adjacent ring body
excludes it by Section2 here. These are exact-degree conditions; no
uncontrolled extra positive reaction is discarded.

No numerical pose search, Lean compilation or CI was used.
