# The four-loaded diagonal five-cycle has a force quadrilateral around zero

**Status:** hand deduction; independent full mathematical review passed (2026-10-29). This gives additional
necessary geometry for C19. It does not exclude that component or its
ten-square completion.

Use the component `U-A1-A2-A3-A4-U` and notation of
[MIXED_FIVE_FOUR_LOADED_GEOMETRY.md](MIXED_FIVE_FOUR_LOADED_GEOMETRY.md).
The radius window and imported dependencies are unchanged. Write the actual
contact points in cyclic order as `q0,...,q4`, where `q0` is U--A1 and
`q4` is A4--U. Orient forces along this cycle. Thus

```text
f4=f0=mu*n,       q0-q4=sqrt(2)*n,       mu>0,
qi cross fi=tau>0.
```

Let `gi=f_(i-1)-fi` be the outward circle-load resultant on Ai, and write
`gi=si*mi`, with `si>0` and `mi` the positive weighted mean of Ai's loaded
circle vertices.

**Theorem.** Each of the four loaded-body contact chords has strictly
positive angular increment. The force vectors `f0,f1,f2,f3` form a strictly
convex counterclockwise quadrilateral containing zero strictly in its
interior. The force turn on every loaded body lies in `(0,pi)`, and the
four turns sum to `2pi`. Both physical force lines on each loaded body
concur on its positive circle-load ray. For the two internal loaded bodies
A2 and A3, those concurrence points belong to their closed squares.

## 1. Every loaded-body contact chord advances in angle

The cited geometric theorem provides consistent angular lifts along the
loaded path. Let `di` be its angular increment inside Ai. Each loaded
square has viewing width strictly less than `pi/3`, so

```text
|di|<pi/3.
```

The closing U chord has angular increment `gamma in (2pi/3,pi)`, and

```text
d1+d2+d3+d4=2pi-gamma>pi.
```

If one `di` were nonpositive, the other three would sum to less than pi,
a contradiction. Thus every `di` is strictly positive. In particular,
each body's two original contact points are distinct. This deduction
does not use a planar embedding of the body-pair graph.

## 2. The four force vertices form a strict convex quadrilateral

Every circle-load resultant ray lies within `beta<pi/12` of its loaded
center ray, while distinct loaded center rays have minor separation
greater than `pi/5`. These are the local estimates in
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md) and
[SEVEN_RING_FORCE_CIRCULATION.md](SEVEN_RING_FORCE_CIRCULATION.md).
Therefore the four resultant rays have the same strict cyclic order as
the four centers.

Summing force balance gives `g1+g2+g3+g4=0`. No consecutive gap between
the resultant rays can be at least pi: otherwise all four nonzero
resultants would lie in a closed semicircle, with at least one strictly
inside it, making their positive sum nonzero. Hence every consecutive
gap lies in `(0,pi)`.

The quadrilateral with vertices `f0,f1,f2,f3` has successive edge vectors
`-g1,-g2,-g3,-g4`. They turn in the stated cyclic order, and consecutive
edge cross products are strictly positive. This makes the quadrilateral
strictly convex: for any one oriented edge, its two nonincident vertices
lie strictly to its left. For example, with edges `e1,...,e4`,

```text
e1 cross (e1+e2)=e1 cross e2>0,
e1 cross (-e4)=e4 cross e1>0.
```

The same computation applies at each edge. In particular the force
vertices are distinct and bound a counterclockwise convex quadrilateral.

## 3. Zero cannot lie outside the force quadrilateral

The nearest-point proof of
[SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md), Section 2,
adapts with one explicit change at the transmission edge.

At a nearest force vertex corresponding to a direct loaded contact, the
same support inequalities give

```text
fi dot mi <= fi dot qi <= fi dot m_(i+1).
```

The nearest-point inequalities put the left side at least zero and the
right side at most zero. All quantities would be zero, contradicting
strict convexity exactly as in the cited proof.

At the force vertex `f0`, the two associated loaded bodies are separated
by U. The support chain is instead the strictly stronger inequality

```text
f0 dot m4 <= f0 dot q4
          < f0 dot q0 <= f0 dot m1,
f0 dot(q0-q4)=mu*sqrt(2)>0.
```

Nearest-point inequalities again require the leftmost quantity to be
nonnegative and the rightmost one nonpositive, which is impossible.

If the nearest point lies inside a force edge belonging to Ai, the same
calculation as the source gives a concurrence point X that is a negative
multiple of gi. Every point x of Ai has `gi dot x>0`: its center norm is
greater than `5/4`, its center/load-ray angle is below `pi/12`, and its
half diagonal is `1/sqrt(2)`, giving the source's strict positive bound.
Both inward contact forces therefore point away from X. Each application
point is then the unique point of the same convex square nearest X.
Section 1 says these points are distinct, a contradiction. Thus zero
belongs to the force quadrilateral.

## 4. Zero cannot be on its boundary

No force vertex is zero. If zero were inside a force edge, its two
endpoint forces would be antiparallel. On the corresponding loaded body
both inward pair forces would point in the same direction. Aggregating
them at their weighted support point, torque balance puts that line
through zero. The loaded-leaf classification consequently makes this
body either a radial diagonal D terminal or a radial side S terminal.

The D terminal has a unique inward support point, which would make its
two contact points equal, contradicting Section 1. For an S terminal,
every unit square supported beyond its inner radial face is circle-clear,
by Section 3 of the force-origin manuscript. But every Ai has at least
one loaded neighbor: A1 and A4 have a loaded path neighbor, while A2 and
A3 have two. This contradiction excludes the boundary case. Notice that
both neighbors need not be loaded for this argument.

## 5. Positive concurrence and the two internal bodies

Strict origin containment gives

```text
gi cross f_(i-1)>0,
Xi=[tau/(gi cross f_(i-1))]*gi.
```

The displayed Xi has cross product tau with both original force vectors,
so it lies on both physical force lines and is a positive multiple of
the circle-load resultant. The force rays themselves turn strictly
counterclockwise with four angles in `(0,pi)` and total turn `2pi`.

For A2 and A3, both neighbors are loaded. The local proof in Sections 4--7
of [SEVEN_RING_INTERNAL_CONCURRENCE.md](SEVEN_RING_INTERNAL_CONCURRENCE.md)
therefore places X2 and X3 inside their closed squares. Its proof needs
positive radial concurrence, distinct contacts, actual support geometry,
and both neighbors loaded; all are available here. This also includes
two geometric circle vertices with arbitrary nonnegative load split.

No closed-square containment is asserted here for X1 or X4, each of which
has the unloaded neighbor U. In particular the all-loaded ring's global
contact-polygon enclosure theorem has not been transferred to this mixed
component.
