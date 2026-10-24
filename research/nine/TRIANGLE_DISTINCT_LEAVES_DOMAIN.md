# Exact domain of the remaining distinct-articulation two-leaf triangle

**Status: complete domain reduction; root and independent full hand audits passed.
The whole remaining layout is open.**
Let the positive component consist of a triangle A,B,C, with a pendant
leaf L_A at A and a different pendant leaf L_B at B. Throughout

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\tag{1}
\]

the complete family reduces to the following domain:

\[
 R>\frac{\sqrt{17}}2,\qquad H\ne0,
 \qquad \text{leaf types S/S or D/S},
\tag{2}
\]

where H is the common signed triangle contact moment. A,B are
physically circle-clear and each meets the disk of radius
\(\delta=\sqrt{R^2-1/4}-2<1/60\). C is loaded, and retains
one or two physical circle corners with every nonnegative weight
mask. All physical side means and all four completion squares remain.
No exclusion or completion capacity for the whole domain (2) is
asserted here.

## 1. Exact loads, leaf poses, and moments

The radial bridge theorem makes A and B physically circle-clear.
C cannot be unloaded: otherwise its two equal opposite positive
forces would transmit a positive width between A and B, which could
not touch. Thus the loaded set is exactly

\[
                            \{L_A,L_B,C\}.
\tag{3}
\]

Put

\[
             d=\sqrt{R^2-\tfrac14}-1,
             \qquad r=R-\sqrt2.
\]

Each leaf is exactly S or D. In a frame with its radial direction
e=e_x, its articulation has the full following domain:

* S: p=(d,0) is a rightmost support point. An aligned articulation is
  \([d-1,d]\times[t-1/2,t+1/2]\), |t|<=1/2. A tilted one is
  \(p+[0,1](-a,-b)+[0,1](-b,a)\), a,b>0,
  a^2+b^2=1, or its reflection.
* D: the articulation is
  \([r-1,r]\times[t-1/2,t+1/2]\), |t|<1/2, and p=(r,0)
  is in the relative interior of its right side.

These are genuine radial support statements, including every aligned
side mean. There is no alignment assumption between A and B.

Both D articulations would contain zero in their open interiors,
since 0<r<1. They cannot be distinct interior-disjoint squares.
Thus D/D is impossible before any triangle contact classification.

Orient the triangle cyclically. If f_i is a positive edge force and
p_i its actual physical application (possibly a weighted side mean),
origin torque at each body gives

\[
                           \det(p_i,f_i)=H
\tag{4}
\]

independent of i. The bridge forces are radial and the circle forces
at C are radial, so they add no origin moment. No midpoint replacement
is made in (4).

## 2. The zero-moment alternative is impossible

Suppose H=0. At C both pair force lines pass through the origin.
If they were nonparallel, their concurrence would be zero. The
positive-concurrence part of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1, rules this
out. Precisely, its rectangle normal-line calculation for a unique
circle corner uses only genuine unit neighbors and the outer-width
obstruction, not a boundary-neighbor hypothesis; for two circle
corners the same calculation gives a strictly positive radial
concurrence. The boundary-neighbor hypothesis of that lemma is needed
only for its separate exclusion of parallel force lines. We do not
use that exclusion here.

The two C pair directions must therefore be parallel. Opposite
outward directions would require a unit neighbor beyond an outer
circle corner or the outer radial S face, both impossible. The
remaining same-sign alternative is exactly radial S or radial D by
the parallel-force normal-form theorem in
`PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`.

For radial D, both applications are its unique inner vertex r e.
The selected nonradial point-normal convention requires each neighbor
to contain that vertex in a side interior. Both neighbors would occupy
the same full tangent half-plane and overlap. This is impossible.

For radial S, rotate its direction east. Every application on its
inner side has normal -e_x. Equation (4) forces both actual means
to be exactly p=(d,0). Neither A nor B can have p in a side interior,
since its full tangent half-plane would leave no room for the other
unit square. Their two right-angle cones therefore fill the opposite
half-plane and force the aligned forms, after labeling,

\[
              A=[d-1,d]\times[0,1],\qquad
              B=[d-1,d]\times[-1,0].
\tag{5}
\]

Their AB mean lies on [d-1,d] times {0}, with vertical normal.
Its zero origin moment implies d<=1. At A, the force toward C is
strictly eastward and the force toward B is strictly downward.
Its leaf direction must consequently have strictly negative x and
strictly positive y components. It cannot be D, whose direction is
an A side axis. For an S leaf its radial application is the northwest
vertex (d-1,1), of norm d. The equation

\[
                         (d-1)^2+1=d^2
\]

forces d=1, when that radial vector is vertical, contrary to its
required strictly negative x-component. Thus H=0 is impossible
throughout (1).

## 3. Radii below sqrt(17)/2 are impossible

Suppose d<1. Every S articulation contains zero. In a genuinely
tilted one the coordinates of zero from its radial support point
are (da,db), both strictly between 0 and 1, so zero is interior.
In an aligned one zero is interior unless t=1/2 or -1/2. Every D
articulation also contains zero in its open interior.

Because A and B are interior-disjoint and both contain zero, neither
can contain it in its interior. Thus both leaves are S, both
articulations are aligned with their own leaf directions, and zero
lies in the relative interior of a transverse side of each. Their
two tangent half-planes must be opposite. Their frames are parallel,
and their leaf directions are parallel to the common side line.

Equal leaf directions repeat the same physical S square. Opposite
leaf directions make the nonzero circle-load vector of C parallel
to one of them, by global force balance. Distinct loaded bodies cannot
have the same circle-resultant direction: each such ray pierces that
body's open inner-circle arc, by
`CYCLIC_GLOBAL_CONTINUATION.md`, Section 8. Either alternative is
impossible. Hence d<1 is excluded.

## 4. The endpoint d=1 is impossible as well

At d=1, a genuinely tilted S articulation still contains zero in
its open interior. The D case is still interior. Consequently both
leaves are S, both articulations are aligned in their own radial
frames, and zero belongs to their inner sides, possibly as a vertex.

If A and B intersect only at zero, their positive AB application
has zero moment, contrary to Section 2. Their intersection must be
a positive-length side segment. Therefore their frames are parallel,
and the two leaf directions are equal, opposite, or perpendicular.
The first two alternatives fail just as in Section 3.

In the perpendicular case rotate and reflect to make the two leaf
directions east and north. Then

\[
                 A\subset\{x\ge0\},\qquad
                 B\subset\{y\ge0\},\qquad
                 m_C=-\alpha e_x-\beta e_y,
                 \quad\alpha,\beta>0.
\tag{6}
\]

Take actual contacts u in A intersect C and v in B intersect C.
Every point of C has positive scalar product with m_C, by the strict
45-degree circle-corner cone theorem
`ACUTE_LOADED_CONTACT_GRAPH.md`, Theorem A.1, summed over its
positive corner weights. Equation (6) thus forces
\(u_x\ge0,u_y<0\) and \(v_x<0,v_y\ge0\), giving u dot v<=0.
But the same theorem, using any one circle corner of C, puts every
point of C in one strict 45-degree cone about that corner. Any two
of its points have positive scalar product. This is a contradiction.

Thus R>sqrt(17)/2 is necessary for the entire distinct-articulation
layout, including the equality and every physical corner mask.

## 5. Complete surviving domain and exact open exit

The orientation-uniform articulation estimate in
`FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`, Lemma 2.1, uses only the
radial leaf and gives

\[
        \operatorname{dist}(0,A),\operatorname{dist}(0,B)
             \le d-1=\delta<\frac1{60}.
\tag{7}
\]

If one leaf is D, its articulation contains zero in its interior,
so the other articulation is S and avoids zero even as a boundary
point. The latter's aligned or tilted domain is still exactly that
in Section 1. For two S leaves neither origin containment nor a
common frame is imposed.

Global force balance retains the exact relation

\[
               \alpha e_A+\beta e_B+m_C=0,
                         \qquad\alpha,\beta>0.
\tag{8}
\]

The two leaf directions cannot be equal or antipodal: equality gives
overlapping radial leaves, and antipodality makes C's nonzero
resultant repeat a leaf direction. Apart from these necessary facts,
all direction angles, both physical C corner counts, their actual
positive/zero masks, the nonzero signed moment H, and every contact
axis and shared-side mean remain variable.

The whole-case exit still required is to exclude every physical
positive S/S or D/S realization satisfying (2), (7), and (8), or to
prove that each such five-body core admits at most three additional
interior-disjoint unit squares. All four candidate completion squares
must be retained until one of those two conclusions is proved.
This source supplies the exact domain for that obligation and does
not supply its final capacity.

No Lean compilation, CI, numerical pose sample, or restriction to a
selected contact-owner pattern is used in this domain reduction.
