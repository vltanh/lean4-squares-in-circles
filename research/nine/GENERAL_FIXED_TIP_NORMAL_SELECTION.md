# Generic selection for every fixed-point unique-circle-corner tip

**Status: complete hand selection theorem; independent full hand audit passed.**
Work throughout the declared radius window

\[
                 79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

A necessary physical certificate can be selected so that the following
holds simultaneously for every degree-two positive-graph body with
exactly one **physical** circle corner.

* If its two actual pair applications are distinct, fixed physical
  points, neither incident edge has a free vertex/vertex normal.
* If the applications coincide, a positive star is impossible unless
  the body is radial D and that point is its radial inner vertex.
  This exact coincident exception is retained.

Neither neighboring body is required to touch the circle. The circle
multiplier of the tip may be zero. The fixed-point premise is essential:
a mean ranging over a positive-length shared side is not silently
replaced by a fixed point.

This strengthens the fixed-point part of
BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md. It does not supersede the
separate shared-side block proofs, and does not close a mixed parent
cell by itself.

## 1. Physical coordinates and the star equations

Choose the tip's own orthonormal side axes so that its unique physical
circle corner is

\[
 z=(a,b),\qquad a,b>1/2,\qquad a^2+b^2=R^2,
 \qquad S=[a-1,a]\times[b-1,b].
\tag{2}
\]

A physical circle point cannot be shared with a different contained
unit square. This is the existing strict circle-corner cone
obstruction, also used in C7_FIXED_APPLICATION_GENERIC_SELECTION.md.
Consequently neither pair application is z.

Let p,q be the two actual applications, and n,m their outward unit
normals from S toward the neighbors. With positive pair magnitudes
mu,nu and the sole circle multiplier lambda>=0, force and origin
torque read

\[
 2\lambda z+\mu n+\nu m=0,\qquad
 \mu\det(p,n)+\nu\det(q,m)=0.
\tag{3}
\]

Taking a determinant of the force equation with z and then eliminating
mu,nu gives the necessary scalar identity

\[
 D(n,m):=
 \det(z,n)\det(q,m)-\det(z,m)\det(p,n)=0.
\tag{4}
\]

The identity is necessary also at lambda=0. Its role is finite
avoidance before multipliers are obtained, rather than alteration of
an already extracted stress.

## 2. The only non-circle vertex collinear with the circle corner

Suppose a non-circle vertex p of S is collinear with z. The adjacent
vertices (a-1,b) and (a,b-1) have nonzero determinants with z, because
a,b>0. For the opposite vertex,

\[
                 \det((a-1,b-1),(a,b))=a-b.
\]

Thus collinearity is possible only when

\[
 a=b=R/\sqrt2,\qquad
 p=(a-1,a-1)=(1-\sqrt2/R)z.
\tag{5}
\]

This is exactly the radial D inner vertex; its coefficient is positive
because R>sqrt(2).

We will use the following further elementary consequence. If q is a
different actual contact of this radial D body, its outward normal m
cannot satisfy

\[
                             q-p\parallel m.
\tag{6}
\]

Indeed q-p has nonnegative side coordinates. At a side-interior q,
the unique square support normal is perpendicular to that side;
a line in that normal direction from p meets the side only at a
vertex, not its relative interior. At either adjacent non-circle
vertex, (6) forces the outward normal along the corresponding
positive side axis. That face has support a=R/sqrt(2), so any unit
neighbor beyond it has maximum projection at least a+1. But

\[
                      R/\sqrt2>R-1
\tag{7}
\]

throughout (1); equivalently R<2+sqrt(2), which follows at once from
R<21/10. Such a neighbor cannot lie in D_R. The remaining vertex is
the unshareable circle point z. A weighted side mean, if genuinely
fixed by some separate argument, is also a point of the same actual
side and obeys the identical support calculation.

This proves (6) impossible without a boundary-neighbor assumption.

## 3. Distinct fixed applications

Suppose p!=q and the edge at p is a point-only vertex/vertex contact.
Its allowed strict common normals form a nonempty open interval,
subject to the previously imposed open constraints. In particular
p is a vertex of S.

First fix the other normal m and assume det(z,m)!=0. As a function
of n, (4) is

\[
 D(n,m)=\det(W,n),\qquad
 W=\det(q,m)z-\det(z,m)p.
\tag{8}
\]

If W=0, then p is collinear with z, since det(z,m)!=0. Section2
makes p the radial D inner vertex and writes p=tau z. Substitution
into W=0 gives

\[
                         \det(q-p,m)=0,
\]

contrary to Section2. Therefore W!=0. A nonzero linear determinant
cannot vanish on an open interval of unit directions. Avoiding its
at most two unit roots makes (4) fail and excludes the positive star.

Now suppose the other normal m is parallel to z. The force equation
in (3), with mu>0, forces n to be parallel to z as well. A free
normal interval cannot consist of these two directions. Avoiding
them excludes this entire alternative, regardless of p,q and the
value of lambda. No nonzero boundary-contact moment is needed.

If the other edge at q is free too, its normal varies over a distinct
junction parameter, because p!=q. Choose a value m nonparallel to z.
The preceding argument supplies a value n with D(n,m)!=0. Hence D
is not identically zero on the product of the two allowed intervals.
Its zero set has empty interior. One can avoid that set simultaneously
with every earlier finite generic exclusion.

Thus every distinct-fixed-application star in the theorem has no
surviving free vertex normal.

## 4. Coincident applications and the exact retained exception

Suppose p=q. Taking torque about that point in (3) gives

\[
                         \lambda\det(p,z)=0.
\tag{9}
\]

If lambda=0, the two positive outward pair forces would be opposite.
Both normals belong to the normal cone of the same convex square
at p; that cone is pointed and cannot contain opposite nonzero
vectors. Thus lambda>0 and p is collinear with z.

If at least one of the contacts is a free vertex contact, p is a
non-circle vertex of S, so Section2 gives exactly the radial D inner
vertex. More generally, if p is in a side interior, all pair normals
are the same side normal. Force balance would require z parallel
to that side normal, impossible in (2), where both coordinates are
strictly positive. Therefore any possible coincident positive star
again has p at the radial D inner vertex.

This theorem deliberately retains that case. Its two outward
normals may have a positive combination opposite z; the determinant
test is then identically degenerate. A separate physical or whole
component argument is required to exclude it in any application.

## 5. Simultaneous selection and preservation

Before invoking the physical multiplier theorem, list every
physical unique-circle-corner body, every candidate pair of incident
point contacts, and every resulting fixed application pair. This
list is finite for nine actual squares. The list includes bodies
whose eventual circle multiplier is zero.

For a star with one free normal and one fixed nonradial normal,
Section3 gives a nonzero linear bad factor. For a fixed radial
normal, it gives the two forbidden parallel directions directly.
For two free normals, it gives a nonzero polynomial determinant
restricted to the product of open unit-normal intervals. The
strict point-normal parameter at a four-square junction is shared
with the prescribed matched opposite pair; distinct application
points correspond to distinct junctions, so the two parameters in
the product case are independent.

There are only finitely many bad factors. Their complements are
open and dense in the already allowed parameter domain. Intersect
them there, including inside earlier nonempty open choices used
for the C7 radial and mirror exclusions. No new choice depends
on extracted force weights or a variable side mean.

Uncrossing preserves surviving point normals and creates only the
already permitted shared-side forces. Every possible final
fixed-point star was in the physical prelist. Conic thinning only
deletes atoms and edges, and the proof includes zero circle weight.
The selection is consequently compatible with the planar, sparse,
unique-component certificate and all earlier completed branches.

If an application to another proof uses a shared-side mean already
uniquely determined by an independent physical calculation, that
proof must establish the independence and finite prelist separately.
The present theorem does not provide it.

## 6. Exact consequences for the open roadmap

For the remaining mixed cyclic cells, a physically unique-circle-
corner degree-two body whose two physical pair intersections are
distinct singleton points has only actual side-axis-owned contacts
in the selected certificate. This applies even when both neighbors
are physically circle-clear.

Every use must still retain:

* a body with two physical circle corners and all its weight masks;
* a genuinely variable shared-side mean;
* the coincident radial-D inner-vertex star;
* all other bodies and all completion squares.

The theorem is a complete uniform normal-selection implication,
not a proof of the unrestricted nine-square inequality or a
completion capacity. No Lean compilation or CI is used.

