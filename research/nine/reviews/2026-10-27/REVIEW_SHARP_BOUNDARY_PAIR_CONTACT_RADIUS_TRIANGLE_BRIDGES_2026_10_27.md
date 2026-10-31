# Independent review: sharp inner radius of an actual boundary-pair contact

Date: October 27, 2026.
Reviewer: triangle_bridges, separate from author rooted_blocks.

**Result: ACCEPTED in the full force-free scope, with no correction.**
Full root review remains separate.

The complete text read and pinned is

    BOUNDARY_PAIR_CONTACT_SHARP_INNER_RADIUS.md
    SHA-256 c0375a272d2f0863044d66ac25e43c10257488505941f9f4895530fa9c1aa6ee.

## 1. Exact physical feature cover

I read and rederived the full three-section proof. Two closed convex
units with disjoint interiors have a genuine common separating support
through every common point P. P cannot be interior to either unit.

At a vertex, a square vertex farther than one from P is necessarily the
opposite corner. Its diagonal lies within pi/4 of every inward supporting
normal in the actual closed vertex cone. At a relative-side-interior P,
the two same-side vertices are at distance at most one, while each
opposite-side displacement has inward normal component one and actual
tangential component in [-1,1]. This gives the same closed pi/4
comparison. The two inward support normals at the contact are opposite,
so the two actual circle-corner displacements have nonpositive dot
product whenever both distances exceed one. Side endpoints and arbitrary
actual mean points are included without a new chosen normal.

## 2. Exact radial contradiction and constants

Assuming s=|P|<sqrt(R^2-1)-1 is exactly the strict inequality
R^2>s^2+2s+2. It gives R>s+1, so every actual circle-corner
displacement is longer than one. Each remains at most sqrt(2) by the
actual unit diameter. The case s=0 contradicts R>sqrt(2) immediately.

For s>0, expansion gives P dot v_i>s, and therefore
cos(angle(P,v_i))>1/|v_i|>=1/sqrt(2). Both displacement vectors
are strictly within pi/4 of the same original radial direction.
Their mutual dot product is consequently positive, contradicting the
complete support-feature observation. No positive circle weight or
unique-corner hypothesis is used.

At R>=sqrt(17)/2, the lower bound is at least sqrt(13)/2-1>4/5.
The squared reserve 13-(18/5)^2=1/25 is exact, so this corollary
is strict even at the critical radius.

## 3. Equality and whole local scope

I checked the equality example directly. With
h=sqrt(R^2-1)-1>0, the two actual aligned units
[-1,0] times [h,h+1] and [0,1] times [h,h+1] are contained
in the original D_R, have disjoint open interiors, touch the
circle at their outer upper corners, and share P=(0,h).
This attains the claimed closed bound. The initial inequality
must therefore not be made strict.

Every actual common-side point is covered directly, so a real aggregate
mean is covered without a separate convexity argument. All physical
circle corners, including zero-weight corners, remain available;
the proof applies to every chosen pair. Arbitrary additional contacts,
forces and degrees are allowed. No original proof gate is closed merely
by this local result.

No mathematical correction was found. No numerical pose, altered
support, load deletion, compilation, CI or shared-status change is
claimed by this review.

