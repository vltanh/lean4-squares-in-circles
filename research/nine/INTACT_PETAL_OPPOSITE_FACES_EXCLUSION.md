# Opposite intact-petal faces are impossible; surviving two-petal roots use adjacent sides

Date: October 26, 2026.

**Status: complete hand theorem; full root and separate independent reviews accepted.**
This is the quarter-disk consequence identified by the root continuation
and written out with its full original physical scope.

Keep the original nine physical unit squares in
79/40<=R<=sqrt(1105)/16 and the common compatible selected certificate.
An intact petal at H is a positive triangle H,U,V whose two private
tips retain their true degree two and positive circle loads. H can
have arbitrary other actual forces and any genuine full degree.

**Theorem.** Two distinct intact petals at H cannot have opposite
actual common sides. Consequently H has at most two intact petals,
and if it has two, their actual common sides are adjacent.

No force at H is discarded to reach this conclusion.

## 1. Original full-radius reduction and common-side margin

The already accepted same-nine-square theorem
NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md excludes R<=2, retaining
all nine actual physical units. Its declared finite arithmetic
certificate remains an inherited dependency. Thus assume R>2
and put r=R-sqrt(2)>2-sqrt(2).

The complete intact-petal origin/common-side theorem gives
O in int H and two actual root ports on the petal's own
common side with transverse coordinates of strictly opposite
signs. The ports are at distance at least r from O because
they belong to physical circle-touching tips.

The two transverse port coordinates differ by at most one.
Therefore at least one has magnitude at most 1/2. If P is
that actual side's positive height,

    P^2 >= r^2-1/4
         > (2-sqrt(2))^2-1/4
         =23/4-4sqrt(2)>9/100.

The final strict comparison follows by squaring
sqrt(2)<283/200. Hence every intact-petal common side satisfies

    P>3/10.                                             (1)

This strengthens the older 1/5 estimate in this full
nine-square caller. It does not change any mean, choose a
new port, or require equal physical circle weights.

## 2. Opposite petal faces put a large disk inside H

Suppose the two actual common sides are opposite. Their
positive heights P and 1-P both exceed 3/10 by (1). Choose
the one with smaller height, so P<=1/2.

Both its actual ports p_- and p_+ have norm at least r.
Writing their transverse coordinates y_-<0<y_+ gives

    y_-^2,y_+^2 >= r^2-P^2
                   >=r^2-1/4>9/100.

Thus

    y_-<-3/10,       y_+>3/10.

The transverse interval of H contains these actual ports,
so both transverse side heights also exceed 3/10. The two
longitudinal heights already had that bound. Therefore

    the entire closed D_(3/10) lies in int H.            (2)

Every physical side endpoint and every parallel or
nonparallel petal interface is included: only the actual
strict port straddling and unit side length were used.

## 3. The eight other original units violate one circle's arc capacity

Every original unit K distinct from H avoids int H.
By (2) it cannot contain any point of D_(3/10), since
interior points of the closed square K approach every one
of its points and would overlap H. Compactness therefore
gives dist(O,K)>3/10>1/4.

For completeness, if p is K's nearest point to O, convexity
gives p.x>=|p|^2 for every x in K. Thus K lies in the
half-plane of unit normal p/|p| and height |p|>1/4.

The force-free whole-orientation theorem in
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section 1, now
assigns each of the other eight original units a single
open-interior arc of length greater than pi/4 on the
circle of radius 5/4. These eight arcs are pairwise disjoint
because all eight original square interiors are disjoint.
Their total length would exceed 2pi, impossible.

This proves the opposite-face theorem on the whole original
radius interval, with the R<=2 dependency retained.

## 4. Complete petal-count and face consequences

The accepted one-petal-per-side theorem in
GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md,
Section 2, permits at most one intact petal per actual H side.
Three distinct square sides contain an opposite pair. Hence
H cannot have three or more intact petals in the original
nine-square packing. If exactly two remain, their sides
are distinct and nonopposite, so they are adjacent.

The statement applies whether or not other cyclic blocks
or bridge forests are attached at H. It does not assume
an intact equation at any higher-degree nonroot body.

Together with TWO_INTACT_PETALS_NO_UNLOADED_NEIGHBOR.md,
it restricts a common-root two-triangle-plus-pentagon
layout to two adjacent petal faces and loaded immediate
pentagon neighbors. Neither those necessary restrictions
nor this theorem alone close the entire C3.335.b0 cell.

No new numerical certificate, sampled pose, Lean
compilation or CI is used.

