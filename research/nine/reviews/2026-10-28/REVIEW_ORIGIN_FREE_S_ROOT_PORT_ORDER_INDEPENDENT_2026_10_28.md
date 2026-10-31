# Independent review: arbitrary-degree moment ports at an origin-free genuine S root

Date: October 28, 2026. Reviewer: diamond; author: two_blocks.

**Verdict: PASS unchanged, at both complete local theorem scopes.** I read
and independently reconstructed the entire source
`ORIGIN_FREE_GENUINE_S_ROOT_DEGREE_FREE_PORT_ORDER.md`, SHA256
`7867c149b6276733c3fcb4c74c89920047319f1253e76673b5b02bb005f07b70`.
The strict moment-port theorem and radial nonleaf exclusion hold at
arbitrary true root degree, with all actual neighbors, normal owners,
applications, shared-side means and endpoints retained. No force or
concurrence equation at the root or a nonleaf neighbor is needed.

No fine or coarse gate closes by these local theorems alone.

## 1. Exact original root classification and dependency scope

I checked the operative genuine-leaf statements in
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, SHA256
`faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676`:
Theorem 6.1 gives the actual S leaf and the midpoint `d*e` of its
inward side; Lemma 3.1 gives the whole actual inward unit segment in
the root. A D leaf's root contains O, so the hypothesis that O is
outside the closed X excludes that form. If `d<=1`, the S-root
segment would also contain O. Thus the whole remaining domain indeed
has an actual S leaf, `d>1`, and X meets closed `D_epsilon` with
`epsilon=d-1<1/60`.

The other operative input is only Section 1's actual contained-center,
support-height and inward-normal-segment geometry in
`GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`,
SHA256
`8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49`.
I re-read those statements. They have no degree or force premise and
do not import that source's later intact-root conclusions.

## 2. The complete occupied-center cap calculation

The universal center bound `|c|<=d+1/2<91/60=M` and half-width
bound `c.n>=h+1/2` are correct for every contained unit orientation.
The cap `c.x>C=3501/2440`, `|c|<M` is contained in the stated
rectangle. Its squared diameter is exactly
`52124381/53582400`, less than one by `1458019/53582400`.
Two distinct physical units cannot both have their centers there,
because their disjoint open incircles force center distance at least one.

For a supporting normal with `u>60/61`, `abs(v)<11/61`, and
height `h>1`, the actual center has `c.n>3/2`. Its transverse
square is strictly less than `181/3600`, and
`(27/120)^2-181/3600=1/2880>0`. Resolving the first coordinate
therefore yields

    c.x > (3/2)*(60/61)-(27/120)*(11/61) =3501/2440.

The signs in this resolution are correct for either sign of v. The
proof uses the actual contained neighbor and does not assign it a
radial position or leaf equation. All normal and support endpoints
specified in the later applications give the required strict height.

## 3. Full aligned-frame port order, including both slider endpoints

When the original S-leaf normal is an own axis of X, the exact root
is `[epsilon,d] x [b,b+1]`, with `-1<=b<=0`. An East nonleaf
normal would force its actual center to have first coordinate at
least `d+1/2` and norm at most that same number. Equality gives
the exact radial S center. Its East half-width must then be one
half, which forces the aligned unit and hence the same real leaf L.
Thus every distinct nonleaf East contact is excluded for every mean.

At the upper-right vertex, a negative moment with both normal
components positive gives `h>d/u>=d`, contrary to containment.
The East axis was already excluded and the North axis has positive
moment. The reflected calculation excludes positive moments at the
lower-right vertex. I checked all remaining cones: the upper-left
and top features have nonnegative moments, the lower-left and bottom
features have nonpositive moments, and a left-side mean has moment
exactly its actual height.

It follows that a negative port has height at most zero and a positive
port height at least zero, while every root point has positive first
coordinate. Equality of their angular positions would require both
heights zero. If zero lies strictly between the two horizontal sides,
the remaining actual feature at that height is the West side and has
zero moment; the East side is excluded. At `b=-1`, all nonzero
moments on the upper side `y=0` are positive. At `b=0`, all
nonzero moments on the lower side `y=0` are negative. These endpoints
therefore cannot produce the two required opposite strict signs either.
The strict angular order is valid on the complete aligned slider.

## 4. Full tilted-frame feature cover retains the occupied leaf

After the stated changes of own frame, the exact strictly tilted root
is `[U-1,U] x [V-1,V]`, with `U>=V>0` and `U^2+V^2=d^2`.
Since `V<1` and X avoids O, necessarily `U>1`; consequently
`0<U-1<epsilon` and `0<V<11/60`. The second interval strictly
straddles zero. A reflection reverses both angular orientation and
determinant signs; interchanging the two port labels makes the target
statement invariant, as the source explicitly does.

The actual S-leaf center has first coordinate
`U*(1+1/(2*d))>91/61>C`, with exact final reserve `139/2440`,
and norm below M. The real leaf thus occupies the cap before any
other contact is considered.

At the actual leaf vertex P of X, every outward root normal has
positive dot product with e. A neighbor with that support contains
`P+t*n` for sufficiently small positive t, including when P is an
actual side endpoint of that neighbor. These points lie in the open
interior of L because P is the midpoint of its actual inward side.
A point of the closed neighbor in `int(L)` forces nearby overlap
of interiors. This excludes the entire nonleaf contact cone at P,
without a strict-owner or vertex-only assumption.

An East contact anywhere on the far root side puts its center beyond
`U+1/2>3/2>C`; the actual cap is already occupied by L. At the
remaining far-lower vertex, a nonnegative moment gives
`h>=U/u>1/u`, also when the horizontal axis is handled directly.
Containment therefore yields `u>1/d>60/61`, with transverse
normal component less than `11/61` and `h>1`. The same cap
excludes its actual neighbor. That neighbor cannot be L: the
strictly tilted root meets the leaf's minimum-e side only at P,
not at this other vertex. Zero-moment and axis endpoints are included
in this contradiction.

The remaining full feature list is then exact. Top and upper-left
ports have strictly positive moment and positive height. Bottom,
lower-left, and the retained far-lower ports have strictly negative
moment and negative height. A West-side mean has moment equal to its
height. Thus every negative nonleaf port has negative height and
every positive one has positive height. All root points have first
coordinate at least `U-1>0`, proving strict counterclockwise advance
on its unique angular branch. Every support cone, side mean and
frame endpoint is covered by the aligned or tilted argument.

## 5. Radial theorem: one fixed missing own interval for all neighbors

For a radial contact different from O, choosing the inner and outer
units puts the actual common point at `p=t*n`, `t>0`. It is the
unique nearest point of the outer unit, and contained-neighbor geometry
gives `t<=d`. If the inner unit avoids O, fix one of its missing
own intervals as `[a,a+1]`, `a>0`. The radial direction has positive
component in that coordinate, so its actual support point has coordinate
`a+1`. Hence `t>1`.

The same chosen missing own axis works simultaneously for every
outward radial contact of that inner unit. Each contact direction has
axis component `(a+1)/t>1/d>60/61` and transverse component less
than `11/61`. Its actual outer neighbor center has longitudinal
projection greater than `3/2`. The previously proved cap therefore
contains every such center in one and the same own coordinate frame,
so there can be at most one distinct outward radial neighbor.

Apply this to the origin-free S root X and an actual T different from
L that also avoids O. If X is outer, its radial nearest distance is
`t>1`, contradicting `dist(O,X)<=epsilon<1/60`. If X is inner,
T and the actual genuine S leaf L would be two distinct outward radial
neighbors. Both are impossible. A contact at O is already excluded by
X's closed origin-avoidance. This proves exactly the stated physical
radial theorem, including zero-stress radial contacts and all means.

The hypothesis that T avoids O is retained; this review grants no
radial exclusion against an origin-containing unit without a separate
argument.

## 6. Exact accounting and retained scope

I independently recomputed all eight rational identities in the
author's exact record, SHA256
`970b5d35abd0f5a92ad9ffd1613e01d65eace872836a08cd6ef697b1e938dc57`.
They agree. Both exact direct operative dependency pins also agree.
The comparison sources are used as history only: every needed cap
and radial step is restated and proved in the new source, and no
true-degree-three concurrence is transferred to a higher-degree root.

The complete original radius interval is retained. The origin-free
hypothesis itself forces `d>1`; no separate radius-two theorem is
assumed. Both port applications are unchanged original applications,
and the real S leaf is retained as an occupied physical square.
Additional root forces and all other original physical units remain.

I accept the source unchanged. Fine and coarse deltas are both zero;
any original block join must still prove the complete local hypotheses
at each actual vertex. No force, normal, mean, degree, physical mask,
source bytes, ledger, Lean file or remote object was changed, and no
Lean build, CI, numeric pose or sampled angular check was performed.
