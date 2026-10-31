# Independent review: complete-contact canonical rotation and its exact survivor

Date: October 30, 2026. Reviewer: common_certificate continuation.

Target:
`CANONICAL_ROTATION_OF_UNBLOCKED_UNIQUE_CIRCLE_TWO_FORCE_BODIES_2026_10_30.md`

Target SHA-256:
`94f4d2ed11af153196d7e68644c5a21b0f3e4619abcb2b042d54a00d1450bda3`.

The final source pin includes the formatting-only insertion of the
closing display delimiter after (2.3). That display was reread; no
mathematical statement, hypothesis or proof step changed.

**Verdict: ACCEPT at the full printed conditional scope.** I read the
complete target, both complete direct sources, and the precise original
one-corner normal-line calculation used by its proper-concurrence caller.
I independently reconstructed the feasible curve, its exact Phi change,
the radial alignment, and every remaining force/port alternative.
The source correctly claims a necessary reduction, not a seven-cycle
exclusion or an original packing-cell closure.

## 1. The motion checks the actual packing, including zero coefficients

The target fixes `q=tau z` inside the moving square with `0<tau<=1`.
For **every** other physically touching square it requires an actual
separator whose unique maximizer on the moving square is a vertex `p`,
with `p-q=alpha n` and `alpha>=0`. This condition is explicit and
stronger than information about the two positive stress neighbors.
Normals at additional zero-weight contacts serve only as geometric
separators and are not added to the selected stress.

Under rotation about `q`, the originally exposed vertex remains the
unique maximizer of its fixed normal for both signs of sufficiently
small angle, because its three support gaps are strictly positive.
Its support change is exactly `alpha(cos(theta)-1)<=0`. Therefore
the old supporting line continues to separate the entire moved square
from that fixed neighbor. The case `alpha=0` is included: the vertex
then stays fixed, and the other support gaps remain strict.

Every originally noncontacting pair involving the moving square has
positive closed-set distance, since both squares are compact and
disjoint. A small enough rigid rotation preserves these separations.
Taking the minimum of finitely many neighborhoods handles all actual
other squares simultaneously. All pairs not involving the moving
square remain unchanged.

The active corner evolves as

    z_theta=tau z+(1-tau)R_theta z,

so its exact squared norm is

    R^2-2tau(1-tau)R^2(1-cos(theta)) <= R^2.

This covers `tau=1` without asserting strict inward motion. All three
other vertices start strictly inside the circle because the physical
circle mask is exactly one corner; they remain inside by continuity.
Convexity of the disk then contains the entire moved square.

Thus Lemma 2.1 proves an actual two-sided feasible curve for the full
original packing. It does not use a first-order Lagrangian direction
as a substitute for feasibility and does not discard an active
constraint because its multiplier is zero.

## 2. The canonical conclusion uses exactly the existing secondary minimum

I read all of
`ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md`,
SHA-256
`be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06`.
Its compact minimum-radius fiber permits the continuous functional
`Phi=sum |c_i|^2` to be minimized before normal or stress selection.
A feasible packing at the same radius with smaller Phi is therefore
a valid contradiction. The target uses precisely this scope; it does
not infer that every equality packing is already a Phi minimizer.

For the rotating center `c_theta=q+R_theta(c-q)`, I obtain

    |c_theta|^2-|c|^2
       =2q.(c-q)(cos(theta)-1)-2det(q,c)sin(theta).

The sign in the sine term agrees with `q.Jc=-det(q,c)`. Feasibility
for both signs implies `det(q,c)=0`; otherwise the linear term has
a decreasing sign. Once this determinant is zero, `q.(c-q)>0`
would make either nonzero small angle decrease Phi. Hence the two
necessary conditions in the target are correct.

Because `q` is a positive multiple of `z`, this forces `c=kappa z`.
The fixed corner-center distance is `sigma=1/sqrt(2)`. Values
`kappa<=0` contradict `R>sigma`; `kappa=1` contradicts the nonzero
corner offset; and `kappa>1` places the opposite vertex outside
the containing circle. Thus

    c=(R-sigma)e,    z=Re,    e=z/R.

The four vertices are exactly `c+-sigma e` and `c+-sigma Je`.
Writing `q=s e`, the second canonical condition gives `s>=R-sigma`,
while `tau<=1` gives `s<=R`. This independently verifies the full
radial-diagonal alignment and its closed interval for `delta=s-r`.

No positive stress equation is needed for this first alignment result.
Its statement correctly retains the geometric complete-contact
hypothesis and the chosen canonical pose.

## 3. Complete two-force classification after alignment

The later theorem adds exactly two original positive body-pair forces,
a positive circle coefficient at the sole physical circle corner,
and nonparallel proper force lines. At the two positive neighbors,
the geometric separators in the motion premise must be the original
selected normals and actual applications. This prevents an accidental
change of the stress equations during the motion argument.

The containing-circle unshareability proof is correct: both inward
orthogonal side axes at a circle corner have negative scalar product
with the corner vector, so a short inward radial segment lies in the
open square. Two owners would share interior points. Therefore neither
positive pair force can apply at the outer circle vertex.

The point `q` lies on the center-to-outer-corner radial segment and
coincides with none of the other three vertices. Proper coefficients
at the actual pair applications are consequently positive, rather
than merely nonnegative. Coincident pair applications would make
the normals parallel, so the two remaining vertices must be distinct.

If one application were the inner radial vertex, its outward normal
would be `-e`. The other would be a lateral vertex with a nonzero
transverse component. Its positive transverse force could not be
cancelled by the radial circle force or the first pair force. This
excludes all inner/lateral choices and leaves precisely the two
opposite lateral vertices.

For their normals I independently obtain

    n_+=(-delta e+sigma Je)/sqrt(delta^2+sigma^2),
    n_-=(-delta e-sigma Je)/sqrt(delta^2+sigma^2).

Comparing support at a lateral vertex with support at the inner radial
vertex gives `sigma^2>sigma*delta`, exactly `delta<sigma`. Equality
would expose a whole side and is legitimately excluded by the unique
vertex premise. The transverse force equation gives equal original
positive magnitudes, and its radial component gives

    lambda R=mu delta/sqrt(delta^2+sigma^2).

Since `lambda,R,mu` are positive, `delta>0`. These computations verify
every line of the target's boxed survivor and retain the original
force magnitudes and applications.

The survivor is not accidentally excluded by the motion: there
`A=q.(c-q)=-s delta<0` and `B=0`, so the same feasible curve increases
Phi to second order. The target explicitly recognizes this and claims
only a reduction.

## 4. The proper-concurrence caller has the asserted local scope

I read all of `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`, SHA-256
`7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282`.
Its Lemma 1.1 is stated for a loaded two-force body with nonparallel
original force lines; it expressly does not require a five-cycle or
circle-touching neighbors. I also checked the original one-corner
calculation in `C7_FORCE_POLYGON.md`, Sections 4--5, and its explicit
local-scope extraction in `TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`,
Lemma 2.1.

For one physical circle corner, the rectangle calculation excludes
outside concurrences using distinct actual contacts, circle-corner
unshareability, and the outward unit-width obstruction. The original
reference's use of the three-boundary-body prohibition at the repeated
inner-corner alternative is replaced here by the explicitly retained
distinct-contact premise; coincident applications are handled directly
in the local lemma. The scalar endpoint inequality for the remaining
lower-right-corner alternative has no boundary-neighbor premise.

Consequently the caller legitimately obtains `q in S`, a positive
radial factor, and proper nonnegative coefficients for both original
applications. In the unique-corner case its resultant is a positive
multiple of `z`; containment gives `|q|<=R` and hence `tau<=1`.
Nonparallelism is assumed in the target and is not imported from
the older all-boundary-cycle proof.

The two-physical-circle-corner branch is correctly excluded from the
rotation theorem even when one of those physical corner weights is
zero. The second active geometric corner cannot be erased by its
coefficient. Likewise, true positive degree two is not confused with
having only two actual physical neighbors.

## 5. Cycle consequence and exact remaining boundary

In a cycle satisfying every printed full-contact premise, each loaded
vertex passes the same pair magnitude across it by the new formula,
and each unloaded true-degree-two vertex does so by force balance.
Following the connected cycle therefore gives one common magnitude.
This is the stated conditional consequence; no neighbor's degree is
shortened to make the theorem apply.

The general short-run seven-cycle still permits physically shared
contacts, contacts owned by the moving body, two physical circle
corners, and additional zero-weight contacts failing the sufficient
motion condition. The surviving radial-diagonal arrangement also
remains. The source lists these limitations, and none is promoted
to a whole-family exclusion.

All direct source pins match the current files. This acceptance is
of the full conditional hand argument at its precise canonical and
physical scope. It changes no original fine/coarse flag and claims
no Lean verification. No numerical pose search, angle mesh, compiler,
or CI was used in the review.
