# Independent review of the exact contact lens and positive far-endpoint loads

**Reviewer:** annular-capacity agent. **Date:** October 30, 2026 UTC.

**Verdict: PASS at the complete stated scope. No source repair is required.**

## 1. Frozen object and scope

I read the complete source
`EXACT_CONTACT_LENS_AND_FAR_ENDPOINT_POSITIVE_LOAD_AT_THIRTY_NINE_TWENTIETHS_2026_10_30.md`
and independently reconstructed every geometric implication and full-force
caller. The reviewed source is 14,415 bytes, with SHA256

`3e9a96293ae14e5ed3e9f2952c396cbef82d44ddd6a9643e54ab597a63e951e3`.

The source itself was not edited. This review covers the actual supporting-face
chord, the complete contact lens, its radius and normal-direction consequences,
the arbitrary-degree unloaded-star restriction, the continuous support-gap
clearance theorem, and the positive-load conclusion for both actual endpoints.
It includes side endpoints, arbitrary vertex normals, original application
means, inactive physical contacts, and all original positive forces.

The source reproduces the only imported geometric argument it needs. I also
checked the three historical input pins against their current bytes:

- `SUPPORT_POINT_UNIT_TRANSLATION_AND_PERPENDICULAR_PARALLEL_W_UNLOADED_TERMINAL_EXCLUSION.md`:
  `3da16659e2080884077c02d85e665814391611c357254ba08a57c3a5a4b75c30`;
- `LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md`:
  `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05`;
- `UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md`:
  `d6adb49263e0c2ffb3c1dc58477bef25ed2d0ae83bde59089c33d76c2d23b705`.

## 2. Supporting-face chord and lens

In a square's own coordinates, let a unit inward normal have components a,b.
At a minimizing supporting point, a positive component forces that coordinate
to zero, a negative component forces it to one, and a zero component leaves
the coordinate free. Adding t times the normal, for every closed parameter
`0<=t<=1`, keeps each coordinate in `[0,1]`, since both component magnitudes
are at most one. This verifies the entire actual unit segment, including
whole support sides and both side endpoints. It also covers every direction
in a supporting vertex's normal cone, without an own-axis assumption.

For a contact datum with normal directed from A to B, the occupied points
are therefore `p-n` in A and `p+n` in B. Disk containment of these two original
points gives exactly

    |p|^2+1+2*|p.n|<=R^2.

Resolving p in the orthonormal frame `(n,Jn)` gives

    (|p.n|+1)^2+(p.Jn)^2<=R^2.

These are equivalent to membership in the two radius-R disks centered at
`n` and `-n`. The absolute value is essential: the locus is the stated lens,
not an ellipse. The theorem asserts this exact necessary contact locus; it
does not claim that every point of the lens admits a square-pair completion.

Dropping the nonnegative normal term gives the closed universal radius
`sqrt(R^2-1)`. If `R<1`, the original inequality is already impossible, so
there are no pair contacts. At any shared point of two actual squares,
convex separation of their disjoint open interiors gives a common support
line containing their intersection. Consequently the radius bound applies
to all physical contacts even when no force normal was selected.

The sharpness family is valid. For `r>=1/2`, the two stated axis-aligned units
have disjoint interiors, both farthest squared corner norms equal `1+r^2`,
and the shared point `(0,r)` with horizontal normal attains the radius bound.
The source correctly confines this to two-body sharpness and does not assert
a nine-square completion or a normalized stress.

## 3. Direction restrictions and whole-star alternative

For `r=|p|>0`, division by `2r` gives the claimed actual-normal bound. Its
right side is below one precisely when `(r+1)^2>R^2`; thus `r>R-1` gives the
stated radial-cone exclusion. At the maximum contact radius it vanishes,
so the actual normal is tangential. The target expression is strictly
decreasing for positive r. Independent exact arithmetic gives

    (Q-1-(7/4)^2)/(2*(7/4)) = 65/896 < 1/12,
    (Q-1-(9/5)^2)/(2*(9/5)) = 163/7680 < 1/40.

If a whole closed positive-u own side lies outside the contact disk, a
normal with positive u component cannot occur at any physical contact: its
supporting face, including a possible single vertex, is contained in that
forbidden side. Thus all actual outward contact normals have nonpositive
u component. Projecting the **complete** unloaded force equation onto u
then makes every positive term vanish individually in that component.
In two dimensions the only possible remaining unit normals are `v` and
`-v`. One original strictly negative component therefore forces positive
circle load, as does a nonparallel positive star.

This argument neither deletes forces nor infers true degree two. A parallel
star may have several neighbors. The source preserves this distinction.
Taking the minimum norm over each entire outward own side yields exactly
the two necessary inequalities in (10), including the case in which the
side interval straddles the other coordinate's zero. The threshold
`|c.u|>=4/3` is valid at equality because

    (11/6)^2-(Q-1)=103/2304>0.

The necessary locus is asserted only for unloaded stars with nonparallel
positive normals; it is not used to bound the number of arbitrary hubs.

## 4. Complete support-gap calculation

For every contained actual square, the farthest-corner identity and the
inequality between the own-coordinate l1 and Euclidean norms give

    R^2 >= |c|^2+|c|+1/2.

At `M=91/60`, the excess over Q is `31/57600>0`. Monotonicity therefore
gives the strict center bound `|c|<M`, with no lower-radius premise.

For a genuine signed support gap at least `39/20`, each endpoint center
has outward projection strictly above `43/30`. The sum of actual endpoint
half-widths is strictly below `13/12`, hence each is below `7/12`. For the
dominant outward own axis, write its normal components as `a>=b>=0` with
`a^2+b^2=1`. Its actual half-width gives `a+b<7/6`; consequently

    (a-b)^2 > 23/36 > (19/24)^2,
    23/36-(19/24)^2 = 7/576.

The complete closed side parameter, including its unfavorable endpoint,
therefore has outward signed projection strictly above

    43/30+19/48 = 439/240.

The exact remaining reserve is

    (439/240)^2-(Q-1) = 53/1800 > 0.

Thus every point of the entire outward own side lies beyond the universal
contact disk. This proves the advertised clearance from every other actual
unit, not merely from selected neighbors or at selected means. All signs
reverse correctly for the opposite endpoint. The proof uses an actual
support-interval gap in the specified direction, not an interchangeable
Euclidean set-distance estimate.

## 5. Full-force endpoint caller

At A, the given original inward normal d has strictly negative projection
onto the outward dominant own axis. Every remaining original body normal
has nonpositive projection by the whole-side theorem. Their complete sum
is therefore strictly negative in that coordinate. Zero total circle load
would contradict the full translational equilibrium equation. The same
argument at B uses its original inward normal `-d` and the opposite outward
own axis. Neither cancellation of other forces nor a degree assumption is
needed. Nonnegative circle atom weights make nonzero total load strictly
positive, with no restriction on which circle corners carry it.

For a genuine two-internal run whose internal bodies are unloaded and
have true positive degree two, full balance propagates one signed unit
normal and its magnitude. Summing the actual tight support equalities
gives endpoint support gap equal to the sum of the two internal widths.
Each width is at least one, so this is a literal caller of the `39/20`
threshold. Additional endpoint chords, branches, or attachments remain in
the full endpoint force equations. No torque, planarity, selected embedding,
or common frame between distinct squares is required.

## 6. Review boundary

All eleven displayed rational constants used above were recomputed exactly
with rational arithmetic. The mathematical review reconstructs the entire
source; it is not based solely on those arithmetic checks or on agreement
with the earlier, weaker contact-radius theorem.

The source does not close the remaining arbitrary large-block problem,
does not change a certificate, and does not delete any of the nine physical
units. The exact contact lens, whole-star restrictions, whole-side clearance,
and positive-load conclusions all pass with their advertised closed and
strict boundary cases intact. No pose search, numerical stress optimization,
Lean compilation, CI run, ledger modification, or publication was performed
for this review.
