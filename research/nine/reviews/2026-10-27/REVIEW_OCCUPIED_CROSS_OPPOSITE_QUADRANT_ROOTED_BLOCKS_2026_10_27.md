# Full independent review: the opposite quadrant of an occupied cross is empty

Date: October 27, 2026.

Reviewer: rooted_blocks, independently of the author and root reviewer.

**Verdict: ACCEPT the complete force-free geometric theorem without
correction.** The proof covers arbitrary containing-circle offset,
every orientation of the extra square, all weak axis equalities, and
all originally stated opposite-quadrant consequences.

Reviewed source:
`CHORDED_HEXAGON_OCCUPIED_CROSS_OPPOSITE_QUADRANT_EMPTY.md`

Frozen SHA-256:
`c824dd96ba8b9505de653248b9bd99bbf429eb706f84f5288d58657db6f9abf7`.

I read the entire frozen source, independently reconstructed every
separating-axis alternative and the final quadratic minimization,
and checked all twelve rational comparisons recorded below. This is
the full local dependency audit requested for the later arbitrary
occupied-cross capacity theorem; it does not substitute for the
separate audit of that larger theorem.

## 1. Arbitrary offset and center localization

The coordinate origin is the actual central cross center, while o is
the containing-circle center. The proof does not silently identify
them. Independent cross-axis reflections put a center in a weakly
opposite quadrant into x,y>=0 with both coordinates of o nonpositive.
If a center coordinate is zero, its reflection can still be chosen
according to the corresponding coordinate of o. Thus the weak-axis
cases are included.

The universal center bound follows from the true farthest-corner
formula and holds for every contained unit without a boundary or
force premise. In the reflected opposite quadrant,

    x^2+y^2<=|(x,y)-o|^2<M^2.

The incircle of an extra unit avoids the interiors of both actual
cross rectangles V and B. These rectangles are unions of actual
cross units; their internal grid lines do not create room for an
open incircle. Hence its center has distance at least 1/2 from each.

If x<=1/2, separation from V requires y>=2, impossible by the
center bound; similarly for y. A coordinate at least 3/2 would then
give squared norm greater than 5/2, again impossible. In the remaining
range, the closest point of V has the same y coordinate, forcing
x>=1, and the closest point of B forces y>=1. This establishes the
full actual localization `1<=x,y<3/2`.

Every point of the extra square consequently has both coordinates
strictly positive, because its cross-axis halfwidth is at most
1/sqrt(2)<1. Its distance from the cross center is therefore no
larger than its distance from the actual circle center o. The necessary
origin-centered disk containment used thereafter is valid for the
unchanged actual square. It is not an asserted motion or replacement
of the original containing disk.

## 2. Exhaustive separating-axis cover

The square's own quarter-turn symmetry and, when necessary, exchange
of the two cross axes give precisely the frame

    u=(c,s), v=(-s,c), c>=s>=0, c^2+s^2=1.

Exchanging the cross coordinates preserves both rectangles as a set
and all preceding localization facts, so both original tilt signs
are covered. Aligned s=0 and maximal c=s are retained.

For either axis-aligned cross rectangle, the complete SAT directions
are its two coordinate axes and the two actual own axes of the extra.
Normals directed from the rectangle toward the extra on negative
cross axes or -u have nonpositive center projection, so cannot achieve
the positive sum of support halfwidths.

I expanded the remaining oblique alternatives. The v separator gives

    c(y-m)>=s(x+ell)+1/2,

and its implication `y>=m+(c+s)/2` is exactly the nonnegative
quantity in source equation (7). The -v separator gives the analogous
right-axis separation by equation (8); if s=0 that downward-normal
separator is impossible directly. Thus no oblique direction is lost
when those two alternatives are replaced by the ordinary positive
cross-axis alternatives. Only the actual northeast own normal u
needs to remain separately.

The source then correctly removes the impossible upper separation
from V and right separation from B using x,y<3/2. The remaining
B own-axis alternative would give center norm greater than 31/20>M.
Therefore the actual necessary conditions are exactly y>=y_0 and
the two displayed V alternatives. This is a whole SAT cover and does
not assume the extra touches any cross arm.

## 3. Both coordinate separations

When x,y>=y_0, the actual far corner displacement (k,h) is a genuine
corner for the displayed orientation. Both resulting coordinates are
positive, so coordinatewise lower bounds give the stated squared
radius estimate.

The identity

    (1/2+c)^2+(1/2+c+s)^2-9/2
      =3(s-2t)+(s-t)^2+t^2, t=1-c,

is exact. For s>0 the comparison `c>1-s/2` follows by squaring two
nonnegative quantities and using s<4/5; hence s-2t>0. The aligned
s=0 case gives equality 9/2. All orientations therefore require a
radius squared at least 9/2, strictly above Q.

## 4. Remaining actual own-axis separator

In the remaining branch, U=cx+sy>=U_0. If s>=1/2, U_0>8/5>M,
so the exact domain is s<1/2 and c>sqrt(3)/2. The localized bounds
x<3/2, y>=1 give W=-sx+cy>1/10. Thus the actual positive-u,
positive-v corner is the one used in the lower squared-norm bound.

The substitution from `y=sU+cW>=y_0` is legitimate with the correct
sign: its lower bound on W is positive because y_0>=1, U<M and
s<1/2 give a numerator greater than 29/120. Squaring W+1/2 can
therefore only increase when W is increased.

I differentiated the exact displayed quadratic F(U). Its unique
critical point is indeed

    U_*=s y_0-(c^2-sc)/2.

The term subtracted is positive, y_0<5/4 and s<1/2, so U_*<5/8.
Meanwhile U_0>17/20. F is therefore increasing on the entire actual
range U>=U_0. This argument includes s=0 and needs no numerical
orientation subdivision.

The evaluation of F(U_0) gives exactly

    y=y_0,
    x=y_0+(s/c)(1-c).

This is an algebraic point used to evaluate a quadratic, not a
purported new physical contact or square. Its positive-u,v corner
has the stated coordinates; the nonnegative extra term in its first
coordinate gives the same lower bound 9/2 as in Section 3. This
excludes every remaining own-axis alternative.

## 5. Exact arithmetic checked

With M=91/60 and Q=1105/256, the exact comparisons are

    M^2+M+1/2-Q = 31/57600 > 0,
    5/2-M^2 = 719/3600 > 0,
    31/20-M = 1/30 > 0,
    8/5-M = 1/12 > 0,
    3/4-(17/20)^2 = 11/400 > 0,
    17/20-3/4 = 1/10,
    1-M/2 = 29/120 > 0,
    17/20-5/8 = 9/40 > 0,
    9/2-Q = 47/256 > 0,
    1/2-(7/10)^2 = 1/100 > 0,
    (4/5)^2-1/2 = 7/50 > 0,
    (3/4)^2-1/2 = 1/16 > 0.

The single equality above is used with already strict inequalities
on c and s, so the asserted W>1/10 remains strict. The endpoint
comparisons and the final lower radius 9/2 are compatible with a
closed containing radius at Q.

## 6. Acceptance boundary

The theorem excludes every actual extra center weakly opposite the
actual containing-circle center in both cross coordinates. The
stated one-empty-quadrant, axis-center and zero-offset consequences
follow directly from that same weak condition. No force, load,
boundary-arm or selected-normal premise entered the proof.

The theorem deliberately leaves the other center quadrants
unrestricted. I accept it as a complete dependency of the later
general capacity result, without treating this review as acceptance
of the separate count of possible units in those other quadrants.

No Lean compilation, CI, numerical pose search, remote operation or
shared-ledger edit was used in this audit.
