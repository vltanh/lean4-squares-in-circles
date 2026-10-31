# Root review: exact radial near-corner angle bound and conditional central capacity

Date: October 26, 2026.

**Result: PASS for the complete stated local lemma and its precisely
conditional one-radial central-capacity consequence.** No full radial
gate is closed.

I independently read SIX_CYCLE_RADIAL_INCIDENT_NEAR_CORNER_ANGLE_BOUND.md
and the complete relevant local arguments in
RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md,
SIX_CYCLE_ZERO_DIAGONAL_TWO_RADIAL_EXCLUSION.md,
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md,
SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md and
SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md.

## 1. The extra physical premise is explicit

The original radial support cover really forces a strict inner vertex
for each actual reserve-one side channel. Its unchanged application on
the other unit is Q=P+g. The hypothesis that an actual circle corner z
obeys |z-Q|<=1 is additional. It holds for an adjacent vertex, but is
not imposed on an opposite vertex or an arbitrary shared mean.

No assertion about the position of a radial force concurrence is used.
The two actual radial corner multipliers, including either zero endpoint,
remain arbitrary. Physical circle contact is sufficient for the local
triangle inequality.

## 2. The full scalar interval has a strict rational contradiction

I re-expanded the squared norm difference. It is exactly

\[
 |Q|^2-(R-1)^2
 =2R-1+\sin\alpha-2d(R)(1+\cos\alpha).
\]

Its radius derivative is strictly negative on the whole original
interval. The comparison d(79/40)>91/100 has the exact squared reserve
101/40000. Substituting the complete-interval sine and cosine bounds
for 0<=alpha<=12/25 leaves the increasing quadratic
(91/100)alpha^2+alpha-69/100. At its upper endpoint this is
-21/62500. The signs of both replacements are correct. This contradicts
|Q|>=R-1 and proves alpha>12/25 for every actual channel satisfying
the stated extra premise. No sampling or coefficient packet is needed.

## 3. Local prerequisites do not import an extra global hypothesis

The radial unit's two actual strict inner ports are distinct by its
original torque signs. The cited local argument does not need a second
radial unit. Applying the angle lemma to both incident channels gives
theta_S=pi-alpha-beta<3pi/4.

The unique-loaded upper-turn argument in Section 1 of the diagonal
capacity source is local. I checked its full axis-owner and vertex
cover, including original shared means and their endpoints: it does
not assume a diagonal transmitter or already-adjacent ports. Therefore
theta_B,theta_C<=3pi/4 is available here. The exact force-turn sum then
forces theta_B,theta_C>pi/2. The radial strict-obtuse premise is retained;
the right-turn endpoint is assigned to the already accepted separate
classification, rather than removed.

For these strict unique turns, the complete local support cover excludes
outer-axis, opposite-vertex and coincident-port alternatives. The two
actual ports lie on one inner side with chord in (0,1]. The radial chord
is one. These are the actual mask-independent premises of the entire
central free-union capacity theorem; its winding/convex-hull argument
therefore covers the full central region, not just an illustrative face.

## 4. Accepted conclusion and remaining scope

The complete both-near-corner one-radial subfamily has central capacity
at most one, and each radial-incident exterior pocket retains its
previous capacity at most one. The third pocket and the joint
three-extra allocation remain open. Cases violating the extra local
distance premise keep all their original obligations.

All nine squares, actual means and forces, zero individual circle
weights and original sliders remain. No original label, coarse cell,
Lean theorem or equality case is declared closed by this source.
No computational certificate, Lean compilation or CI was used.
