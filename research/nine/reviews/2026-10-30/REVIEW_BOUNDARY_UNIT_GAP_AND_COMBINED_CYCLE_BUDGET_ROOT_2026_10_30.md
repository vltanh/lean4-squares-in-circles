# Root review: boundary unit gaps, the full four-load eight-cycle and the combined budget

Date: October 30, 2026 UTC.

**Verdict: PASS for both complete frozen sources and all their stated
geometric and physical callers.** I read both entire manuscripts and
independently reconstructed the fixed-point proof, strict set-distance
conclusion, complete cycle join and combined integer table.

| Source | SHA256 |
| --- | --- |
| BOUNDARY_UNIT_GAP_FORCES_OBTUSE_CENTER_ANGLE_AND_FOUR_LOAD_EIGHT_CYCLE_EXCLUSION_2026_10_30.md | `fa63e0ef4a0d94d47ff05e848b46792ac2861d0504b8369bc109beb3fd7d5e5a` |
| COMBINED_MARKED_CYCLE_BUDGET_AND_EIGHT_BODY_FIVE_LOAD_SIDE_REDUCTION_2026_10_30.md | `dbb9eaeee362c2148a6ada5319a05e0b962b5fdd2ea5ed36772e8175c8af005f` |
| UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` |
| SHARP_LONG_AND_DIAGONAL_RUN_ANGLE_BUDGET_2026_10_30.md | `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc` |

The complete old marked-order and refined-angle inputs have the full
root and separate independent reviews in the preceding checkpoint.
Their exact bytes are unchanged.

## 1. Both fixed points lie in every actual boundary square

In the radius window, every physical boundary center has 5/4<r<91/60.
Put B=13/32, K=1/sqrt(2) and A=K+B. The proposed points are Ae+/-BJe
in disk-centered coordinates, with e the radial center direction.
The lower radical estimate K>70/99 has squared reserve 1/19602.
It gives A+B>M with reserve at least 23/7920, while A<5/4<r.

In a square's own-frame chart c>=s>=0, the two absolute coordinate
deviations are bounded by F_1=(r-A)s+Bc and F_2=(r-A)c+Bs.
Their difference is (c-s)(A+B-r)>=0. The actual boundary-corner
equation gives r<133/64-(s+c)/2, hence the displayed upper bound
G=(6113/6336)s+(13/32)c-(s^2+sc)/2 for F_1.

I checked the directions of both square-root bounds used in 1-2G:
c<=1-s^2/2 throughout; c>=1-(5/9)s^2 on 0<=s<=3/5; and
c>=1-(3/5)s^2 on the full 0<=s<=1/sqrt(2). The positive s*c term
uses the lower estimate and the negative -(13/16)c term the upper.

On the first interval the exact cubic, shifted by z=s-9/20, is

    P(s)=467/140800-(47/31680)z+(21/32-(5/9)z)z^2.

Its quadratic coefficient is at least 55/96 and |z|<=9/20, giving
P(s)>=373/140800>0. I recomputed every coefficient of this identity.
On the second interval the cubic H has H''>9/80,
H'(3/5)=43517/396000>0 and H(3/5)=2107/330000>0. These values and
the monotonicity establish positivity on the entire closed interval.
Both fixed points are therefore strictly inside the actual square,
including at both own-frame boundary orientations and at s=3/5.

## 2. A unit set gap forces an obtuse center angle

For center directions at minor angle theta<=pi/2, choose the two
fixed interior points facing one another. Their distance is exactly

    2|A sin(theta/2)-B cos(theta/2)|.

The expression inside the absolute value increases from -13/32 to
1/2 on 0<=theta/2<=pi/4. Its doubled absolute value is at most one.
Because both chosen points are in open square interiors, a small move
of the first point toward the second strictly reduces a nonzero point
distance; a coincident pair already gives set distance zero. Thus the
actual set distance is strictly less than one, even at a right angle.

This proves the contrapositive theorem for arbitrary independent square
orientations and both physical circle-corner masks. No stress, torque,
compatible graph drawing or application-mean premise enters this pair
theorem.

## 3. Every nonempty supported run consumes more than ninety degrees

The actual support telescoping identity for a run with j internal units
puts every point of one endpoint square at signed gap at least j from
every point of the other. For j>=1 their set distance is at least one.
Physical boundary endpoints therefore have minor center angle greater
than ninety degrees by the new pair theorem.

The previously verified compatible marked order turns these into bounds
for the actual consecutive angular gaps, whose sum is a full turn.
Four nonempty runs would already exceed that sum. Thus there are at
most three nonempty runs for any marked-cycle count and placement.

This excludes the entire alternating four-mark family. On eight bodies
with exactly four marks, the base budget forbids every two-internal run;
four unmarked bodies in four runs then force exactly one per run. The
new argument excludes that whole remainder. Consequently every
compatible eight-body marked cycle needs at least five marks, and an
entire simple positive component with exactly four positive circle-load
bodies has at most seven bodies. This complete join uses only full
translational balance on genuine unloaded degree-two internals.

## 4. The combined budget retains all actual widths and marks

For direct runs, other singletons, diagonal-width singletons and long
runs, the strict lower bounds are respectively 40, 90, 105 and 175
degrees. Let k_1 count all singleton runs, d their actual diagonal-width
subset, and ell the long runs. Since m=k_0+2k_1+3ell, summation gives

    360>40m+10k_1+15d+55ell,
    8m+2k_1+3d+11ell<=71.

The literal inputs have the same actual geometry, marked order and
compatible drawing. No condition is borrowed from a different stress.
All thresholds are strict before the final integer step.

For m=8 the inequality forces ell=0. With t marks it gives k_1=8-t
and 3d<=2t-9. I checked the entire resulting count table: t=5 gives
three singletons and d=0; t=6 gives two singletons and d<=1; t=7 gives
one singleton and d<=1; t=8 gives none. No t<=4 row survives.

The absence of diagonal width is a geometric statement. Concluding that
all three singleton transmitters in the five-load row are side-normal
uses the explicitly retained full moment equations and their exact
side/diagonal classification. The source does not infer that dichotomy
from translational balance alone. Arbitrary additional endpoint contacts
and marked zero-weight physical boundary bodies remain allowed.

The seven-body side-short record has (m,k_1,d,ell)=(7,1,0,1), so its
integer left side is 69 and it survives. The corresponding diagonal
short variant has value 72 and is excluded. The complete five-mark
all-side eight-body family remains open; the table is not an existence
assertion for any row.

## 5. Verification limits

All polynomial coefficients, endpoint derivative values and rational
reserves were recomputed using exact fractions. No sampled orientation
or numerical optimizer is used. Complete independent reviews by
block_ears are separate from this root reconstruction. These sources
close the stated whole cycle families, not the larger chorded parents,
all smaller-core completions, equality classification or unrestricted
nine-square optimality. No Lean compilation, CI or merge was performed.
