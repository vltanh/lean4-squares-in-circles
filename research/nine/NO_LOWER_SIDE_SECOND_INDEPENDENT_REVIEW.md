# Second independent review of the no-lower-side theorem

November 2, 2026. Reviewer: the singleton/mixed-case agent, independent
of the lower-side author and of the root's first physical/code review.
No producer or checker source was modified. No Lean, Lake or CI was run.

**Physical and code review: PASS.** The conclusion is conditional on the
complete acceptance of all 128 specified roots by the reviewed exact
checker, together with the previously accepted input lemmas. This review
does not substitute for that arithmetic acceptance. At the end of this
review, all 128 distinct raw exact reports were present and individually
reported PASS under the same reviewed checker hash. Their independently
summed totals were 27,552,502 leaves, maximum depth 63, and least reserve
3357953 / 2^48. These observations are recorded separately from the
physical review in `no_lower_side_second_review_bindings.json`.

## 1. Reviewed sources and scope

The final manuscript is
`WEAK_MIDDLE_NO_LOWER_SIDE_EXTRA_HAND_TABLE.md`, SHA-256

    1b4bd4182e103a9cb6d065de4097fb54192b8ce514118b92b00d83daa343c329.

The complete exact source is `verify_lower_side_exact.cpp`, SHA-256

    5211852f38acfa94c3d80d29559042bcb346d9d1751c0c5015152fc0ecc6a424.

I read the full manuscript and exact evaluator/parser. I also checked
the physical statements of `LOWER_SIDE_MAIN_PAIR_HEIGHT_BRIDGE.md` and
`SIGNED_LOWER_SIDE_HEIGHT_ENVELOPE.md`, the per-root replay wrapper, the
complete-source/executable binding, and the final root manifest. The two
height-input arithmetic certificates remain separately accepted inputs;
this review does not claim to have replayed them again.

The target concerns a hypothetical original side square S below its
assigned original main M. Upward routing makes selected L and R upper,
so S is a different original. Its independent frame is eliminated only
after the full physical lower-side input theorems produce bounds on that
same M. The other main's frame is retained over its full range in the
height bridge; only M acquires h<31/50. Neither an extra selected cone
nor the desired no-lower-side conclusion is used as an input.

## 2. Complete actual-frame and coordinate coverage

Each selected original has its own folded slope in [0,1] and independent
chirality. The main has its own h in [1/2,31/50] and independent global
chirality sM. Folding modulo a square's quarter-turn symmetry gives the
actual axes (a,sb),(-sb,a), with a>=b>=0. The slope endpoints include
aligned frames and the diagonal frame; the duplicated representations
on those faces cause no omission.

Horizontal reflection and reversal of both marked chains preserve the
palindromic fixed bits 010/11. They permit xP>=0 while carrying every
actual frame and original identity along. The hypothetical lower square
can still be on either side; its side epsilon remains a separate sign.
Reflecting a left original to the right changes its local chirality to
-sM, so the signed profile index epsilon*sM in the checker is correct.

The true selected cone gaps are at least 1/sqrt(2)>707/1000. The outer
center bound then gives xP<=1129/3000 and zR>=7/10. The root interval
zL>=19/60 is a valid enlargement of the stronger actual lower bound.
It includes a selected L in the central strip as well as a true side L.

The source reconstructs the exact product of five independent signs,
two h pieces and two zL pieces: 32*2*2=128 roots. Its root integer uses
the five sign bits in the stated order, followed by the width piece and
left-position piece. The h pieces are [1/2,57/100] and [57/100,31/50];
the zL pieces are [19/60,3/5] and [3/5,13/12]. Both sides of every shared
face are closed. The three slopes, xP and zR have their full common
closed ranges in every root.

The original main coordinate band is relaxed by discarding only the
other main's nonnegative eta. Its reflection in the code has the correct
endpoint order. No main coordinate is assigned independently for a
physical pair that later requires that same coordinate: upper endpoint
maxima only enlarge the permitted set.

## 3. Main-to-P clearance and the first 21 rows

P is above M by the accepted original routing. The full horizontal
gap is at most

    1129/3000 + 61/60 - 1/2 = 893/1000 < 9/10.

Thus a downward owner cannot separate the original M/P pair. The four
upward normals in the source are exactly the two actual owners of M
and the two actual owners of P, with signs chosen to make their vertical
components nonnegative. Their physical support is at least one, so every
physical numerator exceeds 107/1000>1/10. Clamping it from below at
1/10 does not strengthen the bound on a physical configuration.

For the original main's axis-aligned inset, the largest possible
horizontal excess over g is at most

    1129/3000 + 1/60 = 393/1000 < 2/5.

Horizontal and downward separators are therefore impossible, and each
remaining P-owned numerator is greater than 1/2-2/5=1/10. The code's
second clamp is valid for the same reason. Increasing a positive vertical
denominator to at least 1/40 weakens the lower gap. An exactly horizontal
owner was already impossible; adding its finite clipped candidate to a
minimum remains conservative.

The maximum of the physical, inset and radial clearances is therefore
a valid lower gap for the same original M/P pair. Adding the maximum
of the accepted same-M height profiles yields the stated P lower bound.
The old profile is decreasing on all three of its affine pieces; the
signed polynomial is decreasing; the additional wide-height profile
3h-211/100 is enclosed directly. The source's endpoint enclosures have
the required directions.

All four signed original circle corners are reconstructed for L,P,R.
The endpoint rectangle local sign is -sL on the left and sR on the
right, as required by horizontal reflection. The raised left root uses
its own full original frame. On the low left root, the wide-main bands
give horizontal gap at most max(181/780,1/5)<6/25. The stated original
disk clearance and yB>-6/5 imply yL>-1/4. This argument covers central
selected L as well.

The ordered cone contractions preserve the same original heights and
use only the genuine selected L/P and P/R cones. The twelve pair rows
then use the proper height differences E=P-L and E=R-P, respectively.
The weak upper width comparisons are merely weakened to nonnegative
rows. All four true owners and both signs of each projected displacement
are represented in each ordinary pair test. The endpoint resource rows
use eta<=V as a relaxation and neither a good central floor nor the final
cap conclusion.

The signed-support routine encloses the true relative-angle support.
For equal chiralities it uses extreme angle differences and inserts the
minimum one if the slope intervals overlap. For opposite chiralities it
uses the endpoint angle sums and inserts the maximum (1+sqrt(2))/2 when
the exact monotone condition t+u+t*u=1 can be crossed. No actual frame
is replaced by a sampled orientation.

## 4. Why the normalized selected owner lists are exhaustive

For one original frame put

    u=(a,sb), w=(b,-sa),       a>=b>=0,

and let the actual selected displacement be (d,e), with d>0 and |e|<=d.
The four signed normals of this square are u,w,-u,-w. The normal -u
has projection at most (-a+b)d<=0 and cannot supply positive separating
support. Moreover

    u·(d,e) - (-w)·(d,e)
       = (a+b)d + s(b-a)e >= 2bd >= 0.

Thus whenever -w separates, u separates at least as well. Both axes
have the same support sum for a pair of unit squares. Consequently u,w
are an exhaustive necessary owner alternative. This proof includes b=0
and the equality cone faces; it prescribes no height order between the
two selected squares. Applying it to both frames gives exactly the four
owners used in terminals 21 and 22.

## 5. Terminal 21 preserves one actual P height

For each normalized owner, the source forms a lower interval bound N
on sigma-nx*D and a nonnegative interval for |ny|. If N>=0, division by
the upper denominator gives a lower bound on N/|ny|. If N<0 and the
denominator is bounded away from zero, division by the lower denominator
gives the correct lower bound. The integer quotient is rounded down.

When the denominator may be zero and N<=0, omitting the extra condition
is conservative. When it is identically zero and N>0, the owner is
impossible. All vertical components have a fixed sign on their folded
root; there is no unhandled sign-changing denominator. Negating the
rounded lower bound for a negative ny produces an outward upper bound.

The resulting left and right E intervals include every actual height
difference feasible under those owners, the original cone and the height
bounds. For any feasible owner pair, the single actual yP belongs to

    [Pminus,Pplus]
      intersect [Lminus+eLminus,Lplus+eLplus]
      intersect [Rminus-eRplus,Rplus-eRminus].

The source takes outward scalar endpoints for this intersection and
also retains both E-interval widths. A feasible owner pair therefore
makes all three widths nonnegative. Taking their minimum and then the
maximum over all 16 owner pairs is a valid rejection functional: a
strictly negative result excludes every possible pair. This is a box
feasibility test with a direct necessary-condition proof, not an
assumption that separately chosen P heights agree.

## 6. Terminal 22 keeps one main owner and cancels the same P

Let n be the actual upward M/P separating owner. For a shoulder S let
m be an actual selected owner directed from P toward S. The normalized
selected lists are valid by Section 4; the left list is negated when
directing it from P toward L. Thus the code's epsilon multiplier is
correct for both sides.

When my>=0, multiply the M/P inequality by my and the P/S inequality
by ny>=0. The sum is exactly

    (my*nx-ny*mx)*xP + ny*mx*xS - my*nx*xM
      +ny*my*(yS-yM) - my*sigmaMP - ny*sigmaPS >= 0.

The two occurrences of the actual yP cancel algebraically. Since the
height multiplier is nonnegative, using yS<=Splus and yM>=T(h) enlarges
the left side. Maximizing the xM term over its two actual band endpoints
also enlarges it. These are valid bounds even though the maxima need
not be attained at a common point. They can admit extra possibilities,
but cannot reject a physical configuration. When my might be negative,
the code uses only the ordinary original selected projection test.

The exact determinant substitution was checked separately for every
chirality. If P has frame (a,sb), its upward main-pair normals are

    n0=(sa,b), n1=(-sb,a),

and its normalized selected normals directed to side epsilon are

    m0=epsilon*(a,sb), m1=epsilon*(b,-sa).

Direct expansion using a^2+b^2=1 gives

| Coefficient my*nx-ny*mx | m0 | m1 |
|---|---:|---:|
| n0 | 0 | -epsilon |
| n1 | -epsilon | 0 |

This is exactly `ni==qj ? 0 : -epsilon` in the source. It is valid at
aligned frames and uses the same actual P frame on both sides of the
identity. Other owner combinations retain their full signed expression.

For each M/P owner, the source requires its own possible projection and
at least one possible selected owner on each side. It then takes the
maximum over the four M/P owners. A physical configuration supplies one
actual main owner that works in both shoulder tests, so this maximum
must be nonnegative. Strict negativity validly excludes the whole box.
The ordinary selected projection bound remains required even when the
cancellation bound is also used. No negative-weight combination and no
independent replacement main owner are introduced.

## 7. Exact arithmetic and finite acceptance boundary

The arithmetic kernel uses signed directed integer division, exact
128-bit products and checked integer square-root enclosures. Rational
root endpoints and dyadic midpoint coordinates are rebuilt by the
checker. Its parser recognizes only roots 0 through 127, seven split
coordinates, and 23 terminal rules. Each split retains both closed
children. It rejects truncated or trailing events, missing children,
invalid tags and every leaf whose reconstructed upper bound is not
strictly negative. The fixed-root and tree coverage therefore do not
depend on producer floating-point values.

I checked that the supplied complete-source binding recompiles the
whole reviewed source and records a byte-identical executable. Its
source and executable hashes match the final manifest. I also read
the targeted controls, including false whole-root uses of terminals
21 and 22. This audit did not rerun the 27.5-million-leaf arithmetic
forest; that remains the separate complete acceptance requirement.

Subject to that requirement and the accepted height inputs, the final
physical reduction excludes every original lower side square in the
stated low-P-floor 010/11 domain. It includes both sides, all original
frames, all selected vertical orders, and every boundary represented by
the 128 closed roots. It does not by itself assert the whole fixed mask
closed; the parent assembly must supply the remaining original cases.
