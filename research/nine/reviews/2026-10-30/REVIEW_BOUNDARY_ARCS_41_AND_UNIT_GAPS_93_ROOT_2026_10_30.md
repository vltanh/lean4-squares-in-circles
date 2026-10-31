# Root review: complete 41-degree arcs and 93-degree set-gap bounds

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete frozen mathematical source and all its stated callers.**

The whole source
`BOUNDARY_ARCS_41_AND_UNIT_GAPS_93_DEGREES_EXCLUDE_FIVE_LOAD_EIGHT_CYCLES_2026_10_30.md`
was read and reconstructed independently of its author. Its SHA256 is
`aec4e482006c95ceadb6e3c9456c900ff6321511ea7bf61b1f7db2468c6c4c09`.
The separate full review by block_ears was also read in full:
`REVIEW_BOUNDARY_ARCS_41_AND_UNIT_GAPS_93_BLOCK_EARS_2026_10_30.md`,
SHA256 `af9dfd0062a6e0461f120fdfec367ac532f813ac5fea99882d127b911022910f`.

## 1. Entire interior arcs, with both coordinates covered

For each physical boundary square the actual farthest-corner equality,
in its own frame, is

    r^2+r(s+c)+1/2=R^2,  c>=s>=0, c^2+s^2=1.

Completing the square and applying the square-root tangent at sc=3/8
gives exactly

    r<=355/176+(4/33)sc-(s+c)/2.

The common center bound r<91/60 and the boundary lower bound r>5/4
hold on the entire stated radius window. Both proposed arc radii are
strictly below 5/4. Hence every point of either closed arc has positive
inward radial displacement bounded by r-A and transverse displacement
bounded by B. This proves the reductions to both F1 and F2 throughout
the interval; it does not infer arc containment from endpoints alone.

The coefficient of c in the first-coordinate estimate is positive. Its
uniform lower bound on the enlarged interval [0,3/4] is 117/2200. Thus
substituting c<=1-s^2/2 preserves the upper-bound direction. The resulting
quartics and both displayed shifts were independently recomputed using
exact fractions and coefficient identities.

For the boundary profile the shifted quadratic coefficient is at least
6434/20625 and the remaining constant/linear lower reserve is
580337/275000000. For the gap profile the corresponding bounds are
25309/118800 and 359/285120. Negative values of the shifted variable
improve the linear estimates and do not leave an uncovered interval.

The boundary profile has A+B>M, so F1>=F2 globally. The gap profile
requires the source's additional split: on s<=1/2 the convex cubic U
has endpoint reserves 57/4400 and 163/35200 below 1/2; on s>=1/2 the
assumption r>=A+B would exceed Q by more than 39/6400. Thus F1>=F2
on that second interval. Both sides include the split point, and the
diagonal endpoint s=1/sqrt(2) is covered. Both complete closed arcs
therefore lie in the open square interiors with strict reserves.

## 2. Exact trigonometric comparisons and pair consequences

The positive-integral proof of pi<22/7 was checked by multiplying its
stated polynomial quotient by 1+x^2 and restoring the remainder; the
polynomial integral is exactly 22/7. The triple-angle tests at 31/33,
47/50 and 137/400 use the correct monotonic branches. In particular the
sine test exceeds 13/15 by 5941/48000000, and (13/15)^2>3/4.

The addition-formula bounds at 20.5 degrees have exact values

    C0=981141437/1047816000,
    S0=44189/126000,
    3C0-8S0=1206173/349272000>0.

Consequently tan(20.5 degrees)<3/8<439/1170. The latter comparison
has reserve 1/4680. Two boundary centers separated by at most 41
degrees would share a point of the same complete closed interior arcs,
which is impossible for distinct physical squares.

For the 93-degree threshold, the exact rational upper estimate is

    67 cos(delta)+139 sin(delta)<29669/420<707/10<50 sqrt(2),
    delta=pi/120.

The middle reserve is 5/84 and the final positive-square reserve is
2-(707/500)^2=151/250000. For every theta between zero and 93 degrees,
the facing points have distance

    2 |A sin(theta/2)-B cos(theta/2)|<1.

The expression within the absolute value increases from -9/25 to
a value strictly below 1/2. This includes the angle endpoints and
independent square frames. A true set distance at least one therefore
forces a center angle strictly greater than 93 degrees.

## 3. Compatible order and the full cycle caller

The source imports the same actual marked order already fully reviewed
in the frozen base theorem, SHA256
`b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.
The 105/175-degree refinement has unchanged SHA256
`614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc`.
The root previously reconstructed those complete inputs, including the
physical spoke order, arbitrary marked degrees and single-certificate
scope. Their full sources and the present literal joins were checked
again where used.

Actual common-normal supports give endpoint set gap at least one for
each singleton run. Each consecutive directed angular gap is at least
the corresponding minor angle, even when the directed gap is a major
arc. Thus the unchanged full-turn sum gives

    41m+11k1+12d+52ell<360,
    41m+11k1+12d+52ell<=359.

Here d is a subset of singleton count k1, not an additional run count.
The exact integer rows at m=8 are six marks with two nondiagonal
singletons, seven marks with at most one diagonal singleton, or eight
marks with no internal body. In particular the entire five-mark
family exceeds one turn by the estimate 3*93+2*41=361, regardless of
the singleton orientations or placements. The six-mark family with
one diagonal similarly costs more than 362 degrees.

In the full translational caller, every unmarked body has actual zero
circle load and true positive degree two in the whole retained graph.
Arbitrary marked chords and attachments remain. Calling a nondiagonal
singleton a side-normal transmitter requires the same full moment
certificate; that additional requirement is stated explicitly. No
independent stress selections are identified.

The record seven-body orbit has budget 350 and is preserved. The
source's eight-body table is a necessary condition, not a realization
claim or a closure of an arbitrary chorded block. A later stronger
theorem may supersede this table without changing this frozen source.

## 4. Verification boundary

All newly checked constants and quartic identities are recorded in the
checkpoint's exact-arithmetic record. These checks use rational
arithmetic only. They verify the continuous hand proof; they are not a
packing enumeration, numerical pose search, angle grid or formal Lean
verification. No original inventory flag, common-selection gate,
unrestricted lower-bound claim or equality claim is changed by this
review.
