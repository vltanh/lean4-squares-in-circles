# Independent full review: three boundary returns and their actual middle section

Date: October 30, 2026 UTC.
Reviewer: axial-chain agent, independently of the source author.
Verdict: PASS. No mathematical or original-domain repair is required.

## 1. Exact source and scope

I read the complete frozen source
THREE_BOUNDARY_RETURNS_FORCE_A_HIGH_MIDDLE_UNIT_AND_A_UNIT_SECTION_2026_10_30.md,
8,086 bytes, SHA256
99c6d7fc3bb50cf65f8ee36ef1e041dafb344671a5a09830e691746ef1f7f528.
I reconstructed both the section theorem and the whole force-free
three-return theorem, including the closed floor, all orientations,
the actual angular order, and the quantitative disk inclusion.

The source concludes:

- Every actual contained unit wholly above height 3/8 has a
  nondegenerate section at height 5/4 of length at least one, strictly
  greater than one if it is tilted.
- For a physical boundary pair with actual horizontal support gap at
  least two and 2 <= R <= sqrt(1105)/16, there are at most three
  other physical boundary squares wholly in the open upper halfplane.
- If there are three, their actual middle square lies wholly above
  height 83/160 and contains in its open interior the entire closed
  radius-1/40 disk centered at (0,5/4).

These statements do not require selected graph order, positive loads,
endpoint degree equations, a common square frame, or altered means.
They do not assert a complete seven-body or nine-body exclusion.

## 2. Complete section formula and strictness

With a >= b >= 0, a^2+b^2=1, h=(a+b)/2, and
delta=5/4-y, the original floor gives delta <= 7/8-h.
The actual highest vertex has height y+h <= R < 17/8, which
gives delta > h-7/8. Thus |delta| <= 7/8-h. The width formula

    W = min(1/a, (h-|delta|)/(a*b))

for b>0 follows directly by intersecting the two own-coordinate
strips with the horizontal line. In the central band
|delta| <= (a-b)/2 the opposite edges give width 1/a.
Beyond that band the two adjacent edges give the other expression.
The expressions agree at the band endpoints. Reflection of the tilt
does not alter width.

The line lies strictly between the top and bottom supporting lines:
top >= 3/8+a+b >= 11/8, while bottom <= R-a-b < 9/8.
Thus no tangent or empty section enters the proof.

For b>0, a<1, so 1/a>1. Also, with w=a+b in [1,sqrt(2)],

    h-|delta| >= w-7/8,
    w-ab = w-(w^2-1)/2 >= sqrt(2)-1/2 > 7/8.

The derivative of the middle scalar function is 1-w <= 0.
The final radical comparison follows from sqrt(2)>11/8,
whose squared reserve is 7/64. Consequently both candidates in
the minimum are strictly above one. For b=0 the actual section
is exactly one unit long. This proves the claimed full orientation
and equality scope.

## 3. Boundary-angle localization

The two imported geometric premises were already fully reviewed in
this continuation, and their frozen pins match the source:

- CENTERED_INNER_ARC.md, SHA256
  fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5,
  proves physical-boundary center separation strictly above 40 degrees.
- LONG_RUN_RETURN_MARKS_WHOLE_SIDE_CLEARANCE_AND_SHORT_NORMAL_CONE_2026_10_30.md,
  SHA256 c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e,
  Section 2 proves, from the actual support gap alone,
  endpoint center angles within five degrees of the signed long axis.
  I reread that entire local section for this review. Its later
  compatible-cycle order argument is not used here.

Each proposed return center has angle in (0,180 degrees).
Its physical separation from the two long endpoints therefore puts
it in (35,145 degrees). Four such centers would have span strictly
above 120 degrees, inside an interval of width 110 degrees.
There can be at most three. For three ordered centers, the middle
angle is strictly between 75 and 105 degrees. This ordering is the
ordinary ordering of actual center directions; it is not a graph order.

The actual boundary corner gives r >= R-1/sqrt(2)>31/24.
The universal contained-center bound is r<91/60. As
sin(75 degrees)>19/20 and the vertical halfwidth is below 17/24,
the entire middle square has height greater than

    (31/24)(19/20)-17/24 = 83/160.

In particular the first section theorem applies literally to that
unchanged square.

## 4. Quantitative interior disk

The exact trigonometric comparison

    sin(75 degrees)^2 = (2+sqrt(3))/4
                     > 37/40 > (24/25)^2

is valid; the last positive reserve is 17/5000.
For P=(0,5/4), the source consequently has

    |c-P|^2 < r^2+25/16-(12/5)r.

The quadratic is convex on the entire enlarged interval
[31/24,91/60]. Its two exact endpoint values are 377/2880
and 401/1800, respectively, and the second is larger.
Finally

    (19/40)^2-401/1800 = 41/14400 > 0.

Therefore |c-P|<19/40. Every point of the closed radius-1/40 disk
about P has distance strictly below 1/2 from c. The original square's
open incircle contains that entire closed disk. Both strictness and
the inclusion of the proposed disk's boundary are justified.

## 5. Caller and limitations

The source's long-channel caller retains the original force line:
two full unloaded degree-two transmitters give its real occupied
length-four segment, hence R>=2. The separate positive-long-endpoint
theorem supplies actual boundary endpoints. No equation at a return
body is needed. The three other boundary squares may have zero
circle multiplier and need not be a selected path.

The final scope warning is necessary and correct. A full unit-length
middle section can bound a gap between two outer sections only after
both sections exist and their actual line order is proved. Even such
a section gap alone is not a lower bound for the whole-set Euclidean
distance of the outer squares. The source does not make either
unproved inference and does not claim a global completion closure.

This review uses complete continuous proofs and exact fixed rational
comparisons. It used no pose search, parameter mesh, graph mutation,
normal reselection, mean replacement, Lean compilation, CI, or
ledger change.
