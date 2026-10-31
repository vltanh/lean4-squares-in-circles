# Independent full review of the uniform radius-two measure obstruction

Date: October 26, 2026.
Reviewer: block_attachments, separately from the author.

**Verdict: PASS.** The geometric normalization, every analytic
reduction, the fixed-point interval arithmetic, the exhaustive
recursive cover, and the open-interior additive-measure conclusion
are sound. The result is the full geometric theorem that every
packing of nine unit squares has containing radius R>2.

Reviewed sources:

- NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md;
- NINE_RADIUS_TWO_MEASURE_CERTIFICATE.py.

This is a review of one uniform finite certificate with 208
charged leaves, not a table-free proof. No original graph gate
or checklist entry is changed by this review. Any exact original
C6 gate assembly remains the responsibility of its separate
scope review.

## 1. The measure really proves a packing obstruction

The four uniform circle measures and the origin atom define one
nonnegative Borel measure, invariant under all rotations and
reflections about the original disk center. Their integer
weights sum exactly to

    292+714+3858+2424+1709=8997.

Thus the total measure is 8997/1000, strictly below nine.
Charging the open interior of each actual unit by at least one
contradicts finite additivity for nine disjoint open interiors.
This argument does not need the physical square boundaries
to be pairwise disjoint.

The point mass at zero is used only when zero is in the OPEN
square. A shared or tangent origin point receives no atom.
For each positive-radius circle, the intersection of a square's
boundary with that circle is finite; dropping those points
does not alter its uniform angular measure. Thus using closed
coordinate inequalities to compute those angular lengths
does not double-count a positive circle mass.

The conclusion applies to every nine-square packing in a
closed radius-two disk, with arbitrary independent frames.
It has no force graph, load selection, neighbor-degree,
circle-weight, or n=8 prerequisite. The larger-radius
ADDITIVE_MEASURE_OBSTRUCTION.md is compatible: it concerns
the strictly larger disk of squared radius 17/4.

## 2. Own-frame normalization is exact and exhaustive

For each actual square independently, use its actual side axes,
reflect their signs so its center coordinates are nonnegative,
and interchange them so x>=y. Since the same measure is
orthogonally invariant, this is a valid evaluation of that
square's charge under the original common measure.

Writing a=x+1/2, b=y+1/2 gives exactly

    S(a,b)=[a-1,a] x [b-1,b],
    1/2<=b<=a, a^2+b^2<=4.

The farthest own-frame vertex is (a,b), including x=0 or
y=0 ties, so the last inequality is equivalent to full
closed-square disk containment. In particular b<=sqrt(2).
No physical circle vertex, support normal or center-axis
assumption has been added.

The independent normalization for evaluating different
squares is legitimate because the measure is invariant;
the proof still sums the masses of their original disjoint
open interiors. It does not move the packing.

## 3. All four analytic reductions pass

### 3.1 The central region and its boundary

For a<=9/10 and 1/2<=b<=a, the origin is strictly inside
the square and the radius-1/10 circle lies inside it except
for finitely many possible boundary tangencies. Thus the
charge is at least 1006/1000. The equalities a=9/10 and
b=9/10 are included correctly.

### 3.2 The vertical translation comparison

For 9/10<=a<=11/10, 1/2<=b<=9/10, both the origin
contribution and small-circle contribution are independent
of b. This includes a=1, where the origin atom is absent.

For each radius r>=1 and each relevant |y|<=9/10,

    sqrt(r^2-y^2)>=sqrt(19/100)>1/10.

The negative x branch lies outside the square, and the
positive branch automatically satisfies its lower x bound.
The remaining angular density is exactly the displayed
even function

    1/sqrt(r^2-y^2) * 1_{sqrt(r^2-y^2)<a}.

As |y| increases its indicator can only change from zero
to one, and the positive density factor increases. Shifting
[-1/2,1/2] to [b-1,b] removes an interval of absolute
coordinates at most 1/2 and adds an equal-length interval
of coordinates at least 1/2. Therefore the angular integral
cannot decrease. The proof covers discontinuities of the
indicator, since they change only finitely many endpoints
and the comparison is an integral inequality.

This verifies the entire two-dimensional reduction to
b=1/2. The split at a=1 in the finite certificate is
correctly conservative for the atom.

### 3.3 The middle strip's endpoint minimum

For 11/10<=a<=3/2 and 1/2<=b<=1, put A=a-1.
The circle upper-x bound is inactive at radii 1 and 11/10;
A lies in [1/10,1/2]. The lower-x bound leaves the exact
positive-branch angular interval with
t=sqrt(r^2-A^2)>1/2.

The displayed g_r(b) is nondecreasing before b=t and
decreasing afterwards. Before the cutoff, differentiating
its two arcsines gives the nonnegative difference of
1/sqrt(r^2-b^2) and 1/sqrt(r^2-(b-1)^2), because
b>=|b-1|. After the cutoff only the second term varies.
Thus a minimum on [1/2,1] occurs at an endpoint, including
the possible cutoff and endpoint equalities.

At b=1/2 the value is 2asin(1/(2r)). At b=1:

- if t>=1, convexity of asin and asin(0)=0 give the same
  lower bound;
- if t<=1, its value is acos(A/r), which is at least
  acos(1/(2r)) and then at least 2asin(1/(2r)), since
  asin(1/(2r))<=pi/6.

This proves the complete strip estimate.
I independently checked the exact two rational reserves:

    5/11 - (47/100-(47/100)^3/6+(47/100)^5/120)
      =21887804923/13200000000000>0,

    3858/6000+(2424/1000)(47/100)(7/22)-1
      =189/34375>0.

The sine bound is the upper odd Taylor truncation at
47/100 in (0,pi/2). Monotonicity of sine gives
asin(5/11)>47/100. The independently constructed pi
upper bound is below 22/7. No finite box or floating sign
is substituted for any part of this strip.

### 3.4 The outward comparison and all remaining domains

For a>=27/20, all four support radii are at most a.
Hence the upper x constraint is inactive for their
angular measures, except for irrelevant tangent points.
Increasing a to sqrt(4-b^2) raises only the lower x
threshold and cannot increase any of the four charges.
The origin is outside both squares. The comparison
square remains in the normalized domain because
b<=sqrt(2) implies sqrt(4-b^2)>=b.

The five roots cover the exact remaining domain:

- a<=9/10 was already charged analytically;
- for a in [9/10,11/10], b<=9/10 reduces to the line,
  and b>=9/10 is in the corner rectangle;
- for a in [11/10,27/20], b<=1 is in the proved strip,
  and b>=1 is in the middle rectangle;
- a>=27/20 reduces to the outer boundary curve.

All equalities and overlaps are retained. The outer
interval [1/2,3/2] enlarges the actual b range and its
strict empty test removes only b>sqrt(2).

## 4. Whole-box angular lower bounds and origin bookkeeping

For every a in [a_l,a_h] and b in [b_l,b_h], the common
open rectangle

    (a_h-1,a_l) x (b_h-1,b_l)

lies inside every actual square interior in that box.
All nonempty boxes used by the checker have a_l>0 and
b_l>0. Thus the exact origin criterion is a_h<1 and
b_h<1, as implemented. A box ending at 1 receives no
atom, even if some of its interior parameter points
could have received one; this only lowers its charge.

In a nonnegative quadrant, the x and y inequalities give
the maximum of the two lower angular bounds and the
minimum of the two upper angular bounds in the source.
Clipping arguments to [0,1] is correct: when a required
lower coordinate exceeds the radius the resulting
positive-part interval length is zero. Degenerate
rectangle pieces likewise have zero angular measure.
Reflecting into the four quadrants double-counts at most
axis points, of measure zero.

For the outer curve, b is positive and
a_*(b)=sqrt(4-b^2) is decreasing. The lower integer
square root at b_h and upper integer square root plus
one at b_l therefore enclose its complete image.
This also covers boxes straddling b=sqrt(2); the
extraneous part is a harmless enlargement.

## 5. Audit of every fixed-point interval operation

The checker uses coordinate denominator B=83886080 and
angular scale Q=72057594037927936. All acceptance
arithmetic consists of integers; its rational strip
checks use exact Fraction values. No hidden floating
division enters an acceptance branch.

### Arctangent and pi

In atan_small, the stored lower and upper squared
arguments enclose Q*x^2. Induction through the
floor/ceiling product recurrence encloses each scaled
odd power. The positive terms use lower values for
the lower sum and upper values for the upper sum;
the negative terms reverse those roles.

Sixteen terms end at -x^31/31. The exact remainder
integral is positive and bounded above by x^33/33.
The code's next power enclosure is exactly the x^33
one. Thus the lower sum is below atan(x), and adding
the upper next term yields a valid upper bound.

The initial 1/5 and 1/239 arguments are themselves
enclosed outward, and atan is monotone. Machin's
identity combines positive and negative interval
terms with the correct endpoint reversal. Its branch
is elementary: 4atan(1/5)-atan(1/239) is in (0,pi/2)
and has tangent one.

For 1/2<x<=1, the transformed argument
(1-x)/(1+x) lies in [0,1/3]. Its floor and ceiling
are outward, and subtracting its atan interval
from the pi/4 interval uses the correct signs.

### Arcsine and arccosine

For t=n/d in (0,1), the code first encloses t by
scaled integers t_l,t_h. Then

    Q-ceil(t_h^2/Q), Q-floor(t_l^2/Q)

bound Q*(1-t^2) outward. The floor square root
and floor square root plus one correctly enclose
Q*sqrt(1-t^2). The lower ratio uses the lower
numerator and upper denominator; the upper ratio
uses the upper numerator and lower denominator.
Clipping the latter to Q is valid because the
true half-angle ratio is at most one.

Monotonic atan and the exact half-angle identity
then give the stated asin enclosure. The explicit
t<=0 and t>=1 branches cover clipping endpoints.
The arccos bounds subtract the asin endpoints
from pi/2 in the correct order.

In rect_arc_lower, the lower bound on the upper
angular endpoint and upper bound on the lower
angular endpoint yield a rigorous lower length.
The positive-part operation and the sum over
quadrants preserve that lower-bound property.

Finally, the accepted inequality uses the UPPER
pi numerator on the right. Dividing it by
1000*2*pi*Q yields circle charge at least the
remaining mass needed after the origin atom.
Every accepted box therefore proves the original
unit charge, not merely an approximate charge.

## 6. Exhaustive finite cover and independent rational reconstruction

For the corner and middle rectangles, either geometric
empty test is sufficient:

    b_l>a_h, or a_l^2+b_l^2>4.

Both are strict, preserving valid equality boundaries.
For the outer curve the sole empty test b_l^2>2 is
also strict. Every other box is accepted by its whole
rectangle charge or split into two closed children
whose union is the parent. All coordinate midpoints
are integers, and every actual split progresses.
The stack terminates with no unresolved box.

Running the submitted checker reproduced exactly:

| Domain | Charged leaves | Empty leaves | Splits |
| --- | ---: | ---: | ---: |
| line | 95 | 0 | 93 |
| corner | 14 | 3 | 16 |
| middle | 2 | 0 | 1 |
| outer | 97 | 3 | 99 |
| Total | 208 | 6 | 209 |

The maximum depth is 12. The minimum accepted original
integer margin is 4023192202688832. The original pi
numerators are

    226375608064909912,
    226375608064910268.

The ordered leaf digest reproduces exactly:

    d86a26a628643d32387e0ba9800dcfc1830335f7828d0335bcd9c2172767b0c5.

I also wrote a fresh independent implementation at
/tmp/review_radius_two_measure_fraction.py. It does
NOT use the submitted fixed-point power recurrence.
It evaluates every arctangent polynomial directly
as an exact Fraction, uses a separately proved
rational square-root enclosure, reconstructs
arcsines and all quadrant charges, and regenerates
the recursive cover from the five initial domains.

That independent implementation produced the same
208 charged leaves, six empty leaves, 209 splits,
maximum depth 12 and ordered leaf digest. Its
tighter rational enclosure had scaled minimum
margin 4023192205226863, still strictly positive.
Its independently computed pi interval has integer
floor/ceiling numerators

    226375608064910088,
    226375608064910089.

Both lie strictly within the submitted enclosure.
For all 1,974 distinct rational inverse-sine
arguments used by the independent reconstruction,
the submitted interval contained the entire fresh
exact-rational interval. There were zero containment
failures. Thus the arithmetic was checked by a
different evaluation route, beyond merely rerunning
the submitted program.

The digest and leaf count are reproducibility
checks. Exhaustiveness rests on the analytic domain
cover, strict empty predicates and closed-child
partition argument audited above.

## 7. Scope of the accepted theorem and its intended use

The source proves R>2 for arbitrary nine-unit-square
packings, without any of the selected-certificate
prerequisites. Every actual ninth square remains
in the additivity argument. The theorem is strict:
a packing in any radius at most two would also
be contained in the same-center closed radius-two
disk and contradict the measure bound.

Accordingly, any separately accepted original core
theorem forcing R<2 is incompatible with a full
nine-square completion, simultaneously for every
allocation, orientation and contact state of its
remaining extras. No new normal selection or
force perturbation is needed for that logical join.

The exact mapping to original C6 labels should
still be recorded in its own assembly review.
This review does not infer the stronger global
R^2>=1105/256 target, equality classification,
unproved larger graph cells, or Lean verification.
