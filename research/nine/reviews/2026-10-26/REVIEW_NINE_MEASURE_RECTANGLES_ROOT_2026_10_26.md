# Root review: direct analytic charges for both residual rectangles

Date: October26,2026.

**Verdict: PASS for NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md
and its optional rational-identity reconstruction helper.** The entire
corner and middle domains are covered, including all atom boundaries
and every actual coordinate order. No interval charge evaluator is
needed for either domain. This is not by itself the complete global
measure proof; the line and outer regions keep their separate joins.

## 1. Fixed elementary comparisons

The signed Taylor bounds t-t^3/6<=sin(t)<=t-t^3/6+t^5/120 hold
throughout0<=t<=63/50: the alternating terms decrease there.
Every displayed t is less thanpi/2 using pi>3, so monotonic sine
recovers each claimed strict inverse-sine comparison from the displayed
positive rational reserve. I checked all nine lower and five upper
comparisons and ran the exact Fraction identity reconstruction.
It verifies those14 explicit identities and all six final mass reserves;
it contains no inverse-trigonometric evaluator or parameter boxes.

## 2. The four corner regions

For a<1, b<=a makes both lower coordinates strictly negative, so the
actual square receives the origin atom. Its contained rectangle
(0,9/10)^2 does not receive the atom. The rectangle supplies a small-
circle quarter and the two stated large-circle arcs. Separating the
actual atom from that rectangle is essential and is done correctly.
The positive numerator uses1/pi>7/22 and gives reserve11613/2200000.

For b>=1, the common rectangle(1/10,1)^2 lies in every actual
interior, including endpoints. The radius1 and11/10 arcs have exactly
the stated faces: at the latter's upper face the other coordinate
sqrt(21)/10 exceeds1/10. The negative inverse-sine term uses pi>3,
while the positive term uses pi<22/7; both directions are correct.
No small-circle or origin mass is assumed. Reserve5761/90000 follows.

For1<=a<=21/20,b<=1, the fixed rectangle
(1/20,1)x(0,9/10) is contained in each actual interior.
Its small-circle first-quadrant wedge has lengthpi/3, hence weight
w0/6. The large-circle lower x face is inactive, and their upper
faces give precisely the two displayed arcs. This includes b=1
without an atom. The positive numerator gives reserve14681/4400000.

For21/20<=a<=11/10,b<=1, I checked the full measure comparison
to S(21/20,9/10). At radius1, the exact strip arc increases until
b=sqrt(1-(a-1)^2) and decreases afterward. Its lower endpoint is
the smaller one because cos(2*asin(1/10))=49/50>9/10.
For the other radii, on-1/10<=y<=1 the positive x branch is greater
than1/10, making the lower x face inactive and excluding the negative
branch. Its angular density is even and nondecreasing in |y|, including
the upper-x cutoff. Moving b upward removes only small absolute
ordinates and adds larger ones, so the integral cannot decrease.
This proof explicitly retains the possible negative-y contribution
near a=11/10.

At b=9/10 the lower x face remains inactive for all three large
circles, and increasing a can only add charge. The resulting three
comparison arcs are exact; the two larger circles have no negative-y
arc because their upper-x intersections have |y|>1/10. The displayed
Taylor bounds give reserve2423/550000. No square is physically moved.

These four regions cover every9/10<=b<=a<=11/10, including a=1,
b=1 and a=21/20. In particular no limiting boundary atom is used.

## 3. The two middle regions and actual coordinate order

For1<=b<=6/5, the common rectangle is
(7/20,11/10)x(1/5,1). Both coordinate intervals are contained in
every actual interior because a<=27/20 and a>=11/10.
I checked every positive-quadrant face selection:
at radius11/10,400+49<484 selects the upper y face;
at radius27/20,400+49<729 and484+16<729 exclude the lower faces,
and400+484>729 ensures a positive upper-face arc.
The signed arc estimates give a positive combined non-pi numerator,
so pi<22/7 has the correct direction. Reserve19681/550000 follows.

For b>=6/5, the original order b<=a also gives a>=6/5.
The common square(7/20,6/5)^2 is therefore contained in the entire
actual region. The two smaller circles have inactive upper faces.
For radius27/20,625/729<1 excludes the lower faces at the upper
intersections, and2*(8/9)^2>1 makes the upper-face arc positive.
The combined non-pi numerator is negative in this case, so pi>3
is required and correctly used. Reserve2897/75000 follows.
The splitting equality b=6/5 is retained in both arguments.

## 4. Exact scope and integration consequence

The proof removes all14 former corner charge checks, both middle
charge checks and the3 remaining corner empty tests. The actual
order b<=a is used directly; no invalid triangle portion is charged
or discarded by a numerical partition. The14 fixed Taylor reserves
and six mass reserves are displayed hand inequalities, not hidden
interval-certificate output.

With the independently reviewed line and outer reductions, only
five fixed mass enclosures and the outer fixed derivative enclosure
remain as computational charge dependencies. Integration must still
retain the original global normalization, large-domain analytic
reductions and every exact endpoint. The original208-check proof
remains a valid historical alternative. The global theorem still
has finite fixed checks and is not claimed to be table-free.

No force graph, stress, orientation or contact premise has been added.
All nine original squares and every physical mask and individual-weight
possibility remain. No Lean compilation or CI was run.

