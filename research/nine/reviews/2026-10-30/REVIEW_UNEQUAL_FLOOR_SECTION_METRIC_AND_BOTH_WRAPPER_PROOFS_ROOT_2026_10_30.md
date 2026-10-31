# Full root review: unequal-floor section metric and both oblique-wrapper proofs

Date: October 30, 2026 UTC.

**Verdict: PASS for the full stated continuous domains.** I read all four
sources below completely, reconstructed the actual section coordinates,
monotonicity, corner inequalities, contact-type cover, exact interval
polynomial, and literal physical callers. This is a full mathematical
review, not approval based only on arithmetic or an author's summary.

| Frozen source | SHA256 |
| --- | --- |
| UNIFORM_FLOOR_POSITIVE_TILT_LEFT_SECTION_BOUND_2026_10_30.md | `5029d8729481ff2a461fa1e3fd0aef05c1c89b1a555f9443f76fd5b8f3ffdbf0` |
| UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md | `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94` |
| OBLIQUE_ALIGNED_ENDPOINT_RETURN_SECTION_BOUND_BY_ACTUAL_UPPER_CORNER_TANGENT_2026_10_30.md | `a43df2c0bdf368d43c5858829e9a5594b8ac202fcfcf5b59e10d9282f8572bea` |
| ALIGNED_ENDPOINT_CORNER_WRAPPERS_OBEY_THE_UNEQUAL_FLOOR_SECTION_BOUND_2026_10_30.md | `55607f2ab5a25c056fcc12e893b3d4c7e60814c6d2e607c21b806277d29de5bc` |

The two wrapper authors exchanged scope questions and endpoint geometry.
Their actual inequalities are different: one uses an explicit tangent
contradiction and the other a direct positive squared difference. Both
are reconstructed below. Root previously suggested the corner-profile
direction, then reviewed the complete frozen proofs independently of
their derivations. These collaborations are not described as blind work.

## 1. Whole-floor section existence and every orientation

Set Q=1105/256, z=5/4, g(Y)=sqrt(Q-Y^2), C=g(f+1), with
3/8<=f<=1/2. For every unit square above f, its vertical width is
w=a+b>=1. Its top is at least f+w>=11/8>z; its bottom is at
most sqrt(Q)-w<=sqrt(Q)-1<9/8<z. Thus the section is a genuine
nondegenerate interval, with relative interior in the actual square
interior. No original mean or force is moved onto this auxiliary line.

Quarter-turn relabeling and reflection cover all frames by
u=(a,+/-b), with a>=b>=0, a^2+b^2=1. I solved the original side
inequalities and recovered all four left-edge formulas in the source.
The reflected formulas give the right endpoint. The b=0 case is
treated separately; no division by a vanishing tilt is used.

## 2. Positive tilts: complete monotonicity and active-edge cover

For the first left candidate the actual top vertex gives
a*ell_1=a*P_x+b*P_y-1-b*z. Its height is at least f+a+b.
The function a*g(Y)+b*Y decreases on the entire actual height
interval, because f+a+b>sqrt(Q)*b. The stated estimate is strict:
sqrt(Q)<17/8 and b<=1 give f+(2-sqrt(Q))*b>1/4.

The tangent inequality at f+1 has its correct concave direction. The
remaining algebra is exactly

    4[1-a+(3/4)a(a+b-1)-b(a+b-3/4)]
      =b(3+2a-a^2-7ab)/(1+a)>0.

Here 2a-a^2>=3/4 and ab<=1/2 leave the positive reserve1/4.
The strict first-candidate bound therefore holds without any active
edge restriction.

The second candidate is active precisely when delta>=t. Combining
this with the actual floor gives a<=k=z-f<=7/8. The source retains
the factor a/b in its comparison function F, which is essential.
I differentiated F with respect to f: the two g terms have positive
combined derivative, and the added a/b is positive. Reducing f to3/8
preserves all radical domains. At that floor, replacing D'(a+b)<2
in the derivative of F gives a^3+3b^3-7/8. The replacement has the
correct sign because b-a<=0. This cubic combination decreases on
the whole allowed interval and at a=7/8 exceeds239/256. The full
derivative is positive, not merely its sampled values.

The diagonal endpoint bound is exactly
31/20-17/16+7/5-7/8=81/80>1. The supplied radical comparisons
are strict positive-square comparisons. This covers both active edges
and their transition, over all floors and positive tilts.

## 3. Negative tilts: curvature, rational parameter and positive identity

For the first negative-tilt candidate I recovered the actual rightmost
corner identity and the function V. Differentiation gives

    partial_f V=b-a*integral_(f+a)^(f+1) Q/g(Y)^3 dY.

Both endpoints are at most3/2. The exact maximum17680/12167<3/2,
together with a(1-a)<b/2, proves partial_f V>b/4>0. The reduction
to floor3/8 is therefore uniform, including the diagonal orientation.

On the relevant lower interval Y>17/16, the curvature bound
-g''>3/4 follows from
Q^2-(9/16)(51/16)^3=13583/32768>0. Integrating in the correct
concave direction gives the upper tangent estimate with the negative
quadratic remainder -(3/8)(1-a)^2. Discarding that remainder would
not reproduce the claimed proof; it is retained throughout.

With tau=b/(1+a), the actual range is0<tau<=sqrt(2)-1<5/12.
The replacement K_0<221/250 has the right sign. I expanded the
entire rational expression after multiplication by8(1+tau^2)^2 and
obtained exactly

    N=1+(116/125)tau-14tau^2+22tau^3-15tau^4+(1134/125)tau^5.

I separately expanded every Bernstein basis term at tau=5xi/12.
All six ordinary coefficients agree exactly. Its six Bernstein
coefficients are the stated positive rational numbers, with minimum
24119/115200. Since their basis weights sum to1, this is a rigorous
positive lower bound on the full continuous interval. It is neither an
angle grid nor a numerical certificate.

For the second negative-tilt candidate the actual top corner gives
b*m_2<=sqrt(Q)-a*z-1. The needed concave function of a attains its
minimum at one of its two interval endpoints. Both lower bounds exceed
9/8>sqrt(Q)-1. This covers its entire domain without an active-edge
restriction. Together these steps prove strictness for every nonzero
tilt, and reflection completes both section endpoints.

## 4. Aligned equality and the sharp two-square metric

For an aligned square, actual farthest-corner containment gives
(|x|+1/2)^2+(y+1/2)^2<=Q. Equality in the section bound requires
the floor to be attained, the relevant sign of x, and the outer upper
corner to be on the Q circle. This gives exactly the stated equality
centers, with no unproved orientation-rigidity step.

For two actual sections, overlap implies actual set distance zero.
Otherwise the two actual endpoint points bound the set distance by
the section gap. The two whole-floor inequalities yield

    dist(S_1,S_2)<=g(f_1+1)+g(f_2+1)-2.

The displayed aligned squares attain this bound because their vertical
intervals overlap and their horizontal separation is positive. Strict
concavity of g and its strict decrease force f_1=f_2=7/16 when
the floor sum is at least7/8 and the actual distance is at least1.
The centers are then(-1,15/16),(1,15/16), and their outer corners
have squared normQ. An actual smaller disk is impossible.

The vertical-return cycle caller correctly derives nonpositive endpoint
heights from the full y-force equation, including the two-circle mask
at zero center height. It uses W's original support gap, not an assumed
horizontal short normal or a floor on W. The resulting sharp equality
fixes the four boundary anchors and the short direction; internal
transverse coordinates and original means remain physical variables.

## 5. Complete oblique contact cover and genuine section existence

The inner-face exclusion is valid with kappa=x+1, ell=1-f>=1/2,
and kappa-ell=x+f>1. The tangent manuscript reconstructs it fully.
A return lying in the inward horizontal halfplane would have every
corner strictly inside the actual q circle. It therefore cannot be a
physical boundary unit. This is a face/halfplane statement; it does
not incorrectly exclude a vertex using an oblique normal.

At the upper-inner vertex, a return-square vertex has a ninety-degree
interior cone avoiding B's southeast interior cone. Its two possible
geometric sectors put it wholly above the top side or wholly in the
forbidden inward halfplane. Equivalently the two equal-length support
normal intervals share a boundary axis. A strict original oblique normal
also excludes an aligned above-floor vertex. The remaining actual
contact is a return side-interior point, with its unchanged own normal
and full original side parameter. No generic-position or owner premise
is introduced.

Both sources prove section existence before using its endpoint. The
block proof uses C wholly above zero and the bound257/72 for its
entire norm if its top were at most5/4. The actual boundary B gives
q>15061/3600, with reserve737/1200. Annular's stronger local
statement does not need a positive floor on C: under the same supposed
top bound, all corners lie in(-1/2,3/2) x [-5/8,5/4], so their
norm squared is below61/16<4<q. Both arguments retain physical
circle contact and cover every permitted angle and slider.

## 6. The independent tangent proof of the wrapper bound

Eliminating the actual side parameter at height5/4 gives precisely the
two active left edges. On the opposite face,
(1-beta*k)^2-alpha^2(1-k^2)=(beta-k)^2>=0. Thus ell<=x-sqrt(1-k^2).
The sum g(h+1)+sqrt(1-(5/4-h)^2) is increasing throughout the
floor interval, because Q(5/4-h)^2>(h+1)^2. Its lower endpoint
exceeds163/80, yielding the uniform strict margin1/48.

For the other edge, assuming ell>=A0-1 bounds the actual slider
by r0. Its positivity gives beta>3/4. The actual upper corner Z
has z0.Z>=z0.Z0, where z0=(A0,B0) is on the Q circle and Z0
is only a comparison point. I expanded the exact tangent difference:

    (z0.Z0-Q)/alpha
      =(B0-A0)+(9A0/4-B0*K)beta
       +alpha[ A0*K+9B0/4-Q-(A0+B0)/(1+beta) ].

The coefficient67/320 is positive. Its first grouped term exceeds
281/1280. Concavity of J reduces its lower bound to two exact
endpoint comparisons,11929/6400 and7333/3840, both greater than
37/20. Since A0+B0<3, the last bracket exceeds19/140. The
result z0.Z>Q contradicts Cauchy for the actual contained corner.
Every side parameter is retained, and Z0 is never substituted into a
physical square or force equation.

## 7. The independent positive-square proof of the wrapper bound

Annular uses the actual upper corner P and its own coordinates to give

    beta*ell_1<=sqrt(Q-E^2)-1-alpha*z,
    E=1-alpha*x+beta*f.

The radical domain follows from the actual corner. With d=g(f+1)-1,
I expanded the exact difference between the squared proposed upper
bound and Q-E^2. It equals alpha times the displayed braces in
Section4. The estimates have their correct strict directions:
2(z-x)>7/15, zd-xf>=37/960, and the bracket is greater than
-3/16. Since alpha<=1, the whole braces exceed67/240. The
comparison quantity1+alpha*z+beta*d is positive, so the square
comparison yields ell_1<d over both angular halves.

For ell_2 the actual outer corner of B is indispensable. It implies
D=x+1-g(f+1)<=g(1-f)-g(1+f). Rationalizing gives
D<7f/6 because the denominator is greater than24/7. Convexity of
(7f/6)^2+(5/4-f)^2 bounds it by its larger endpoint245/256<1.
Cauchy then proves alpha*D+beta*k<1 and ell_2<d. This controls
both candidates separately, including their active-edge transition.

## 8. Caller and adoption boundary

The wrapper bounds are one-sided: the right return supplies its left
endpoint bound and the left return its right endpoint bound. A full
cycle join must prove their section order. Actual contact x coordinates
and square width<=sqrt(2) put the entire right return in x>-1/2
and the entire left return in x<1/2. Reversed section order would
give a gap<1 and contradict their actual set distance>=1. This
supplies the missing order without assuming center order determines
section order.

With that explicit order and the actual coupled floor sum, the sources
are sufficient for a sharp theorem for the entire opposite long/short
seven-cycle. Its separate joined proof must state the original full
true-degree and physical-boundary hypotheses. None of these sources
alone covers arbitrary chorded seven-body blocks, the adjacent orbit,
or all remaining physical completions.

Exact rational and polynomial checks are recorded in the next checkpoint.
No Lean/Lake build or CI was used. The earlier off-scope exploratory grid
is disclosed by the cap source and the preceding adoption; no numerical
observation was used in this review or in any adopted mathematical step.
