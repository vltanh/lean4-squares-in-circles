# Independent full review: centered boundary arc without coefficient tables

Date: October 28, 2026 UTC. Reviewer: s_family, separate from the author.
Read base: c31ecd109097dde3c8faa1db11a84655575e87ab.

**Verdict: PASS at the exact source hash below.** The complete new source
proves every mathematical export of the former centered-arc source. The
replacement removes both seven-coefficient Bernstein rows from this
theorem's mathematical dependency. This review assigns no new original
fine or coarse closure and does not certify unrelated caller premises.

## 1. Frozen sources and the complete export comparison

The reviewed new source is

    BOUNDARY_CENTERED_NINE_EIGHTHS_ARC_WITHOUT_COEFFICIENT_TABLES.md
    SHA256 a7227187917d53d0012bc04c002b0d24e33e5419da798381e899477a3861d1ab.

The old source was separately read in full:

    BOUNDARY_UNIT_CENTERED_NINE_EIGHTHS_ARC.md
    SHA256 1d0be3caa6be9257a6f4a3998281fe0c858229ccffde8ec6fa8942fae31aa8f6.

Both sources export exactly the following physical theorem. For an actual
unit square contained in D_(sqrt(1105)/16), if its actual center has norm
at least 27/20, its entire closed radius-9/8 arc centered at its actual
center direction, with halfwidth beta=atan(7/20), belongs to the square's
open interior. Both include every orientation and arc endpoint and have
no force, degree, circle-load or contact-owner premise.

Both export the same consequence for every actual boundary unit throughout
sqrt(17)/2<=R<=sqrt(1105)/16. Both also export, with alpha=atan(2/5),

    alpha+beta>2pi/9,
    atan(6)-alpha-beta<2pi/9.

The new source retains all three exports, with the same strictness. Its
new scalar proof is self-contained; the old polynomial or its coefficient
rows are not mathematical premises.

## 2. Actual containment and the complete affine radius estimate

Choosing a positively oriented own frame with nonnegative center
coordinates is legitimate for every original square, using signed
quarter-turns and interchange of its own orthogonal directions. With
c=r(x,y), x,y>=0 and x^2+y^2=1, the farthest-corner identity is exactly

    r^2+r(x+y)+1/2<=1105/256.

The orientation variable t=x+y traverses the entire closed interval
[1,sqrt(2)]; neither aligned endpoint is omitted. The proposed affine
comparison L(t)=28/15-(7/20)t is positive throughout. For example
sqrt(2)<3/2 gives L(t)>161/120>0.

Direct hand expansion of L(t)^2+tL(t)+1/2-1105/256 gives precisely

    -(91/400)t^2+(14/25)t-19121/57600.

Its concavity makes its minimum on the whole interval occur at an
endpoint. The displayed endpoint values are correct: 31/57600 at one,
and a lower bound 3799/1440000 at sqrt(2), using sqrt(2)>141/100.
The latter radical comparison has the stated positive reserve 119/10000.
Thus the original containment and strict monotonicity in r imply r<L(t)
throughout the full domain. No interval grid or sampled orientation enters.

## 3. Independent expansion of the completed squares

The proposed identity was expanded term by term. The first square supplies
the x^2 coefficient 9/20, xy coefficient 7/20 and linear x coefficient
-13/16. Its y^2 coefficient is 49/720; adding the second square's 23/720
gives 1/10. The two linear y terms add to -3/8. The constant terms,
including 11/1840, add to 2/5. Thus the right side is exactly

    (9/20)x^2+(7/20)xy+(1/10)y^2
      -(13/16)x-(3/8)y+2/5.

Its difference from the asserted left side is exactly
(x^2+y^2-1)/10. Hence the identity is valid on the whole actual circle,
not only at finitely many orientations. Both squared coefficients and
the remainder 11/1840 are strictly positive.

The comparison 1559/1920<13/16 has positive difference 1/1920.
Multiplying the affine r bound by x>=0 is valid even at x=0. The
displayed scalar inequality therefore holds with its uniform reserve
of at least 11/1840, retaining both x=0 and y=0. The proof uses one
sum-of-squares identity in ordinary real variables, not a hidden
orientation-dependent coefficient table.

## 4. Both coordinate deviations and the closed angular endpoints

For beta=atan(7/20), the exact trigonometric comparisons are correct:
cos(beta)>15/16 and sin(beta)<1/3, with integer squared reserves 1375
and 8. For every |tau|<=beta, the first coordinate deviation is

    (rho cos(tau)-r)x-rho sin(tau)y,  rho=9/8.

Since r>=27/20>rho and x,y>=0, its positive part is below 3/8. Its
negative is bounded above by (r-135/128)x+(3/8)y and hence is strictly
below 1/2 by the full scalar argument. Exchanging x,y and reversing
tau proves both bounds on the second coordinate as well. This is exactly
the open-square criterion; no angular projection of the whole unit is
substituted for the actual occupied inner arc.

Every inequality used here holds also when tau equals either closed
endpoint. Thus the closed arc is wholly inside the open square, which
is the strict statement needed by the original callers.

For an actual boundary unit, |c|>=R-1/sqrt(2). The rational comparisons
sqrt(17)/2>103/50 and 1/sqrt(2)<71/100 have reserves 4/625 and 41/10000.
They give |c|>27/20 including the critical radius endpoint. No physical
mask or weight assumption is introduced.

## 5. The angle comparisons and their branches

The addition/subtraction formulas yield 75/86, 28/17 and 441/536
exactly as displayed. The sums and differences are all in (0,pi/2),
so the principal arctangent comparisons use the right branches.

Both atan(5/6) and atan(6/7) lie strictly between pi/6 and pi/4;
their triples lie in the second quadrant. Their exact triple tangents
are -415/234 and -666/413. The squared reserves 7957 and 68151 give,
respectively, a tangent smaller than -sqrt(3) and a tangent larger
than -sqrt(3). Strict monotonicity of tangent on that quadrant gives

    atan(5/6)<2pi/9<atan(6/7).

Together with 441/536<5/6 and 75/86>6/7 this proves both original
mixed-gap exports with strict endpoints. No numerical inverse-angle
bound is needed.

## 6. Exact direct caller inventory and substitution boundary

A repository text search at the read state found four mathematical
callers naming the old source. Their full uses of the old exports were
read, including their radius premises:

| Direct caller | Literal export used | Premise checked |
| --- | --- | --- |
| CENTRAL_S_ROOT_THREE_BOUNDARY_PATH_CAPACITY.md | Closed centered beta arc and both alpha/beta angle comparisons | Stated full high-radius interval; actual boundary centers exceed 27/20 |
| S123_POSITIVE_CHANNEL_RADIAL_MIDDLE_COMPLETE_EXCLUSION.md | Closed centered beta arc in each interboundary gap | d=1+epsilon>1, original radius at most target; actual boundary centers exceed 27/20 |
| S123_POSITIVE_CHANNEL_UNIQUE_MIDDLE_COMPLETE_EXCLUSION.md | Same closed centered beta arc | Same literal strict high-radius domain and original boundary units |
| S123_ZERO_CHANNEL_STRICT_MIDDLE_COMPLETE_EXCLUSION.md | Same closed centered beta arc | Same literal strict high-radius domain and original boundary units |

Those callers retain the same rho, beta, actual centers, open-interior
membership and endpoint convention. The new theorem can replace their
old centered-arc invocation without changing any of their geometric
hypotheses or conclusions. The additional comparison beta>pi/12 is
unchanged because beta itself is unchanged; it is not a changed export.

Other search matches are historical reviews of the old source or its
callers. They do not introduce a fifth mathematical export. Their old
source pins may remain as provenance, provided the new active replacement
is recorded explicitly and no historical review is silently represented
as a review of the new hash. This separate review supplies that new-hash
mathematical audit.

This exact substitution retires fourteen coefficient premises (two
degree-six Bernstein rows with seven coefficients each) from the operative
centered-arc dependency. It does not retire the other certificates in
any caller, reopen or newly close a whole original gate, or replace the
remaining capacity, force, topology or equality proofs. No Lean/Lake
execution, CI, sampling, workflow dispatch or remote write was performed.
