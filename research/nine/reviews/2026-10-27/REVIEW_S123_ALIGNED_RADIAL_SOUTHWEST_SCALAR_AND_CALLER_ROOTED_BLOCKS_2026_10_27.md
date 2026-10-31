# Independent review: aligned radial-Southwest S123 and its exact scalar cover

Date: October 27, 2026.
Reviewer: rooted_blocks, independently of the author.

**Result: ACCEPTED in full.** The complete radial-C Southwest feature,
its finite rational scalar certificate, every original return, and the
join with the already accepted unique-C source pass. No correction is
requested. The scalar step is a finite exact cover, not a numerical
pose test or a short hand inequality. Root review remains separate.

## 1. Exact frozen sources and prerequisites

I read the complete following sources and checker:

| Source | SHA256 |
| --- | --- |
| S_LEAF_C5_ALIGNED_SOUTHWEST_RADIAL_FAR_EXCLUSION.md | f2ee0deda127697157c9dc5a4de2eb73b37fc9157bb8a407d3ea94386721615d |
| S123_ALIGNED_RADIAL_SOUTHWEST_PORT_SCALAR_CERTIFICATE.md | 554663e37705b7b8dc792a9846eae3590d5232ac2e3ee6847debf3f87bc12cfe |
| certificates/s123_aligned_radial_southwest_port_certificate.py | 883147e3ebce01bf617283299203ce4a5d0f54b68a4bebbbabac110fa0d62745 |

The complete necessary-domain source9ccacf5e and unique-C source0d46e152
already passed my full independent review
REVIEW_S123_ALIGNED_SOUTHWEST_DOMAIN_AND_UNIQUE_FAR_ROOTED_BLOCKS_2026_10_27.md
(1f8e6419). I checked their literal scope in the new caller. I also
read the full local loaded-middle source4497b0c7 again, and the full
physical path argument in Sections1--3 of FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md.
The sharp actual boundary-contact radius is the previously fully
reviewed c0375a27 theorem. Its hypotheses are applied only to real
B--M points of the unchanged loaded path.

The graph remains A--B--M--C--U--A with its real leaf A--L.
A is true degree3; B,M,C are loaded true degree2; U is the
original unloaded side transmitter. Every original force, circle mask,
individual zero weight, actual side mean and all three extra squares
remain. No B--C contact or shortened middle force is introduced.

## 2. Original radial-C domain and the whole K interval

The accepted necessary domain proves B owns m and is physically
unique, while C owns n. In the radial-C mask its actual support
identity is a^2=2epsilon K+epsilon^2. Thus the two-variable
parametrization epsilon=a^2/(sqrt(K^2+a^2)+K) is an identity
of the actual star, including its radius; it is not a new choice
of pose. The B box and both proper-length quantities follow
from the unchanged full B2 force and moment equations.

I checked the complete hand reduction to1/4<K<7.

First the numerator b^2-epsilon*K is greater than9241/20000;
after division this gives N>0, and separately N<b<1. The incoming point has norm
r_P=sqrt(epsilon^2+b^2)<1 because epsilon<a and0<a<1.
The circle identity therefore gives1/2<W<11/6; the upper
squared comparison has the exact reserve103/2304.

If K<=1/4, the radial identity gives a^2<31/3600 and b>9/10.
All three factors in the displayed N/r_P estimate are in the
correct direction. Their product exceeds20/21 by335/117117.
The original lambda>=0 equation gives RN<=r_P(N+1).
Together with r_P<1 this yields R<41/20, contradicting
R>sqrt(17)/2 with squared reserve19/400. No original
proper endpoint is discarded.

For the upper bound I re-derived D0,E0 and both actual center
coordinates. The real boundary path puts M between B,C, and its
two touching gaps have sum below pi. Hence the endpoint minor
gap is greater than80 degrees, exactly at the scope of the
accepted physical path theorem. It implies
B_n<cot(80 degrees)|B_f|<(9/50)|B_f|.
The elementary sine/cosine estimate gives the stated rational
reserve1053/390850 without a decimal angle premise.

For K>=7, kappa=K-ab/K is positive and B_f>0. Using only
N>0 and W<11/6 gives
(B_n-B_f/5)/E0>(7/30)kappa-43/30>=23/120.
This contradicts the preceding actual path guard. It proves
the entire K interval before the scalar certificate is invoked.

## 3. Complete return cover and every scalar guard

The actual positive-j circle corner and the full B2 equation
make the return direction have negative j component. Near vertex,
owned -j side, and far vertex are therefore the complete support
cover. Their listed points, direction vectors, and forced side
mean are the original ones.

The far direction cannot vanish. If lambda=1, its defining
equation gives z=W and then eta=1. Thus lambda=1,eta=0
never occurs. The scalar checker nevertheless subdivides whenever
its interval denominator cannot yet be proved positive; it does
not remove such a box.

The actual sharp radius guard at a near or side B--M port is
valid for every physical M mask. For the near point I independently
re-derived
|Q|^2=V-2(N+W) and
(N+W)^2-(V-1)=2N(W-1).
Since N>0, the guard implies W<=1 and
N>=sqrt(V-1)-1. Both equalities remain. These justify precisely
the two feature-specific interval intersections in the checker;
they are not imposed on the other return.

Every closed input range contains the strict actual range, and
the path guard is the actual unchanged boundary-path consequence.
All square-root radicands and positive divisor requirements have
the stated guards. No assertion about M being unloaded or about
a new application mean is used.

## 4. Audit of the author's complete outward integer cover

I checked the entire interval implementation. Multiplication uses
all four endpoint products; reciprocals round outward after a
strictly positive denominator check. Squares use zero when their
interval crosses zero. Integer square roots use the exact square
test at the upper endpoint. Absolute value retains the full
image of a zero-crossing interval.

Each intersection with epsilon,V,N,W,lambda,eta preserves every
actual star. Losing their correlation only enlarges an enclosure.
A whole box is removed only when one literal guard is impossible.
The strict path guard is tested by a nonnegative lower bound on
B_n-(9/50)|B_f|, so its discard direction is correct.

A near or side feature is removed only if its whole norm upper
bound is below the lower bound on the necessary sharp radius.
For the near feature the clipped N lower bound uses the lower
radical enclosure, which is conservative. None of these feature
discards removes the other return.

All acceptances prove D0>1/4, far support>61/60 and every
remaining actual point bound throughout the box. The midpoint
subdivision keeps both closed children. The weighted-width rule
and its tie convention give the stated complete binary tree.

Running the author's checker reproduced exactly:

    accepted13096, impossible5885, splits18980;
    terminal boxes18981=18980+1; maximum depth21;
    depth nodes1,2,4,8,16,32,62,124,192,366,492,956,1338,2614,
               3822,7416,4638,7844,2756,4660,340,278.

All six displayed endpoint numerators and all six exact rational
reserves were reproduced. No unresolved box is accepted, omitted,
or treated as a sampled pose.

## 5. Separately written exact Fraction audit

I additionally wrote and ran

    certificates/review_s123_radial_southwest_independent.py
    SHA2567769a424627b06cd4e7f94933f2cf33a97344ed932ae4b81c07551dfd69331ed.

It imports no author checker or interval class. Ordinary operations
use exact Fraction endpoints without lattice rounding. Only radicals
are enclosed, on the different and finer2^-48 lattice. The actual
formulas, all guard and feature intersections, full binary tree and
strict acceptance tests are reconstructed independently.

This implementation gives exactly the same node classifications,
maximum depth and full depth distribution. Independently rounding
its positive margins down on its own lattice gives:

| Strict margin | Independent exact lower bound |
| --- | ---: |
| h_far-61/60 | 5099814433/281474976710656 |
| D0-1/4 | 21072823539/281474976710656 |
| Q_n-1/10 | 4254729483/281474976710656 |
| 3/4-Q_n | 26581002637591/281474976710656 |
| Q_f-1/2 | 20371048264703/140737488355328 |
| 43/50-Q_f | 443790981/281474976710656 |

The geometric and force hypotheses are established separately
in Sections2--3 of this review. Executing a checker alone would
not establish those original-scope obligations.

## 6. Normal signs and the complete loaded-middle contradiction

The far support bound exceeds d, so the actual contained M
cannot lie beyond it. This uses the genuine unit half-width
lower bound and the universal center radius, not a force assumption.

For the owned return, -j=E0 n-D0 f gives the two required signs
immediately. For the near return the sharp-contact intersections
give N>4/5, hence K<3/4 using the monotonic upper bound
N<1/sqrt(K^2+1). Thus0<D0/E0<K<3/4.
Also eta>0 and eta<1. The eta=1 endpoint would make the
actual incoming point one unit from its real circle corner,
contradicting r_P<1<R-1. Since S>W in this near-feature domain,
lambda-eta=-(S-W)(1-eta)/W<0. These facts give
g_n=eta E0-lambda D0>0 and
g_f=-lambda E0-eta D0<0,
including lambda=0 and W=1.

I checked the full C radial-cone inference with both physical
corner weights retained. Its negative incoming transverse mean
forces h_f>0. A positive h_n would expose an unshareable physical
circle corner. Therefore its actual return is exactly the inner
upper vertex or the entire upper owned side.

At the inner vertex the actual chord squared is below one by
2711/90000. The two actual M outward normals have negative
dot product. Section2 of4497b0c7 is the complete physical
support-point theorem requiring distance at least one, with
all side means and endpoints included. The present caller
correctly uses that chord scope, not the narrower sufficient
rectangle in the local theorem's initial statement.

For the C-owned upper side, Section3 of4497b0c7 requires
only Q_f<9/10 and the two g signs. I re-read its full proof:
the M-owned axis has impossible height3/2; otherwise the real
minimum-f vertex forces inward axes(-c,s),(s,c), s<2/5,
c>9/10. The actual corner comparisons establish the unique
M mask before invoking its inside-unit radial concurrence.
That concurrence has f coordinate>1 on the unchanged C line,
but at most Q_f<9/10 on the original B proper ray. All original
C means, both M forces and zero proper lengths remain.

Thus every actual radial-C return is excluded.

## 7. Exact whole Southwest join and remaining scope

The new source closes the entire radial-C mask. The complementary
unique-C mask is the full already accepted0d46e152 theorem,
and9ccacf5e supplies exactly the same necessary domain and
the exhaustive physical C-mask cover. Their join therefore
closes the entire high aligned Southwest direct-normal feature.

The actual South normal and the separate tilted side-mean
feature remain distinct obligations. This review does not
claim a whole S123 fine or coarse closure. No actual normal
is reselected after extraction, no positive force or loaded
middle unit is deleted, and all nine physical units remain.
No compilation, CI, shared-ledger edit or remote action is used.



## Dated review transcription correction: October 27, 2026

During root's complete source audit, root correctly identified that the
first sentence of Section 2 attached the lower bound9241/20000 to N
instead of to its numerator b^2-epsilon*K. The sentence is corrected
above to the literal original source statement: that numerator is
strictly positive, hence N>0 after division by the positive L_b.
The separate upper bound N<b<1 remains unchanged.

The stronger erroneous lower bound on N was not used in any subsequent
K-range estimate, scalar certificate, independent reconstruction, or
original-force caller. The frozen proof f2ee0ded and both scalar/checker
chains are unchanged. I reread the source's complete Section 2 and
verified the corrected attribution. Complete mathematical acceptance
remains unchanged; the previous review pin7251a05dbf3a86aaef34ce0e45d1d065d371070aaead1364936083d6a1ae120d
is superseded only by this explicit review correction.
