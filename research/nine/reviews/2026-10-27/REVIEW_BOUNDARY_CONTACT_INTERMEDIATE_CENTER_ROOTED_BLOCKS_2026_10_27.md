# Independent review of the intermediate-center boundary-contact theorem

Date: October 27, 2026.
Reviewer: rooted_blocks.

**Verdict: ACCEPTED, complete stated physical scope.**

Source:

    BOUNDARY_CONTACT_EXCLUDES_INTERMEDIATE_UNIT_CENTER.md
    c36f103d80ab0ab218a96d3358bca62c07dcb31726f5400abaaebca9eb6250de

I read the full source and independently checked both variance
identities, all endpoint estimates, the closed angular-ray cases
and the path export. No correction is requested.

## 1. Every original geometric hypothesis is sufficient

The proof uses actual unit centers, not substitute circles or a
hypothetical boundary load at the third unit. Every actual unit's
radius-1/2 incircle gives pairwise center distance at least1.
A physical contact gives endpoint-center distance at most sqrt(2).
The established physical boundary-center lower bound is strictly
5/4, and the exact upper bound is M=91/60, with original reserve
31/57600. The boundary minor angle is strictly less than pi.

Consequently every ray in its closed minor arc meets the actual
center segment in exactly the stated radial direction, with
0<=t<=1. The segment avoids O, so its radial coordinate y is
positive. The endpoint cases t=0 and t=1 retain a genuine
distinct third center and the same distance-at-least-one bound.

## 2. The exact weighted identities and both radial orders

Writing Y=t c_A+(1-t)c_B=y v and c_E=rho v, I independently
expanded

    t|c_A|^2+(1-t)|c_B|^2=y^2+V,
    t|c_A-c_E|^2+(1-t)|c_B-c_E|^2=(y-rho)^2+V,

with V=t(1-t)|c_A-c_B|^2<=1/2. Both are exact. Their left
distance side is at least1, including either segment endpoint.

If rho<=y, y<sqrt(M^2-V) bounds the nonnegative difference
y-rho by sqrt(M^2-V)-rho. Squaring in that sign range is
legitimate. Replacing V by1/2 increases the resulting upper
bound, giving the printed convex quadratic F(rho). It is
harmless that the comparison interval [2/3,M] is wider than
the actual rho<=y subdomain.

The endpoint estimates check exactly:

    M^2-1/2=6481/3600>16/9,
    F(2/3)<3481/3600<1,
    F(M)=M/[M+sqrt(M^2-1/2)]<1.

Convexity then proves the strict upper bound throughout.

If rho>=y, the actual strict boundary lower bounds give

    y^2>25/16-V>=17/16>1.

Thus rho-y<M-1, and the entire weighted distance is less than

    (M-1)^2+1/2=2761/3600<1.

This covers equality rho=y as well as every V endpoint.
Both cases contradict the unchanged actual unit-center distance
bound, proving the whole theorem.

## 3. Path and disk exports

The path conclusion applies the same local theorem to each genuine
consecutive boundary contact. It excludes every other actual center
of radius at least2/3 from the traversed minor gaps, with no force
or circle-status premise on that other unit. It makes no unwarranted
claim about an entire square or its full inner-circle arc.

If another physical root contains closed D_(1/5), every distinct
unit avoids its open interior and has distance from O at least1/5.
Its own contained radius-1/2 incircle therefore gives actual center
radius at least7/10>2/3. This is a valid physical substitution;
the implication uses containment of the incircle in the actual unit.

The source explicitly leaves any required connected inner arc,
center-point property, pocket routing and capacity count to its
caller. I accept exactly this local theorem and these literal
exports, not an unstated whole C5 closure.

All actual frames, contacts, circle masks, zero weights, degrees
and side means survive. No numerical pose, graph contraction,
selected-normal substitution, compilation or CI was used.

