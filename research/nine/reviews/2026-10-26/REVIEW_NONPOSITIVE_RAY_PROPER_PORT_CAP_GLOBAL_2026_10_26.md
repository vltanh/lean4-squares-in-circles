# Independent full review: negative ray and two proper root ports

Date: October 26, 2026.

Reviewer: global-closure subagent.

**Decision: ACCEPT the complete uniform local geometric theorem.**
The negative concurrence, both proper root ports, and avoidance of the
nonpositive ray of the same actual pair resultant remain necessary
caller premises. This review declares no whole graph/load parent closed.

Reviewed source:
ROOTED_NONPOSITIVE_RAY_PROPER_PORT_CAP_EXCLUSION.md, SHA-256

    73c0f974372e3ea6a58e673cb3e9194431c92af252413193aa90c3437c830ab4

I read the entire source and checked the original sharp center/support
bound used from END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md. The proof
uses no load or true-degree assumption on either actual neighbor, and
does not impose a shortened force equation at the root.

## 1. Actual convex combination and forced own-frame geometry

The nonparallel positive pair has nonzero resultant M. Its given
q=-tM belongs to the excluded ray, hence is outside closed K. Both
proper lengths are therefore strictly positive. The positive weighted
average of the actual ports, with weights proportional to mu_i/a_i,
is exactly q+M/W. Avoidance of the nonpositive ray forces its scalar
coefficient of M to be strictly positive.

Since O is outside the actual closed square, an own-coordinate interval
strictly misses zero. Reflecting that coordinate gives [a,a+1], a>0,
without moving the original origin. The positive-ray point in K gives
M_x>0, while q_x<0. Each original outward normal thus has positive
x-component and each actual port lies on the same far side x=A=a+1>1.

Two strictly positive transverse components, or two strictly negative
ones, would place both ports at the same vertex and put the genuine
nonparallel concurrence in K. Otherwise the proper-port relations put
q_y between the actual port heights; a zero transverse component places
it at the actual mean height. Together with the positive-ray point,
this forces the transverse interval of K to contain zero. All side
means, endpoint means, and zero proper-length cases are accounted for;
the latter were excluded only by the actual forbidden-ray premise.

## 2. Exact moment and support inequality

The summed origin moment is zero because the pair sum is M and their
concurrence is -tM. Consequently M_y/M_x is a positive weighted average
of y_i/A. The displayed formula for each actual normal slope is the
convex combination of its own y_i/A and that weighted average.

For the upper endpoint the slope is at most y_i/A; for the lower
endpoint it is at least y_i/A. Multiplication by the corresponding
signed transverse normal gives, in both cases,

    y_i(n_i)_y >= A(n_i)_y^2/(n_i)_x.

The axis case has both sides zero. Thus the actual support satisfies
h_i>=A/(n_i)_x. The original contained-neighbor support bound gives
h_i<=d<61/60, proving (n_i)_x>60/61, |(n_i)_y|<11/61, and h_i>1.
This inequality comes from the actual two-port moment, not a prescribed
orientation or a reset application.

## 3. Whole-neighbor center contradiction

Each actual neighbor has directional halfwidth at least one half, hence
c_i.n_i>3/2, and the universal contained-center bound is |c_i|<91/60.
Its transverse component relative to its own normal is strictly below
sqrt(181)/60<27/120. Combining these bounds, with their correct signs,
gives the common original horizontal bound

    (c_i)_x > (3/2)(60/61)-(11/61)(27/120)
              =3501/2440=L.

Both original centers therefore lie in the same open rectangle
L<x<91/60, |y|<sqrt((91/60)^2-L^2). Its entire squared diameter is

    52124381/53582400 = 1-1458019/53582400 < 1.

This contradicts the distance of at least one required by the two
actual disjoint open unit incircles. No physical boundary or force
premise was added to those neighbors in this step.

Independent exact rational arithmetic checked the normal-component
identity, center-cap identity, strict transverse rational reserve,
horizontal threshold, rectangle diameter, and final strict reserve.

## 4. Exact accepted scope

The theorem is valid for arbitrary root degrees and arbitrary loads at
the two displayed neighbors. It concerns their actual common ports
and original normals. It cannot be applied to a root with an improper
port, or to a private-branch resultant when a possible additional root
circle force still belongs to the full external aggregate. The source
states these limitations correctly.

No sampled pose, numerical stress solve, Lean compilation, CI, remote
mutation, or shared-ledger edit was used.

