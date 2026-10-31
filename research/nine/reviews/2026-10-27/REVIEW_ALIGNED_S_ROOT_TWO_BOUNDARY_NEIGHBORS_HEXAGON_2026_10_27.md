# Independent full review of the aligned S3 root with two boundary neighbors

Date: October 27, 2026.

Reviewer: hexagon, independently of the source author.

**Decision: ACCEPTED at the entire stated d>=1 local scope.**

I read ALIGNED_S_LEAF_ROOT_TWO_BOUNDARY_NEIGHBORS_EXCLUSION.md
in full, at SHA256
`7c0e55bc75013f14d667a85635cd743361b325f7180f4710fd832c4f14ab9873`.
I checked the equality case of the contained-unit support bound,
the actual radial S-root chart, every support and side-mean case,
the real leaf screen and all four corner bounds. I independently
differentiated the final comparison function and verified the
displayed rational comparisons by exact fraction arithmetic.

## 1. The proof uses precisely the original three-force star

Only the genuine root's degree-three force and origin-moment
equations are used. B,D are physical boundary units with arbitrary
actual degrees and other forces. Their mutual adjacency is never
needed. The proof is therefore correctly stated as a three-edge
star, without manufacturing a triangle or a cyclic block.

Reflection gives 1/2<=h<=1, and the exact radius lower bound
makes the whole low-height left-face segment ineligible as a
boundary contact. The sharp support equality at x=d identifies
the unique east-cap square with the actual S leaf, so no other
positive neighbor can use that normal. The h=1/2 case is then
impossible by the full horizontal equation. Two west normals
would have strictly positive actual application heights and
strictly positive origin moments, contradicting the unchanged
torque equation.

For the downward normal, the negative-x alternative is at the
ineligible lower-left vertex. The positive-x alternative enters
the real S leaf from its inner-face relative interior, including
h=1. Thus the normal is exactly south. The other normal must
be northwest by full force balance. This yields the exact ports
in (3), with the complete actual bottom-side mean x retained.
There is no unexamined horizontal or axis endpoint alternative.

## 2. The scalar geometric domain and real-leaf screen are valid

The bound r^2>419/1000 follows from the displayed exact radical
comparison. It gives h>647/1000 and the original southern mean
x>27/50, with no selected or centered contact. Thus all of the
b,t,d intervals used later are valid at both d=1 and d>1.

For an aligned southern unit, the open vertical projections with
the real S leaf overlap. Horizontal nonoverlap forces its right
endpoint at most d; the alternative of lying beyond d+1 contradicts
its actual contact. Every aligned corner is strictly internal.

The tilted parameterization covers both tilts because c,s are
positive and unordered. If x+c<=d, all horizontal corners are
bounded by D_0 and all vertical corners by B_0+sqrt(2), giving
the stated strict reserve. Otherwise the actual downward-right
edge crosses x=d before its endpoint. A crossing above the real
leaf's lower inner corner enters its open interior; therefore
g s>=t c. The equality case at that corner remains included.
The argument also excludes g=0 without an omitted boundary case.

## 3. The complete four-corner calculation checks

The actual top and left adjacent vertices satisfy the large
aligned reserve. For the right adjacent vertex, I checked the
global maximum of sqrt(1-s^2)(1-t/s): its positive stationary
point has s^3=t and value (1-t^(2/3))^(3/2). Since t>1/8 this
is below 2/3; its nonpositive region and both axis limits pose
no exception. The split s<=4/5 and s>=4/5 then gives exactly
the two displayed strict rational radius reserves.

For the opposite vertex, c<=s reduces to the earlier large
reserve. In c>=s, the original positive x and the actual screen
give the full interval 1<=k<1430/441<13/4. The first coordinate
of that corner is positive. Replacing d by D_0 and t by t_0
therefore increases its positive-coordinate bound; replacing
b by t_0-1/2 increases the magnitude of its negative vertical
coordinate. Thus the comparison with F(k) is monotone in the
correct directions throughout the entire original interval.

I independently expanded F and obtained the stated derivative
formula

    F''/2=t_0^2-N(k)/(1+k^2)^(5/2).

The lower quadratic bound on N has strictly positive coefficient
reserves. The difference from (1+k^2)^2/6 is concave on the whole
closed interval, and its two endpoint values are exactly 343/75
and 152999/38400. Hence the global second-derivative bound is
proved without a grid. The exact remaining reserve in
1/21-t_0^2-1/40 is 21211/21000000>0.

At k=2, the radical bounds give the stated upper F value
4266766619/1006200000, below 4241/1000 by
527581/1006200000. The two derivative bounds are exactly
-2705123/139812500 and -672961/34937500; both lie in (-1/50,0).
The uniform Taylor upper bound is valid on either side of 2,
and its maximum is F(2)+10 F'(2)^2<849/200<17/4.

I also checked the three earlier rational corner comparisons:
their positive reserves below 17/4 are 762019/9000000,
782819/9000000 and 9357823/112500000, respectively. Every actual
corner is strictly internal, including screen equality, real
shared-side means and the aligned limits.

## 4. Original-scope conclusion

The contradiction excludes physical boundary contact of D,
so it retains all initially permitted circle masks and individual
zero weights. It uses neither a neighboring degree-two equation
nor any force or moment at B,D. It applies only when the root
really has its three original forces; the source correctly warns
against suppressing additional root contacts to fit the theorem.

For the opposite-S/S C4 caller, both private neighboring tips are
physically boundary by the original load cover. An aligned root
at d>=1 therefore satisfies the theorem exactly. At d=1 a tilted
genuine root instead contains O openly, while the other genuine
root contains O closed; this covers the remaining critical cases.
The strict-high both-tilted family is correctly retained separately.
No whole S/S gate is claimed without that final branch.

No missing original endpoint, application, physical mask or frame
case was found. Exact arithmetic in this review only checks the
displayed human inequalities; no sampled pose or numerical maximum
is a proof premise. No Lean compilation, CI, remote mutation or
shared metadata change was used.
