# Independent review: opposite-root S123 contact at a strict boundary vertex

Date: October 27, 2026.
Reviewer: rooted_blocks, independently of the author.

**Result: ACCEPTED in full. No correction is requested.**

Reviewed complete source:

    S_LEAF_C5_THREE_LOAD_OPPOSITE_ROOT_STRICT_BOUNDARY_VERTEX_EXCLUSION.md
    SHA256 c057680aa67f4211242639bd9ba8849959c34aefcbe2e8637b976435131b0227.

I read the entire source and its exact original-domain prerequisites:
S_LEAF_C5_THREE_LOAD_RADIAL_ROOT_HALFPLANES.md, the complete tilted
channel and physical-C-mask sources that it imports, the full original
two-force proper-concurrence proof, and THREE_BOUNDARY_PATH_RESULTANT_CONE.md.
I also checked the actual endpoint-angle use in
FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md. The radial-root source
has its separate complete independent review
REVIEW_S123_RADIAL_ROOT_HALFPLANES_TRIANGLE_BRIDGES_2026_10_27.md,
pin d23ca6752a9f1de8a3092fc8880abf54e2cf663ca607288612e17b296165bde8.

## 1. The literal original feature and physical mask

The positive component stays A--B--M--C--U--A with the genuine S
leaf at A. A is true degree three; B,M,C retain their full loaded
degree-two equations; U is the real unloaded side transmitter.
The B--M--C path is physical and loaded throughout. No middle force,
actual side mean, physical circle corner or completion body is removed.

The reviewed feature is exactly u>0 at the actual opposite A vertex,
with B not owning the incoming normal. Thus the actual point
P=(A0,F0) is a strict B support vertex. Its norm is strictly below d,
excluding every physical radial two-corner B. Since R-d>1, both
adjacent B vertices are strictly inside the circle. Its actual
opposite vertex is therefore the unique physical circle corner.

This mask conclusion precedes every use of concurrence inside B.
The other original neighbor M is physically boundary, so the complete
true-B2 proper theorem applies literally, with tau in(0,1] and
ell>=0. No corresponding inside-concurrence assertion is imposed on
the physical radial C.

## 2. Both actual diagonal coordinates and the angle are controlled

I independently checked the ell=0 exclusion: positive radiality would
give |P|=R-sqrt(2)<7/10, contradicting F0>37/50.

The second diagonal coordinate is positive directly from properness.
For the first, the case A0>=0 uses the strictly positive first
concurrence coordinate, which also makes Z1 positive before applying
tau<=1. In the contrary A0<0 case, tau>F0/R and the unchanged first
concurrence line give |Z1|<epsilon*R/F0<1/20. The stated exact
reserve41/13320 is correct. The resulting second diagonal coordinate
exceeds7/5, making the actual circle height larger than107/50>R.
The same argument excludes Z1<=0 after D1>0 has been established.

Thus D and Z have the required positive components. I re-derived

    det(m,D)=((1-tau)/tau)det(m,P),
    det(m,P)=q(a-b)/sqrt(r^2+s^2)>0.

Both vectors lie in the first quadrant, so the actual diagonal angle
is at least the incoming-normal angle, which is at least pi/4.
This includes tau=1 and every genuine zero proper coefficient that
was not already excluded.

## 3. The first whole diagonal comparison is correct

On the full quadrant interval, the scalar projection of P on the
unit diagonal direction is positive and concave. Its minimum is
therefore at an endpoint. The vertical endpoint is larger than the
pi/4 endpoint, even when the actual A0 is initially negative.
This gives P dot D>=A0+F0 exactly as stated.

Expanding the actual opposite-corner norm gives

    R^2>=d^2+8-4d(a+b).

Consequently a+b>283/244. Since a+b increases with b for a>b,
the whole b<=1/6 range is excluded by the endpoint comparison
with (sqrt(35)+1)/6. I recomputed the reserve7589/14884.
Thus b>1/6 and F0<5/6 hold in both the strict and side-normal
channel cases.

## 4. The actual strict-channel identity and full monotonicity proof

For t>0, the actual A channel point is fixed. In world coordinates
its normal is proportional to (k-a,-b), and the already proved
negative first component gives k<a<1. Its actual support is

    epsilon*l=1-da+k(d-a),
    l^2=1+k^2-2ak.

I independently solved this identity without changing the pose.
Putting H=1-a gives

    epsilon*(l+1-k)=(d+k)H,
    l-(1-k)=2k*epsilon/(d+k).

Substitution yields precisely

    a=1-2(d-1)(d-k^2)/(d+k)^2.

There is no extraneous squared branch. All quantities rationalized
here have their original positive signs.

The vertical endpoint of the concave diagonal comparison exceeds
the containing radius by48511/160000. A contained B would therefore
require the endpoint in the actual m direction to have norm at most R.
Its exact squared-norm excess is the source's F(d,k,S).

I re-derived all three partial derivatives of F, the two derivatives
of a(d,k), and the bracket decomposition

    2d+k^3-k(d+k)S=(d-k)(2-kS)+k M^2>0.

Thus F decreases with d and S and increases with k. Since
S=a+sqrt(1-a^2) decreases with a on a>b, the actual composite
increases with k and decreases with d. The comparison rectangle
to k=1/5,d=61/60 retains d>k, k<1 and a>b: its minimum a is
the displayed rational a_*, which is greater than1/sqrt(2).
Hence all derivative signs remain valid along the entire comparison,
not merely at its endpoints.

At that exact comparison I recomputed

    a_*=26059/26645,
    b_*^2=30884544/709956025,
    (1187/1000-a_*)^2-b_*^2
       =4997160729/28398241000000,
    M^2=3913/2500,
    L=15183/20000,
    B=16969/20000,
    2L^2-B^2 M^2=25880986607/1000000000000.

The last positive reserve proves F>0 with both square-root signs
justified. This excludes the full k>=1/5 range, rather than a
sampled parameter family.

The resulting positive A0 formula is valid: its numerator is at
least12/25 on d>=1,k<=1/5. At t=0 the proof does not use this
strict-channel parameterization. It uses the actual accepted
side-mean identity da=1-epsilon, retaining its entire original Y.
Therefore A0>0 holds in both literal original channel domains.

## 5. The endpoint angle contradiction retains the real middle unit

With A0,Z1>0, the exact opposite-corner distance gives the strict
Z2 bound. The scalar expression decreases with F0 throughout its
actual interval; enlarging the other positive parameters gives
Z2<97/50 with exact reserve9959/2131200. The actual radius lower
bound then gives Z1>69/100, with additional squared reserve103/10000.

The genuine B center consequently has positive coordinates and
argument below atan(832/207). For t>0, the unchanged channel
identity gives t/x=bk/(1-ak)<b/4<1/15. At t=0 the angle is exactly
zero and the actual side mean is still unrestricted.

I checked the exact tangent subtraction and the lower estimate

    atan(2273/12687)>11/63>pi/18.

Its rational reserve is113200759447/42884081660763. Therefore the
actual B/C minor center angle is strictly below eighty degrees.

The complete physical boundary-path theorem applies to B--M--C
with C's full radial mask and every individual zero weight. The
two actual contact gaps are each greater than forty degrees, and
the physical circular-neighbor order makes their sum the minor
endpoint angle. Each contact gap is also below pi/2, so their sum
is indeed the minor lift. This contradicts the strict upper bound.
No direct B--C edge or unloaded reserve replaces M.

## 6. Acceptance boundary and exact verification

The entire strict-B-vertex alternative of the original u>0 feature
is excluded. The conclusion is exactly that every survivor has B
owning its actual incoming normal. Its actual side mean and full
B2 equation are not fixed or shortened.

The u=0 original A-owned side and the high aligned root are separate
obligations. No whole S123 or coarse-cell closure is inferred here.

All symbolic comparisons above were independently re-derived. The
listed rational reserves were independently recomputed by exact
integer/fraction arithmetic. No numerical pose, sampled interval,
source-author verification, compilation, CI, remote edit or shared
metadata change is a premise of this review. No correction is requested.

