# Independent full review of the sharp quarter-clear arc and interval capacity

Date: October 28, 2026 UTC. Reviewer: two_circle_v_review continuation.

**Verdict: PASS for all three complete force-free theorems, including
the sharp equality classification, weak-clearance tangent residue, and
strict interval-capacity inequality. No source repair is required.**

Reviewed complete source:

    SHARP_QUARTER_CLEAR_RADIUS_FIVE_QUARTERS_ARC_AND_INTERVAL_CAPACITY.md
    SHA256 bca528af5320cc8314839eb0d53cf6f15ec381ac42d5bd353f62a27a47101f67

This review is pinned to those exact bytes. I read the whole source and
checked every own-frame case, all endpoint comparisons, the full actual
equality geometry and the complete interval argument. Both direct
predecessor sources were also read in full in this continuation, and
their current hashes match the displayed pins.

I did not author the sharp bound or suggest its extremizer. Root proposed
the diagonal extremizer; the mixed-capacity author supplied the printed
quadratic, whole-domain comparisons and equality-overlap proof. As the
source discloses, root adoption is an author/integration check. The
present review is the separate independent check.

## 1. Exact scope and constant comparisons

The unit-square domain is the entire set of actual closed squares of
arbitrary orientation contained in the closed disk of squared radius
Q=1105/256. The measure theorem assumes only distance at least1/4.
The connected-arc theorem assumes strict distance greater than1/4.
No positive degree, circle load, selected force, physical corner mask,
normal owner, graph, or completion allocation is imposed.

With rho=5/4, v=sqrt(Q/2), D=v-1, alpha_*=asin(D/rho), and
Lambda=pi/2-2*alpha_*, all radical and angle comparisons are valid.
In particular

    15/32<D<47/100,
    pi/4<Lambda<2*asin(2/5)<pi/2.

The lower D comparison has exact squared reserve1/1024. The upper
comparison has reserve863/320000. The lower bound on sin(pi/8)^2
and its comparison with (47/125)^2 have the correct signs and reserve
4421/875000. The other angle comparison uses

    sin(pi/4-asin(2/5))=(sqrt(21)-2)/(5*sqrt(2))
       <13/35<3/8<D/rho.

Both relevant angles lie on the increasing sine branch before inversion.
The printed 1/280 strict reserve is exact. These facts establish the
positive ranges of sin(Lambda), cos(Lambda), and every subsequent
principal inverse-trigonometric comparison.

## 2. Complete own-frame cover

Choosing signs and order of the actual square's axes makes its actual
center coordinates x>=y>=0 without moving the origin or the square.
The representation

    E=[A,a] times[B,b],
    a>=b>=1/2, A=a-1, B=b-1,
    q=a^2+b^2<=Q

uses exactly its farthest-corner containment. The nearest-point formula
(max(A,0),max(B,0)) is correct. The three cases a>rho, a<=rho with
B>0, and a<=rho with B<=0 exhaust the complete domain, including
center-axis ties and every weak-clearance endpoint.

## 3. Full inner-face quadratic and its equality classification

In a>rho, the bounds A>1/4, A<41/40, -1/2<=B<=D<1/2 and
A^2+B^2<2081/1600<rho^2 all hold. The possible equality B=D
is correctly retained at the final diagonal extremizer.

For s=sin(Lambda), the exact expansion is

    F_s=A^2+B^2+2sAB
       =(1-s)q+s(a+b)^2-2(1+s)(a+b)+2(1+s).

It is strictly convex in a+b. At fixed q, the full own-frame interval
has endpoints b=1/2 and a=b. Enclosing the actual a>rho range in
that full interval is legitimate for an upper bound even when an
endpoint does not obey the current case premise.

At b=1/2, the strict s>7/10 comparison and the complete convex
quadratic bound give F_s<933/1600. At a=b=w, the whole allowed
interval 3/4<w<=v gives

    F_s<=2(1+s)D^2.

The lower bound 2(1+s)D^2>765/1024 exceeds the first endpoint by
4197/25600. Consequently

    F_s<=2(1+s)D^2=rho^2*cos(Lambda)^2.

The final identity follows from s=cos(2alpha_*)=1-2D^2/rho^2.
Strict convexity excludes every interior fixed-q point. The b=1/2
endpoint is strictly smaller. At a=b, the alternative w=2-v solving
(w-1)^2=D^2 is below3/4. Therefore equality is possible exactly
at a=b=v. The fixed-q endpoints are distinct in the actual range,
so no collapsed-interval exception is missing.

## 4. Actual inner-face arc and both competing endpoints

The closed intersection is precisely

    [beta,min(alpha,gamma)],
    alpha=acos(A/rho), beta=asin(B/rho),
    gamma=asin(min(b/rho,1)).

The strict positive x half-plane, a>rho and A^2+B^2<rho^2
exclude an omitted second component. The actual open-interior
intersection is the corresponding open interval.

The quadratic bound is exactly equivalent to

    (A+sB)^2<=cos(Lambda)^2*(rho^2-B^2).

Since cos(Lambda)>0, taking the upper square-root bound is valid
even if A+sB is negative. It yields A<=rho*cos(beta+Lambda).
The source checks the entire angle branch: beta+Lambda>0 and
beta+Lambda<=pi/2-alpha_*<pi/2. Hence

    alpha-beta>=Lambda.

Equality forces equality in the quadratic and therefore a=b=v.

The other possible arc length is strictly larger than Lambda. For
b<=rho, the complete derivative comparison gives

    asin(b/rho)-asin((b-1)/rho)>=2*asin(2/5)>Lambda.

It retains b=1/2 and the continuous endpoint b=rho. For b>rho,
gamma=pi/2 and beta<=alpha_* give an even larger strict bound.
Thus the minimum of the two candidate lengths has precisely the
stated lower bound and equality case.

Conversely [D,v]^2 has exact open interval
(alpha_*,pi/2-alpha_*), of length Lambda, because v>rho.
Its clearance sqrt(2)D is strictly greater than1/4. This verifies
attainment in the actual geometric domain, not merely equality in a
polynomial estimate. Reflections give the same rotated square family.

## 5. Entire positive outer-face case

For a<=rho and B>0, weak clearance is exactly

    0<B<=A<=h=1/4, A^2+B^2=k^2>=h^2.

The displayed complete closed interval has four possible upper-minus-
lower differences. Both opposite-face differences have the strict
strip comparison above. The inner-inner difference exceeds Lambda
because D/rho>3/8>1/5.

For the remaining outer-outer difference, the fixed-k path from
A=B=k/sqrt(2) to the actual A>=B stays in 0<A,B<=h throughout.
I checked the derivative comparison and factorization. Its sign is
the sign of

    (A-B)*[(A+B-h)^2+(k^2-h^2)*(A+B+1)],

which is nonnegative including k=h. Expanding the bracket gives
exactly (A+B)^2+(k^2-2h-h^2)(A+B)+k^2. Continuity handles
the h endpoints where a derivative may be infinite.

The resulting diagonal lower bound is strictly greater than the strip
angle. The source's comparison reduces, with positive sides, to

    4sqrt(2)-1>sqrt(21),

whose squared form is 12>8sqrt(2). This is valid from sqrt(2)<3/2.
The angle pi/4+asin(2/5) lies below pi/2, so applying inverse sine
has the stated direction and no branch ambiguity.

All four candidate differences are therefore strictly greater than
Lambda, proving a single nonempty actual open arc and excluding every
equality square in this entire case, including weak clearance k=h.

## 6. Complete weak tangent residue

When a<=rho and B<=0, the nearest-point formula and weak clearance
force exactly a=rho, A=1/4, -1/2<=B<=0 and b=B+1 in[1/2,1].
The inner x face does not cut the full interval between
beta=asin(B/rho) and gamma=asin(b/rho), since A^2+b^2<=17/16<rho^2
and b>=|B|.

The outer face x=rho is tangent at angle zero. Thus the actual
open-interior intersection is (beta,gamma) with zero removed if it
belongs. For B<0 there are two connected components; for B=0 the
removed point is already an endpoint. The source correctly claims
only angular measure in this weak residue. Its total measure is at
least the strip angle, strictly greater than Lambda. A point of zero
measure is not mislabeled as part of the open square.

This residue is impossible under strict clearance. Consequently the
whole strict domain has exactly one connected open arc, as claimed
in Theorem B. No weak tangent was passed through an unjustified
connectedness limit.

## 7. Radial center point

The nearest-point supporting line and projection halfwidth at least1/2
give |c|>3/4 under strict clearance. The farthest actual corner gives
|c|^2+|c|+1/2<=Q, hence |c|<91/60 with exact reserve31/57600.
It follows that ||c|-rho|<1/2. The radial point rho*c/|c| lies in
the actual open incircle and therefore in the already proved connected
open arc. The source does not incorrectly claim that this entire arc
is centered at that radial direction.

## 8. Actual overlap of adjacent equality squares

The equality square is uniquely determined by its arc midpoint: the
diagonal square [D,v]^2 has midpoint pi/4, and its reflected variants
are the same rotated family. Two equal-length equality arcs adjacent
without gap therefore give actual units S and Rot(-Lambda)S after
one common rotation.

With T=sqrt(rho^2-D^2), the actual point P=(T,D) lies in the relative
interior of S's bottom side because D<T<rho<v. Rotating P back by
Lambda gives (D,T), in the relative interior of the other actual
square's left side. This uses the exact identity
alpha_*+Lambda=pi/2-alpha_*.

The common inward direction

    w=(1+sin(Lambda),cos(Lambda))

has positive second component for the first square. Its first component
after rotation by Lambda is exactly cos(Lambda)>0, so it also enters
the second square. All other side margins at P are strict. Thus
P+epsilon*w lies in both open interiors for all sufficiently small
positive epsilon. This is an explicit geometric overlap, including
the exact shared arc endpoint; it does not rely on a drawing or a
strict inequality being inferred from disjoint angular measures alone.

## 9. Strict N*Lambda interval capacity

Under the stated strict clearance and whole-arc routing premises,
the N actual connected open arcs are pairwise disjoint and each has
length at least Lambda. Hence L>=N*Lambda. If equality held, each
unit would be an equality square and the ordered lifted intervals
would have no positive intervening gap. For N>=2 there is an adjacent
pair, precisely the impossible pair of Section 8. Therefore

    L>N*Lambda.

The argument handles a lifted interval of length up to2*pi, including
its endpoint case, because complete routing of each full arc into that
one lift is an explicit premise. It does not assume a center gap
determines whole-square allocation. The two-unit consequence at
L<=2*Lambda is therefore strict and valid even at exact equality of
the interval threshold. Its threshold is larger than pi/2 by the
already proved Lambda>pi/4.

## 10. Exact pins, arithmetic and adoption limits

The two predecessor source hashes match:

| Source | SHA256 |
| --- | --- |
| UNIFORM_INNER_CIRCLE_ARC_FAMILY_AND_SMALL_CENTRAL_DISK_EXCLUSION.md | c8c9dc223e11dbcd7be9063818d546a3d3c0bc77b66cdac181b9ea97d51bae69 |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb |

The present sharp proof is complete in its own stated domain. These
sources identify the unchanged predecessor kernels and their caller
obligations; their old byte-specific reviews are not substituted for
the present review.

The printed rational identities and reserves were independently checked
exactly. They include1/1024,863/320000,4421/875000,1/280,219/6400,
419/1600,4197/25600,1/2,31/57600,1/4900,1/25 and4/25. No angle
sampling or pose search was used. These calculations check the written
continuous proof rather than supply a separate exclusion certificate.

This source is a reusable force-free sharp measure and capacity kernel.
It does not itself prove a physical face allocation or close an original
fine/coarse row. Every caller must retain the actual units and prove
strict quarter-clearance and complete routing into its claimed interval.
No original graph/load identifier, count or flag changes through this
review.

No source alteration, Lean/Lake invocation, build, CI/workflow dispatch,
original-ledger edit, commit, remote write or pull-request merge was
performed for this review.
