# Independent complete review of the two boundary-point diameter lemmas

Date: October 28, 2026. Reviewer: recovery_audit.

**Verdict: PASS for both general force-free lemmas and the entire printed
positive-transverse North-return exclusion.** I read the whole source
and independently rederived every premise, estimate and literal caller
join. The source required no edit.

Reviewed exact source:

    BOUNDARY_CORNER_RETURN_AND_RADIAL_SIDE_TWO_PORT_DIAMETER_EXCLUSION.md
    bytes: 8110
    SHA-256: 40b4d692d48b172bca4320a9da98a34239007a61ebcff1fa7811291548086974
    Git blob: 1f91f3ddae9be88a51733bf769a9d9a862d24ed8

The two general statements hold for every R>=2 without an upper-radius,
force, degree, selected-normal or circle-weight assumption. The caller
uses the exact original North-roof chart; neither the whole North
interface nor roof ABC.S is closed by this source or this review.

## 1. Full circle-adjacent return diameter proof

In an arbitrary orthonormal frame (n,e), let |Z|=R>=2,
Z.n<=0, Z.e>=1/2, and let j be a unit vector with j.e>=0. For
V=Z+j and P.n>=1, P.e=1/2, the n-coordinate difference has absolute
value at least |Z.n|: P.n-j.n>=0, and -Z.n>=0. The e-coordinate
difference has absolute value at least Z.e-1/2. Thus

    |P-V|^2>=(Z.n)^2+(Z.e-1/2)^2
             =R^2-Z.e+1/4
             >=R^2-R+1/4>=9/4>2.

This contradicts the diameter of any actual unit containing both
points. All weak endpoints are present. The point P can be any actual
shared mean because the proof only uses its real membership in that
same unit. The vector j is the actual unit vector stated in the
hypothesis; no force normal is selected or replaced.

## 2. Full physical-corner sign proof

For an actual point P of a unit K, with |P.j|<=1/2 and P.w>0,
suppose a physical circle corner Z had Z.w<=0. Then
P.Z<=R/2. Consequently

    |Z-P|^2>=R^2-R+|P|^2>=2+|P|^2>2.

The strictness is supplied by P.w>0. This contradicts the same real
unit diameter. Every physical circle corner of K therefore has positive
w projection, independently of its eventual coefficient. A nonzero
nonnegative full circle resultant has positive w projection as well.
No physical two-corner mask is reduced to a unique-corner mask here.

## 3. Entire continuous North-domain premise check

I independently reviewed the exact new necessary-domain source
74fa5a6f in a separate full record. It supplies the true A3, B2, C2,
both H3 rows, the original means and the actual pose

    A=Q+[0,1]j+[0,1]w,
    Q=(k,1-b), j=(-C_A,S_A), w=(S_A,C_A),
    Z_A=Q+w, q_j=Q.j<-1/2,
    0<a<=epsilon, sqrt(2epsilon)<b<31/120,
    k=(1-a)t/b in(1/2,1), 0<t<b.

C has its entire physical radial mask in the frame
n=(-C_n,-S_n), e=(-S_n,C_n). Its actual CB point has n projection
at least d>1 and e projection exactly 1/2. The full original AB
vector has G.j>0 at the actual side j=1.

From k>1/2 one gets t>b/2. The unchanged hub strip gives
alpha<=epsilon/t<b^2/(2t)<b. In the side row S_n=alpha. In the
opposite row, zeta<=c/(1+a_H)<t beta<b beta, hence
S_n=(alpha+zeta beta)/sqrt(1+zeta^2)<2b. Thus both complete
rows satisfy S_n<31/60 and C_n>5/6. I checked the exact squared
reserve 139/3600 for the latter estimate.

If S_A>=1/2, then C_A<=sqrt(3)/2 and
q_j>-sqrt(3)/2+89/240>-1/2, a contradiction. The last comparison
has squared reserve 481/57600. Hence S_A<1/2 and C_A>6/7.
The actual unique circle corner therefore satisfies

    0<(Z_A)_x<3/2,
    (Z_A)_y>1343/840,
    Z_A.n<0,
    Z_A.e>-(31/60)(3/2)+(5/6)(1343/840)
           =2809/5040>1/2.

The final reserve is 289/5040. Finally j.e=C_A S_n+S_A C_n>0.
Every premise of the general diameter lemma is now proved for the
unchanged actual Z_A, actual j and original actual CB mean. The bounds
hold continuously in both H3 rows and do not use a sampled pose.

## 4. Exact feature exclusion and entire residual mean

If G.w>0, then its two strictly positive own components make the
original AB point Q+j+w=Z_A+j. The same real B contains this point
and the original CB application. Section 1 gives distance squared
at least 9/4>2, a contradiction. This excludes the complete G.w>0
return feature across both physical B masks and both independent C
circle coefficients.

The source correctly retains the entire original residual:

    G.w<0: P_AB=Q+j;
    G.w=0: P_AB=Q+j+yw, 0<=y<=1.

It does not delete either endpoint in the zero case. At all these
points, q_j>-k>-1 and q_j<-1/2 imply 0<P_AB.j<1/2, while
P_AB.w=q_w+y>0. The second general lemma therefore applies to
every physical B circle corner, so F_B.w>0 for the original full
circle resultant.

The exact A3/B2 projections then give

    G_w=M C_A+mu-kappa(q_w+1)<=0,
    0<F_B.w=G_w+delta(g.w),
    M C_A+mu<=kappa(q_w+1)<M C_A+mu+delta(g.w).

This algebra preserves the separate North and HA forces at A. Neither
an A2 equation nor equal C circle coefficients appears. The unique-
versus-two-circle B alternatives, all surviving CB supports and the
full zero-w mean remain real obligations.

## 5. Exact input, acceptance and limits

The sole direct pin matches the current input bytes:

| Source | SHA-256 |
| --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 |

Its separate full audit is
REVIEW_NORTH_RADIAL_RETURN_UNIQUE_A_CORNER_RECOVERY_AUDIT_2026_10_28.md.
The present review independently checks the complete literal use of
that chart as well as both new general geometric proofs.

No source bytes, original 2513/58 inventory entry, gate flag or metadata
were changed. All nine units, true degrees, original normals, means,
physical masks and zero individual weights remain. No Lean, CI,
numerical exclusion packet, pose mesh or remote write was used.
