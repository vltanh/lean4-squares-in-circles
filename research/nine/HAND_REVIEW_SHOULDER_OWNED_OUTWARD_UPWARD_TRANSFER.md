# Independent review: outward shoulder-owned upward transfer

November 2, 2026 UTC. Reviewer: the weak-chain/full-grid proof thread.
Hand algebra and exact rational checks only. No mathematical program,
numerical search, Lean, Lake, or CI.

Reviewed the frozen source
`SHOULDER_OWNED_OUTWARD_UPWARD_TRANSFER_HAND_PROOF.md`, Sections 1--7.
**Result: PASS under the source's stated physical hypotheses.**

## Physical owner and support checks

The separator is n=(-t,s), owned by the shoulder A. Its support is
H_A(n)=1/2; no ownership of the subsequent (1,z) separator is used.
The actual-four endpoint and side-strip bounds give 2/5<d<31/30
and y_A-y_M<197/120. Together with g_M>15/32 these yield exactly
(563/480)s-(139/160)t>1/2. The t>=5/9 comparison reduces to
95/192<1/2, so t<5/9 and s>4/5 follow.

For the first main-square chirality, the n-support changes between
th+sj and sh-tj exactly at beta=t: t alpha>=s beta is equivalent
to t>=beta. The proposed vertex (j,h) yields the two expressions
in Section 3. Their concavity and derivative arguments prove
P_M>=k+as. In the other chirality the vertex (h,j) yields
(a+ks)alpha+(a-kt)beta, whose displayed derivative lower bound
is positive. Thus both chiralities and the transition ties are covered.

The shoulder-owned basis gives exactly
P_A=k+b(t+s), not a lower surrogate, and
D_A=(1+mu)(s-1)+t. These signs agree with n=(-t,s).

## Cap curvature and reserve

The endpoint values are K(0)=32Q=T+a+b+2k and K'(0)=-k/2.
The eight printed squared values for A and B at the table endpoints
were checked from their definitions. Each integer upper bound in
the table is strict; each rational lower bound for a squared
coefficient divided by its cube is valid. The smallest row sums
are strictly greater than 79/2000. Hence
-K''>(5511/16)(79/2000)>27/2 on the entire stated interval.

Subtracting the physical support penalties and retaining bD_A gives
exactly J(t)=(k/2)t+(27/4)t^2-(a-k)(1-s). With u=t/(1+s),
the scalar comparison is
J(t)/t>207/32-(1661/80)(31/100)=259/8000.
The intermediate cross-product 1797 and the final numerator 259
are correct. At t=0 the resulting weak inequality is valid; a
positive t or a smaller containing radius gives the stated strictness.

## Whole-square floor and subsequent transfer

The actual-four endpoint budget gives
y_M+h_M>=3/8+(4611/5500)beta. In the first chirality with
beta>=t, the floor loss is at most (28/45)beta, below this reserve.
With beta<=t, the subtraction from y_M+j_M is compensated by
tau(h_M+d-j_A), leaving at least (1311/5500)beta. The beta=0,
t>0 case has positive gain directly. In the other chirality,
d+j_M-j_A>0. All cases therefore prove the physical floor
y_A-h_A>=3/8. No center-height substitute is used.

For the arbitrary-owner physical separator from A to B, the disk
height slack ell=r-h_B-y_B>=0 gives precisely
1-d'-h_B+h_A<=D_A-Psi_A(z)-E_B(z)-z ell.
Adding it to the cap proves the stated transfer with its retained
central support excess and height slack.

The universal 81/100 estimate in
`SHARED_CENTRAL_ORIENTATION_AND_ALL_MIXED_SHOULDER_SIGNS_HAND_PROOF.md`
supplies the first reserve for every slope. For 0<z<=1 its excess
over (21/10-r)z is (17/200)z. For z>=1, the shoulder's actual
large side component is s>4/5, and
Psi_A(z)>=D_A+z(s-kappa)>(21/10-r)z because
kappa+(21/10-r)=29/40. Thus the second reserve really holds
for every positive upward slope.

The source appropriately retains its shoulder owner, outward sign,
nearvertical normal, actual-four, and side-column premises. It makes
no assertion for inward or nearly horizontal endpoint normals, or
for downward transfers from this shoulder-owned endpoint. No global
extraction or unrestricted A.2 conclusion follows from this review.
