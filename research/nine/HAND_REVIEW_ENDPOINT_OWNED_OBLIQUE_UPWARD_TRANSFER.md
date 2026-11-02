# Independent hand reconstruction of the endpoint-owned upward transfer

November 2, 2026 UTC / November 1 America/Chicago. Review by a second
agent of `ENDPOINT_OWNED_OBLIQUE_UPWARD_TRANSFER_HAND_PROOF.md`, including
its final Sections 6--7 with no second-normal ownership condition.
No mathematical script, numerical search, Lean, Lake, or CI was used.
This is agent hand review, not human peer review or kernel verification.

**Result: the stated owner-branch theorem and its all-slope reserve
extension pass this reconstruction.** The review does not supply the
missing global extraction or extend the theorem to other endpoint
separator owners.

## 1. Physical weighted cap with A's one orientation retained

I reconstructed the containment supports in directions -a e_x-k n
for M and -b e_x+k n for A. Adding the physical separator directed
M toward A gives exactly the two penalties P_M,P_A in equation (10).
The sign of the k term in each support is consistent with that
separator; no vertical projection comparison is substituted.

The endpoint-owned formula for P_M is the physical side-frame
calculation: k+a(c+s) for c>=0, and k+as for -k/a<c<0.
The bound |c|<1/14 ensures the latter domain. The epsilon and s
estimates in (7), including the integer reserve 194, are correct.

I checked the maximizing-vertex choices for A in both chiralities.
The three listed differences are (-beta,alpha), (-alpha,beta), and
(-alpha+beta,alpha+beta); each has x-component between -1 and 0 and
y-component between 0 and sqrt(2). Using the same two vertices as
witnesses at n gives the signed term
k[c Delta_x+(s-1)Delta_y] in (13), and P_A(0)=b+k+bD_A.

Combining it with the concave tangent bound on H yields the two
reserves

\[
 (a-3k/2)c-(a+3k/2)(1-s),\qquad
 (k/2)|c|-(a+3k/2)(1-s).
\]

Substitution of (1-s)/|c|<2/55 gives exactly
Gamma(c)=(42619/1760)c for positive c and
(7199/1760)|c| for negative c. The strictness statements follow
from the strict endpoint-angle bounds or from subcritical disk support.

## 2. Whole-shoulder floor and its payment

The actual-four strip bounds give 2/5<d=x_A-x_M<31/30.
The endpoint budget gives
y_M+h_M>=3/8+(87/50)(h_M-1/2), with coefficient 1+37/50.
The exact identity

\[
                 \frac1{2s}-h_M=-\frac{|c|}{s}j_M
\]

then proves (17) directly from the physical separator. The outward
case c<0 has no lost floor, because its d term improves the bound.
For the inward case c>0, the printed loss coefficient is less than
32/25; the difference is 4331/445500. The use of an actual topmost
vertex of A is legitimate for either chirality.

Rearranging the A-to-B separator with the whole-floor bound gives
(21). Adding it to the retained cap cancels precisely bD_A and leaves
-Gamma+bz delta. The payment at z=7/5 has exact positive reserve
1027c/44000. All signs of the central containment slack
r-h_B-y_B are preserved.

## 3. All upward slopes without a second owner premise

The adjusted floor loss delta_A in (24) retains the actual j_A.
Its maximum with zero is harmless in (25), since that displayed
coefficient is positive. The bounds delta_A<16/175 and
Gamma/b>=(7/5)delta_A follow from the preceding estimates.

For z>=1 I independently checked

\[
 H_A(1,z)\ge\max(h_A+j_Az,-j_A+h_Az).
\]

It is the exact two-branch support for one chirality. In the other,
the actual branch j_A+h_Az dominates both displayed terms because
beta(z-1)>=0 and 2j_A>=0. Thus the maximum in (30) remains valid
without assuming that A owns the A,B separator.

For alpha/beta>=7/5, the comparison alpha>13/16 is correct, with
integer squared reserve 38. Splitting at alpha=5/6 proves
alpha-29/40-delta_A>0; the two rational margins 7/80>1/14 and
71/4200>0 are valid. This makes the first affine branch's slope
strictly greater than lambda=21/10-r. Its value at z=7/5 exceeds
49/320 after the payment identity, so it also exceeds 1/10.

For alpha/beta<=7/5, the second affine branch is active for every
z>=7/5 and its slope exceeds lambda by more than 257/1400.
At z=7/5 the payment identity bounds it below by
D_A+(7/5)(alpha-kappa), which is at least D_A+alpha-kappa.
The established 81/100 shoulder estimate at z=1 applies exactly,
because H_A(1,1)=alpha in either chirality. The resulting anchor
81/100-kappa exceeds 1/10. Its excess over lambda(7/5) is
(2/5)r-151/200>9/200, using r>2. Both required inequalities
therefore persist for all larger z.

For slopes at most 7/5, the adjustment is nonnegative and the
previously proved original shoulder reserve applies. At z=0 the
adjusted reserve is nonnegative. These establish both bounds in
(27) for the whole stated slope range.

## 4. The exact accepted scope

The theorem now permits every upward shoulder-to-central slope,
with arbitrary ownership of that second separator, when the
shoulder/outer-main pair has an upward nearvertical separator owned
by the outer main and satisfies the stated side-column premise.
The adjusted reserve pays the same shared-central-orientation and
mixed-height losses as the prior paired proofs. The central whole
floor and opposite downward-transfer premises are still needed
where those paired proofs use them.

This review does not extend the theorem to a separator owned only
by the shoulder, a nearly horizontal endpoint-owned separator, or
an oblique endpoint pair in a downward transfer. It does not infer
such separators from the full-nine occupancy data, and it does not
close unrestricted A.2 or classify global nine-square equality.
