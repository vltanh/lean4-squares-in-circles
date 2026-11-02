# Independent hand reconstruction of the endpoint-owned downward center transfer

November 2, 2026 UTC / November 1 America/Chicago. Review by a second
agent of `ENDPOINT_OWNED_OBLIQUE_DOWNWARD_CENTER_TRANSFER_HAND_PROOF.md`.
No mathematical script, numerical evaluation, Lean, Lake, or CI was
used for this review. This is agent hand reconstruction, not human
peer review or kernel verification.

**Result: the stated complete nearvertical endpoint-owned branch
passes the reconstruction, for both horizontal normal signs and every
downward slope.** The remaining endpoint-owner classes and global
geometric caller are outside this acceptance.

## 1. Support elimination and exact central cost

I combined k times the physical M-to-A separator with b times the
physical A-to-B separator, using the two containment vectors
-a e_x-k n and -b e_x+k n+bz e_y. The center terms give
-a x_M-b x_B+bz y_B. Replacing y_B by h_B+f therefore produces
the negative term -bfz and the exact central penalty
b[(1+z)h_B+H_B(1,-z)] in (6)--(7). In particular no sign of a
physical separator or of the whole central floor is reversed.

The reference expression U_0 uses the actual orientations of A,B.
It is only a scalar comparison expression. The original center-cost
proof's triangle and two-vector estimates apply to it without
asserting that the actual M,A pair is vertically separated. The
orientation-independent reference endpoint penalty is a+k; the
perturbation comparison below separately handles the actual P_M.
Adding b(h_B+1/2) turns the left side into exactly
a(-x_M-h_M)+b(1/2-x_B).

## 2. Endpoint and norm perturbations

Ownership of n by M gives h_M=(s+|c|)/2. The hypothesis h_M<8/15
therefore implies |c|<1/14 and
(1-s)/|c|<2/55. The physical P_M evaluations in (12) agree with
the side-frame calculation for both signs of c.

The first norm has r L_M'(0)=2k because L_M(0)=23r and a=46.
The second squared-norm identity is exactly

\[
 V_A(c)^2-(bL)^2=-2bk c+2bkz(s-1).
\]

The c>=0 comparison is nonpositive. When c<0 the square-root
tangent gives V_A(c)-bL<=k|c|/L, with the z(s-1) term improving
that upper bound. These estimates hold for the entire half-line z>=0.

## 3. The signed shoulder vertex sum

The two varying support terms both contain +kn, so their witness
perturbations involve the **sum** v+w. A difference would be wrong;
the source uses the correct sum.

For one chirality the possible sums have x-components -beta and
alpha-beta, with the positive case available only when W>=alpha/beta.
For the other they have x-components -alpha and -(alpha-beta).
Their y-components are alpha, beta, or alpha+beta. Thus the complete
orientation and tie analysis gives

\[
 -1\le X\le\max(0,(W-1)/\sqrt{1+W^2}),\qquad
                       0\le Y\le\sqrt2.
\]

The positive x-bound follows from monotonicity of
(u-1)/sqrt(1+u^2) on u>=1. The beta=0 case remains in the first
branch for finite W, so the division by beta creates no endpoint gap.

For mu<=W<=1 the identity sqrt(1+mu^2)=2r/3 gives r/L<=3/2.
For W>=1, the envelope becomes (r+W-1)/sqrt(1+W^2), whose derivative
has numerator 1-(r-1)W<0. Its maximum is r/sqrt(2)<3/2, since
Q<9/2. The full envelope (18) is therefore valid.

## 4. The two strict signed reserves

For c>0, the norm and vertex bounds give the upper difference

\[
 -(a-3k)c+(a+3k/2)(1-s).
\]

The exact coefficient after the 2/55 ratio bound is

\[
 \frac{115}{16}-\frac2{55}\frac{2093}{32}
                     =\frac{529}{110}>0.
\]

For c<0, the signed vertex upper bound and the envelope give

\[
 -\frac{k}{2}|c|+(a+3k/2)(1-s)
                  <-\frac{7199}{1760}|c|<0.
\]

At c=0 the comparison is an identity. Hence the perturbed physical
support bound never exceeds U_0 and is strictly smaller for a
nonvertical endpoint-owned normal. This proves the claimed transfer
and its oblique strictness. Subcritical containment and positive z
retain the strictness of their corresponding support/scalar steps.
At z=0, the central orientation bound is h_B>=1/2, so equality
requires B aligned, as claimed.

## 5. Mixed-sign reserves and scope

The perturbation comparison is independent of the chosen floor f.
With f=1/10 it therefore preserves both the exact central orientation
excess E_B^-(z) and the floor slack z(y_B-h_B-1/10). The reference
floor-1/10 proof supplies the all-slope E,N,D scalar bound, so
equation (22) follows without a surrogate vertical separator.

The full paired caller must retain common disk containment of its
physical squares and the appropriate whole central floor. Its upward
side uses the separately reviewed adjusted upward reserve; its
downward side uses the present center-cost or retained-floor formula.
The owner condition concerns the endpoint/shoulder separator only;
ownership of the shoulder/central separator remains arbitrary.

This accepts the complete upward-nearvertical, endpoint-owned class
of endpoint/shoulder pairs for all signed shoulder/central slopes.
It does not supply such normals for every physical pair, and does
not cover shoulder-only ownership or a nearhorizontal endpoint-owned
normal. No global nine-square exclusion or equality classification
follows until those physical caller domains are joined.
