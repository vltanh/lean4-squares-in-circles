# Independent review: outward downward transfers and endpoint-owner union

November 2, 2026 UTC. Reviewer: the weak-chain/full-grid proof thread.
Hand algebra and exact rational checks only. No mathematical program,
numerical search, Lean, Lake, or CI.

Reviewed the frozen sources
`SHOULDER_OWNED_OUTWARD_DOWNWARD_TRANSFER_HAND_PROOF.md` and
`MATCHED_SHOULDER_ENDPOINT_OWNER_UNION_HAND_PROOF.md`.
**Result: PASS under their stated physical hypotheses.**

## 1. Downward physical support reduction

Multiplying the actual M-to-A separator by k and the actual
A-to-B separator by b gives the main support vector ae_x+kn,
the shoulder support vector -be_x+kn+bz e_y, and the remaining
term -bz y_B. Thus the signs and whole-floor accounting in (11)
are correct. In particular P_B contains (1+z)h_B, and the exact
floor excess is retained with a negative sign.

For the actual shoulder basis n=(-t,s),(s,t), evaluating the two
absolute coordinates yields exactly
P_A=k+b(t+sz+|s-tz|). The only breakpoint is R=s/t.
The source's two-vector formula C(z) and its derivative
C''(z)=3(1-z)/(2(1+z^2)^(5/2)) agree with the center-cost
dependency.

## 2. Retained ordinary transfer on every slope

After adding b to the starting inequality and retaining the exact
E_B^-, the scalar G in (16) has coefficient -(11b/10)z.
It is convex on each side of R and has strictly negative limiting
slope. Consequently its maximum occurs at 0 or R; the argument
does not assume convexity across the absolute-value breakpoint.

At zero the previously reviewed physical cap applies with both
bD_A and J(t) retained. At R, L=mu+1/t and the scalar reduces
to (20). The tangent inequality rA<=23Q-2kt, the constant
1575/1024, and all coefficients in (23) were checked. The final
AM--GM product is 567/512>1, giving the stated strict
-473/1024 bound. The t=0 case is exactly the already proved
vertical endpoint theorem.

## 3. Center-cost transfer and its complete slope coverage

Adding b(h_B+1/2) replaces the central penalty by
b(z h_B+H_B)-b/2, so the scalar F in (25) has the correct
center cost and floor7/60.

On z<=R-mu, the actual maximizing reference vertex is
v=(-h,j), because s-(mu+z)t>=0. Together with the top vertex
w=(j,h), it has v+w=(-t,s). Hence the support change is at
least k(1-s). The norm-increment comparison has the stated
direction since (z+mu s)/(1+mu t)<=z+mu. These changes cost
at most -J(t) relative to the original orientation-dependent
algebraic reference bound. This step uses no auxiliary packing.

At z=1, the replacement K_1<13 is legitimate because s+t-1>=0.
The upper convex endpoint value is 1097/360, whereas the aligned
reference reserve exceeds 62667/15360>4. Thus the asserted
margin343/360 is valid. At R, the exact value C(R)=1/t+j
gives (34). The coefficients -153/8,5275/183, and
-12123/(48000t) in (35) are correct. The AM--GM comparison
12123/16000>16/25 gives the stated margin317/5120.

For z>=1, F is convex separately on [1,R] and [R,infinity),
with negative limiting slope, so those two anchor bounds cover
the entire range. A possible remaining gap forces t>9/20 and
z>1607/3000>1/2. In the two-row table, both upper values of
L^2, both upper values of L, both displayed lower fractions for
the first curvature term, and the upper bounds24/55<7/16 and
2304/7921<3/10 were checked directly. They prove F_zz>0
on the complete possible gap. Its two endpoints were already
covered, so no slope interval is missing.

All strictness claims follow: t>0 gives strict scalar reserves,
t=0 and z>0 uses the strict vertical theorem, and a smaller
containing radius makes the positive disk-support step strict.

## 4. Endpoint-owner union and its new direction reduction

The three alternative endpoint classes supply the same retained
ordinary downward terms, center-cost downward inequality, and
upward orientation/height terms. The source joins them with the
same physical central square. The downward/downward, upward/upward,
and two mixed-sign additions therefore use exactly the previously
proved shared-orientation and shared-height inequalities. Endpoint
owner choices can be made independently on the two sides.

For the new bounded-inner reduction, the premises
2/5<d_x<1 and 0<d_y<197/120 are sufficient. Every unit normal
with nonpositive vertical component has center projection at most
d_x<1, below the physical support sum, which is at least one.
Thus every directed separating normal is upward.

An outward normal (-t,s) with t>=s>0 would have projection
strictly less than
(149/120)s<=149/(120 sqrt(2))<1; the exact squared comparison
is22201<28800. Therefore every outward separating axis is
nearvertical. A side-axis witness is then either main-owned or
shoulder-owned, and the corresponding completed transfer theorem
applies. A vertical comparison is separately covered.

The residual statement is appropriately a necessary condition:
an uncovered matched pair must have no vertical comparison,
no main-owned nearvertical separator, and only strictly inward
separating axes. The source does not claim that this residual
domain is empty. Neither review changes unrestricted A.2 status
or the canonical root counts.
