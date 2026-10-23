# A positive AB2 error supplies the missing negative-BT1 comparison

## 1. Actual prefix and the additional charge bound

Use the actual G0--G2 boundary cycle and constants
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 c_0=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2,
 \quad \kappa=49/50,\quad K=13/12.
\tag{1}
\]
Suppose the original AB owner is 2 with error \(v\ge0\),
and the original BT owner is 1 with error \(-z\le0\).
Both errors have magnitude below \(7/10\). The already
proved signs are \(y_A=b_A>0\), \(y_T=b_T>0\); B has
either sign. The exact contacts are
\[
 a_A\sin v+b_A\cos v-y_B\ge W(v),\qquad
 a_T-a_B\sin z+y_B\cos z\ge W(z),
\tag{2}
\]
where \(W(t)=(1+\cos t+\sin t)/2\) for \(t\ge0\).
Section 2 of HAND_G3_NEGATIVE_BT1_PREFIX_COMPARISONS.md
proves \(|y_B|<1/2\) and \(a_B\ge7/12\) in this branch.

Put
\[
 b'=1+y_B,\qquad
 R_1(z)=\frac32+\frac12\sec z+K\tan z,
\]
\[
 g(t)=\kappa t+(2-\kappa)(t-c_0)_+,
 \qquad x_+=\max\{x,0\}.
\tag{3}
\]
The second contact in (2) gives the exact necessary inequality
\[
                         b'+\sec z\,a_T\ge R_1(z).
\tag{4}
\]
Unlike the actual A tangent, \(b'\) need not be at most \(c_0\).
The required replacement for that unavailable upper bound is
\[
                         \boxed{v+\kappa b_A\ge g(b').}
\tag{5}
\]
Its additional linear term is retained throughout the proof.
No primary cap is silently imposed on the original T.

## 2. Prove the stronger AB charge bound on the whole interval

The positive AB2 comparison in Section 5 of the prefix note gives
\[
                         v+\kappa b_A\ge\kappa b'.
\tag{6}
\]
It remains to prove the second affine lower bound
\[
                         v+\kappa b_A\ge2b'-(2-\kappa)c_0.
\tag{7}
\]
By the first inequality in (2), it is enough to show
\[
 H(v):=v+2(W(v)-1)+(2-\kappa)c_0
      -\sup_A\{2a_A\sin v+(2\cos v-\kappa)b_A\}\ge0,
\tag{8}
\]
where the supremum is over the full sorted shifted corner disk.
It includes all actual core and outer A states.

For \(0\le v\le2/5\), both force components are nonnegative
and \(2\sin v\le2\cos v-\kappa\). Indeed
\[
 \cos v-\sin v\ge1-v^2/2-v\ge13/25>49/100.
\]
Sorting and \(a_A+b_A\le2c_0\) put the support at the diagonal.
Thus on this interval
\[
 H(v)=v-2(c_0-\tfrac12)(\sin v+\cos v-1)
          \ge(2-2c_0)v>\frac15v\quad(v>0).
\tag{9}
\]
At zero, H is zero.

For \(2/5\le v\le7/10\), unrestricted shifted-circle support
gives the lower bound
\[
 H(v)\ge h(v):=
 v+2(\sin v+\cos v)-1-\frac\kappa2+(2-\kappa)c_0-RN(v),
\]
\[
                    N(v)=\sqrt{4+\kappa^2-4\kappa\cos v}.
\tag{10}
\]
The function h is strictly concave. In fact
\[
 N''(v)=
 \frac{2\kappa(2-\kappa\cos v)(2\cos v-\kappa)}{N(v)^3}>0,
\tag{11}
\]
because \(\cos v>3/4\). Hence \(h''=-2(\sin v+\cos v)-RN''<0\).
It suffices to check the two endpoints.

Use \(R<1.979\), \(c_0>.899\), and the degree-6 lower
cosine and degree-7 lower sine polynomials. The rational
norm upper bounds at \(v=2/5\) and \(v=7/10\) are respectively
\[
 N(2/5)<1.1621,\qquad N(7/10)<1.4009.
\]
Their positive-square reserves, after substituting the lower
cosine polynomials in \(N^2\), are
\[
 \frac{2859493}{4500000000},\qquad
 \frac{2669489}{9000000000}.
\tag{12}
\]
The resulting endpoint bounds are
\[
 h(2/5)>
       \frac{466649627}{3150000000}>\frac7{50},\qquad
 h(7/10)>
       \frac{621776101}{3600000000}>\frac7{50}.
\tag{13}
\]
Thus (8), and hence (7), hold on the whole interval.
The maximum of the affine bounds (6)--(7) is exactly g,
proving (5).

## 3. The extra charge removes the need for an upper bound on b'

Let the original TD error be negative, \(-u\), with
\(0\le u<7/10\), and fix any TD multiplier
\[
                              3/5\le c\le\kappa.
\tag{14}
\]
Set \(\eta=0\) for TD0 and \(\eta=u\) for TD2.
The part of the weighted prefix and TD charge involving T
is bounded below, by (4)--(5) and monotonicity of g, by
\[
 J(z)=\min_T\left\{
 -z+g(R_1(z)-\sec z\,a)
                   +c\sin\eta\,a-c\cos\eta\,b\right\}.
\tag{15}
\]
The minimum is over the full sorted shifted T disk:
\(a\ge b\ge0\), \((a+1/2)^2+(b+1/2)^2\le Q\).
The desired comparison is
\[
 \boxed{J(z)\ge J_0:=
 2\kappa-
 \left[
 R\sqrt{(\kappa-c\sin\eta)^2+c^2\cos^2\eta}
 -\frac{\kappa-c\sin\eta+c\cos\eta}{2}
 \right].}
\tag{16}
\]
The right side uses the aligned-prefix charge and full circle
support. All D and E terms remain unchanged.

Put
\[
 A(z)=\frac12+(\frac32-c_0)\cos z+K\sin z.
\tag{17}
\]
This is the threshold where \(R_1(z)-\sec z\,a=c_0\).
It is increasing on \([0,.7]\), starts at \(2-c_0>1.1\),
and exceeds \(a_0\) before \(z=.325\), as proved in
HAND_G3_NEGATIVE_BT1_HIGH_PRIMARY_DUAL_TRANSPORT.md.

### The part with a>=A(z)

Here g uses its slope kappa. The minimum is exactly the
restricted-support expression of the high-primary transport
theorem, so it is at least \(J_0\). When \(A(z)>a_0\),
this part of the actual sorted disk is empty.

### The part with a<=A(z)

Here the expression in (15) is
\[
 -z+2R_1(z)-(2-\kappa)c_0
          -(2\sec z-c\sin\eta)a-c\cos\eta\,b.
\tag{18}
\]
Both force components are positive. Its maximum-support
point is on the outer sorted circle, possibly with the
additional upper-primary constraint \(a\le A(z)\) active.
No interior radial state can have a larger support value.
The lower diagonal endpoint is also allowed; the argument
below does not discard either circular endpoint.

If \(a=A(z)\) is active, (18) equals the value at the
common boundary of the preceding part. That point belongs
to the high-primary domain, so its charge is already at least
\(J_0\). This observation is used only when \(A(z)\le a_0\).

On any open interval where the upper-primary constraint
is inactive, the envelope derivative of the minimum (18)
is, with a denoting its maximizing primary,
\[
 \frac{2K-1-2(a-\tfrac12)\sin z+\sin^2z}{\cos^2z}>0.
\tag{19}
\]
The same derivative holds at a fixed circular endpoint.
Indeed \(a-\tfrac12\le a_0-\tfrac12<.915\), and for
\(0\le s\le13/20\),
\[
 2K-1-1.83s+s^2
 =\frac76-\frac{183}{100}s+s^2
 \ge\frac{1199}{3000}>0.
\tag{20}
\]
The quadratic decreases on the stated interval; its minimum
is the displayed right-endpoint value.

At \(z=0\), the entire minimum (15) is at least \(J_0\)
directly, since \(g(t)\ge\kappa t\) and \(R_1(0)=2\).
The minimum is continuous in z. If the low-primary part
were ever below \(J_0\), a connected component of that
strict sublevel set would contain no active-cap point.
Equation (19) would make it strictly increasing throughout
that component, but its left boundary has value at least
\(J_0\), either by continuity or by the preceding zero-endpoint
comparison. This is impossible.

This proves (16) on the whole original interval, including
the range \(A(z)>a_0\), where the upper-primary constraint
is automatically inactive.

## 4. Consequence and scope

Every original positive-AB2, negative-BT1 prefix therefore
has the aligned-prefix dual lower bound (16), for either
TD owner and every fixed multiplier in (14). The proof
uses the actual AB and BT witnesses, the true-core lower
bound for B, and the original sorted A and T circles.
The extra term in g is essential: (4) alone does not bound
\(b'\) by \(c_0\).

Together with the other branches in
HAND_G3_NEGATIVE_BT1_PREFIX_COMPARISONS.md and the
high-primary transport theorem, this supplies all negative
BT1 prefix comparisons. The remaining TD--DE tail still
needs its own lower bound with a multiplier satisfying
(14). A later assembly must verify that condition and
retain the same chosen tail parameters throughout the
z comparison. No angle mesh or numerical minimum is used.
