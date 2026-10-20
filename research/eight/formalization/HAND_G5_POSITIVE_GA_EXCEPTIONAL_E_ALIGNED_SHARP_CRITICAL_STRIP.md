# The positive-GA exceptional E-aligned endpoint on the critical tilt strip

## 1. Scope and sharp conclusion

Put
\[
 q_L=19577/5000,\qquad Q_1=1957767069/500000000,
 \qquad h=.7.
\tag{1}
\]
All decimals below are exact rationals. Let \(q_*\in(q_L,Q_1)\)
be the unique stationary hard-chain minimum constructed in
[the stationary-existence note](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md).
This note proves a sharp obstruction, rather than a strict obstruction
at the larger ceiling \(Q_1\).

Consider the normal anchor signs H,A positive and B,D negative,
with arbitrary signs of G,T. Let E have nonnegative signed tangent
coordinate \(y_E\). Every square is sorted and contained at a common
ceiling \(q\le q_*\). Retain the actual owners
\[
 HG2,\quad GA1,\quad AB0\text{ or }AB2,\quad BT2,\quad TD0,
 \quad DE3,\quad EH0,
\tag{2}
\]
whose errors are respectively
\[
 u,x,\alpha,\beta,\gamma,e,0,
 \qquad x,e\ge0,\qquad t=x+e\in[.1,.16].
\tag{3}
\]
Assume the actual aligned EH contact
\[
                         a_H+y_E=1
\tag{4}
\]
and the ordinary cyclic variation bounds
\[
 u+\alpha+\beta+\gamma=-t,
 \qquad \sum d_i^+=\sum(-d_i)^+\le h.
\tag{5}
\]

**Theorem.** Under (1)--(5), \(x=0\). In particular, an actual
positive GA1 cannot survive this exceptional endpoint when
\(.1\le x+e\le.16\). The statement permits all ordinary error
signs, both AB owners, either radial kind of G,T,E, and weak owner
ties. At \(x=0\) the proof retains the hard-chain zero; it does not
assert a false strict exclusion of the sharp equality case.

This is the only E-positive endpoint left by
[the paired-E transport](HAND_G5_POSITIVE_PAIRED_E_SAME_RADIUS_ENDPOINT_REDUCTION.md),
restricted here to its critical total-angle strip. The outer-H/E
hypotheses used to obtain (4) are unnecessary once (4) holds.

## 2. The sharp supporting chain and its weights

Throughout this proof set \(R=\sqrt{q_*}\). At each fixed
\(t\in[.1,.16]\), let u\(_0\) be the unique position minimizer of
\[
\begin{aligned}
 r&=\sqrt{q_*-u_0^2},& U&=\sqrt{q_*-(2-u_0)^2},\\
 V&=3-U,&Y&=\sqrt{q_*-V^2},\\
 v&=2-Y,&w&=\sqrt{q_*-v^2},\\
 k_1&=2-\cos t(r-1)+\sin t\,u_0,&
 k_2&=1+\cos t\,v-\sin t(w-1),\\
 F(q_*,u_0,t)&=k_1^2+k_2^2-q_*.
\end{aligned}
\tag{6}
\]
The full-domain position convexity and the stationary-existence
proof give
\[
                 F_{u_0}=0,\qquad F(q_*,u_0,t)\ge0.
\tag{7}
\]
Define
\[
 \eta=v/w,\quad \lambda=\cos t+\eta\sin t,\quad
 k=\lambda V/Y,\quad l=k(2-u_0)/U,\quad c=k_1/k_2.
\tag{8}
\]
Differentiating (6), clearing the positive product \(rUYw\), and
using (7) gives the useful exact identity
\[
                    l=c\{\sin t+\cos t\,u_0/r\}.
\tag{9}
\]
No approximation enters (6)--(9).

The following uniform bounds hold on this entire strip:
\[
\begin{gathered}
 .998-.635t<u_0<1.002-.64t,\\
 .27<\eta<.31,\quad 1<\lambda<1.04,\quad
 .925<k<.985,\quad .925<c<1,\\
 l<.67,\quad l/k<.675,\quad .63<l/c<.68,
 \qquad c/k<1.02,\quad c-k<.02.
\end{gathered}
\tag{10}
\]
Section 7 supplies a finite exact polynomial certificate for all
these bounds. In particular every sorted pair used below has ratio
at least one half, and \(c-l>.296\).

## 3. The actual stress and strict primary split

Hold t and the weights (8) fixed. For \(x+e=t\), put
\[
 n(x)=k(\cos x+\eta\sin x),\qquad
 p(e)=\cos e+\eta\sin e.
\tag{11}
\]
Weight the actual seven witnesses (2) by
\[
                           (n,k,l,c,c,1,p).
\tag{12}
\]
If \(y_G\) denotes G's signed tangent, its force is
\(k\sin x(a_G+\eta(-y_G))\). Therefore, with
\[
                   \sigma_\eta=R\sqrt{1+\eta^2}-(1+\eta)/2,
\tag{13}
\]
its support is at most \(k\sigma_\eta\sin x\), for either sign
of G. T cancels exactly.

The DE3 and aligned EH0 projections are
\[
 a_D+a_E\sin e-y_E\cos e\ge W(e),\qquad a_H+y_E\ge1.
\tag{14}
\]
Their E force is \(\sin e(a_E+\eta y_E)\). The four remaining
zero-error pairs are
\[
                         (p,n),(k,l),(l,c),(1,c).
\tag{15}
\]
Only B can have two ordinary angular arguments; H,A,D each have
one. The actual negative coefficients are respectively
\[
                              n,\ l,\ c,\ c.
\tag{16}
\]

Perform the split in x,e before maximizing the anchor supports,
and keep the actual E coordinates during this split. The term
with the varying coefficient p is exactly zero by (4). The sorted
H residual satisfies
\[
                 W(u)-a_H\sin u-b_H\cos u>-.065
\tag{17}
\]
on \([-h,h]\), as proved in the
[sole-EH stress](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md).
Also \(\sigma_\eta-.5<.935\), \(a_E-.5<.915\), and
\(y_E\ge0\). Consequently the split second derivative is at most
\[
 k\{-.435\cos x+.956\sin x\}
                         -.5\cos e+.915\sin e.
\tag{18}
\]
On \(x+e=t\le.16\), its endpoint values are less than -.74 and
-.75, respectively, using (10). It is a linear combination of
\(\cos x,\sin x\); division by the positive cosine makes its
sign affine in \(\tan x\). Both endpoint signs are negative, so
(18) is strictly negative on the whole split interval.

It is therefore enough to compare the two intrinsic scalar endpoints
\[
                         (x,e)=(0,t),\quad(t,0).
\tag{19}
\]
For every interior split the actual relaxed weighted expression is
strictly larger than the chord between its endpoint values. This
argument asserts no physical motion and requires no packing at a
relaxed endpoint.

## 4. The full ordinary-angle envelope is the B charge

For a positive pair a,b write
\[
\begin{aligned}
 H_{a,b}(s)&=R\{\sqrt{a^2+b^2}-\sqrt{a^2+b^2-2ab\sin s}\},\\
 V_{a,b}^{\nu}(s)&=H_{a,b}(s)+\nu(\cos s-1),\\
 U_{a,b}(s)&=\min(a,b)(\cos s+\sin s-1)\\
 &\hspace{12mm}-R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\}.
\end{aligned}
\tag{20}
\]
Set \(V_B=V_{l,c}^{c}\). The separately concave angle reduction
in [the scalar-envelope note](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
applies to (15). For H,A,D the actual one-angle functions are
concave because their negative coefficient is at least the smaller
pair coefficient and
\(-RN''(-s)<.762\min(a,b)<\min(a,b)\cos h\).
Only B uses the mixed-sign two-angle function with its larger
negative coefficient. Thus it suffices to check pure negative
charges at t, B's same-block charge, and separated charges
\(U_i(h-t)+V_j(h)\).

### 4.1 Pure charges and the same B block

At either endpoint (19), the H and D pairs have both coefficients
at least .925 and one at least 1. Their negative coefficients are
below 1.04. Since
\[
 \frac{\sqrt{q_L}(.925)}{\sqrt{1+.925^2}}>1.343,
\]
monotonicity of the norm gain gives
\[
 V_H(t),V_D(t)>1.25t,
 \qquad V_B(t)<1.102t.
\tag{21}
\]
The latter follows from concavity and its initial slope, using
\(l<.67,c<1\).

For A, if \(c\le k\), monotonicity of H in the larger coordinate
and \(l<c\) give \(V_A\ge V_B\). If \(c>k\), then throughout
\(k\le z\le c\), \(l/z<.675\), and
\[
 \partial_z H_{l,z}(t)
 =\int_0^t
 \frac{R(l/z)^2(l/z-\sin s)\cos s}
      {\{1+(l/z)^2-2(l/z)\sin s\}^{3/2}}\,ds<.5t.
\tag{22}
\]
Therefore
\[
 V_A(t)-V_B(t)>(c-l)(1-\cos t)-.5(c-k)t>0.
\tag{23}
\]
For the last step use \(c-l>.296\), \(c-k<.02\), and
\((1-\cos t)/t>.1/2-.1^3/24\) on this strip.

The same-block B charge exceeds \(V_B(t)\), because
\[
 .63\{\cos(h-t)+\sin(h-t)-1\}-\cos t+\cos h>0.
\tag{24}
\]
Indeed this function has positive second derivative, negative
first derivative at .16, and value greater than .011 at .16.

### 4.2 Separated charges

All positive charges satisfy the uniform bound
\[
                       U_i(P)\ge-.545(1.04)P.
\tag{25}
\]
At h, monotonicity of H along coefficient rectangles with ratio
above \(\sin h\) gives
\[
                         V_H(h),V_D(h)>.83,
 \qquad V_B(h)<.66.
\tag{26}
\]
For A the preceding comparison is repeated with the simpler bound
\(\partial_zH_{l,z}(h)<1\). Its reserve is
\((c-l)(1-\cos h)-(c-k)>.049\), hence \(V_A(h)>V_B(h)\).

Finally, the derivative of V increases with the ratio l/c, and
its fixed-ratio derivative is positive on \([0,h]\). Thus
\[
 V_B(h)-V_B(t)
 \ge .925\{V_{.63,1}^{1}(h)-V_{.63,1}^{1}(t)\}
 >.925(.7)(h-t).
\tag{27}
\]
For the last inequality, put
\(J(t)=V_{.63,1}^{1}(h)-V_{.63,1}^{1}(t)-.7(h-t)\).
On \([.1,.16]\), \(J'<0\); positive squaring gives
\(J(.16)>.049\). Here the smaller radius \(\sqrt{q_L}\) is
used in the lower bound. Since
\[
                     .925(.7)-.545(1.04)>.08,
\tag{28}
\]
(25)--(27) prove that every separated charge exceeds \(V_B(t)\).
All endpoint types are now covered, so the complete ordinary-angle
contribution is at least \(V_B(t)\).

## 5. Exact identification of the E endpoint with the hard defect

Define
\[
 C_\eta(t)=1+2\cos t+
              \{1+2\eta-R\sqrt{1+\eta^2}\}\sin t.
\tag{29}
\]
After the support bounds and before its ordinary negative charge,
the E endpoint \((x,e)=(0,t)\) is
\[
 B_E=3k+2l+3c+C_\eta(t)
 -R\{\sqrt{\lambda^2+k^2}+\sqrt{k^2+l^2}
                    +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\tag{30}
\]
The exact support points in shifted coordinates \((a+.5,b+.5)\)
are
\[
                 B=(r,u_0),\quad A=(U,2-u_0),\quad
                 H=(Y,V),\quad E=(w,v).
\tag{31}
\]
E's second coordinate here is the positive signed coordinate
\(y_E+.5\). H,A,B,E lie on the circle of radius R. The four
ratios in (8)--(9) say exactly that their forces at the pure B
negative endpoint are positive multiples of these radius vectors.
The required D point is \((k_2,k_1)\), with force \((1,c)\).

For completeness, the paired actual contacts in (31) are
\[
\begin{aligned}
 b_H+a_A&=2,& b_A+b_B&=1,&a_H+y_E&=1,\\
 a_B\cos t-b_B\sin t+b_D&=1+W(t),\\
 a_D+a_E\sin t-y_E\cos t&=W(t).
\end{aligned}
\tag{32}
\]
Thus all weighted contact residuals vanish at (31) and the required
D point. The sole support discrepancy is D's radial discrepancy.
With \(N=\sqrt{k_1^2+k_2^2}\), this proves the identity
\[
                 B_E+V_B(t)
                   =\frac{N^2-RN}{k_2}
                   =\frac{N(N-R)}{k_2}\ge0.
\tag{33}
\]
The last inequality is exactly (7). This preserves the sharp zero,
rather than replacing it by a rounded positive reserve.

## 6. The positive-GA endpoint is strictly stronger

At \((x,e)=(t,0)\), the corresponding baseline is
\[
 B_G=3+2l+3c+kC_\eta(t)
 -R\{\sqrt{1+k^2\lambda^2}+\sqrt{k^2+l^2}
                    +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\tag{34}
\]
Subtracting (30) gives the exact formula
\[
 B_G-B_E=(1-k)\{3-C_\eta(t)\}
 +R\{\sqrt{\lambda^2+k^2}-\sqrt{1+k^2\lambda^2}\}>0.
\tag{35}
\]
Indeed \(k<1\), \(\lambda>1\), and \(C_\eta(t)<3\).
For the latter, \(\eta<.31\) and
\(q_L(1+.31^2)>(1+2(.31))^2\) show that the sine coefficient
in (29) is negative.

By (33), (35), and Section 4, the E endpoint is nonnegative and
the G endpoint is strictly positive. The strict concavity of
Section 3 makes every interior split positive as well. An actual
feasible weighted witness sum is nonpositive after subtracting
its support upper bounds. This contradiction proves \(x=0\).

## 7. Finite exact certificates for the strip and envelope

Here is an explicit rational construction of the inequalities in
(10), so their premise is the entire continuous interval. Put
\(z=t-.1\in[0,D]\), \(D=.06\), and set
\[
                    u_-=.998-.635t,\qquad u_+=1.002-.64t.
\tag{36}
\]
For a polynomial \(P(z)=\sum a_nz^n\), write
\[
\begin{aligned}
 B_0(P)&=\sum_n a_nD^n4^{-n}\binom{2n}{n},\\
 B_j(P)&=2\sum_{n\ge j}a_nD^n4^{-n}\binom{2n}{n-j}\quad(j\ge1),\\
 L(P)&=B_0(P)-\sum_{j\ge1}|B_j(P)|,\qquad
 U(P)=B_0(P)+\sum_{j\ge1}|B_j(P)|.
\end{aligned}
\tag{37}
\]
The shifted Chebyshev identity gives \(L(P)\le P\le U(P)\)
on the whole interval.

The following single radical operation is used recursively.
For a positive polynomial A, let rho be the nearest multiple of
\(10^{-12}\) to \(\sqrt{A(0)}\), determined by rational square
comparisons, and put
\[
 d=\frac{[A]_{\le6}-A(0)}{A(0)},\qquad
 P_A=\left[\rho\sum_{j=0}^{6}\binom{1/2}{j}d^j\right]_{\le6},
 \qquad A_\pm=P_A\pm10^{-7}.
\tag{38}
\]
For the three chains formed from
\((u_-,u_-),(u_+,u_+),(u_-,u_+)\), use qL for lower radical
arguments and Q1 for upper arguments in the recursions (6).
More explicitly, for any input \(a\le u_0\le b\), enclose in order
\[
\begin{gathered}
 r\in[\sqrt{q_L-b^2},\sqrt{Q_1-a^2}],\quad
 U\in[\sqrt{q_L-(2-a)^2},\sqrt{Q_1-(2-b)^2}],\\
 V\in[3-U_+,3-U_-],\quad
 Y\in[\sqrt{q_L-V_+^2},\sqrt{Q_1-V_-^2}],\\
 v\in[2-Y_+,2-Y_-],\quad
 w\in[\sqrt{q_L-v_+^2},\sqrt{Q_1-v_-^2}],
\end{gathered}
\tag{39}
\]
replacing each displayed root by (38). All generated root
comparisons have the uniform exact reserves
\[
 L(A_-)>1.4395,\quad L(A-A_-^2)>2.875\,10^{-7},\quad
 L(A_+^2-A)>2.88\,10^{-7}.
\tag{40}
\]
Thus these are genuine lower and upper root bounds, independent
of the formal binomial-series motivation of (38).

Use the alternating Taylor lower/upper polynomials
\(S_{15},S_{13},C_{14},C_{16}\) for sine and cosine. The numerator
of \(F_{u_0}/2\) after multiplication by \(rUYw\) is
\[
 J=k_1(\cos t\,u_0+\sin t\,r)UYw
       -k_2(2-u_0)V(\cos t\,w+\sin t\,v)r.
\tag{41}
\]
Interval substitution from (39) gives
\[
             U(J\text{ at }u_-)<-.0274,\qquad
             L(J\text{ at }u_+)>.0482.
\tag{42}
\]
Strict position convexity proves (36). The same positive-denominator
substitutions in (8), followed by (9) for l/c, give (10).
The smallest coefficient-norm reserves for the assertions
\(\eta>.27,\eta<.31,\lambda>1,\lambda<1.04\) exceed respectively
\(.0205,.0278,.0219,.0029\). The bounds for k,c,l and the three
ratios have positive reserves exceeding .005. For c/k, use that
\[
 \frac{c}{k}=\frac{(2-u_0)/U}{\sin t+\cos t\,u_0/r}
\tag{43}
\]
decreases with u\(_0\), and use the \((u_-,u_-)\) chain;
its cleared numerator reserve exceeds .0064.

The remaining envelope comparisons use only rational squaring
and endpoint Taylor bounds. In particular, (22) follows from
\[
 Q_1(.675)^6<(.5)^2\{1+.675^2-2(.675)(.16)\}^{3}.
\tag{44}
\]
The endpoint comparisons (21), (24), (26), (27) use respectively
positive reserves \(1.25-1.102\), .011, \(.83-.66\), and .049.
The decreasing claim in (27) follows from
\[
 q_L(.63)^2\cos^2(.16)>
 \{.7+\sin(.16)\}^2(1+.63^2).
\tag{45}
\]
All radical endpoints in these last comparisons are enclosed
between consecutive multiples of \(10^{-12}\), checked by
positive squaring. Equations (36)--(45), together with the displayed
analytic reductions, are a finite certificate on whole intervals;
no sampled angle, optimizer output, or state partition is a premise.
