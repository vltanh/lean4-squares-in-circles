# The hard middle path has only small wrong intermediate signs

## 1. Original scope and conclusion

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 h=\frac7{10},\quad p=\frac{50}{49},\quad
 S_0=2\sqrt{Q-1}-3,\quad \varepsilon=\frac{27}{160000}.
\tag{1}
\]
Retain the original G0--G2 necessary system, actual sorted
corner circles at a common ceiling \(q\le Q\), true central
exclusion, and real frames contained in an interval of length
at most h. The signed tangents at H,A are nonnegative and
those at B,D,E are nonpositive. The signed tangents \(y_G,y_T\)
are arbitrary. Retain
\[
 HG,AB,TD\in\{0,2\},\qquad GA0,\quad BT2,\qquad
 DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
For a necessary system presented separately from an original
candidate, retain also the original implications
\[
                   HG2\Longrightarrow y_G<0,\qquad
                   TD0\Longrightarrow y_T>0.
\tag{3}
\]

**Theorem.** Every such system has
\[
                         y_G<\frac1{10},\qquad
                         y_T>-\frac1{10}.
\tag{4}
\]
Consequently the hypotheses concerning intermediate signs in
[the small-wrong-sign AB theorem](HAND_G5_AB_ALIGNMENT_WITH_SMALL_WRONG_INTERMEDIATE_SIGNS.md)
hold globally in the class (1)--(3). That theorem aligns A
and B between the unchanged G and T frames, normalizes their
tangent sum to one, and retains its separate strict-circle
loss conclusions. No original AB alignment or H/D/E frame
order is assumed here.

The proof is an inequality for the original three middle
contacts. It does not change G or T, replace their signed
tangents by magnitudes, or assume a full normal-sign reduction.

## 2. The outer contacts give a budget with uniform strict slack

[The signed intermediate-order theorem](HAND_G5_SIGNED_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md)
already gives
\[
 \eta=\theta_G-\theta_T>0.
\]
Write
\[
 g=-y_G,\quad t=y_T,\quad
 h_G=\theta_G-\theta_H,\quad h_T=\theta_D-\theta_T,\quad
 \alpha_{\rm out}=\theta_H-\theta_D.
\tag{5}
\]
The same theorem, Section 5, proves the original unclipped
zero-edge charges
\[
                  b_H+g\ge1-ph_G,\qquad
                  t+b_D\ge1-ph_T.
\tag{6}
\]
Its H/D/E estimate can retain the following uniform reserve:
\[
           b_H+b_D+S_0-p\alpha_{\rm out}<2-\varepsilon.
\tag{7}
\]
This follows directly from the printed whole-domain bounds in
[the all-mixed-owner endpoint estimate](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md),
Sections 3--5, and its cited
[primary endpoint proof](HAND_G5_GLOBAL_INTERMEDIATE_FRAME_ORDER.md),
Sections 3--6. The two rotated owners give \(2-1/500\).
The primary positive-span range up to \(1/2\) gives
\(2-27/160000\), and the remaining positive-span range gives
\(2-87/6125\). The short negative-span range gives \(2-1/500\);
the long-range convexity endpoints give \(2-909/24500\) and
\(2-1/175\). The two-primary nonnegative-span estimate is
bounded by the same \(2-27/160000\) certificate. Every displayed
reserve is at least \(\varepsilon\). The endpoint proof uses
only H,D,E and their actual mixed contacts, so arbitrary G/T
signs introduce no new hypothesis into (7).

Since \(h_G+h_T=\eta-\alpha_{\rm out}\), (6)--(7) imply
\[
                         g+t+p\eta>S_0+\varepsilon.
\tag{8}
\]
We will prove that either \(g\le-1/10\) or \(t\le-1/10\)
instead forces
\[
                         g+t+p\eta<S_0+\frac1{10000}.
\tag{9}
\]
The two budgets differ by \(11/160000>0\).

## 3. An unequal positive stress on the actual middle path

First take the actual AB0 witness. Normalize \(\theta_G=0\),
and put
\[
 x=\theta_A-\theta_G,\quad s=\theta_T-\theta_A,\quad
 d=\theta_B-\theta_A,\quad w=\theta_B-\theta_T=d-s.
\tag{10}
\]
Then \(x+s=-\eta\), and every pairwise difference of the
four frames has absolute value at most h. The constraints are
\[
\begin{aligned}
 a_A\cos x+b_A\sin x-g&\ge W(x),\\
 b_A+a_B\sin d+b_B\cos d&\ge W(d),\\
 a_B\cos w-b_B\sin w-t&\ge W(w),
\end{aligned}
\qquad W(v)=\frac{1+\cos v+|\sin v|}{2}.
\tag{11}
\]
Use weights \((a,b,c)\), where either
\[
 (a,b,c)=(\alpha,\beta,1)\quad\hbox{if }g\le-\frac1{10},
 \qquad
 (a,b,c)=(1,\beta,\alpha)\quad\hbox{if }t\le-\frac1{10}.
\tag{12}
\]
All weights below satisfy
\[
 \frac34\le\alpha\le1,\quad
 \frac{13}{20}\le\beta\le\frac{23}{25},\quad
                 \frac{\beta}{\alpha}\le\frac{23}{25}.
\tag{13}
\]
In particular \(b\le a,c\), and
\(13/20\le b/c\le23/25\).

Define
\[
 N_v(z)=\sqrt{v^2+b^2+2vb\sin z},
\quad
 K_s(d)=c\{\cos(d-s)+(-\sin(d-s))_+\}
                       +b\{\cos d+(\sin d)_+\}.
\tag{14}
\]
The collected A force is \((a\cos x,a\sin x+b)\).
The B force is \((b\sin d+c\cos w,b\cos d-c\sin w)\);
its squared norm is \(N_c(s)^2\). Applying Cauchy to the
two actual shifted corners gives exactly
\[
 ag+ct\le R\{N_a(x)+N_c(s)\}
       -\frac{a+c}{2}-b-a\{\cos x+(\sin x)_+\}-K_s(d).
\tag{15}
\]
The wrong-side assumption and \(\alpha\le1\) give
\[
 g+t+p\eta\le
 R\{N_a(x)+N_c(s)\}
 -a\{\cos x+(\sin x)_+\}-K_s(d)-p(x+s)+C,
\quad
 C=-\frac{2\alpha}{5}-\frac35-b.
\tag{16}
\]
Only the actual A/B circles and the exact three witnesses
were used in this collection.

## 4. Exact minimization of the remaining angular penalty

Let \(r=b/c\), so \(13/20\le r\le23/25<1\). Then
\[
 \frac{K_s(d)}c\ge
 \begin{cases}
  1+r(\cos s+\sin s),&s\ge0,\\
  \cos(-s)+r,&s\le0.
 \end{cases}
\tag{17}
\]
The following elementary Taylor bounds suffice throughout:
\[
 \sin h<\frac{13}{20},\quad
 \cos h>\frac{19}{25}>\sin h,\quad
 \cos(h/2)>\frac{15}{16},\quad
 \sin(h/2)<\frac{343}{1000}.
\tag{18}
\]

For \(s\ge0\), the expression on \(0\le d\le s\) is
\(\cos(s-d)+\sin(s-d)+r(\cos d+\sin d)\).
It is concave, and its smaller endpoint is \(d=s\).
For \(d=-v\le0\), subtract its value at zero and divide by
\(2\sin(v/2)\). The remaining bracket is
\[
 \cos(s+v/2)-\sin(s+v/2)-r\sin(v/2).
\]
Since \(s+v\le h\), it is bounded below by
\[
 (\cos h-\sin h)\cos(v/2)
                +(\cos h+\sin h-r)\sin(v/2)>0.
\]
For \(d=s+v\), the corresponding bracket is
\[
 r\{\cos(s+v/2)-\sin(s+v/2)\}-\sin(v/2).
\]
After the same replacement its cosine coefficient is positive.
If its sine coefficient is nonnegative, the sign is immediate.
Otherwise it decreases up to \(v/2=h/2\), where it exceeds
\[
 \frac{13}{20}\left(\frac{15}{16}-\frac{343}{1000}\right)
                         -\frac{343}{1000}>0.
\tag{19}
\]
This proves the first line of (17).

For \(s=-v\le0\), the expression on \(-v\le d\le0\) is
\(\cos(d+v)+r\cos d\). Concavity reduces to its endpoints;
the smaller is \(d=0\), with value \(\cos v+r\).
For \(d=-v-u\), subtract the value at \(-v\). After division
by \(2\sin(u/2)\), the bracket is
\[
 \cos(u/2)-\sin(u/2)-r\sin(v+u/2).
\]
Using \(v+u\le h\), it is bounded below by its value with
\(v+u/2=h-u/2\). That expression decreases as \(u/2\)
increases up to \(h/2\), and is greater than
\[
                  \frac{15}{16}
                   -\left(1+\frac{23}{25}\right)\frac{343}{1000}>0.
\tag{20}
\]
Finally, if \(d\ge0\), concavity on \(0\le d\le h-v\)
leaves the endpoint \(d=h-v\). Its excess above \(\cos v+r\)
is
\[
 D(v)=\cos h-r+(r(\cos h+\sin h)-1)\cos v
                                -r(\cos h-\sin h)\sin v.
\]
Here \(D(h)=0\). If \(1-r(\cos h+\sin h)\le0\), then
\(D'<0\). Otherwise \(D'\) increases with v, and
\(D'(v)\le D'(h)=\sin h-r<0\). Thus \(D(v)\ge0\),
proving the second line of (17).

## 5. The three-frame hull leaves only two scalar endpoints

For fixed admissible weights define
\[
 f_v(u)=R\sqrt{v^2+b^2-2vb\sin u}-v\cos u+pu,
                         \qquad 0\le u\le h.
\tag{21}
\]
These functions are strictly convex whenever \(b\le v\le1\).
Indeed, with \(A=vb\), \(B=v^2+b^2\), and
\(n(u)=\sqrt{B-2A\sin u}\),
\[
 n'''(u)=\frac{A\cos u}{n(u)^5}
            \{B^2-AB\sin u+A^2\sin^2u-3A^2\}>0.
\tag{22}
\]
The brace divided by \(A^2\) is
\(z^2-z\sin u+\sin^2u-3\), where \(z=B/A\ge2\).
It is increasing in z and equals \((1-\sin u)^2>0\)
at z=2. Consequently
\[
 f_v''(u)\ge v\cos h-\frac{Rv^2b^2}{(v^2+b^2)^{3/2}}
       \ge v\left(\cos h-\frac{R}{2\sqrt2}\right)
       >\frac{3v}{50}>0.
\tag{23}
\]
We used \(R/\sqrt2<7/5\) and (18).

Two exterior-frame derivatives are also useful. For
\(b\le v\le1\),
\[
 A_v(u)=R\sqrt{v^2+b^2+2vb\sin u}
                          -v(\cos u+\sin u)-pu
\]
strictly decreases. In fact, putting \(r=b/v\le1\) and
using that \(r/\sqrt{1+r^2+2r\sin u}\) increases in r,
\[
 A_v'(u)\le H_1(u)-p,\qquad
 H_1(u)=\frac{R}{\sqrt2}\{\cos(u/2)-\sin(u/2)\}-\cos u+\sin u.
\tag{24}
\]
The function \(H_1\) increases: its derivative is
\(\cos u+\sin u-(R/(2\sqrt2))(\cos(u/2)+\sin(u/2))>0\).
Taylor bounds at h give
\[
 H_1(u)\le H_1(h)
 <\frac{1028912663}{1440000000}<\frac{18}{25}<p.
\tag{25}
\]

For \(13/20\le b/c\le23/25\) and \(c\le1\), the function
\[
 B_c(u)=R\sqrt{c^2+b^2+2cb\sin u}-b(\cos u+\sin u)-pu
\]
also strictly decreases. Writing \(r=b/c\), Cauchy gives
\[
 B_c'(u)+p
 \le r\sqrt{1+\left(\frac{R}{\sqrt{1+r^2}}-1\right)^2}.
\tag{26}
\]
The square on the right increases in \(0\le r\le1\).
For completeness, on writing \(v=\sqrt{1+r^2}\), its
derivative with respect to v is
\[
 2\left(2v-R-\frac{R}{v^2}+\frac{Q}{v^3}\right)>0;
\]
the first two terms are positive because \(R<2\), and the
last two combine to \(R(R-v)/v^3>0\), since \(v\le\sqrt2<R\).
At \(r=23/25\),
\[
 \frac{R}{\sqrt{1+r^2}}-1<\frac{457}{1000},\qquad
 r^2\left(1+\left(\frac{457}{1000}\right)^2\right)
                                      <\left(\frac{253}{250}\right)^2.
\]
Therefore
\[
                        B_c'(u)<-\frac{103}{12250}<0.
\tag{27}
\]

Now define the width of the three-frame hull
\[
 \rho=\max(\theta_G,\theta_A,\theta_T)
                         -\min(\theta_G,\theta_A,\theta_T)\le h.
\tag{28}
\]
Choose the weights as a function of this actual \(\rho\);
keep them fixed during the following scalar comparisons.

If A lies below T, write \(x=-u\), \(s\ge0\). Then
\(u=\rho=\eta+s\). By the first line of (17), (16) is
\(f_a(u)+B_c(s)+C-c\). Equation (27) lowers s to zero
in this upper bound, giving the common-frame endpoint A=B=T
at parameter \(\rho=u\).

If A lies above G, write \(s=-v\), \(x\ge0\), so
\(v=\rho=\eta+x\). The second line of (17) gives the upper
bound \(A_a(x)+f_c(v)+C-b\). Equation (25) lowers x to
zero, giving the common-frame endpoint A=B=G at \(\rho=v\).

If A lies between T and G, put \(x=-u\), \(s=-v\).
Then \(u+v=\eta=\rho\), and the upper bound is
\(f_a(u)+f_c(v)+C-b\). By (23), its maximum on this
segment is at \(u=0\) or \(v=0\). These are precisely
the same two endpoints.

Thus, for either choice in (12), (16) is bounded above by
the larger of
\[
\begin{aligned}
 U_T(\rho;\alpha,\beta)
 &=R\left\{\sqrt{\alpha^2+\beta^2-2\alpha\beta\sin\rho}
                          +\sqrt{1+\beta^2}\right\}
   -\frac{2\alpha}{5}-\frac85-2\beta-\alpha\cos\rho+p\rho,\\
 U_G(\rho;\alpha,\beta)
 &=R\left\{\sqrt{\alpha^2+\beta^2}
                          +\sqrt{1+\beta^2-2\beta\sin\rho}\right\}
   -\frac{7\alpha}{5}-\frac35-2\beta-\cos\rho+p\rho.
\end{aligned}
\tag{29}
\]
Interchanging which side has weight \(\alpha\) merely exchanges
the two endpoint formulas. No endpoint circle or moved packing
is asserted in this comparison: (29) is an upper bound on the
original stress.

## 6. Three explicit analytic weight families

Use the following exact rational coefficients; finite decimals
in this section denote exact rationals:
\[
(\alpha,\beta)=
\begin{cases}
 (4/5,\ 13/20),&0\le\rho\le7/20,\\[2mm]
 (0.9588+1.68x+0.75x^2,\quad
  0.78585+1.34x+x^2),\
       x=\rho-9/20,&7/20\le\rho\le47/100,\\[2mm]
 (1,\quad0.612+0.435\rho),&47/100\le\rho\le7/10.
\end{cases}
\tag{30}
\]
The weights need not agree at the joins; each is independently
admissible on its entire displayed interval. In the middle
interval, \(-.1\le x\le.02\), both polynomials increase,
\[
 .7983\le\alpha\le.9927,\qquad .66185\le\beta\le.81305,
\]
and
\[
 \frac{23}{25}\alpha-\beta
                    =.096246+.2056x-.31x^2>0
\tag{31}
\]
by concavity and its two endpoints. The outer families plainly
satisfy (13) as well. We now prove
\[
               U_T(\rho),U_G(\rho)<L<S_0+\frac1{10000},
 \qquad L=.4151256.
\tag{32}
\]

Let \(S_n,C_n\) denote the usual degree-n Taylor polynomials
for sine and cosine. On \([0,h]\),
\(S_7\le\sin\le S_5\) and \(C_6\le\cos\le C_4\).
We use
\[
 \overline R=1.978788,\qquad
 \underline S_0=.4150256,\qquad L=\underline S_0+\frac1{10000}.
\tag{33}
\]
Their positive square reserves are
\[
 \overline R^2-Q=\frac{121809}{62500000000},\qquad
 Q-1-\left(\frac{\underline S_0+3}{2}\right)^2
                                      =\frac{59119}{1562500000000}.
\tag{34}
\]

### 6.1 The first family uses only the two interval endpoints

For fixed weights, each expression in (29) is a constant plus
one of the convex functions (21). It therefore suffices to
check \(\rho=0,7/20\). At these points the four required norm
upper bounds are
\[
\begin{aligned}
 \sqrt{(4/5)^2+(13/20)^2}&<1.030777,\\
 \sqrt{1+(13/20)^2}&<1.192687,\\
 \sqrt{(4/5)^2+(13/20)^2-2(4/5)(13/20)\sin(7/20)}&<.840171,\\
 \sqrt{1+(13/20)^2-2(13/20)\sin(7/20)}&<.988298.
\end{aligned}
\tag{35}
\]
All follow by squaring, with \(S_7(7/20)\) in the last two.
Using \(C_6(7/20)\) in the elementary terms gives
\[
 U_T(0)=U_G(0)<\frac{19}{50},\qquad
 U_T(7/20)<\frac{409}{1000},\qquad
 U_G(7/20)<\frac{197}{500}.
\tag{36}
\]
Each is less than L.

### 6.2 The two middle-family norm bounds

Put
\[
\begin{array}{ll}
 A_T=\alpha^2+\beta^2-2\alpha\beta S_7(\rho),&
 B_T=1+\beta^2,\\
 A_G=\alpha^2+\beta^2,&
 B_G=1+\beta^2-2\beta S_7(\rho),\\
 E_T=L+\frac{2\alpha}{5}+\frac85+2\beta+\alpha C_6(\rho)-p\rho,&
 E_G=L+\frac{7\alpha}{5}+\frac35+2\beta+C_6(\rho)-p\rho.
\end{array}
\tag{37}
\]
For any positive auxiliary polynomials \(r_1,r_2\), define
\[
 P_i=2r_1r_2E_i-\overline R
           \{r_2(A_i+r_1^2)+r_1(B_i+r_2^2)\},
                                  \qquad i=T,G.
\tag{38}
\]
The inequality \(\sqrt v\le(v+r^2)/(2r)\), together with
(33)--(34), shows that \(P_i>0\) implies \(U_i<L\).

For T use
\[
 r_1=.938801+.910295x-.346828x^2,\qquad
 r_2=1.271842+.826895x+1.00681x^2.
\tag{39}
\]
For G use
\[
 r_1=1.2397+2.148807x+1.215908x^2,\qquad
 r_2=.966416-.247658x+.092273x^2.
\tag{40}
\]
All four are greater than \(4/5\). For example, the constant
coefficient minus the sum of the absolute nonconstant terms
at \(|x|=1/10\) already exceeds \(4/5\) in every case.

Here are complete whole-interval coefficient certificates
for (38). Their polynomials are defined entirely by
(30), (33), and (37)--(40); no fitted remainder is an input.
For explicit coefficient recovery, if \(P(x)=\sum P_nx^n\),
then
\[
                  [y^j]P(a+y)=\sum_{n\ge j}\binom njP_na^{n-j}.
\tag{41}
\]

For T expand at \(\rho=91/200\), equivalently
\(x=1/200+y\):
\[
                  P_T=\sum_{j=0}^{13}a_jy^j.
\]
Exact rational multiplication gives
\[
 a_0>\frac{167}{10^6},\qquad
 |a_1|<\frac{1111}{500000},\qquad
 a_2-\sum_{j=3}^{13}|a_j|
                      \left(\frac{21}{200}\right)^{j-2}>\frac65.
\tag{42}
\]
Since \(|y|\le21/200\) on the entire interval,
\[
 P_T>\frac{167}{10^6}
       -\frac{1111}{500000}|y|+\frac65y^2
 \ge\frac{167}{10^6}
       -\frac{(1111/500000)^2}{4(6/5)}
 >\frac1{6250}>0.
\tag{43}
\]

For G expand at \(\rho=41/100\), equivalently
\(x=-1/25+y\):
\[
                  P_G=\sum_{j=0}^{11}b_jy^j.
\]
The exact coefficient bounds are
\[
 b_1+\sum_{j=2}^{11}j|b_j|
                         \left(\frac3{50}\right)^{j-1}<-\frac14,
 \qquad P_G(47/100)>\frac7{2500}.
\tag{44}
\]
Here the argument in the last expression is \(\rho\).
Since \(|y|\le3/50\), (44) proves that \(P_G\) decreases
and remains positive on the entire middle interval.

### 6.3 The last family has one common endpoint formula

Here \(\alpha=1\), so \(U_T=U_G\). Set
\(x=\rho-47/100\), \(0\le x\le23/100\), and use (37)--(38)
with the T definitions and
\[
\begin{aligned}
 r_1&=.962844-.591585x-.297613x^2+.067787x^3,\\
 r_2&=1.290965+.275113x+.043889x^2-.008793x^3.
\end{aligned}
\tag{45}
\]
Again both auxiliaries exceed \(4/5\), directly by the
absolute-coefficient bound at \(23/100\). Write
\(P_T=\sum_{j=0}^{12}c_jx^j\). Exact rational multiplication
gives
\[
 c_0>\frac{23}{50000},\qquad
 c_1+\sum_{\substack{2\le j\le12\\c_j<0}}
                       c_j\left(\frac{23}{100}\right)^{j-1}
                                                 >\frac{51}{1000}.
\tag{46}
\]
It follows that
\[
                          P_T>\frac{23}{50000}+\frac{51}{1000}x>0.
\tag{47}
\]
Equations (35)--(47) prove (32) for all three complete
continuous intervals.

## 7. The original sign capture and AB alignment

For AB0, if either signed middle variable is at most
\(-1/10\), choose the corresponding weights (12) at the
actual hull width (28). Sections 3--6 prove (9).

For AB2, exchange A with B and G with T, reverse the local
frame direction, and negate signed tangents. The actual
middle equations become AB0 with the same hard owners in
their displayed roles. The new \(\eta\) is unchanged,
the new pair \((g,t)\) is \((t,g)\), and the corner circles
and frame span are unchanged. Since the argument already
covers either member at most \(-1/10\), the same (9) follows.
This is a relabeling of the original three inequalities,
not a change to any H/D/E state or its sign.

But (8) and (9) are inconsistent, because
\[
                 \frac{27}{160000}-\frac1{10000}
                                      =\frac{11}{160000}>0.
\tag{48}
\]
Thus \(g>-1/10\) and \(t>-1/10\), proving (4).
The already proved signed intermediate order and
[the small-wrong-sign AB alignment theorem](HAND_G5_AB_ALIGNMENT_WITH_SMALL_WRONG_INTERMEDIATE_SIGNS.md)
now apply to the original system, with all their original
witness, sorting, true-core, and separate strict-loss conclusions.

The mathematical inputs are the actual middle stress,
whole-sector angular comparisons, convexity on one segment,
and the explicitly defined rational polynomial certificates.
No state or angle mesh, numerical acceptance premise, Lean
compilation, or CI result is used.
