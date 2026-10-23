# Whole-interval scalar certificates for sole E and negative T

## 1. Exact scalar family

This is the scalar companion to
[the complete ordinary sole-E negative-T theorem](HAND_G5_POSITIVE_GA_SOLE_E_NEGATIVE_T_EXCLUSION.md).
Use its exact coefficients k,l,c,g,eta,lambda, its two endpoints
E,G and its constants
\[
 Q_1=1957767069/500000000,\quad R=\sqrt{Q_1},\quad h=.7,
 \quad a_0=\sqrt{Q_1-1/4}-1/2,\quad \ell=1.05c.
\tag{1}
\]
All terminating decimals below are rational numbers.

Put
\[
 C_v(t)=1+2\cos t+(1+2v-R\sqrt{1+v^2})\sin t,
 \quad n(t)=k(\cos t+g\sin t),
 \quad p(t)=\cos t+\eta\sin t.
\tag{2}
\]
For EH0 and EH1 the baselines are
\[
\begin{split}
 B_E(t)={}&3k+2l+3c+C_\eta(t)\\
 &-R\{\sqrt{1+k^2}+\sqrt{k^2+l^2}
                +\sqrt{l^2+c^2}+\sqrt{p(t)^2+c^2}\},\\
 B_G(t)={}&3+2l+3c+kC_g(t)\\
 &-R\{\sqrt{1+n(t)^2}+\sqrt{k^2+l^2}
                +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{3}
\]
For EH2, BG is unchanged and
\[
\begin{split}
 B_E(t)={}&3+\sin t-2R\sin(t/2)+3k+2l+3c\\
 &-R\{\sqrt{1+k^2}+\sqrt{k^2+l^2}
                      +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{4}
\]
For DE0 and DE1, \(\lambda=1.25\) and
\[
\begin{split}
 B_E(t)={}&1+\tfrac12\cos t+(\tfrac12-a_0)\sin t
                              +\tfrac32\lambda+3k+2l+3c\\
 &-R\{\sqrt{\lambda^2+k^2}+\sqrt{k^2+l^2}
                      +\sqrt{l^2+c^2}+\sqrt{1+c^2}\},\\
 B_G(t)={}&\tfrac32(1+\lambda)+2l+3c+kC_g(t)\\
 &-R\{\sqrt{\lambda^2+n(t)^2}+\sqrt{k^2+l^2}
                      +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{5}
\]

For the data below, set n=k at E and n=n(t) at G. In EH0/EH1
set p=p(t) at E and p=1 at G; in EH2 set p=1 at both endpoints.
The old negative charges are
\[
 V_i(w)=\nu_i(\cos w-1)
                   -R\{\sqrt{v_i-2b_i\sin w}-\sqrt{v_i}\},
\tag{6}
\]
with
\[
\begin{array}{c|c|c|c}
 & (v_H,v_A,v_B,v_D)&(b_H,b_A,b_B,b_D)&(\nu_H,\nu_A,\nu_B,\nu_D)\\ \hline
 \mathrm{EH}&(1+n^2,k^2+l^2,l^2+c^2,p^2+c^2)&(n,kl,lc,pc)&(n,l,c,c)\\
 \mathrm{DE}&(\lambda^2+n^2,k^2+l^2,l^2+c^2,1+c^2)&(\lambda n,kl,lc,c)&(\lambda,l,c,c).
\end{array}
\tag{7}
\]
The D coefficient c in the EH row is used only in EH1/EH2,
where c≥p. No shifted pure charge is required in EH0.
The DE scalar set uses only indices H,A,B; its D norm remains
in the baseline, with no ordinary D angle.

Put
\[
 J_0(t)=.32(c-p)^2\quad\text{in EH1/EH2},
 \qquad J_0(t)=0\quad\text{otherwise}.
\tag{8}
\]
The complete set of new scalars consists of
\[
       B_\varepsilon+J_0+\ell t
                    \quad\text{on a diagonal interval},
\tag{9}
\]
and
\[
       B_\varepsilon+J_0+.3\ell+V_i(t-.3)
                    \quad\text{on a shifted interval}.
\tag{10}
\]
Here \(\varepsilon=E,G\), and the intrinsic intervals are
\[
\begin{array}{c|c|c|c}
 \text{family}&t\text{ interval}&\text{form}&\text{negative indices}\\ \hline
 \mathrm{EH}_0&[0,.2]&(9)&\text{none}\\
 \mathrm{EH}_1&[.2,.3]&(9)&\text{none}\\
 \mathrm{EH}_1&[.3,.35]&(10)&H,A,B,D\\
 \mathrm{EH}_2&[.35,.7]&(10)&H,A,B,D\\
 \mathrm{DE}_0&[0,.3]&(9)&\text{none}\\
 \mathrm{DE}_0&[.3,.35]&(10)&H,A,B\\
 \mathrm{DE}_1&[.35,.7]&(10)&H,A,B.
\end{array}
\tag{11}
\]
There are 34 scalars. The only cut besides the already fixed
coefficient families is the intrinsic negative-error cap t=.3.
No interval has been subdivided for a sampled sign test.

## 2. Explicit rational positive-mass numerators

Take
\[
 R_+=1.978770866>R,\qquad
 A_+=1.914558470771>\sqrt{Q_1-1/4},
\tag{12}
\]
and the Taylor polynomials
\[
 S(t)=\sum_{j=0}^7\frac{(-1)^jt^{2j+1}}{(2j+1)!},
 \qquad C(t)=\sum_{j=0}^8\frac{(-1)^jt^{2j}}{(2j)!}.
\tag{13}
\]
Positive squaring proves (12). On [0,h], the errors in S and C
are less than \(7\cdot10^{-18}\) and \(3\cdot10^{-19}\).

For any row [a,a+D] of (11), use the local variable z=t−a.
Substitute the exact polynomial coefficient family from the
main note. The following instructions specify each numerator
over the rationals without fitted coefficients or fitted roots.

First form the outside part A and four squared norms from
(3)--(5), replacing all sine/cosine terms by (13). Replace R
by R+ in every negative support term. In the E endpoint of
(5), replace \(\tfrac12-a_0\) by \(1-A_+\). This only
decreases the expression. Extract every tilted support radical
from A as one additional pair (squared norm, nonnegative weight):
\[
 (1+\eta^2,S(t))\quad\text{for E in EH0/EH1},
 \qquad (1+g^2,kS(t))\quad\text{for every G endpoint}.
\tag{14}
\]
The four anchor norms have weight 1. For E in EH2, there is
no additional pair; put \(-2R_+S(t/2)\) directly in A. For
E in DE, there is no additional pair either.

Add J0, using the same substituted p, to A. For a diagonal
case add \(1.05ct\). For a shifted case let w=t−.3, add
\[
                          .315c+\nu_i\{C(w)-1\}
\tag{15}
\]
to A and replace its corresponding squared norm by
\[
                             v_i-2b_iS(w).
\tag{16}
\]
The original norm cancels exactly in (10); after (16), every
remaining radical has a nonpositive coefficient.

For each resulting squared-norm polynomial v(z), put
\(v_0=v(0)>0\), and make three rational Newton steps:
\[
 \rho_0=1,\qquad \rho_{j+1}=(\rho_j+v_0/\rho_j)/2
                             \quad(j=0,1,2).
\]
With truncation in z, define the cubic positive mass
\[
 u=([v]_{\le3}-v_0)/v_0,\qquad
 m_v=[\rho_3(1+u/2-u^2/8+u^3/16)]_{\le3}.
\tag{17}
\]
For all resulting squared norms and weights \((v_j,w_j)\),
define the rational polynomial
\[
 P(z)=2A(z)\prod_jm_{v_j}(z)
     -R_+\sum_jw_j(z)\{v_j(z)+m_{v_j}(z)^2\}
                                     \prod_{r\ne j}m_{v_r}(z).
\tag{18}
\]
Every mass is positive by the exact bounds below. The identity
\[
        \frac{v+m^2}{2m}-\sqrt v
                     =\frac{(\sqrt v-m)^2}{2m}\ge0
\tag{19}
\]
therefore makes \(P/(2\prod m_{v_j})\) a lower bound for the
Taylor-substituted scalar. Formula (19) is valid for any positive
mass. No assumption that (17) approximates a square root is used.

## 3. One coefficient-norm rule on the complete intervals

For a rational polynomial \(F(z)=\sum_{n=0}^Na_nz^n\) on
[0,D], define
\[
 B_0=\sum_na_n\frac{D^n}{4^n}\binom{2n}{n},\qquad
 B_j=2\sum_{n\ge j}a_n\frac{D^n}{4^n}\binom{2n}{n-j}
                              \quad(j\ge1),
\]
\[
                      \mathcal C_D(F)=B_0-\sum_{j\ge1}|B_j|.
\tag{20}
\]
These are finite rational sums. The identity
\(F(z)=\sum_jB_jT_j(2z/D-1)\) and \(|T_j|\le1\) give
\[
                              F(z)\ge\mathcal C_D(F).
\tag{21}
\]
This single whole-interval norm verifies the following uniform
inequalities for the explicitly defined family (11),(17),(18):
\[
 \deg P\le47,\qquad
 \mathcal C_D(v_j)>.8,\qquad
 \mathcal C_D(m_{v_j})>.99,\qquad
                  -\mathcal C_D(-m_{v_j})<1.7.
\tag{22}
\]
For 33 of the 34 polynomials,
\[
                              \mathcal C_D(P)>.00058.
\tag{23}
\]
The one exception to (23) is EH2, E endpoint, shifted negative
index A. On its entire interval, a=.35,D=.35, use the exact
identity
\[
                      P(z)=P(0)+z\,\frac{P(z)-P(0)}z.
\tag{24}
\]
Its rational coefficients satisfy
\[
                P(0)>.0033,\qquad
 \mathcal C_{.35}\left(\frac{P(z)-P(0)}z\right)>.476.
\tag{25}
\]
Equations (17)--(25) are compact certificates for the complete
family: they require only rational additions, multiplications,
divisions by positive constants and the binomial coefficients
in (20). There is no coefficient-sign inventory over sampled
angles or small cells. In particular the first quotient in
(24) is one polynomial on the whole high-family interval.

To check the substitution error, keep all masses (17) fixed
when replacing the Taylor inputs by the actual trigonometric
inputs. They remain positive, and (19) remains valid. There
are at most five masses, each less than 1.7; every outside
part has absolute value below 30, every squared norm below 5,
every weight below 2, and their input partial derivatives
have absolute value below 30. Directly differentiating (18)
with these coarse bounds gives absolute input partials below
\(10^7\). There are at most five distinct sine/cosine inputs
in a numerator. Thus the total error is below \(10^{-8}\),
far below (23) and (25). All scalars (9)--(10) are strictly
positive on their complete closed intervals.

## 4. Auxiliary exact comparisons used by the angular proof

For the reader wishing to reproduce the elementary bounds in
the main note, the same coefficient rule (20) proves the two
norm-gain derivative comparisons without any additional angle
partition. Define
\[
 T_{r,L}(z)=L^2(1+r^2-2rz)^3
                        -Q_1r^4(r-z)^2(1-z^2).
\tag{26}
\]
Then
\[
                       \mathcal C_{.6443}(T_{.72,.4})>.00114.
\tag{27}
\]
For \(T=T_{.81,.53}\), expand \(T'(.4+v)=b_0+b_1v+b_2v^2+b_3v^3\).
The rational quantities obey
\[
 q_2=b_2+.4|b_3|<-.987,\qquad
                    b_0-\frac{b_1^2}{4q_2}<.001,
\]
\[
                         T(.6443)-.001(.6443)>.0367.
\tag{28}
\]
Because \(|v|\le.4\), the first two bounds make T′<.001;
the last proves T>0 on [0,.6443]. This is a completed-square
proof on one interval, not a subdivision.

For the far-angle A comparisons, use the upper Taylor
polynomial \(C_8(.4)\). Direct rational inequalities are
\[
 .346\frac{1-C_8(.4)}{.4}-.4(.06)>.044,
 \qquad
 .303\frac{1-C_8(.4)}{.4}-.53(.1055)>.0038.
\tag{29}
\]
The fixed radical bounds used for H/D and B are
\[
\begin{split}
 H(.86265,1;h)-1.05(1-\cos h)&>.791>1.13h,\\
 \frac{.86265}{h}V_{.585,1}^{1}(h)&>.66,\\
 \frac{.903}{h}V_{.625,1}^{1}(h)&>.75.
\end{split}
\tag{30}
\]
They follow by positive-sided squaring using
\(1.978770865<R<1.978770866\), the S15 lower bound for
sin h and the C14 lower bound for cos h. Equivalently, an
explicit rational enclosure for any positive rational root
in these three comparisons is obtained by
\[
 m=\left\lfloor\sqrt{10^{24}v}\right\rfloor,
 \qquad \frac m{10^{12}}\le\sqrt v<\frac{m+1}{10^{12}},
\tag{31}
\]
with both sides checked by integer squaring. Formula (31)
is only a way to express exact positive-sided radical bounds;
no sampled-angle assertion is involved.

The remaining inequalities in the main angular proof are the
explicit family ranges, the quadratic discriminant (19) there,
positive-sided squares, and the parent sole-E chord and
curvature bounds on their original complete intervals.
Together with (23)--(25), these provide the strict endpoint
contradictions required for every ordinary sign allocation.
No numerical optimizer, state mesh, Lean compilation or CI
is a premise of these certificates.
