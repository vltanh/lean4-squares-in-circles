# A precise obstruction to completing the clipped labels edge by edge

## 1. Scope of the obstruction

The all-sign zero-edge theorem in
`HAND_G4_ALL_SIGN_ZERO_LINEAR_CHARGE.md` uses the six labels
\[
\begin{array}{lll}
 L_H=p\max(y_H,0),&L_A=p\max(y_A,0),&L_T=p\max(y_T,0),\\
 L_G=p(1+\min(y_G,0)),&L_B=p(1+\min(y_B,0)),
   &L_D=p(1+\min(y_D,0)),\qquad p=49/50.
\end{array}                                                     \tag{1}
\]
The E label has not been specified. This note shows that **no choice
of a single-vertex E label can complete these six labels by seven
independently quantified constant pair bounds with a near-sharp total
budget**. It does not exclude a coupled inequality using a common
seven-vertex configuration, a multi-edge charge, or different labels.

In particular, it would be invalid to apply the new zero bounds on
three edges and retain incompatible historical quarter bounds on the
other four edges. The obstruction is already present at exactly
aligned frames, so changing a coefficient of the mismatch charge
cannot remove it.

Fix a radius parameter
\[
             \frac{39141}{10000}<q\le Q:=\frac{9789}{2500}.        \tag{2}
\]
This interval contains both Q and
\(1957767069/500000000\), the sharper radius ceiling in the later
handproof. Write
\[
 a_*(b)=\sqrt{q-(b+1/2)^2}-1/2.                                 \tag{3}
\]
Every state \((a_*(b),\pm b)\) below is an original own-frame state
on the outer corner circle. Our convention is that the physical
center has own-frame coordinates \((a,-y)\).

Suppose that for each edge i of the candidate cycle there is a
constant \(\gamma_i\) such that the independently quantified pair
inequality
\[
 \phi_i-\rho_i h(|d_i|)+L_i-L_{i+1}\ge\gamma_i,
 \qquad h(x)=\frac{\sin x+\cos x-1}{2},                          \tag{4}
\]
holds over its entire original local domain. The real coefficients
\(\rho_i\) are arbitrary. The E label may be any function of its
single-vertex state and q; the same function must be used on DE and
EH. The other labels are exactly (1).

**Proposition.** Even if the local domains in (4) impose all four
proposed G3 tangent cuts, the original radial conditions, the gap
bounds \(19/25<g<3\pi/4\), and the original feasible-owner
disjunction, their constants necessarily obey
\[
                 \boxed{\ \sum_i\gamma_i
                      <2\pi-\frac{539}{5000}.\ }               \tag{5}
\]
All test pairs used to prove (5) have \(d_i=0\). The four quarter
tests use the **same E state** wherever E occurs. The tests on
different edges are independent; they are not asserted to assemble
into one feasible seven-cycle.

## 2. Four quarter tests with a common E state

Put
\[
 b=\frac{69}{100},\qquad a=a_*(b),\qquad
 g=a-1,\qquad c=a_*(g),\qquad r=a_*(1),\qquad e=a_*(0).          \tag{6}
\]
Consider these aligned quarter pairs:
\[
\begin{array}{c|cc|c}
 \text{edge}&(a_i,y_i)&(a_{i+1},y_{i+1})&
          \text{original contact projections}\\ \hline
 GA&(c,-g)&(a,b)&P_0=P_1=a-g=1\\
 BT&(a,-b)&(c,g)&P_2=P_3=a-g=1\\
 DE&(1,-r)&(e,0)&P_2=P_3=1\\
 EH&(e,0)&(1,r)&P_0=P_1=1.
\end{array}                                                     \tag{7}
\]
Here \(\phi=\pi/2\), \(d=0\), and the separating width is 1.
The two listed contact projections in each row are original axes,
with a permissible tie. No owner is replaced or selected by a
radial optimization. In particular, both appearances of E are the
identical actual state \((e,0)\), with the required E sign.

We verify the domains by short rational comparisons. The corner
values at \((43/40,69/100)\) and \((11/10,69/100)\) are,
respectively,
\[
 \frac{155869}{40000}<\frac{39141}{10000},\qquad
 \frac{39761}{10000}>Q.
\]
Therefore
\[
 \frac{43}{40}<a<\frac{11}{10},\qquad
 \frac3{40}<g<\frac1{10},\qquad
                  1<c<\frac{283}{200}.                        \tag{8}
\]
The last lower bound follows, for example, by testing
\((1,1/10)\) in the containing-circle inequality. All displayed
states satisfy \(a_i\ge |y_i|\) and the central-disk lower bound
on \(a_i\); in fact their primary coordinates exceed 1 except for
the two primary coordinates exactly equal to 1. The universal
upper bound in (8) follows by testing
\((283/200,0)\).

Since
\[
 (3/2)^2+(129/100)^2=\frac{39141}{10000},\qquad
 (3/2)^2+(13/10)^2=\frac{197}{50}>Q,
\]
we also have
\[
                        \frac{79}{100}<r<\frac45.              \tag{9}
\]
Thus the G/T tangent magnitudes in (7) satisfy
\[
 \frac{g}{c}>\frac{3/40}{283/200}=\frac{15}{283}>\frac1{20},
 \qquad \frac{g}{c}<\frac1{10}<\frac45,
\]
and the H/D magnitudes are \(r>1/2\). Their signs are precisely
the proposed G3 signs.

For GA and BT the physical gap is
\[
             \frac\pi2-\arctan(g/c)-\arctan(b/a).
\]
The two positive arctangents have sum less than
\(1/10+13/20=3/4\), using (8),
\(b/a<138/215<13/20\), and \(\arctan t<t\).
The gap is consequently greater than
\(\pi/2-3/4>41/50>19/25\). For DE and EH it is
\(\pi/2-\arctan r>\pi/2-4/5>77/100>19/25\).
All four gaps are less than \(\pi/2<3\pi/4\).

The sum of the four left sides of (4), evaluated on (7), is
\[
 \begin{split}
 2\pi&+(L_G-L_A)+(L_B-L_T)+(L_D-L_E)+(L_E-L_H)\\
     &=2\pi+p\{3-2(g+b)-2r\}.                                \tag{10}
 \end{split}
\]
The E values cancel because the test E states agree. Equations
(8)--(9) give
\[
 2(g+b)+2r>
 2\left(\frac3{40}+\frac{69}{100}\right)
       +2\frac{79}{100}=\frac{311}{100}.
\]
Hence the sum of the four quarter constants is strictly less than
\[
                         2\pi-\frac{539}{5000}.               \tag{11}
\]

## 3. Each zero constant is at most zero

Use the following independent aligned zero-quarter pairs:
\[
\begin{array}{c|cc}
 HG&(a_*(4/5),4/5)&(a_*(1/5),-1/5)\\
 AB&(a_*(1/2),1/2)&(a_*(1/2),-1/2)\\
 TD&(a_*(1/5),1/5)&(a_*(4/5),-4/5).
\end{array}                                                     \tag{12}
\]
Every pair has \(d=\phi=0\) and the original transverse contact
projections \(P_0=P_2=1\). Its two transverse magnitudes sum to 1,
so the label difference in (1) is exactly zero.

All states remain in the original radial and sorted-coordinate
domains. The elementary bounds
\[
  \frac9{10}<a_*(4/5)<1,\qquad
  1<a_*(1/5)<\frac32,\qquad
  1<a_*(1/2)<\frac{121}{100}
\]
follow directly from (2)--(3). The first two establish the G/T and
H/D tangent cuts in (12).

For HG and TD the positive physical gap exceeds
\[
 \arctan(4/5)+\arctan(2/15)
 \ge\frac45-\frac{(4/5)^3}{3}
       +\frac2{15}-\frac{(2/15)^3}{3}
 =\frac{7714}{10125}
 =\frac{19}{25}+\frac{19}{10125}.                              \tag{13}
\]
For AB the gap exceeds
\[
 2\arctan(50/121)
 \ge2\left(\frac{50}{121}-\frac{(50/121)^3}{3}\right)
 =\frac{4142300}{5314683}>\frac{19}{25}.                        \tag{14}
\]
The arctangent lower bound follows by integrating
\(1/(1+t^2)\ge1-t^2\). Sorted coordinates give the required
upper gap bound as well. Thus these are valid full-domain local
tests, and each zero constant in (4) is at most zero. Together
with (11), this proves (5).

## 4. Consequence for this particular proof design

Summing a valid seven-edge budget of the form (4) in one actual
cycle would give
\[
                 \sum_i\rho_i h(|d_i|)
                         \le2\pi-\sum_i\gamma_i.              \tag{15}
\]
For the common rate \(\rho_i=1/50\), or for a subset of charged
edges at that rate, (5) forces the upper bound produced by this
argument to exceed \(539/5000\). Yet on the entire frame range,
\[
 \sum_i\frac1{50}h(|d_i|)
 \le\frac7{100}(\sqrt2-1)<\frac{147}{5000}<\frac{539}{5000}.
\]
It is therefore weaker than the elementary charge bound even
before a bad-mismatch lower bound is used. In particular it cannot
yield either coarse G4 contraction by summing independent constant
pair inequalities with these six labels and this charge rate.

The obstruction concerns **independent pair budgets**, not the
existence or geometry of a shared cycle. The four tests in (7)
use incompatible states at their common zero-edge vertices if
one tries to combine them with (12). Enforcing those common
vertices is exactly the extra information a successful coupled
cycle estimate must retain.
