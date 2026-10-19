# The mixed tilt cannot satisfy |t| <= S at S <= 3/200

## 1. The theorem

Assume the actual geometric hypotheses of
`HAND_E_OWNER_CHAIN_AT_THREE_TWO_HUNDREDTHS.md`, and suppose the chosen
original G and E witnesses both belong to `{0,1}`. The latter restriction
is supplied for every feasible witness by that note and
`HAND_G_HIGH_INDEX_OWNERS_AT_THREE_TWO_HUNDREDTHS.md`.

**Theorem.** Every such feasible cycle satisfies `|t|>S`.
This includes the intended pair G0/E1 as well as all three unwanted
low-index pairs. All original aligned owners and all ties are retained.
The result requires neither the old final mismatch contraction nor a
terminal tilt window.

The proof below supplies the actual geometric hypotheses for the reserve
previously recorded only arithmetically in
`HAND_SMALL_MISMATCH_BYPASS_AUDIT.md`. It is not a claim that the earlier
global cuts or mismatch contractions have been obtained.

Suppose, for contradiction, that `|t|<=S<=3/200`. Write

\[
 x_1=\theta_B,\quad x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad x_4=\theta_E-\theta_D,
 \quad h=\theta_H-t,
\]
\[
 S=\sum_{j=1}^4|x_j|+|h|,\qquad
 z=t+h-x_1-x_2-x_3-x_4.
\tag{1}
\]

In particular `|z|<=2S`. The actual coordinate bounds needed here are

\[
 7/12\le a_G,a_T<349/250,
 \quad b_G,b_T<4/5,
 \quad 447/800<a_E<283/200,\quad 0\le b_E<9/10.
\tag{2}
\]

The primary bounds follow from the G/T cuts and core/circle geometry.
For the transverse bound, `b>=4/5` and `b/a<=4/5` would give `a>=1`
and a farthest-corner squared norm at least `1.5^2+1.3^2=3.94>Q`.

## 2. One constant four-circle stress for all four mixed pairs

Put

\[
 p=24/41,\qquad e=36/31.
\]

Give HG,G,AB,BT,TD,DE,E the weights

\[
                      (1,1,p,1,1,e,e),               \tag{3}
\]

and complete the A,B,D,H circles with masses

\[
                 (12/41,12/41,12/31,12/31).          \tag{4}
\]

The remaining G,T,E coordinates stay actual and free. On every anchor
use the exact support

\[
 Xa+Yb\le mQ+(X^2+Y^2)/(4m)-(X+Y)/2.
\tag{5}
\]

Let Phi be weighted actual demand minus this coordinate upper bound.
Feasibility of the selected original witnesses implies `Phi<=0`.
At `x_1=x_2=x_3=x_4=h=t=0` the four forces are `(1,p),(1,p),(e,1),(e,1)`.
Their virtual centers are

\[
 A^*=B^*=(29/24,1/2),\qquad D^*=H^*=(1,19/24).
\tag{6}
\]

All free-coordinate terms cancel at this reference, so

\[
 \Phi(0)=\frac{1728}{1271}\left(\frac{2257}{576}-Q\right)
                     =\frac{3027}{794375}=:\Psi_0.
\tag{7}
\]

The virtual centers are derivatives of (5), not assumed actual centers.

For explicit owner coverage, the five original aligned projections are

\[
\begin{aligned}
 HG:&\ b_H-a_G\sin h+b_G\cos h,
       \quad-a_H\sin h+b_H\cos h+b_G;\\
 AB:&\ b_A+a_B\sin x_1+b_B\cos x_1,
       \quad a_A\sin x_1+b_A\cos x_1+b_B;\\
 BT:&\ a_B+a_T\sin x_2-b_T\cos x_2,
       \quad a_B\cos x_2+b_B\sin x_2-b_T;\\
 TD:&\ b_T+a_D\sin x_3+b_D\cos x_3,
       \quad a_T\sin x_3+b_T\cos x_3+b_D;\\
 DE:&\ a_D+a_E\sin x_4+b_E\cos x_4,
       \quad a_D\cos x_4+b_D\sin x_4+b_E.
\end{aligned}                                       \tag{8}
\]

The mixed projections are the literal G0/G1 formulas at t and E0/E1
formulas at z from the preceding notes. Each width is
`(1+cos(w)+|sin(w)|)/2` at its actual relative error w.

## 3. An exact first-order cycle flux

Let

\[
 R_G=1/2\text{ for G0},\qquad R_G=a_G\text{ for G1},
\]
\[
 R_E=19/24\text{ for E0},\qquad R_E=a_E\text{ for E1}.
\]

The full first-order term, including all seven linear cusps, is

\[
\begin{aligned}
 \mathcal L={}&R_Gt+|t|/2+e\{|z|/2-R_Ez\}
       +R_Hh+|h|/2\\
 &+\sum_{j=1}^4\{(\lambda_j/2)|x_j|-\lambda_jR_jx_j\},
\end{aligned}                                       \tag{9}
\]

where `(lambda_1,lambda_2,lambda_3,lambda_4)=(p,1,1,e)` and the
actual receiver alternatives are

\[
 R_H\in\{a_G,1\},\quad R_1=29/24,\quad
 R_2\in\{a_T,1/2\},\quad R_3\in\{1,a_T\},\quad
 R_4\in\{a_E,19/24\}.
\tag{10}
\]

These follow by differentiating (8), (5), and the mixed projections
at (6). They preserve both choices on every aligned edge.

For any real D in
`[e(R_E-1/2),e(R_E+1/2)]`, the exact cusp inequality gives

\[
                     e\{|z|/2-R_Ez\}\ge-Dz.
\tag{11}
\]

After substituting (1), the smooth aligned coefficients are
`R_H-D` and `D-lambda_j R_j`; the mixed G term becomes
`(R_G-D)t+|t|/2`. Set

\[
                           c_0=97/1550.              \tag{12}
\]

For E0 choose `D=1`. Its interval in (11) is `[21/62,3/2]`.
For either G choice, the G term is nonnegative by (2).
All aligned cusp intervals contain 1 except possibly the actual-E
receiver on DE. Its excess is at most

\[
 e(a_E-1/2)-1\le e(283/200-1/2)-1=97/1550.
\]

Therefore `L >= -c_0 S` in both E0 cases.

For E1 choose

\[
                     D=\max\{112/125,e(a_E-1/2)\}.
\tag{13}
\]

This belongs to (11) and satisfies

\[
             112/125\le D\le1647/1550<13/12.
\]

It belongs to every interval `[a_G-1/2,a_G+1/2]` and
`[a_T-1/2,a_T+1/2]` allowed by (2), and to the fixed H/TD/DE anchor
intervals. Only AB and the anchored BT receiver can exceed their
upper endpoint 1, by at most `c_0`; their errors together cost at
most `c_0 S`. The G1 mixed term is nonnegative. For G0 it is bounded
below by `-c_0|t|` (and is nonnegative when t<=0).
Consequently all four mixed pairs satisfy the single bound

\[
                         \mathcal L\ge-c_0(S+|t|).
\tag{14}
\]

The same D is used throughout the entire cycle. No independent error
budget is allocated to the two mixed angles.

## 4. One uniform Hessian estimate for every owner

Remove all seven sine cusps from Phi and call the remaining smooth
function F. Use the six variables `(x_1,x_2,x_3,x_4,h,t)`; their total
absolute value is at most `2S<=.03`.

The nonconstant part of the four negative force-norm terms is exactly

\[
 -\sin(a x_1-\chi_Gt)
 -\sin((1-a)x_1+b x_2)
 -(3/2)\sin(d x_3+f x_4)
 -(3/2)\sin(\chi_E z-g h),                            \tag{15}
\]

where `chi_G=1` for G0 and 0 for G1, and `chi_E=1` for E0 and 0
for E1. The bits `a,b,d,f,g` select respectively the second AB,
second BT, first TD, second DE, and second HG projections in (8).
Every argument in (15) has absolute value at most `.03`, and each
variable has coefficient 0 or +/-1. Thus the sum contributes less
than `.15` to the absolute value of any Hessian entry.

Combining the widths and linear corner shifts in (5) with the actual
free coordinates gives elementary one-angle expressions. For example,
the AB term divided by p is `1+cos(x_1)+sin(x_1)/2`.
The BT alternatives are

\[
 1+(1/2+b_T)\cos x_2-a_T\sin x_2,
 \quad1/2+\cos x_2+\sin x_2/2+b_T.
\]

The HG, TD and DE alternatives follow directly from (8) in the same
way. Equations (2) show that every aligned smooth second derivative
has absolute value less than `1.321`. These aligned terms occupy
separate coordinate diagonals.

The two mixed G smooth terms are

\[
 1/2+\cos t-\sin t/2+b_G,
 \quad1+(1/2+b_G)\cos t+a_G\sin t.
\]

They obey the same `1.321` bound and occupy only the t diagonal,
which is different from the aligned diagonals.

The two mixed E smooth terms, divided by e, are

\[
 1/2+\cos z+\sin z/2+b_E,
 \quad1+(1/2+b_E)\cos z-a_E\sin z.
\]

Because `|z|<=.03`, every Hessian entry contributed by either is at
most `e(1.4+1.415(.03))<1.676` in absolute value.
Adding the bounds proves

\[
                       |F_{ij}|<.15+1.321+1.676<4.   \tag{16}
\]

This is a symbolic owner-bit calculation and a whole-segment bound;
there is no list of fitted owner certificates.
Taylor's theorem and (16) lose at most
`2(S+|t|)^2<=8S^2`.

Finally `|sin v| >= |v|-|v|^3/6`. The five aligned cusps lose less
than `S^3/10`; the G cusp loses at most `S^3/12`; the E cusp loses
less than `4S^3/5`, since `|z|<=2S`. Their sum is less than `S^3`.

## 5. Strict contradiction

Equations (7), (14), and (16) yield

\[
 \Phi\ge\Psi_0-2c_0S-8S^2-S^3.
\]

All loss terms increase with S. At `S=3/200` the remaining reserve is
exactly

\[
\boxed{
 \frac{3027}{794375}-\frac{97}{775}\frac3{200}
 -8\left(\frac3{200}\right)^2-\left(\frac3{200}\right)^3
 =\frac{1319283}{10168000000}>0.}                     \tag{17}
\]

This contradicts `Phi<=0` and proves `|t|>S`.
The zero-error case and both signs of each mixed angle are included.
In particular (17) is now backed by the explicit stress, the actual
cycle flux, and the complete Hessian argument, rather than being an
arithmetic-only observation.

No Lean source or historical table was changed, no compilation or CI
was run, and no sampled or optimized value is a mathematical premise.
