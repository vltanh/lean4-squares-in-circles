# The middle/high frame estimate without its five coefficient rows

**Status: the complete scalar replacement is proved below.** This note
removes all five Bernstein premises from Section 6 of
`../MID_HIGH_WHOLE_PAIR_HAND_PROOF.md`. It retains that manuscript's
geometric support choices, actual contact argument across the quarter
turn, original signs and axes, and strengthened pair target `.8926`.
Together they prove the entire M/H entry without a continuous lookup.
No small frame-spread or mismatch assumption is used.

Every terminating decimal denotes an exact rational number. The new
arguments use a fourth-derivative sign on two complete intervals and
one common monotonicity theorem for the other three supports. The
few fixed scalar comparisons below follow from alternating Taylor
bounds and positive square comparisons.

## 1. The two varying-multiplier supports

Use the folded coordinates and constants of the original manuscript:

\[
 Q=9789/2500,\quad \mathcal R=\sqrt{2Q},\quad
 u=.089293,\quad v=.480179,\quad k=1.534906,\quad q=.045313.
\]

The last middle-arc endpoint is \((a_2,b_2)\), where

\[
 b_2=3a_2/5,\qquad (a_2+1)^2+b_2^2=2Q.
\]

Put

\[
 L_2=\pi/4+2.143075-ka_2+qb_2,\qquad
 A=1+a_2-b_2,\quad B=1-a_2-b_2.
\tag{1}
\]

The elementary endpoint brackets give

\[
 1.62343405<a_2<1.62343407,\quad
 2.79842813<\mathcal R<2.79842814,
 \quad 0<A<1.65,\quad B<-1.597.
\tag{2}
\]

For the positive or negative H source, respectively, the exact support
after minimizing the source circle and using the last M endpoint is

\[
\begin{split}
 F_\sigma(x)={}&x+.09+L_2+2\lambda-\sigma u\mathcal R
 +(\lambda A-.09)\cos x+(\lambda B-.09)\sin x
 -\mathcal R N_\sigma,\\
 N_\sigma^2={}&(\lambda-\sigma u)^2+(\lambda-v)^2.
\end{split}
\tag{3}
\]

The two complete cases from the geometric cover are

\[
 \sigma=+1,\quad \lambda=.66-.4x,\quad .1\le x\le.42,
\tag{4}
\]

\[
 \sigma=-1,\quad \lambda=.64-.365x,\quad .4\le x\le.6.
\tag{5}
\]

Both multipliers are positive. The original whole-arc derivative
arguments justify the same last M endpoint throughout (4) and (5);
no assertion about a numerically chosen support point is needed.

### 1.1 A common fourth-derivative sign

Write \(\lambda=L-mx\), with \(m=.4\) or \(.365\), and set

\[
 \Delta=m^2(v-\sigma u)^2>0,\qquad
 T=m(\sigma u+v-2\lambda).
\]

Differentiation of the one norm in (3) gives

\[
 N'=T/N,\qquad N''=\Delta/N^3,\qquad
 N^{(4)}=3\Delta(4T^2-\Delta)/N^7.
\tag{6}
\]

The quantities \(2\lambda-\sigma u-v\) and
\(v-\sigma u\) are positive in both cases. Moreover,

\[
 4\lambda-\sigma u-3v
 \ge
 \begin{cases}
 4(.492)-.089293-3(.480179)>0,&\sigma=+1,\\
 4(.421)+.089293-3(.480179)>0,&\sigma=-1.
 \end{cases}
\]

This is exactly the stronger positive comparison
\(2(2\lambda-\sigma u-v)>v-\sigma u\), so
\(4T^2>\Delta\) and \(N^{(4)}>0\).

The fourth derivative of the trigonometric part of (3) is

\[
 (\lambda A-.09+4mB)\cos x
 +(\lambda B-.09-4mA)\sin x.
\tag{7}
\]

Both coefficients are negative throughout both intervals. For the
first, the common bounds \(\lambda\le.62\), \(m\ge.365\),
and (2) give

\[
 \lambda A-.09+4mB
 <(.62)(1.65)-.09-4(.365)(1.597)<0.
\]

The second is negative directly from \(A>0\), \(B<0\),
\(m,\lambda>0\). Since sine and cosine are positive here,
(6)--(7) prove

\[
 \boxed{F_\sigma^{(4)}<0.}
\tag{8}
\]

Thus \(F_\sigma''\) is concave on its entire required interval.
This sign statement controls all interior angles without a partition.

### 1.2 The positive source: decreasing to its last endpoint

The exact second derivative used at the endpoints is

\[
 F''=(-\lambda A+.09-2mB)\cos x
       +(-\lambda B+.09+2mA)\sin x
       -\mathcal R\Delta/N^3.
\tag{9}
\]

Substitution of (2), \(3.14159<\pi<355/113\), and the
alternating sine and cosine bounds gives

\[
 F_+''(.1)>.16,\qquad F_+''(.42)>.16,
 \qquad F_+'(.42)<-.08,\qquad F_+(.42)>.899.
\tag{10}
\]

For these substitutions one may use the positive norm brackets

\[
 .54881673<N_+(.1)<.54881678,\qquad
 .40288043<N_+(.42)<.40288048.
\]

Each follows by squaring in (3), whose coefficients and endpoint
arguments are rational. The trigonometric bounds
\(S_{11}<\sin<S_{13}\) and \(C_{14}<\cos<C_{12}\)
are more than sufficient for (10).

Concavity of \(F_+''\) and its two positive endpoints give
\(F_+''>.16\). Consequently \(F_+'\) is increasing and
is everywhere at most its negative right-end value. Therefore

\[
 F_+(x)\ge F_+(.42)>.899>.8926
 \qquad(.1\le x\le.42).
\tag{11}
\]

### 1.3 The negative source: one strong-convexity estimate

The same comparisons in (9) give

\[
 F_-''(.4)>.6,\qquad F_-''(.6)>.6.
\tag{12}
\]

One fixed interior point suffices for its value and slope:

\[
 F_-(14/25)>.89273,\qquad |F_-'(14/25)|<.0014.
\tag{13}
\]

Suitable positive square brackets, in the order `.4`, `.6`, `14/25`,
are

\[
 \begin{gathered}
 .58345669<N_-(.4)<.58345674,\\
 .51371303<N_-(.6)<.51371308,\\
 .52678261<N_-(14/25)<.52678266.
 \end{gathered}
\]

Together with (2) and the same Taylor inequalities these prove
(12)--(13) by rational substitution. The first derivative formula is

\[
 F'=1-2m+(\lambda B-.09-mA)\cos x
            +(-\lambda A+.09-mB)\sin x-\mathcal R T/N.
\tag{14}
\]

By (8), (12), \(F_-''>3/5\) on the whole interval. Integrate
that lower bound twice from \(14/25\) and complete a square:

\[
 F_-(x)>.89273-\frac{(.0014)^2}{2(3/5)}
 >.89272>.8926\qquad(.4\le x\le.6).
\tag{15}
\]

This removes the delicate second coefficient row as well as the first.

## 2. A common derivative theorem for the three remaining supports

Put

\[
 p=k-q=1.489593,\qquad r=k+q=1.580219,\qquad R=\sqrt Q.
\]

For any \(.8\le L\le.87\), consider

\[
 \mathcal F_L(x)=x+K+(L-.09)\sin x-.09\cos x-R\mathcal N_L(x),
\]

\[
 \mathcal N_L^2=p^2+r^2+L^2+2L(p\sin x-r\cos x),
\tag{16}
\]

where \(K\) is independent of \(x\). We prove
\(\mathcal F_L'>0\) whenever

\[
 1/8\le z:=\tan(x/2)\le5/8.
\tag{17}
\]

This one enlarged interval includes all the required arguments
`.42` through `.93`.

Let \(D=1+z^2\), \(s_0=2z\), \(c_0=1-z^2\), and define
the degree-six polynomial

\[
\begin{split}
 P(L,z)={}&\{D+(L-.09)c_0+.09s_0\}^2
 \{(p^2+r^2+L^2)D+2L(ps_0-rc_0)\}\\
 &-QL^2(pc_0+rs_0)^2D.
\end{split}
\tag{18}
\]

All compared factors are positive in this part of the first quadrant.
Thus squaring the actual derivative comparison, with its signs retained,
shows that \(P(L,z)>0\) implies \(\mathcal F_L'>0\).

At \(L=.87\), Section 4.1 of
`HAND_FOUR_TYPE_SCALAR_REPLACEMENTS.md` supplies a direct proof on
the whole interval (17). Specifically, putting \(y=z-3/8\), its
single exact polynomial expansion gives

\[
 P(.87,z)>.003-.034|y|+14y^2>0
 \qquad(|y|\le1/4).
\tag{19}
\]

The second inequality is completing a square; it holds on the whole
real line. This is the analytic M/M derivative estimate, not its old
Bernstein row.

We extend (19) to every \(L\) in the displayed range at once.
Set \(h=.87-L\), so \(0\le h\le.07\). Expand (18) in this
single parameter:

\[
 P(.87-h,z)=P(.87,z)+hC_1(z)+h^2C_2(z)+h^3C_3(z)+h^4C_4(z).
\tag{20}
\]

Direct multiplication in the explicitly defined (18) gives
the following convenient coefficientwise lower bounds:

\[
\begin{aligned}
 C_1&>9+26z+12z^2+6z^3+77z^4-60z^5+18z^6,\\
 C_2&>-8-11z-26z^3-61z^4-3z^6,\\
 C_3&>-3-7z-9z^2-6z^5-5z^6,\\
 C_4&=(1-z^2)^2(1+z^2)\ge0.
\end{aligned}
\tag{21}
\]

These statements are expansions of the single polynomial (18) in
\(h\); they do not choose multipliers by any angle index. In the
first line, group \(77z^4-60z^5=z^4(77-60z)\).
On \(0\le z\le5/8\), the resulting bound is greater than 9.
In the next two lines, substitution of \(5/8\) in their negative
monomials gives, respectively, lower bounds greater than \(-32\)
and \(-12\). Hence (20) yields

\[
 P(.87-h,z)\ge P(.87,z)+h(9-32h-12h^2)>0.
\tag{22}
\]

The last bracket is positive already at its right endpoint `.07`.
This proves the common monotonicity theorem (16)--(17).

## 3. Application to all three constant-multiplier cases

The actual folded target-M norm is

\[
 N^2=k^2+q^2+2\lambda^2
       +2\lambda\{(k-q)\sin x-(k+q)\cos x\}.
\tag{23}
\]

With \(L=2\lambda\), (16) gives exactly
\(\mathcal N_L=\sqrt2 N\), so \(R\mathcal N_L=\mathcal R N\).
Thus the actual scalar, including the correct constant, is

\[
 F=x+K+(2\lambda-.09)\sin x-.09\cos x-\mathcal R N.
\tag{24}
\]

For row 3 of the original cover, \(\lambda=.43\),
\(.42\le x\le.61\), and

\[
 K=.09+c_M+k+\lambda-\lambda a_0,
 \quad c_M=\pi/4+2.143075,\quad a_0=\mathcal R-1.
\tag{25}
\]

For rows 4 and 5, respectively,
\(\lambda=.42\), \(.6\le x\le.7\), and
\(\lambda=.4\), \(.7\le x\le.93\). In both cases

\[
 K=.09+c_M+k+2\lambda+u\mathcal R
       -\mathcal R\sqrt{(u+\lambda)^2+(v-\lambda)^2}.
\tag{26}
\]

Their doubled multipliers are `.86`, `.84`, and `.8`, all in the
single range covered by (22). They are consequently increasing
over their complete required intervals.

Only each first endpoint remains. The same square and Taylor bounds
as above give the strict comparisons

\[
 F_{.43}(.42)>.8951,\qquad
 F_{.42}(.6)>.8932,\qquad
 F_{.4}(.7)>.8984.
\tag{27}
\]

For explicit reproduction of these three scalar comparisons, the
target norm (23) is contained, respectively, in

\[
 (1.41748860,1.41748865),\quad
 (1.52373418,1.52373423),\quad
 (1.57441825,1.57441830).
\]

The source norms appearing in (26) are contained, respectively, in
\((.51283608,.51283613)\) and
\((.49581880,.49581885)\). All are positive square comparisons
with the fixed rational arguments and the alternating sine/cosine
brackets. Equations (25)--(27) use the actual lower bound for \(\pi\)
and both endpoints for \(\mathcal R\), so no floating approximation
of either constant is a premise.

Monotonicity and (27) prove all three supports strictly greater
than `.8926` throughout their domains.

## 4. Coverage and dependency boundary

Equations (11), (15), and (27) replace all five former polynomial
rows, including the second row that formerly required degree
elevation. The source/target support choices and all angle endpoints
agree with the original cover. The other sign and axis branches
already use endpoint calculus or the exact contact deformation of
Section 5 of the original manuscript. Reflection and reversal
supply the target axes and preserve their ties.

Therefore the strengthened complete M/H pair estimate `.8926`
needs no coefficient table. The proof uses one common geometric norm
curvature identity, one polynomial derivative identity for an entire
multiplier range, and fixed endpoint arithmetic. Independent exact
rational calculations checked the displayed expansions and scalar
comparisons during preparation; they are not proof premises. No
Lean source, compilation, CI, or historical certificate was changed.
