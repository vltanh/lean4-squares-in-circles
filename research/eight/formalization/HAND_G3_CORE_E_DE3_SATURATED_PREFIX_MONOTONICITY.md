# Prefix monotonicity for the saturated core-E DE3 multiplier

All decimals in this note are exact rationals. Put

\[
 Q=9789/2500,\quad R=\sqrt Q,\quad \kappa=49/50,
 \quad m=1.077372,\quad d=2/5,\quad A=13/12,
 \quad c(p)=3/5+dp.
\tag{1}
\]

For positive a and c, define

\[
 N(a,c,p)=\sqrt{a^2+c^2-2ac\sin p}.
\tag{2}
\]

The two concentrated core-E tail expressions are

\[
\begin{split}
 L_B(p,t;e)={}&\pi-p-t+\frac32\kappa+2c+e
 +\frac e2\cos t+eA\sin t+\kappa\cos p\\
 &-R\{N(\kappa,c,p)+\sqrt{e^2+c^2}\},\\[2mm]
 L_W(p,t;e)={}&\pi-p-t+\frac52\kappa+c+e
 +\frac e2\cos t+eA\sin t+c\cos p\\
 &-R\{\sqrt{\kappa^2+c^2}+N(e,c,p)\}.
\end{split}
\tag{3}
\]

Here c always means c(p). This note proves the stronger strip
statement

\[
 \partial_p L_B(p,t;e)>0,\qquad
 \partial_p L_W(p,t;e)>0,
 \qquad 0\le p\le7/10,\quad m\le e\le1.41.
\tag{4}
\]

The parameter t is fixed in these derivatives. In particular, if
`1/5<=t<=7/10`, `0<=p<=7/10-t`, and `e=m sec t`, both expressions
are bounded below by their value at p=0. That value is the scalar
already proved strictly larger than `16761/4520` in Section 4 of
`HAND_G3_CORE_E_DE3_BASE_SCALAR.md`.

The proof uses two explicitly defined polynomials and one
coefficient-sum bound over the whole interval for each. No
subdivision into angle samples is used.

## 1. Exact derivatives and monotonicity in the multiplier

Write `s=sin p` and `C=cos p`. Differentiating (3), including the
dependence `c'=d`, gives

\[
\begin{split}
 F_B:=\partial_pL_B
 ={}&-\frac15-\kappa s
 +R\left\{
 \frac{\kappa cC+d\kappa s-dc}{N(\kappa,c,p)}
 -\frac{dc}{\sqrt{e^2+c^2}}\right\},\\[1mm]
 F_W:=\partial_pL_W
 ={}&-\frac35+dC-cs
 +R\left\{
 \frac{ecC+des-dc}{N(e,c,p)}
 -\frac{dc}{\sqrt{\kappa^2+c^2}}\right\}.
\end{split}
\tag{5}
\]

The first expression increases with e. For the second, the only
e-dependent ratio has derivative

\[
 \partial_e\left(
 \frac{e(cC+ds)-dc}{N(e,c,p)}\right)
 =\frac{cC\{c^2+e(dC-cs)\}}{N(e,c,p)^3}.
\tag{6}
\]

Throughout the stated strip,

\[
 3/5\le c\le22/25,\qquad C>3/4,\qquad 0\le s<13/20.
\tag{7}
\]

Since `3/10-(13/20)c<0`, these bounds imply

\[
\begin{split}
 c^2+e(dC-cs)
 &\ge c^2-\frac{141}{100}
                  \left(\frac{13}{20}c-\frac3{10}\right)\\
 &=c^2-\frac{1833}{2000}c+\frac{423}{1000}
 \ge\frac{2331}{10000}>0.
\end{split}
\tag{8}
\]

The last quadratic increases for `c>=3/5`; its value there is the
printed lower bound. Thus both derivatives in (5) increase with
e. It suffices to prove them positive at e=m.

## 2. Rational trigonometric and norm bounds

Define

\[
\begin{split}
 S(p)&=p-p^3/6+p^5/120-p^7/5040,\\
 U(p)&=p-p^3/6+p^5/120,\\
 C_-(p)&=1-p^2/2+p^4/24-p^6/720.
\end{split}
\tag{9}
\]

The alternating Taylor bounds on `[0,7/10]` give

\[
 0\le S\le\sin p\le U<13/20,
 \qquad 3/4<C_-\le\cos p.
\tag{10}
\]

For example U increases and C_- decreases on this interval, and

\[
 \frac{13}{20}-U(7/10)=\frac{69193}{12000000},
 \qquad
 C_-(7/10)-\frac34=\frac{10685351}{720000000}.
\tag{11}
\]

We also use

\[
 r_-=1.978<R<1.979=r_+,
\tag{12}
\]

whose squared reserves are respectively `779/250000` and
`841/1000000`.

For `b>0`, the function

\[
 h_b(c)=\frac{c}{\sqrt{b^2+c^2}}
\]

is increasing and concave, since

\[
 h_b'(c)=\frac{b^2}{(b^2+c^2)^{3/2}},\qquad
 h_b''(c)=-\frac{3b^2c}{(b^2+c^2)^{5/2}}<0.
\tag{13}
\]

Set

\[
 \rho_m=1.233178,
 \qquad \rho_\kappa=1.149086,
 \qquad
 T_b(p)=\frac{3/5}{\rho_b}+\frac{db^2}{\rho_b^3}p
 \quad(b=m,\kappa).
\tag{14}
\]

These are upper bounds for `h_b(c(p))`: the exact tangent at
`c=3/5` is an upper bound by (13), and replacing its positive root
denominators by the smaller numbers rho_b only increases it. The
exact squared reserves are

\[
 m^2+9/25-\rho_m^2=\frac{24467}{10000000000},\qquad
 \kappa^2+9/25-\rho_\kappa^2
                       =\frac{341151}{250000000000}.
\tag{15}
\]

For `a=κ,m`, define the polynomials

\[
\begin{split}
 B_a(p)&=ac(p)C_-(p)+daS(p)-dc(p),\\
 X_a(p)&=a^2+c(p)^2-2ac(p)S(p),\\
 P_\kappa(p)&=1.1491-0.3082p-0.2931p^2,\\
 P_m(p)&=1.2332-0.3332p-0.3167p^2,\\
 D_a(p)&=X_a(p)+P_a(p)^2.
\end{split}
\tag{16}
\]

Here `B_a>=c(3a/4-d)>0`, and
`X_a>=N(a,c,p)^2>0`. Both P polynomials decrease, and their
values at `7/10` are respectively `0.789741` and `0.844777`, so
their values and D_a are positive throughout the interval.

For any positive N and P,

\[
 \frac1N\ge\frac{2P}{N^2+P^2};
\tag{17}
\]

after multiplication by the positive denominators this is simply
`(N-P)^2>=0`. Consequently (9), (10), and (16) imply

\[
 \frac{ac\cos p+da\sin p-dc}{N(a,c,p)}
 \ge\frac{2B_a(p)P_a(p)}{D_a(p)}.
\tag{18}
\]

Thus the chosen P polynomials require no approximation claim or
error estimate.

## 3. Two whole-interval polynomial inequalities

Using only the polynomials and rational constants already
displayed, define

\[
\begin{split}
 H_B(p)={}&
 \{-1/5-\kappa U(p)-r_+dT_m(p)\}D_\kappa(p)
 +2r_-B_\kappa(p)P_\kappa(p),\\
 H_W(p)={}&
 \{-3/5+dC_-(p)-c(p)U(p)-r_+dT_\kappa(p)\}D_m(p)
 +2r_-B_m(p)P_m(p).
\end{split}
\tag{19}
\]

These have degrees 13 and 14, respectively. The signs already
proved in Section 2 justify using the lower R bound on the
positive ratios and the upper R bound on the negative tangent
terms. Equation (5) at e=m therefore gives

\[
 F_B\ge\frac{H_B(p)}{D_\kappa(p)},\qquad
 F_W\ge\frac{H_W(p)}{D_m(p)}.
\tag{20}
\]

Here is a direct coefficient certificate for the entire interval.
For either polynomial H, write

\[
 H(7/20+x)=\sum_{j=0}^{\deg H}h_jx^j,
 \qquad
 h_j=\sum_{i=j}^{\deg H}[p^i]H\binom ij(7/20)^{i-j}.
\tag{21}
\]

Expansion of the factored rational expressions (14), (16), and
(19) gives

\[
\begin{array}{c|c|c}
 H&\deg H&h_0-\displaystyle\sum_{j\ge1}|h_j|(7/20)^j\\ \hline
 H_B&13&>317/10000\\
 H_W&14&>22/2500.
\end{array}
\tag{22}
\]

For clarity, the two unrounded rational expressions in the last
column lie respectively in
`(0.03170316,0.03170318)` and
`(0.00888129,0.00888131)`. Formula (21) and the explicit
definitions make (22) fixed rational arithmetic inequalities;
they do not quantify over samples of p. Since `|x|<=7/20`, the
triangle inequality bounds each H below by its corresponding
coefficient expression in (22). Both are strictly positive on
the whole interval. Equations (20), (8), and (6) prove (4).

## 4. Consequence for the negative-DE3 tail

Let `1/5<=t<=7/10` and set `e=m sec t`. The relevant multiplier
indeed belongs to the strip in (4): `e>=m`, and

\[
 \frac{141}{100}C_-(7/10)-m
                  =\frac{25283497}{24000000000}>0
\tag{23}
\]

gives `e<1.41`. For every `p>=0` with `p+t<=7/10`, (4) yields

\[
\begin{split}
 L_B(p,t;e)&\ge L_B(0,t;e)=L_0(t),\\
 L_W(p,t;e)&\ge L_W(0,t;e)=L_0(t),
\end{split}
\tag{24}
\]

with strict inequalities when p>0. Explicitly, at p=0 the common
value is

\[
 L_0(t)=\pi-t+\frac52\kappa+\frac65
 +e\{1+\tfrac12\cos t+A\sin t\}
 -R\{\sqrt{\kappa^2+9/25}+\sqrt{e^2+9/25}\}.
\tag{25}
\]

Section 4 of `HAND_G3_CORE_E_DE3_BASE_SCALAR.md` proves this
strictly larger than `16761/4520` throughout the present interval.
Thus both concentrated tail placements are excluded on the whole
negative-error triangle with `t>=1/5`.
