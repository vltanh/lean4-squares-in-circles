# A whole-domain tilt bound for a negative left singleton

**Status: complete hand domain theorem; author, root and separate independent full saved-source, direct-prerequisite and exact-polynomial audits passed. This is a domain reduction, not an exclusion of the whole left-singleton family.**

Work throughout

\[
79/40\le R\le\sqrt{1105}/16,\qquad
q=R^2,\qquad q_0=6241/1600.
\]

Let A have one physical circle corner, positive total circle load and true positive pair-degree two, with actual neighbors H and K. Assume K physically touches the circle, HA is an H-owned singleton, and \(c_H\cdot z_A<0\). Suppose the actual A-to-K normal is the left A side axis and the physical AK intersection is a singleton. Retain the actual H side offset, all original application means, every physical circle mask, every individual circle weight, all other H/K forces and all completion squares.

**Theorem.** In the complete large-coordinate frame below, the actual tilted K has its unique physical circle corner at \(T+e\), and its unchanged tilt satisfies

\[
                         0<c<\tfrac12<s<1.
\tag{1}
\]

In particular this corner has positive ordinary first coordinate. No force or moment equation at K is used. The result therefore applies both when K is the true degree-two middle body of the H4/intact-petal ABC component and when K is the true degree-three middle body of the H5 diamond.

## 1. All physical corners and the original pressure

Section 1 of NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md is degree independent at K. Together with NEGATIVE_H_OWNED_LEFT_AXIS_SMALL_COORDINATE_EXCLUSION.md it supplies the remaining frame

\[
\begin{gathered}
z_A=(a,b),\quad a>b>3/5,\quad a^2+b^2=q,\quad
3/2<a<2,\\
P=(a-1,b-1),\quad x=a-1\in(1/2,1),\\
T=(x,\beta),\quad \beta=\kappa b,\quad
\delta=1-\kappa\in[0,1/a),\quad 0<\beta\le b,\\
n=(u,v)=\frac{(1-\delta a,1-\delta b)}
 {\sqrt{(1-\delta a)^2+(1-\delta b)^2}},\quad0<u\le v,\\
c_H=P-n/2-\eta Jn,\qquad -1/2\le\eta\le1/2.
\end{gathered}
\tag{2}
\]

The strict selected singleton has T in the relative interior of A's side, so its actual K support is a vertex with two strictly tilted inward edges. Retaining the closed endpoint \(\beta=b\) only enlarges the estimates. Write the original K as

\[
K=T+[0,1]e+[0,1]f,\qquad
e=(-c,s),\quad f=(-s,-c),\quad c,s>0,\quad c^2+s^2=1.
\tag{3}
\]

The orientation-uniform physical right-support lemma in Section 1 of NEGATIVE_H_OWNED_LEFT_AXIS_SMALL_COORDINATE_EXCLUSION.md gives

\[
\beta\ge\sqrt{q-x^2}-1>1/2.
\tag{4}
\]

Indeed \(q-x^2>q_0-1>9/4\). All four K corners are now accounted for without proper concurrence at K:

\[
\begin{aligned}
|T|^2&=x^2+\beta^2<q,\\
|T+f|^2-|T|^2
 &=|T+e+f|^2-|T+e|^2\\
 &=1-2(xs+\beta c)<1-(s+c)<0.
\end{aligned}
\tag{5}
\]

Since K physically reaches the circle and all its corners are contained in it, its unique physical circle corner must be

\[
z_K=T+e=(x-c,\beta+s),\qquad
(x-c)^2+(\beta+s)^2=q.
\tag{6}
\]

The exact circle identity can also be written

\[
\beta^2+2\beta s-b^2=2x(1+c).
\tag{7}
\]

The original H side offset in (2) gives

\[
c_H\cdot z_A\ge q-a-b-
 \frac{(a-b)u+(a+b)v}{2}.
\tag{8}
\]

The rest of the proof shows this lower bound is strictly positive whenever \(c\ge1/2\).

## 2. A complete rectangular comparison domain

Suppose \(c\ge1/2\). By \(\beta\le b\), (7) gives

\[
b\ge x\frac{1+c}{s}\ge\sqrt3\,x.
\]

Hence \(q\ge a^2+3(a-1)^2\). The latter polynomial is increasing for \(a\ge3/2\), and its value at \(17/10\) is \(109/25>1105/256\). Thus the entire actual domain lies in

\[
3/2\le a\le17/10,\qquad q_0\le q\le1105/256,
\qquad b=\sqrt{q-a^2}>1.
\tag{9}
\]

The last squared reserve is \(q_0-(17/10)^2-1=17/1600\).

For fixed q and x, the circle expression

\[
\beta(c)=\sqrt{q-(x-c)^2}-\sqrt{1-c^2}
\]

strictly increases on \([1/2,1)\). Its derivative is
\(c/s+(x-c)/\sqrt{q-(x-c)^2}\). When \(x\ge c\) it is positive immediately; when \(x<c\), the second denominator exceeds s and \(c-x<c\), so it is still positive. Consequently

\[
\beta\ge\sqrt{q-(a-3/2)^2}-\sqrt3/2.
\tag{10}
\]

Put

\[
\lambda=\frac{707107}{10^6}>\frac1{\sqrt2},\qquad
h=q-q_0,\qquad t=a-\frac{13}{8},
\]

and define the following two rational polynomials on the full rectangle (9):

\[
\begin{aligned}
\beta_L&=\frac{1108974}{10^6}+\frac6{25}h
             -\frac{51}{200}(a-3/2)^2,\\
D&=q-a^2-\frac{81}{64},\\
b_L&=\frac98+\frac49D-\frac18D^2.
\end{aligned}
\tag{11}
\]

They satisfy \(\beta>\beta_L>1\) and \(b\ge b_L\).

Here are exact justifications on the entire rectangle. Since \(\sqrt q<25/12\), integrating the derivative of \(\sqrt q\) from \(q_0\) gives
\(\sqrt q\ge79/40+(6/25)h\). Also
\(\sqrt{q-(a-3/2)^2}>49/25\), so rationalizing its difference from \(\sqrt q\) gives

\[
\sqrt{q-(a-3/2)^2}
>\sqrt q-\frac{200}{787}(a-3/2)^2
\ge\sqrt q-\frac{51}{200}(a-3/2)^2.
\]

The last coefficient margin is \(137/157400>0\). Use
\(\sqrt3/2<866026/10^6\), whose squared margin is \(258169/(25\cdot10^{10})>0\), to obtain the first bound in (11). Its minimum lower estimate is \(1108974/10^6-51/5000>1\).

For the other bound, apply Taylor's formula with integral remainder to \(\sqrt y\), between \(y=81/64\) and \(y=b^2\). Every intermediate square root is at least one by (9), so the second derivative is at least \(-1/4\). This gives precisely \(b\ge b_L\). Finally \(\lambda^2-1/2=309449/10^{12}>0\).

## 3. One exact polynomial proves positive pressure on the whole domain

Let \(S=a+b\), and set

\[
k=\frac{\delta(a-b)}{2-\delta S}\ge0.
\]

Both terms \(1-\delta a\) and \(1-\delta b\) are positive. Rewriting the actual support term in (8) gives

\[
\frac{(a-b)u+(a+b)v}{2}
 =\frac{a+bk}{\sqrt{2(1+k^2)}}
 \le\lambda(a+bk).
\tag{12}
\]

The positive denominator \(L=2b-(b-\beta)S\) satisfies

\[
L\{q-a-b-\lambda(a+bk)\}
 =N(q,a,b,\beta),
\]

where

\[
N=2b(q-a-b-\lambda a)
 -(b-\beta)\{(a+b)(q-a-b)-\lambda q\}.
\tag{13}
\]

The coefficient of \(\beta\) in N is strictly positive. Indeed \(S\le\sqrt{2q}\), \(S>q/2\) on (9), and \(S(q-S)\) decreases for \(S>q/2\). Therefore

\[
S(q-S)-\lambda q
 \ge q\{\sqrt{2q}-2-\lambda\}>0,
\tag{14}
\]

using \(\sqrt{2q}>279/100\) and \(\lambda<71/100\).

After replacing \(\beta\) by \(\beta_L\) and using \(b^2=q-a^2\), the expression is linear in b:

\[
N(q,a,b,\beta_L)=A_0b+B_0,
\]

\[
\begin{aligned}
A_0&=q(3+\lambda-a)-2(1+\lambda)a
                      +\beta_L(q-2a),\\
B_0&=-(q-a^2)(q+2-2a)+\beta_Lq(a-1-\lambda).
\end{aligned}
\tag{15}
\]

The coefficient \(A_0\) is positive throughout (9): \(q-2a>0\), \(\beta_L>1\), and its first two terms are at least
\(13q_0/10-17/5+\lambda(q_0-17/5)>0\).
Thus (11), (14) give the completely polynomial lower bound

\[
N(q,a,b,\beta)>\mathcal P(t,h):=A_0b_L+B_0.
\tag{16}
\]

For clarity, the finite coefficient verification of \(\mathcal P>0\) is supplied here. It is one global algebraic inequality, with no subdivision of a pose or angle domain. In the variables from (11), \(|t|\le1/8\), \(0\le h\le2661/6400<1/2\), and write

\[
\mathcal P(t,h)=P_0(t)+hP_1(t)+h^2P_2(t)+h^3P_3(t)+h^4P_4(t).
\]

Expansion of the exact formulas (11), (15) gives the following rational coefficient bounds. The entries after the constant column are upper bounds on the absolute values of the successive coefficients; omitted coefficients are zero.

| Polynomial | Constant coefficient lower bound | Bounds for coefficients of \(t,t^2,t^3,t^4,t^5,t^6\) |
|---|---:|---|
| \(P_1\) | \(114/100\) | \(7/8,10,21/10,17/10,53/100,4/125\) |
| \(P_2\) | \(8/25\) | \(25/8,1,7/8,1/10\) |
| \(P_3\) | \(-5/16\) | \(2/5,1/10\) |
| \(P_4\) | exactly \(-3/100\) | all zero |

Consequently, for every \(|t|\le1/8\),

\[
P_1>4/5,\qquad P_2>-1/10,\qquad P_3>-2/5,
\qquad P_4>-1/20.
\tag{17}
\]

For an independently reproducible check of the only small-reserve term, the exact coefficients of \(P_0\), in increasing degree, are

\[
\begin{split}
(&12937967117325027/6553600000000000000,\quad
-28639916149839/655360000000000,\\
&1175926800066601/294912000000000,\quad
21849422407123/1843200000000,\\
&2055140513471/307200000000,\quad
250561027/768000000,\quad
-1048509/2560000,\quad-51/800).
\end{split}
\tag{18}
\]

These give a constant exceeding \(197/100000\), a linear coefficient of absolute value below \(11/250\), and a quadratic coefficient exceeding \(39/10\). The absolute values of degrees three through seven are respectively below \(12,7,1/3,1/2,1/10\). On \(|t|\le1/8\), their sum after division by \(t^2\) is below \(33/20\). Hence

\[
\begin{aligned}
P_0(t)&>\frac{197}{100000}-\frac{11}{250}|t|+\frac94t^2\\
&\ge\frac{197}{100000}-\frac{(11/250)^2}{9}
 =\frac{7897}{4500000}>0.
\end{aligned}
\tag{19}
\]

Finally the positive h part is bounded below, using (17) and \(0\le h<1/2\), by

\[
h\left\{\frac45-\frac h{10}-\frac{2h^2}{5}-\frac{h^3}{20}\right\}
\ge\frac{103}{160}h\ge0.
\tag{20}
\]

Thus \(\mathcal P>0\), then \(N>0\), and (8), (12), (13) give \(c_H\cdot z_A>0\). This contradicts the original negative pressure and excludes the entire \(c\ge1/2\) domain.

## 4. Exact consequences and retained scope

We have proved (1), in fact \(s>\sqrt3/2\). Since \(x>1/2\), equation (6) gives \((z_K)_x=x-c>0\).

The actual K corner has positive coordinates in its outward corner axes e and \(-f\):

\[
A_K=z_K\cdot e=1-xc+\beta s,
\qquad B_K=-z_K\cdot f=xs+\beta c.
\]

The same original circle identity gives

\[
A_K-a=\frac{b^2-\beta^2}{2}\ge0,
\qquad A_K^2+B_K^2=q,
\qquad 0<B_K\le b<23/16<3/2.
\tag{21}
\]

The strict original side-interior singleton has \(\beta<b\), and then both middle inequalities are strict. None of these conclusions assumes K2, a selected positive circle corner on a physical radial square, a change in the original mean, or a replacement of H's actual side offset. The full left-singleton return and completion problems remain their respective separate obligations; this source adds no roadmap closure claim.
