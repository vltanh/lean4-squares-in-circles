# Scalar envelopes for the TD2 whole-angle concentration

## 1. Definitions and purpose

Use \(Q,R,h,c_0\), the admissible weights, and the scalar
functions of
HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md. In particular,

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \qquad \phi(t)=\cos t+\sin t,
\]

and, for \(0<p\le q\), \(p/q\ge1/2\),

\[
 \begin{split}
 N(s)&=\sqrt{p^2+q^2+2pq\sin s},\\
 U_{p,q}(t)&=p\{\phi(t)-1\}-R\{N(t)-N(0)\},\\
 V_{p,q}(t)&=q(\cos t-1)-R\{N(-t)-N(0)\},\\
 M_{p,q}(z)&=p\{\phi(h-z)-1\}+q(\cos h-1)
                                  -R\{N(-z)-N(0)\}.
 \end{split}
\tag{1}
\]

All variables in (1) lie in \([0,h]\). The concentration note
proves that \(U\) and \(V\) are concave on that whole interval.

This note supplies four universal comparisons:

\[
 \begin{gathered}
 U_{p,q}(t)\ge-\frac{109}{200}qt,\qquad
 V_{p,q}(h)>\frac{87}{100}p,\\
 q/p\le3/2\ \Longrightarrow\ M_{p,q}(z)\ge V_{p,q}(z),\\
 p/q\ge2/3\ \Longrightarrow\ V_{p,q}'(t)>\frac23q.
 \end{gathered}
\tag{2}
\]

It also proves coordinatewise monotonicity of \(V_{p,q}(z)\)
on the low-angle interval \(0<z\le1/6\). These comparisons reduce
the concentration theorem to four scalar functions for the
low-angle coefficient family, and two single-negative functions
for the balanced high-angle family. The particular weight
polynomials and their final positive certificates are separate
from the universal lemmas here.

All decimal constants below are exact rationals.

## 2. The positive-angle envelope

Concavity and \(U(0)=0\) imply

\[
                         U(t)\ge\frac{t}{h}U(h).
\tag{3}
\]

Write \(r=p/q\in[1/2,1]\), \(S=\sin h\), \(C=\cos h\), and

\[
 f(r)=\frac{U(h)}q
     =r(S+C-1)-R\{\sqrt{1+r^2+2rS}-\sqrt{1+r^2}\}.
\tag{4}
\]

This function is strictly convex:

\[
 f''(r)=R\left\{
 \frac1{(1+r^2)^{3/2}}
 -\frac{C^2}{(1+r^2+2rS)^{3/2}}\right\}>0.
\tag{5}
\]

At the single rational pivot \(r_0=97/100\), direct alternating
Taylor and square bounds give

\[
                      f(r_0)>-.3811,\qquad
                         -.0015<f'(r_0)<0.
\tag{6}
\]

For explicit reproduction of (6), use

\[
 \begin{gathered}
 1.978787<R<1.978788,\\
 1.3931618<\sqrt{1+r_0^2}<1.3931620,\\
 1.7862480<\sqrt{1+r_0^2+2r_0S}<1.7862482,
 \end{gathered}
\tag{7}
\]

together with

\[
 \begin{split}
 S_7&=h-h^3/6+h^5/120-h^7/5040<S\\
    &<S_9=S_7+h^9/362880,\\
 C_6&=1-h^2/2+h^4/24-h^6/720<C\\
    &<C_8=C_6+h^8/40320.
 \end{split}
\tag{8}
\]

For example the lower bound for \(f(r_0)\) is

\[
 r_0(S_7+C_6-1)
       -1.978788(1.7862482-1.3931618)>-.3811.
\]

For its derivative bound, put

\[
 g_-=\frac{r_0+S_7}{1.7862482}
             -\frac{r_0}{1.3931618}>0,\qquad
 g_+=\frac{r_0+S_9}{1.7862480}
             -\frac{r_0}{1.3931620}.
\]

The two rational comparisons are

\[
 S_7+C_6-1-1.978788g_+>-.0015,\qquad
 S_9+C_8-1-1.978787g_-<0.
\tag{9}
\]

The tangent to the convex function (4) is a lower bound.
Since its slope in (6) is negative, that tangent is minimized
on \([1/2,1]\) at \(r=1\). Thus

\[
 f(r)>-.3811-.03(.0015)=-.381145
              >-.3815=-\frac{109}{200}h.
\tag{10}
\]

The last reserve is \(71/200000\). Equations (3)--(10) prove
the first inequality in (2), with equality at \(t=0\) permitted.

## 3. The large negative endpoint

Put \(u=q/p\in[1,2]\). Then

\[
 \frac{V_{p,q}(h)}p
 =u(C-1)+R\{\sqrt{1+u^2}-\sqrt{1+u^2-2uS}\}.
\tag{11}
\]

This is strictly concave in \(u\). Its second derivative is

\[
 R\left\{\frac1{(1+u^2)^{3/2}}
       -\frac{C^2}{(1+u^2-2uS)^{3/2}}\right\}<0.
\tag{12}
\]

Indeed \(2u/(1+u^2)\ge4/5\) and \(S>5/8\), so
\(1+u^2-2uS<(1+u^2)/2\), while \(C^2>1/2\).
These imply the strict sign in (12).

Only the two intrinsic endpoints \(u=1,2\) remain. The coarse
rational enclosures

\[
 \begin{gathered}
 S>.6442,\quad C>.7648,\quad R>1.9787,\\
 \sqrt2>1.4142,\quad \sqrt5>2.2360,\\
 \sqrt{2-2S}<.8436,\quad
 \sqrt{5-4S}<1.5567
 \end{gathered}
\tag{13}
\]

give

\[
 \begin{split}
 C-1+R(\sqrt2-\sqrt{2-2S})-.87
    &>\frac{1192311}{50000000}>0,\\
 2(C-1)+R(\sqrt5-\sqrt{5-4S})-.87
    &>\frac{373091}{100000000}>0.
 \end{split}
\tag{14}
\]

This proves \(V_{p,q}(h)>.87p\).

One related bound will be useful for the H pair:

\[
                  \frac12\le k\le\frac{17}{20}
                  \quad\Longrightarrow\quad V_{k,1}(h)<\frac45.
\tag{15}
\]

The function on the left is increasing in \(k\). To check this,
differentiate its two square roots. If \(k-S\le0\) the sign is
immediate; otherwise squaring the positive fractions leaves
\(S\{2k-(1+k^2)S\}>0\). Here
\(2k/(1+k^2)\ge4/5>S\).
At \(k=17/20\), use

\[
 \sqrt{1+k^2}<1.3125,\qquad
 \sqrt{1+k^2-2kS}>.7919.
\]

Then the right side of (15) minus its upper bound is

\[
 .8-\{.7649-1+1.9788(1.3125-.7919)\}
                        =\frac{61709}{12500000}>0.
\tag{16}
\]

## 4. Same-block saturation and balanced coefficients

The same-block correction has the exact form

\[
 M_{p,q}(z)-V_{p,q}(z)
       =p\{\phi(h-z)-1\}-q(\cos z-\cos h).
\tag{17}
\]

For \(q/p\le3/2\), put \(a=h-z\). The right side divided by
\(p\) is at least

\[
 \left(1-\frac32\cos h\right)(\cos a-1)
       +\left(1-\frac32\sin h\right)\sin a\ge0.
\tag{18}
\]

Both terms are nonnegative because \(\cos h>2/3\),
\(\sin h<2/3\), and \(0\le a\le h\). This proves the
third inequality in (2).

Now suppose \(p/q\ge2/3\). Since \(V\) is concave,
\(V'(t)\ge V'(h)\). Put \(r=p/q\). Then

\[
 \frac{V'(h)}q
       =-S+\frac{RrC}{\sqrt{1+r^2-2rS}}.
\tag{19}
\]

The fraction in (19) is increasing in \(r\in[2/3,1]\):
after a positive factor is removed, its derivative is \(1-rS>0\).
At \(r=2/3\), (13) and

\[
       \sqrt{1+\frac49-\frac43S}<.7652
\]

give the explicit reserve

\[
 -.6443+\frac{1.9787(2/3)(.7648)}{.7652}-\frac23
                       =\frac{143037}{19130000}>0.
\tag{20}
\]

Thus \(V'(t)>(2/3)q\), the fourth inequality in (2).

Consider now the three coefficient pairs of the concentration
note. Suppose all obey

\[
 p_i/q_i\ge2/3,\qquad
 q_{\min}:=\min_iq_i\ge1,\qquad
 q_{\max}:=\max_iq_i\le\frac65q_{\min}.
\tag{21}
\]

Every same-block case is at least the corresponding single case
by (17)--(18). For \(a=h-z\), equations (2) and (20) give

\[
 \begin{split}
 \min_i U_i(a)&\ge-\frac{109}{200}q_{\max}a,\\
 \min_j V_j(h)&\ge\min_jV_j(z)+\frac23q_{\min}a.
 \end{split}
\tag{22}
\]

The D positive alternative is also at least the first lower
bound in (22), since \(c_0-1/2<.4<(109/200)q_{\max}\).
Their sum is at least

\[
          \min_jV_j(z)
             +\frac{19}{1500}q_{\min}(h-z).
\tag{23}
\]

Therefore the entire endpoint envelope (9) of the concentration
note reduces exactly to

\[
                              {\cal E}(z)=\min_iV_i(z)
\tag{24}
\]

under (21). In the important case \(l=1\), the G and H pairs
coincide, leaving only \(V_H(z)\) and \(V_B(z)\).

## 5. Coordinatewise monotonicity on the low-angle interval

Allow here \(p,q>0\) with \(1/2\le p/q\le2\), and
\(0<z\le1/6\). Define \(V\) by the same formula (1), even
when \(p>q\). Then

\[
                  \partial_p V_{p,q}(z)>0,\qquad
                  \partial_q V_{p,q}(z)>\frac z{40}>0.
\tag{25}
\]

Put \(A=p^2+q^2\) and \(s=\sin z\). For the first derivative,

\[
 \frac1R\partial_p V
       =\frac p{\sqrt A}
          -\frac{p-qs}{\sqrt{A-2pqs}}.
\]

Both numerators are positive. Squaring reduces the sign to

\[
                    q^2s(2pq-As)>0,
\tag{26}
\]

which follows from \(2pq/A\ge4/5>s\).

For the second derivative define

\[
 g(s)=\frac q{\sqrt A}
             -\frac{q-ps}{\sqrt{A-2pqs}}.
\]

Direct differentiation gives

\[
 g'(s)=\frac{p^2(p-qs)}{(A-2pqs)^{3/2}}
       \ge\frac{2p^3}{3A^{3/2}}
       \ge\frac{2}{15\sqrt5}.
\tag{27}
\]

Here \(s\le1/6\) and \(q/p\le2\), while \(p/q\ge1/2\).
Since \(g(0)=0\),

\[
 \begin{split}
 \partial_qV
 &\ge\cos z-1+\frac{2R}{15\sqrt5}\sin z\\
 &\ge z\left\{
       \frac{2R}{15\sqrt5}\frac{215}{216}-\frac1{12}\right\}
 >\frac z{40}.
 \end{split}
\tag{28}
\]

The last inequality already follows from \(R>197/100\) and
\(\sqrt5<9/4\). Its rational reserve is

\[
 \frac{2(197/100)}{15(9/4)}\frac{215}{216}
                 -\frac1{12}-\frac1{40}
                    =\frac{1147}{145800}>0.
\tag{29}
\]

At \(z=0\), all \(V\) values are zero, so non-strict
coordinatewise comparison remains valid there.

## 6. Four scalar obligations for a low-angle family

Suppose \(0\le z\le1/6\), the concentration conditions hold,
and in addition

\[
              \frac23\le k\le\frac{17}{20},\qquad
                  1\le l\le m\le\frac32l.
\tag{30}
\]

The coordinatewise paths from \((k,1)\) to \((k,l)\) and
to \((l,m)\) stay within \(1/2\le p/q\le2\):
for the latter path first increase \(p\) from \(k\) to \(l\)
at \(q=1\), then increase \(q\) from \(1\) to \(m\).
Use \(l\le2k\le17/10<2\) and \(m/l\le3/2\).
Thus (25) gives

\[
                           V_G(z),V_B(z)\ge V_H(z).
\tag{31}
\]

The H and B same-block cases are at least their corresponding
single cases by (18), because their coefficient ratios are
at most \(3/2\). Also

\[
                         V_B(h)>.87l\ge.87>V_H(h)
\tag{32}
\]

by (14)--(16). Finally the largest positive coefficient among
the three pairs is \(m\), and the D alternative satisfies

\[
 -(c_0-\tfrac12)(h-z)\ge-\frac{109}{200}m(h-z).
\]

Consequently the concentration lower bound is positive if the
following four scalar functions are positive on the whole
low-angle interval:

\[
 \begin{split}
 &B(z)+V_H(z),\\
 &B(z)+M_G(z),\\
 &B(z)-\frac{109}{200}m(h-z)+V_G(h),\\
 &B(z)-\frac{109}{200}m(h-z)+V_H(h).
 \end{split}
\tag{33}
\]

These are continuous coefficient envelopes for the intrinsic
endpoint theorem. No enumeration of arbitrary angular samples
or additional geometric frame assumption is needed.
