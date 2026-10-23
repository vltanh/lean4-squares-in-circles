# A common secant gain merges two negative flat-core angles

## 1. Statement and notation

All decimals in this note are exact rational numbers. Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 h=\frac7{10},\qquad K=\frac{13}{12},\qquad .65\le k\le .751.
\tag{1}
\]
For \(0\le x\le h\), define
\[
 F_k(x)=\sec x+K\tan x-R\sqrt{\sec^2x+k^2}
                         -1+R\sqrt{1+k^2}.
\tag{2}
\]
For positive p,q and \(0\le d\le h\), use
\[
 V_{p,q}(d)=q(\cos d-1)
       -R\{\sqrt{p^2+q^2-2pq\sin d}-\sqrt{p^2+q^2}\}.
\tag{3}
\]
The following estimates hold on their full stated domains:
\[
 \begin{split}
 F'_k(x)&>.9,\\
 F'''_k(x)&>1.1,\\
 F''_k(r)+F''_k(s)&<-.008-1.1(h-r-s)
                         &&(r,s\ge0,\ r+s\le h),\\
 \frac{\partial^2}{\partial r^2}V_{k,\sec r}(d)&\le .78d
                         &&(0\le r,d\le h).
 \end{split}
\tag{4}
\]
Consequently, for \(r,s,d\ge0\) and \(r+s+d\le h\), with
\(S=r+s\),
\[
 \begin{split}
 F_k(r)+F_k(s)&\ge F_k(S),\\
 F_k(r)+F_k(s)+V_{k,\sec r}(d)
 &\ge F_k(S)+\min\{V_{k,1}(d),V_{k,\sec S}(d)\}.
 \end{split}
\tag{5}
\]
The same second inequality holds with s in place of r in the
secant. These are continuous allocation lemmas: both negative
angles are allowed to vary over the whole interval \([0,S]\).

We also prove the endpoint principle
\[
 F_k(S)+\min\{V_{k,1}(t-S),V_{k,\sec S}(t-S)\}
 \ge \min\{V_{k,1}(t),F_k(t)\},\qquad 0\le S\le t,
\tag{6}
\]
in either of the following two domains:

* \(.15\le t\le h\), for every k in (1);
* \(0\le t\le .15\), when \(k=.65\).

## 2. Exact derivatives of the common gain

Write \(y=\sin x\), \(p=k^2\), and
\[
 A=1+p-py^2,\qquad
 B=(1+p)(1+y^2)-2py^4,
\]
\[
 C=(1+p)(5+8p)+(1+p)(1-12p)y^2-2py^4+4p^2y^6.
\tag{7}
\]
Direct differentiation gives
\[
 \begin{split}
 F'_k(x)&=\frac{K+y-Ry/\sqrt A}{1-y^2},\\
 F''_k(x)&=\frac{2Ky+1+y^2-RB/A^{3/2}}{(1-y^2)^{3/2}},\\
 F'''_k(x)&=\frac{2K+5y+4Ky^2+y^3-RyC/A^{5/2}}
                         {(1-y^2)^2}.
 \end{split}
\tag{8}
\]
Throughout the domain, \(0\le y<.645\) and
\(R/\sqrt A<1.773\). The latter follows by squaring at
\(k=.65,y=.645\); the positive reserve is
\[
 1.773^2\{1+.65^2(1-.645^2)\}-Q=.0035301419349375.
\tag{9}
\]
The quadratic
\[
 .9y^2-.773y+K-.9
\]
has positive leading coefficient and negative discriminant,
since \(.773^2<4(.9)(K-.9)\). This proves \(F'_k>.9\).

The second derivative increases with k:
\[
 \partial_kF''_k(x)
 =\frac{Rk\cos x\{1+k^2(1+2\sin^2x)\}}
              {(1+k^2\cos^2x)^{5/2}}>0.
\tag{10}
\]
The third derivative also increases with k. On differentiating
(10) with respect to x, its sign, for x>0, is the sign of
\[
 (1+p)(8p-1)-2p(5+2p)y^2-4p^2y^4.
\tag{11}
\]
This decreases with \(y^2\) and increases with p on
\(.4225\le p\le .564001,\ 0\le y^2\le .645^2\).
At the adverse corner its value is exactly
\[
 \frac{77261501555759}{64000000000000}>0.
\tag{12}
\]
At x=0 the third derivative is independent of k. Thus its
lower bound may be proved with \(k=.65\).

## 3. A whole-domain certificate for the third derivative

In this section put \(p=.4225\), \(a=1+p\), and
\(v=(p/a)y^2\). Then \(v<.124\). The binomial series gives
\[
 (1-v)^{-5/2}
 \le 1+\frac52v+\frac{35}{8}v^2+8v^3=:L(v).
\tag{13}
\]
Indeed the coefficient of \(v^3\) is \(105/16\), and the
successive ratios in the remaining tail are at most
\((11/8)(.124)\); the resulting geometric majorant has
coefficient less than 8. Also
\[
 R/a^{5/2}<.819915,
\tag{14}
\]
as follows from \(.819915^2a^5-Q>0\).
The polynomial C in (7) is positive for \(0\le y\le .645\).
It follows from (8), (13), and (14) that
\((1-y^2)^2(F'''_{.65}-1.1)\) is bounded below by the explicitly
defined rational polynomial
\[
 \begin{split}
 P(y)={}&2K-1.1+5y+(4K+2.2)y^2+y^3-1.1y^4\\
        &-.819915\,yC(y)L((p/a)y^2).
 \end{split}
\tag{15}
\]
Here C is evaluated with \(p=.4225\).

For a compact exact coefficient certificate, define
\(P(.4+u)=\sum_{j=0}^{13}a_ju^j\). Expansion of (15) over
the rationals gives
\[
 a_0>.08194,\qquad |a_1|<.50025,\qquad
 a_2-\sum_{j=3}^{13}|a_j|(.4)^{j-2}>2.66.
\tag{16}
\]
These three inequalities specify the entire certificate and
are reproducible from (7), (13), and (15) by polynomial
multiplication. Since \(|u|\le .4\) contains the whole
required y interval, completion of the square yields
\[
 P(y)>.08194-\frac{.50025^2}{4(2.66)}>.0584.
\tag{17}
\]
This proves \(F'''_k>1.1\) for every k in (1).

## 4. A symmetric upper envelope for the second derivative

Define the cubic
\[
 E_2(x)=-.004+1.32(x-.35)-.1(x-.35)^2+1.9(x-.35)^3.
\tag{18}
\]
We prove
\[
                         F''_{.751}(x)<E_2(x)
                         \qquad(0\le x\le h).
\tag{19}
\]
Set \(p=.751^2\), \(a=1+p\), \(q=p/a\). Positive
squaring gives \(R/a^{3/2}>1.01168\), and the positive
binomial series gives
\[
 (1-v)^{-3/2}\ge 1+\frac32v+\frac{15}{8}v^2
                             +\frac{35}{16}v^3=:L_2(v).
\tag{20}
\]
Let
\[
 S(x)=\sum_{j=0}^{7}\frac{(-1)^jx^{2j+1}}{(2j+1)!},\qquad
 C_*(x)=\sum_{j=0}^{8}\frac{(-1)^jx^{2j}}{(2j)!}.
\tag{21}
\]
On \([0,h]\), their errors are less than \(7\cdot10^{-18}\)
and \(3\cdot10^{-19}\), respectively. Define the rational
polynomial
\[
 \begin{split}
 J(x)={}&E_2(x)C_*(x)^3-2KS(x)-1-S(x)^2\\
        &+1.01168\{a(1+S(x)^2)-2pS(x)^4\}
                                      L_2(qS(x)^2).
 \end{split}
\tag{22}
\]
With \(J(.35+u)=\sum_{j=0}^{150}b_ju^j\), exact rational
expansion gives
\[
 \begin{gathered}
 b_0>.006356,\quad |b_1|<.001805,\quad b_2>.23599,\\
 .19703<b_3<.19704,\quad b_4>-.85627,\quad
                         -1.44289<b_5<0,\\
 \sum_{j=6}^{150}|b_j|(.35)^{j-2}<.024264.
 \end{gathered}
\tag{23}
\]
For \(|u|\le .35\), the bracket \(b_3+b_5u^2\) is positive
because \(.19703-1.44289(.35)^2>0\). Therefore
\[
 b_3u+b_5u^3\ge-.19704(.35).
\]
After factoring \(u^2\) out of all terms of degree at least
two, (23) consequently gives the positive quadratic reserve
\[
 .23599-.19704(.35)-.85627(.35)^2-.024264>.03786.
\tag{24}
\]
Hence
\[
 J(x)>.006356-\frac{.001805^2}{4(.03786)}>.006334.
\tag{25}
\]
Replacing the two polynomials in (22) by sine and cosine
changes its value by less than \(10^{-8}\). For example,
on \(|S|\le .646, |C_*|\le1.001\), the sum of the absolute
partial derivatives of the expression in (22), with respect
to S and \(C_*\), is less than 100; the errors after (21)
are much smaller than this stated allowance.
Using (8) and (20), inequality (25) proves (19).

Now \(E_2(x)+E_2(h-x)=-.008-.2(x-.35)^2\). Combining
(10), (17), and (19), for \(r+s\le h\), gives
\[
 \begin{split}
 F''_k(r)+F''_k(s)
 &\le F''_{.751}(r)+F''_{.751}(h-r)-1.1(h-r-s)\\
 &<-.008-1.1(h-r-s).
 \end{split}
\tag{26}
\]
This is the third assertion of (4). The same envelope shows
\(F''_k(x)<0\) on \([0,.15]\): (18) increases there and
\(E_2(.15)=-.2872\).

## 5. The second derivative of a secant-weighted negative block

Temporarily let \(1\le q\le1.308\), \(u=\sin d\), and
\(N=\sqrt{k^2+q^2-2kqu}\), \(N_0=\sqrt{k^2+q^2}\).
Differentiating (3) in q gives
\[
 V_{qq}=-Rk^2\left\{\frac{1-u^2}{N^3}-\frac1{N_0^3}\right\}
                                                        \le0.
\tag{27}
\]
Indeed \(u\le .645<2kq/(k^2+q^2)\) throughout this rectangle;
thus \(N^2/N_0^2\le1-u^2\), which proves the sign.

Next,
\[
 \frac{d}{dd}V_q
 =-\sin d+\frac{Rk^2\cos d(k-q\sin d)}{N^3}.
\tag{28}
\]
For \(u\ge k/q\), this is nonpositive. On the remaining
interval put \(\rho=k/q\). The numerator controlling the
derivative of \(\cos d(k-q\sin d)/N^3\), after its positive
scale is removed, is exactly
\[
 (2\rho^2-1)+(u-\rho)u(\rho^2+2-\rho u)-\rho^2u^2
                                                  \le .129.
\tag{29}
\]
Here \(\rho\le .751\), \(u\le\rho\), and
\(N^2/q^2\ge1-u^2\). Consequently the derivative of (28)
is at most
\[
 -.764+\frac{R(.751)^2(.129)}{(1-.645^2)^{5/2}}<0.
\tag{30}
\]
The last comparison follows by positive squaring. Since
\(V_q(0)=0\), equations (28)--(30) imply
\[
 V_q(d)\le\frac{Rk^3}{(k^2+q^2)^{3/2}}d.
\tag{31}
\]

For \(q=\sec r<1.308\), we have
\(q'=q\tan r\), \(q''=q(2q^2-1)\). Equations (27) and
(31) give
\[
 \frac{d^2}{dr^2}V_{k,\sec r}(d)
 \le \frac{Rk^3q(2q^2-1)}{(k^2+q^2)^{3/2}}d<.78d.
\tag{32}
\]
The coefficient increases with k and q. For q, its derivative
has positive numerator \(2q^2+(6q^2-1)k^2\). The final bound
is the positive-square comparison at \(k=.751,q=1.308\).

At fixed \(S,d\) with \(S+d\le h\), the second derivative of
\[
 r\longmapsto F_k(r)+F_k(S-r)+V_{k,\sec r}(d)
\]
is, by (26) and (32), less than
\[
 -.008-1.1(h-S)+.78d\le-.008-.32d<0.
\tag{33}
\]
Its minimum is therefore at r=0 or r=S. This proves the
second inequality of (5). Omitting V gives the first.

## 6. Removing the common negative total

For the secant term in (6), put \(x=\tan S\). Up to a
constant independent of x, the exact expression
\(F_k(S)+V_{k,\sec S}(t-S)\) is
\[
 (K+\sin t)x
       -R\sqrt{(x+k\cos t)^2+(1-k\sin t)^2}.
\tag{34}
\]
This is strictly concave in x, since \(1-k\sin t>0\).
Its endpoint values are \(V_{k,1}(t)\) and \(F_k(t)\).

For the unaffected term put
\(f(S)=F_k(S)+V_{k,1}(t-S)\). Section 4 of
[the negative-A concentration theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
proves, on the full signed norm interval, that
\(C=-RN''\) is increasing and concave and \(C'(0)>1/3\).
Therefore
\[
 V'''_{k,1}(d)=\sin d-C'(-d)<.645-1/3<.312,
 \qquad f'''(S)>.788.
\tag{35}
\]
For \(t\ge .15\), the endpoint derivative is negative:
\[
 f'(t)=F'_k(t)-\frac{Rk}{\sqrt{1+k^2}}<1.064-1.078<0.
\tag{36}
\]
For completeness, \(F'_k\) increases with k and is convex
in its angle by (17). Thus its maximum on \([.15,h]\) is
bounded by the two endpoints at \(k=.751\):
\[
 F'_{.751}(.15)<1.03,\qquad F'_{.751}(h)<1.064.
\tag{37}
\]
Use \(1.978787<R\), sine bounds \(S_{11}<\sin<S_9\),
cosine bound \(C_{10}<\cos\), and upper bounds 1.245555
and 1.153227 for \(\sqrt{1+.751^2\cos^2t}\) at those two
endpoints. Each assertion then follows by rational
substitution and positive squaring. Also
\(R(.65)/\sqrt{1+.65^2}>1.078\) by squaring.

A convex first derivative with a negative right endpoint
cannot change from negative to positive inside the interval:
once it is nonpositive, convexity keeps it negative through
the right endpoint. Thus f has its minimum at an endpoint.
For \(k=.65,t\le .15\), the same conclusion follows directly
from \(F''_k<0\), proved after (26), and the concavity of V.
Together with (34), this proves (6).
