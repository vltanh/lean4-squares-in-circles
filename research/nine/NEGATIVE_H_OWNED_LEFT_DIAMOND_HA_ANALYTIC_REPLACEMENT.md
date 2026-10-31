# The diamond HA pressure sign: an unsquared analytic replacement

Date: October 26, 2026.

**Status: accepted complete hand argument after root and separate independent
full-domain and algebra reviews.** See
REVIEW_DIAMOND_HA_ANALYTIC_ROOT_2026_10_26.md and
REVIEW_DIAMOND_HA_ANALYTIC_CERTIFICATE_REPLACEMENT_2026_10_26.md.
This replaces the 288-sign scalar certificate in
NEGATIVE_H_OWNED_LEFT_DIAMOND_HA_PRESSURE.md on the entire original
physical domain. The original proof text, coefficient artifact and
reconstruction program are retained as historical proofs; the original
manuscript now identifies the accepted analytic route.

The replacement uses one exact quartic identity, a uniform remainder
bound obtained directly from the factored formula, and an elementary
quadratic comparison. No parameter grid, Bernstein packet or list of
high-degree coefficient signs is a premise. Every rational constant
used below is displayed or defined by the short polynomial identities.

The conclusion is exactly the original one: the true H-to-A normal n
has c_H dot n>0 in the low left-singleton diamond. No degree, force,
contact point, physical circle mask, original mean or completion square
is changed. In particular the argument does not claim the old scalar
inequality on the extraneous nonphysical region w<rho; the original
physical derivation always gives rho<w.

## 1. Original physical domain and the scalar to be replaced

Retain the true notation of the original pressure source:

\[
 \begin{gathered}
 q_0=\frac{6241}{1600}\le q=R^2<\frac{17}{4},\qquad
 z_A=(a,b),\quad a>b>0,\quad a^2+b^2=q,\\
 n=(u,v),\qquad u^2+v^2=1,\qquad
 \frac56<\rho=\frac uv\le1,\qquad
 h=v-u\ge0,\qquad U=u+v=\sqrt{2-h^2}.
 \end{gathered}
\tag{1}
\]

Under the contrary assumption c_H dot n<=0, the original unchanged
A2 concurrence and H support comparison give positive z and

\[
 z_A=z(wn-Jn),\qquad q=z^2(1+w^2),\qquad \rho<w<4.
\tag{2}
\]

For completeness, the strict upper bound follows from
Z=z_A dot n<=sqrt(2)+1/2 and

\[
 16q_0-17\left(\frac94+\frac{99}{70}\right)=\frac{41}{350}>0,
 \qquad \sqrt2<\frac{99}{70}.
\tag{3}
\]

Thus 17Z^2<16q, and (2) gives w<4. The strict lower bound w>rho
is simply the positive coordinate b=z(wv-u)>0. No comparison parameter
is introduced independently of the original A square.

Define the same physical scalar quantities as the original proof:

\[
 \begin{gathered}
 A_0=wu+v,\qquad B_0=wv-u>0,\qquad
 g=\frac12+\frac25w,\\
 \chi=U-hw-\rho
      =U-1+h\left(\frac1v-w\right),\\
 S=\sqrt{1+\chi^2},\qquad s_*=\frac1S,\quad c_* =\frac\chi S,\\
 \mathcal D=(1+c_*)^2+(s_*-hB_0)^2>0,\\
 C_0=2(A_0-g)+hB_0^2(2-gh),\qquad
 C_1=2\chi(A_0-g)-2B_0(1-gh).
 \end{gathered}
\tag{4}
\]

The original exact scalar identity is

\[
                         \mathcal D(G-g)=C_0+s_*C_1.
\tag{5}
\]

Every physical pose in (1)--(2) satisfies

\[
             0\le h\le\frac1{\sqrt{61}}<\frac{13}{100}=:H,
                    \qquad 0<\chi<\frac12.
\tag{6}
\]

Here h=(1-rho)/sqrt(1+rho^2). The chi bounds are the original
whole-domain comparisons: w<4 gives
chi>=(5rho-3)/sqrt(1+rho^2)-rho, whose minimum on [5/6,1] is
7/sqrt(61)-5/6>0; w>rho gives
chi<=sqrt(1+rho^2)-rho<1/2. The exact lower-endpoint squared reserve
is 42^2-25 times 61=239. These comparisons include h=0 and do not
divide by h.

We prove G>g directly from (5), without squaring C_0 S+C_1.

## 2. The entire physical part w<=1 is immediate

In this part B_0=wv-u lies in [0,h]. Also
u>=5/sqrt(61)>16/25 and v>=1/sqrt(2)>7/10, so

\[
              A_0-g>\frac6{25}w+\frac15\ge\frac25.
\tag{7}
\]

On the whole physical domain g<=21/10 and gh<273/1000<1.
Because chi>0 and 0<s_*<=1, (4)--(7) give

\[
 \begin{split}
 C_0+s_*C_1
 &=2(A_0-g)(1+s_*\chi)-2s_*B_0(1-gh)
                         +hB_0^2(2-gh)\\
 &\ge 2(A_0-g)-2B_0
  >\frac45-\frac{26}{100}=\frac{27}{50}>0.
 \end{split}
\tag{8}
\]

This covers every original rho<w<=1 pose, including all its physical
mask endpoints. It does not rely on a claimed sign of C_1.

## 3. One rational lower polynomial on 1<=w<=4

In the remaining part enlarge only to the single rectangle

\[
                         0\le h\le H,\qquad 1\le w\le4.
\tag{9}
\]

Put

\[
 \begin{gathered}
 \alpha=\frac{140}{99},\quad \beta=\frac{99}{70},\quad
 \gamma=\frac{41}{99},\quad \kappa=\frac{47}{100},
 \quad \eta=\frac38,\quad \zeta=\frac{11}{8},\\
 U_L=\alpha-\eta h^2,\qquad U_U=\beta,\qquad
 c=\gamma+(\alpha-w)h-\zeta h^2,\\
 A=\frac{U_L(w+1)+h(1-w)}2-g,\\
 B=\frac{U_L(w-1)+h(w+1)}2,\qquad
 \overline B=\frac{U_U(w-1)+h(w+1)}2.
 \end{gathered}
\tag{10}
\]

The letter c in this section is only the scalar lower bound for chi;
it is not the original K-frame cosine. The needed bounds are

\[
 U_L\le U<U_U,\qquad 0<c\le\chi,\qquad A>\frac12,
                    \qquad 0\le B\le B_0\le\overline B.
\tag{11}
\]

Here are complete elementary checks. Both U and sqrt(2) exceed 7/5
on (9), so

\[
 \sqrt2-U=\frac{h^2}{\sqrt2+U}
               \le\frac5{14}h^2\le\frac38h^2.
\tag{12}
\]

The strict rational comparisons alpha<sqrt(2)<beta give the first
bound in (11). Further,

\[
 \frac1v=\frac2{U+h}\ge\sqrt2-h\ge\alpha-h,
\tag{13}
\]

because (sqrt(2)-h)(U+h)<= (sqrt(2)-h)(sqrt(2)+h)<=2.
Combining (12)--(13) with (4) gives chi>=c. The scalar c decreases
with w and is concave in h, so its minimum on (9) is at h=0,w=4
or h=H,w=4. Both are positive; the smaller value is

\[
                    c(H,4)=\frac{433559}{7920000}>0.
\tag{14}
\]

Also U_L>7/5, with exact endpoint reserve 61807/7920000.
Consequently

\[
 A>\frac3{10}w+\frac15-\frac{13}{200}(w-1)
   =\frac{47}{200}w+\frac{53}{200}\ge\frac12.
\tag{15}
\]

The B bounds in (11) now follow from w>=1 and the U bounds.

For 0<=chi<=1/2 the positive square comparison gives

\[
                         S\ge1+\kappa\chi^2.
\tag{16}
\]

Indeed
1+chi^2-(1+47chi^2/100)^2
is at least 191chi^2/40000>=0. Every factor needed below has its
correct sign: A,c,B,h are nonnegative, and 1-gh,2-gh are positive.
Multiplying (5) by S and using (11),(16),

\[
 \begin{split}
 \mathcal D(G-g)S
 &=2(A_0-g)(S+\chi)-2B_0(1-gh)
                             +hB_0^2(2-gh)S\\
 &\ge Q(h,w),
 \end{split}
\tag{17}
\]

where the ordinary rational polynomial is exactly

\[
 \boxed{\displaystyle
 Q=2A(1+c+\kappa c^2)-2\overline B(1-gh)
                    +hB^2(2-gh)(1+\kappa c^2).}
\tag{18}
\]

Its degrees in h,w are at most (10,5). We next prove Q>0 on all
of (9), by a factored remainder estimate rather than an enumeration
of its monomial signs.

## 4. A short exact expansion identifies the cubic term

For fixed w write

\[
 A=a_0+a_1h+a_2h^2,\qquad B=b_0+b_1h+b_2h^2,
                          \qquad \ell=\alpha-w,
\tag{19}
\]

with the explicit coefficients

\[
 \begin{array}{lll}
 a_0=\alpha(w+1)/2-g,&a_1=(1-w)/2,&a_2=-3(w+1)/16,\\
 b_0=\alpha(w-1)/2,&b_1=(w+1)/2,&b_2=-3(w-1)/16.
 \end{array}
\tag{20}
\]

Define J=1+kappa c^2 and F=J+c. Their coefficients are

\[
 \begin{array}{ll}
 J_0=1+\kappa\gamma^2,&J_1=2\kappa\gamma\ell,\\
 J_2=\kappa(\ell^2-2\gamma\zeta),&J_3=-2\kappa\zeta\ell,\\
 J_4=\kappa\zeta^2,&
 \end{array}
\tag{21}
\]

and F_0=J_0+gamma, F_1=J_1+ell, F_2=J_2-zeta,
F_3=J_3, F_4=J_4. Let t_i be the coefficients of B^2:

\[
 (t_0,t_1,t_2,t_3,t_4)
 =(b_0^2,2b_0b_1,b_1^2+2b_0b_2,2b_1b_2,b_2^2),
                  \qquad r_i=2t_i-gt_{i-1},
\tag{22}
\]

where t_i=0 outside 0<=i<=4. Thus r_i are exactly the coefficients
of B^2(2-gh). If Q=sum P_i(w)h^i, its cubic coefficient is

\[
 P_3=2(a_0F_3+a_1F_2+a_2F_1)+r_0J_2+r_1J_1+r_2J_0.
\tag{23}
\]

The term -2 overline B(1-gh) has degree at most two in h, so it
contributes nothing to (23) or the higher-degree remainder.

Here is a compact exact quartic identity for (23). Put t=w-3,
so -2<=t<=1, and define

\[
 \begin{gathered}
 A_3=\frac{585820705123}{192119202000},\qquad
 B_3=-\frac{878272333}{1587762000},\qquad
 M_3=-\frac{47649981901}{64039734000},\\
 D_3=\frac{26992252289}{9605960100},\qquad
 E_3=\frac{2657662}{4851495}.
 \end{gathered}
\tag{24}
\]

Substitution of (20)--(22) into (23), collecting powers of t, gives

\[
 P_3(w)=A_3+B_3t+M_3t^2
                  +(t+2)t^2\{D_3+E_3(t-2)\}.
\tag{25}
\]

This displayed identity is the only quartic expansion needed. Its
last term is nonnegative throughout the interval, since

\[
 E_3>0,\qquad
 D_3-4E_3=\frac{5943569249}{9605960100}>0.
\tag{26}
\]

The remaining quadratic is concave because M_3<0. Its minimum on
[-2,1] is therefore at one of its endpoints, both strictly positive:

\[
 \begin{split}
 A_3-2B_3+4M_3&=\frac{23116297}{19602000}>0,\\
 A_3+B_3+M_3&=\frac{112199935709}{64039734000}>0.
 \end{split}
\tag{27}
\]

Thus P_3(w)>0 on the entire interval 1<=w<=4. No sign of its
individual power coefficients or any subdivision of that interval
has been assumed.

## 5. The whole higher-degree tail has a structural bound

The following small set of bounds follows directly from the factors
in (20)--(22). Since 1<=w<=4,

\[
 0<a_0<\frac32,\quad |a_1|\le\frac32,\quad |a_2|<1,
 \qquad
 0\le b_0<\frac{15}{7},\quad 1\le b_1\le\frac52,
                  \quad -\frac35<b_2\le0.
\tag{28}
\]

For example, a_0 increases with w and has maximum 1421/990<3/2;
b_0<15/7 uses alpha<10/7; and |b_2|<=9/16<3/5.
Consequently

\[
 |t_0|<5,\quad |t_1|<11,\quad |t_2|<7,\quad
                         |t_3|<3,\quad |t_4|<\frac25.
\tag{29}
\]

The bound for t_2 retains its opposite-sign terms:

\[
 |b_1^2+2b_0b_2|
 \le\max\{b_1^2,2b_0|b_2|\}
 <\max\{7,18/7\}=7.
\tag{30}
\]

Using g<=21/10 in r_i=2t_i-gt_{i-1} now gives, without expanding
any polynomial in w,

\[
 (|r_0|,|r_1|,|r_2|,|r_3|,|r_4|,|r_5|)
                         <(10,33,38,21,8,1).
\tag{31}
\]

In particular every |r_i|<38.

Also gamma<5/12, |ell|<13/5 and zeta=11/8. The formulas (21)
give directly

\[
 (|J_0|,|J_1|,|J_2|,|J_3|,|J_4|)
 <\left(\frac{11}{10},\frac{11}{10},\frac{16}{5},
                         \frac{17}{5},\frac9{10}\right),
                   \qquad \sum_{j=0}^4|J_j|<10.
\tag{32}
\]

For the difference in J_2 use
|ell^2-2gamma zeta|<=max(ell^2,2gamma zeta); the larger uniform
bound is (13/5)^2, and kappa times that is 7943/2500<16/5.
The other comparisons are immediate positive products. The same
difference argument gives

\[
 |F_2|=|\kappa\ell^2-\zeta(1+2\kappa\gamma)|<\frac{16}{5},
        \qquad |F_3|<\frac{17}{5},\quad |F_4|<\frac9{10}.
\tag{33}
\]

Every coefficient of h-degree at least four in 2AF therefore has
absolute value less than 20. The largest of the three needed product
bounds is

\[
 2\left(\frac32\frac9{10}+\frac32\frac{17}{5}
                                  +\frac{16}{5}\right)
                                  =\frac{193}{10}<20;
\tag{34}
\]

the degree-five and degree-six bounds are smaller, and all later
coefficients vanish. By convolution, every coefficient of
h B^2(2-gh)J has absolute value less than
38 sum |J_j|<380. Thus the original factored Q satisfies the single
uniform coefficient-size estimate

\[
                         |P_i(w)|<400\qquad (4\le i\le10)
\tag{35}
\]

for every 1<=w<=4. This is a factor-norm estimate, not a check of
any list of coefficient signs.

Put x=h/H in [0,1] and y=(w-1)/3 in [0,1]. Using P_3>0 and
the geometric-series bound from (35),

\[
 \begin{split}
 Q(h,w)&\ge P_0(w)+P_1(w)h+P_2(w)h^2
                         -\frac{400h^4}{1-h}\\
 &\ge P_0(w)+P_1(w)h+P_2(w)h^2
                   -\frac{28561}{217500}x^2\\
 &\ge P_0(w)+P_1(w)h+P_2(w)h^2-\frac7{50}x^2.
 \end{split}
\tag{36}
\]

Here h^4/(1-h)<=H^4 x^2/(1-H), and the fixed exact reserve is

\[
 \frac7{50}-\frac{400H^4}{1-H}
 =\frac7{50}-\frac{28561}{217500}
 =\frac{1889}{217500}>0.
\tag{37}
\]

No high-degree coefficient has been individually evaluated in deriving
(35)--(37). Their actual signs are unrestricted.

## 6. The retained quadratic is positive over the whole rectangle

Set z=1-y in [0,1]. Directly collecting just the constant, linear
and quadratic h terms of (18) gives the exact identity

\[
 P_0(1+3y)+H P_1(1+3y)x+H^2P_2(1+3y)x^2-\frac7{50}x^2
                    =G_0(x)+zG_1(x)+z^2G_2(x)+z^3G_3(x),
\tag{38}
\]

where the four small polynomials are

\[
 \begin{split}
 G_0={}&\frac{163484479}{3396046500}
       -\frac{4481744579}{29648025000}x
       +\frac{1672106022967}{5692420800000}x^2,\\
 G_1={}&\frac{842722577}{566007750}
       -\frac{224074596694}{233478196875}x
       -\frac{280634044962661}{426931560000000}x^2,\\
 G_2={}&\frac{866485830821}{933912787500}x
       +\frac{3135287044981}{53366445000000}x^2,\\
 G_3={}&\frac{321340201559}{2223601875000}x^2.
 \end{split}
\tag{39}
\]

Equations (18)--(22) define every coefficient of this identity; it
requires no rational interval or radical endpoint packet. Clearly
G_2,G_3 are nonnegative for x>=0. Simple rational comparisons give

\[
 \begin{split}
 G_0(x)&>f(x):=\frac6{125}-\frac{19}{125}x+\frac{29}{100}x^2,\\
 G_1(x)&>l(x):=\frac{186}{125}-\frac{24}{25}x
                                            -\frac{329}{500}x^2.
 \end{split}
\tag{40}
\]

For explicit checking, the three coefficient differences in the first
row are respectively

\[
 \frac{474247}{3396046500},\quad
 \frac{24755221}{29648025000},\quad
 \frac{21303990967}{5692420800000},
\tag{41}
\]

and those in the second row are

\[
 \frac{100609}{113201550},\quad
 \frac{64472306}{233478196875},\quad
 \frac{286921517339}{426931560000000}.
\tag{42}
\]

All six displayed rationals are positive. These fixed comparisons
round one explicit low-degree identity; they are not a parameter
subdivision or a new finite sign certificate for the original radical.

The whole x interval is now elementary. The function l decreases for
x>=0, with

\[
                   l(9/10)=\frac{4551}{50000}>0,
                       \qquad l(1)=-\frac{13}{100}.
\tag{43}
\]

If 0<=x<=9/10, then zG_1>=0. Completing the square gives

\[
                      f(x)\ge\frac{509}{18125}>
                                      \frac{161}{10000}>0.
\tag{44}
\]

If 9/10<=x<=1, then zG_1>-13/100, because 0<=z<=1 and
G_1>l>=-13/100. The function f increases on this interval and
f(9/10)=1461/10000. Thus (36),(38)--(44) give the uniform strict bound

\[
                         \boxed{Q(h,w)>\frac{161}{10000}>0.}
\tag{45}
\]

Both parts are broad scalar intervals of one elementary quadratic;
no physical family is restricted or lost at their common endpoint.
Equation (17), with D and S positive, now proves G>g for every
original physical w>=1 pose. Together with Section 2 it covers the
entire original rho<w<4 domain.

## 7. The unchanged physical contradiction and precise replacement scope

The original HK contact classification gives r=L/(rho+c_K/s_K)<1,
where L=U-hw and the actual K-frame cosine c_K satisfies
c_K/s_K>chi. For the original fixed T, its actual circle corner
has squared radius q, while the comparison vector e_*=(-c_*,s_*)
satisfies

\[
                       |T+e_*|^2-q>0.
\tag{46}
\]

This uses the strict monotonicity of that norm as c_K increases,
with the original a>3/2 and beta_T>0. It does not move any physical
square. The exact original algebraic identity is

\[
                       |T+e_*|^2-q=\mathcal D(1-zG).
\tag{47}
\]

Our replacement proves G>g>0 on every pose used in (46)--(47).
The function (1+w^2)/g^2 increases for w>=5/6, since its derivative
has the sign of w/2-2/5>0. Therefore w<4 and (2) give

\[
 \frac{1+w^2}{G^2}<\frac{1+w^2}{g^2}
 \le\frac{1700}{441}<\frac{6241}{1600}\le q,
                    \qquad zG>1,
\tag{48}
\]

with exactly the original radius reserve

\[
              \frac{6241}{1600}-\frac{1700}{441}
                             =\frac{32281}{705600}>0.
\tag{49}
\]

Equations (47)--(48) contradict (46). Thus the contrary original
projection assumption is impossible, and c_H dot n>0 follows at
the full original physical scope.

The physical HA/AK owners and every true H5/K3/A2/B2 force remain.
The argument uses the real A2 concurrence and the forced original HK
offset; it never supplies a fictitious K2 equation. It includes the
h=0 comparison endpoint, every actual mean and B mask, the intact
HXY petal and all three original extra squares. Any accepted later
local-pressure generalization retains its own separately audited
physical join; this scalar replacement neither strengthens nor changes
its degree or force premises.

The historical 288-sign certificate established a larger rectangular
algebraic statement including w<rho. That enlargement is unnecessary
for the original physical theorem and is not asserted here. The
replacement preserves every original physical case and the same final
radius contradiction while removing those 288 signs from this proof
route. It adds no roadmap gate and does not by itself change a whole
component or global theorem status.

No numerical sample, Lean compilation or CI is used as a premise.
