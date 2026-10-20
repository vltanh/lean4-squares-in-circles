# The G-zero stress remains positive opposite a negative outer error

## 1. Statement on the full mixed scalar domain

Use the constants and the two continuous affine weight formulas in
`HAND_G5_G_ZERO_TWO_AFFINE_STRESS_SCALARS.md`. To distinguish the
negative geometric error from a stress weight, write those five
weights as
\[
 (a,\beta,\varepsilon,\kappa,\lambda)
 =(a,b,e,k,\lambda)_{\rm old}.
\]
Thus their values at x=0, .17, .204 are, respectively,
\[
\begin{aligned}
 &(.780,1.240,1.376,.382,1.128),\\
 &(.755,1.100,1.090,.431,1.090),\\
 &(.7495,1.030,.964,.416,1.080),
\end{aligned}
\tag{1}
\]
with affine interpolation on the two intervening intervals. Put
\[
\begin{gathered}
 Q=9789/2500,\quad R=\sqrt Q,\quad K=13/12,\\
 k_0=\sqrt{Q-1/4}-1,\quad L=311/1000,\quad h_0=107/1000,\\
 f=\varepsilon\cos x+\kappa\sin x,\qquad
 g(h)=\tfrac12+\tfrac12\cos h-k_0\sin h.
\end{gathered}
\tag{2}
\]
Every terminating decimal here denotes an exact rational number.

The scalar domain is
\[
\begin{gathered}
 0\le x\le51/250,\qquad h_0\le h\le L-x,\\
 t,u,e,d,v\ge0,\qquad t+u+e=x,\qquad d+v=x,
 \qquad e\le3/25.
\end{gathered}
\tag{3}
\]
Consider five sorted anchors H, A, B, D, E with corner ceilings at
most Q. H, A, B and D have nonnegative own-frame coordinates. E
may have either signed transverse coordinate b_E, with its actual
corner condition written using |b_E|. Retain the six inequalities
\[
\begin{aligned}
 b_H&\ge g(h),\\
 a_A\cos(t+h)-b_A\sin(t+h)&\ge W(t+h),\\
 b_A+b_B&\ge1,\\
 a_B\cos u-b_B\sin u+(\sec e)b_D
  &\ge W(u)+\tfrac12+\tfrac12\sec e+K\tan e,\\
 a_D+a_E\sin d+b_E\cos d&\ge W(d),\\
 a_H+a_E\sin v-b_E\cos v&\ge W(v),
 \qquad W(z)=\tfrac12(1+\cos z+\sin z).
\end{aligned}
\tag{4}
\]

**Mixed-endpoint exclusion.** No system (3)--(4) satisfies these
five circle bounds. More precisely, its explicit circle stress
below obeys
\[
                    N_{\rm neg}>\frac{13}{50000}
                                      +\frac{3e}{1000}.
\tag{5}
\]
The theorem permits e=0. The angular domain is an explicit
hypothesis of this scalar statement; the separate note
`HAND_G5_MIXED_G_ZERO_NEGATIVE_DOMAIN.md` proves it for the
geometric G-zero endpoint opposite a large-transverse negative
outer error. No sign of E is required by either statement.

## 2. The old five-center stress, with its negative error retained

Give (4) the positive weights
\(\lambda,1,a,\beta,f,\varepsilon\). The force rows are
\[
\begin{array}{c|cc}
 &F_1&F_2\\ \hline
 A&\cos(t+h)&a-\sin(t+h)\\
 B&\beta\cos u&a-\beta\sin u\\
 D&f&\beta\sec e\\
 E&f\sin d+\varepsilon\sin v&f\cos d-\varepsilon\cos v\\
 H&\varepsilon&\lambda.
\end{array}
\tag{6}
\]
The demand is
\[
 \mathcal D_{\rm neg}=\lambda g(h)+W(t+h)+a
 +\beta\{W(u)+\tfrac12+\tfrac12\sec e+K\tan e\}
 +fW(d)+\varepsilon W(v).
\tag{7}
\]
Subtract the four usual corner-disk supports for A, B, D, E and
the exact sorted-H support from the old note:
\[
 N_{\rm neg}=\mathcal D_{\rm neg}
 -\sum_{i=A,B,D,E}\left(R|F_i|-\frac{F_{i1}+F_{i2}}2\right)
 -H(\varepsilon,\lambda).
\tag{8}
\]
Here H is exactly the piecewise support in equation (8) of the old
note. For signed E the same support remains an upper bound by
replacing its force's second component by its absolute value
before applying its actual circle. Thus feasibility of (4) implies
\(N_{\rm neg}\le0\).

At fixed x, h, e the E force and all its split-dependent terms
are unchanged from the old stress. Section 2 of the old note
therefore gives the same worst E split d=x, v=0. Write
\[
 A(z)=\cos z-R\sqrt{1+a^2-2a\sin z},\qquad
 B(z)=\beta\cos z-R\sqrt{\beta^2+a^2-2a\beta\sin z}.
\tag{9}
\]
The remaining t-dependent part is
\(A(t+h)+B(x-e-t)\). The old concavity and derivative comparison
\(B'(z)>A'(z)\), valid for all \(0\le z\le x\), apply on the
shorter interval \([0,x-e]\) as well. Its worse endpoint is
\[
                         t=x-e,\qquad u=0.
\tag{10}
\]
These comparisons use the same weights throughout each split.

Let N_old(x,h) be the old stress at its worst two frame splits
t=x, u=0, d=x, v=0. Its proved scalar theorem gives
\[
                         N_{\rm old}(x,h)>13/50000
\tag{11}
\]
for every x,h in (3), without any additional h minimization here.
Put r=f/beta, and define
\[
 \Phi_r(y)=\sec y+K\tan y-R\sqrt{r^2+\sec^2y}.
\tag{12}
\]
Directly collecting (6)--(8), after (10), gives
\[
 N_{\rm neg}\ge N_{\rm old}(x,h)+\Delta(e),
\qquad
 \Delta(y)=A(x-y+h)-A(x+h)
             +\beta\{\Phi_r(y)-\Phi_r(0)\}.
\tag{13}
\]
All quantities x,h,a,beta,f stay fixed while y varies. In
particular this is a comparison within one stress, not a change
of its anchor circles. The remainder of the proof shows
\(\Delta(e)\ge3e/1000\).

## 3. Uniform derivatives of the A term

Throughout both weight intervals,
\[
                  37/50<a\le39/50,\qquad0\le z\le L.
\tag{14}
\]
On this rectangle one has the useful bounds
\[
             -\frac58<A''(z)<0,
                 \qquad0<\frac{\partial A'(z)}{\partial a}<\frac95.
\tag{15}
\]
The strict upper curvature bound is already proved in equation
(15) of the old note. Here are direct rational proofs of the two
new bounds. With \(n^2=1+a^2-2a\sin z\),
\[
 A''(z)=-\cos z+
 R\frac{a(a-\sin z)(1-a\sin z)}{n^3}.
\tag{16}
\]
As proved in the old note, the positive fraction decreases as
sin z increases. Substituting sin z<=L, and then the endpoints
in (14), gives
\[
 R\frac{a(a-\sin z)(1-a\sin z)}{n^3}
 >\frac{(197/100)(37/50)(37/50-L)(1-(39/50)L)}{6/5}
 =\frac{39473965817}{100000000000}>\frac38.
\tag{17}
\]
The denominator bound used here is
\[
 [1+(39/50)^2-2(39/50)L]^3<(6/5)^2;
\]
its positive reserve is `356936344559/15625000000000`.
Since -cos z>=-1, this proves the lower curvature bound.

Also
\[
 \frac{\partial A'}{\partial a}
       =\frac{R\cos z(1-a\sin z)}{n^3}>0,
 \qquad n^2>1+(37/50)^2-2(37/50)L=27183/25000.
\]
Using R<2 gives the upper bound 9/5 in (15). Its positive-square
reserve is
\[
 (9/5)^2(27183/25000)^3-4
       =64461118736447/390625000000000>0.
\tag{18}
\]

## 4. The initial gain is uniform in the common frame span

Define
\[
                    I(x)=\beta K-A'(x+h_0).
\tag{19}
\]
The dependence of A on the affine weight a is included when
differentiating this function. On the first interval the slopes
of a,beta are -5/34,-14/17; on the second they are
-11/68,-35/17. Equation (15) therefore gives, respectively,
\[
\begin{aligned}
 I'(x)&<-(14/17)(13/12)+5/8+(5/34)(9/5)=-1/408,\\
 I'(x)&<-(35/17)(13/12)+5/8+(11/68)(9/5)=-2681/2040.
\end{aligned}
\tag{20}
\]
The weights, hence I, are continuous at .17. Thus I is strictly
decreasing on the whole interval [0,.204].

At its right endpoint z=L, a=1499/2000 and beta=103/100.
Alternating Taylor bounds give
\[
       153/500<\sin L<49/160,
       \qquad\cos L<953/1000.
\]
The sine lower bound uses the seventh-degree Taylor polynomial;
the upper bounds use degrees five and four. Moreover
\[
 R<1979/1000,
 \qquad1+(1499/2000)^2-2(1499/2000)(49/160)
                              >(21/20)^2.
\tag{21}
\]
Their squared reserves are 841/1000000 and 363/2000000.
Consequently
\[
 A'(L)<-\frac{153}{500}
 +\frac{(1979/1000)(1499/2000)(953/1000)}{21/20}
 =\frac{2184494513}{2100000000}<\frac{1249}{1200}.
\tag{22}
\]
The last reserve is `1255487/2100000000`. Since
\((103/100)K-3/40=1249/1200\), equations (19)--(22) imply
\[
                             I(x)>\frac3{40}.
\tag{23}
\]
For the actual h>=h0, the concavity of A gives
\[
 \Delta'(0)=\beta K-A'(x+h)
               \ge\beta K-A'(x+h_0)>3/40.
\tag{24}
\]

## 5. A lower curvature bound for the negative-error term

First the affine formulas give
\[
                              r=f/\beta>99/100.
\tag{25}
\]
Here is a whole-interval rational verification. Alternating
Taylor bounds show that
\[
 f-(99/100)\beta
 \ge P(x):=\varepsilon(1-x^2/2)
                  +\kappa(x-x^3/6)-(99/100)\beta.
\tag{26}
\]
On the first and second weight intervals the coefficients of P,
in ascending powers of x, are respectively
\[
\begin{aligned}
 &(371/2500,-4123/8500,-1699/4250,39653/51000,-49/1020),\\
 &(569/2000,-4937/4250,-553/425,90199/51000,5/68).
\end{aligned}
\tag{27}
\]
For a translated polynomial `P(m+y)=sum p_j y^j`, the elementary
lower bound on |y|<=rho is
\[
 p_0-\sum_{j\text{ odd}}|p_j|\rho^j
        +\sum_{j\ge2\text{ even}}\min(p_j,0)\rho^j.
\tag{28}
\]
At the respective center/radius pairs (.085,.085), (.187,.017),
this equals
\[
       343390007/6000000000>0,
       \qquad101982556609/12000000000000>0.
\tag{29}
\]
These are coefficient sums on the two entire weight domains.
They prove (25) without an angular cover.

For 0<=y<=3/25, put w=sec y and T=tan y. The elementary bounds
\[
                   1\le w<126/125,
                   \qquad0\le T<121/1000
\tag{30}
\]
follow from cos y>=1-y^2/2. The respective rational reserves are
58/78125 and 161/1250000 after multiplication by the positive
denominator. In particular cos y>99/100, so (25) gives
\[
 \sqrt{1+r^2\cos^2y}>7/5,
 \qquad \frac{Rw}{\sqrt{r^2+w^2}}<99/70,
\tag{31}
\]
using R<99/50. The first positive-square reserve is
`1+(99/100)^4-(7/5)^2=59601/100000000`.

Set n=sqrt(r^2+w^2). Differentiating (12), with r fixed, yields
\[
 \Phi_r''(y)=w(1+2T^2)(1-Rw/n)
                  -R\frac{r^2w^2T^2}{n^3}+2K w^2T.
\tag{32}
\]
The final term is nonnegative and `r^2/n^3<=1/w`. Thus
(30)--(31) give
\[
\begin{split}
 \Phi_r''(y)&>
 -\frac{29}{70}\frac{126}{125}
                         \left(1+2\left(\frac{121}{1000}\right)^2\right)
 -\frac{99}{50}\frac{126}{125}\left(\frac{121}{1000}\right)^2\\
 &=-\frac{1434528927}{3125000000}>-\frac{23}{50}.
\end{split}
\tag{33}
\]
The last reserve is `2971073/3125000000`.

## 6. The old strict margin survives on the entire mixed domain

For every 0<=y<=e, the argument x-y+h lies in [h0,L]. Also
0<beta<5/4. From (15), (33),
\[
 \Delta''(y)=A''(x-y+h)+\beta\Phi_r''(y)
             >-\frac58-\frac54\frac{23}{50}=-\frac65.
\tag{34}
\]
Since Delta(0)=0, integrating this uniform lower curvature bound
with (24) gives, for e>0,
\[
 \Delta(e)>\frac{3e}{40}-\frac{3e^2}{5}
       \ge e\left(\frac3{40}-\frac35\frac3{25}\right)
       =\frac{3e}{1000}.
\tag{35}
\]
At e=0 one has Delta(e)=0. Equations (11), (13), (35) prove
(5), contradicting the necessary inequality from (8).

The geometric domain theorem supplies (3) at a positive G-zero
endpoint opposite a negative outer error. It even proves
u+e<3/25, whereas the scalar comparison used only e<=3/25.
Thus this excludes that endpoint and, by reflection with signed E,
the corresponding T-zero endpoint. The proof retains the same
five circle supports, uses the original two continuous affine
weight formulas, and absorbs the negative-error contribution by
one derivative comparison. It has no sampled minimizer, angle
mesh, new endpoint inventory, or numerical-oracle premise.
