# A common primary charge for every high quarter in the remaining branch

## 1. Statement and the common outer potential

Work on the G0--G2 boundary geometry at
\(Q=9789/2500\). Put
\[
 R=\sqrt Q,\qquad a_0=\sqrt{Q-1/4}-1/2,
 \qquad c_0=\sqrt{Q/2}-1/2,
 \qquad \kappa=\frac{103}{100},\quad \rho=\frac{11}{10}.
\]
An outer state has coordinates
\[
 a=a(b)=\sqrt{Q-(b+1/2)^2}-1/2,
             \qquad 0\le b\le c_0.
\]
Use exactly the established outer marker F, with its original
L, M, or H chart. Extend the H formula to the entire outer arc:
\[
 F_H^*(a,b)=\frac\pi4-.569472(a-c_0)+.390886(b-c_0).
\]
Define, once per outer state,
\[
 J(a,b)=F_H^*(a,b)-F(a,b),\qquad
                 \Pi(a,b)=\kappa a+\rho J(a,b).       \tag{1}
\]
The constants written as terminating decimals are exact rationals.
At a marker junction the argument below allows either adjacent
original marker. No new radial state is substituted.

Consider an original quarter edge whose source is outer and has
signed tangent \(-b\le0\), and whose target has signed tangent Y
and primary A. Assume that the target is either outer or a core
state with strictly positive tangent. The actual high-owner
alternatives are
\[
 \begin{split}
 P_2&=a\cos d+b\sin d-Y\ge W(d),\quad\hbox{or}\\
 P_3&=a+A\sin d-Y\cos d\ge W(d),\\
 W(d)&=(1+\cos d+|\sin d|)/2,
                         \qquad |d|\le7/10.
 \end{split}                                                    \tag{2}
\]
Then
\[
 \boxed{\qquad d+\Pi(a,b)-\kappa Y\ge\kappa.\qquad} \tag{3}
\]
The inequality is strict if d is nonzero. At d=0 equality occurs
exactly when the source uses its H marker and a-Y=1.

No G1 upper charge cap, physical-gap bound, frame order, or
hypothesis on another edge is used to prove (3). In the actual
all-high branch, every high-quarter source is outer by
`HAND_G3_EVERY_QUARTER_HAS_AN_OUTER_ANCHOR.md`; a nonpositive target
among H,A,T is outer by
`HAND_G3_NONPOSITIVE_ZERO_SOURCE_IS_OUTER.md`. Thus the target
condition in this theorem applies to each repeated quarter into
H, A, or T in that branch.

This note proves the quarter component for the common potential
(1). The compatible zero-edge and outer-to-outer bridge bounds are
separate obligations before this potential can exclude a cycle.

## 2. Elementary bounds and properties of J

The defining square identities give
\[
 .89921<c_0<.89922,\qquad
 1.41457<a_0<1.41458,\qquad R<1.979.                  \tag{4}
\]
On \([0,.7]\), use \(\cos z>.76\), \(\sin z<.65\), and
\(\sin(.7)>.64\). Their alternating Taylor proofs are the same
whole-interval comparisons as in
`HAND_G3_GLOBAL_D_IS_OUTER.md`, Section 2.

Here are the properties of J needed below:
\[
 \begin{gathered}
 J\ge0\quad\hbox{on every outer chart},\qquad
 J=0\quad\hbox{exactly on the H chart},                 \tag{5}\\
 b\le33/100\quad\Longrightarrow\quad J>1/40.           \tag{6}
 \end{gathered}
\]
We also need one quadratic comparison. Set
\[
 r=\frac{1151}{2400},\quad s=\frac7{60},\quad
 t=b+\frac12,\quad x=a+\frac12,\quad
 D=r(x-1)-st.
\]
For \(b<1/\kappa-1/2\),
\[
 D>0,\qquad
        4\kappa\rho J D>(1-\kappa t)^2.              \tag{7}
\]
Section 7 proves (5)--(7) directly on the two whole arcs L and M.
It uses only concavity and the printed rational endpoint bounds.

## 3. Original owner 2

### 3.1 Nonnegative error

For d>=0, rearranging P2 gives
\[
 a-Y-1\ge(a-1/2)(1-\cos d)+(1/2-b)\sin d.
\]
Since b<c0<9/10 and J>=0,
\[
 d+\kappa(a-Y-1)+\rho J
       \ge d-\frac{2\kappa}{5}\sin d
       \ge(1-2\kappa/5)d.                            \tag{8}
\]
This is positive for d>0.

### 3.2 Negative error

Write d=-z, with z>0. The same original projection gives
\[
 a-Y-1\ge(b+1/2)\sin z+(a-1/2)(1-\cos z).
\]
Thus it suffices to prove
\[
 g(z):=-z+\kappa\{t\sin z+(x-1)(1-\cos z)\}
                                      +\rho J>0.     \tag{9}
\]
If \(b<1/\kappa-1/2\), use
\(\sin z\ge z-z^3/6\),
\(1-\cos z\ge z^2/2-z^4/24\), and z<=7/10:
\[
 \begin{split}
 g(z)&\ge\rho J+(\kappa t-1)z
 +\kappa\left\{\frac{1151}{2400}(x-1)-\frac7{60}t\right\}z^2\\
 &\ge\rho J-\frac{(1-\kappa t)^2}{4\kappa D}>0
 \end{split}                                                     \tag{10}
\]
by (7). This is a single quadratic completion on the entire angle
interval, not an angle partition.

For \(b\ge1/\kappa-1/2\), examine
\[
 g'(z)=-1+\kappa\{t\cos z+(x-1)\sin z\}.
\]
The expression in braces is concave in z. At z=0 it is at least
1/kappa. At z=.7, use \(t\ge1/\kappa\),
\(x-1\ge c_0-1/2>.399\), and (4):
\[
 \kappa\{t\cos(.7)+(x-1)\sin(.7)\}-1
   >\frac{19}{25}+\kappa\frac{399}{1000}\frac{16}{25}-1
                  =\frac{3597}{156250}>0.           \tag{11}
\]
Concavity places the expression above its endpoint chord. Hence
g' is positive on the open angle interval, and g(z)>g(0)>=0.
This completes owner 2 with every target sign and radial kind.

## 4. Original owner 3 with positive error

Write d=z>0 and put \(\eta=c_0-1/2\),
\[
 V=\sqrt{Q-(\sin z-\eta)^2},\qquad
 \lambda=\kappa\left\{\cos z+
                \frac{(\sin z-\eta)\sin z}{V}\right\}.           \tag{12}
\]
We have V>1.9 and \(0<\lambda\le\kappa\). For positivity,
\[
 \lambda/\kappa>.76-\frac{.4\cdot.65}{1.9}>0.
\]
For the upper bound, it is immediate when sin z<=eta. Otherwise
\[
 \frac{(\sin z-\eta)(1+\cos z)}{\sin z}
 <2\left(1-\frac{.399}{.65}\right)<1.9<V,
\]
which is exactly \(\lambda\le\kappa\).

Every actual target, including a signed core target, satisfies
\[
                    (A+1/2)^2+(Y+1/2)^2\le Q.       \tag{13}
\]
For Y<0 this follows by decreasing the absolute transverse corner
coordinate. Add \(\lambda(W-P_3)\le0\) to
\(z+\kappa(a-Y-1)\), retain the source lower bound a>=c0,
and use the disk support in (13). Since kappa-lambda>=0,
\[
 \begin{split}
 z+\kappa(a-Y-1)
 &\ge z+\kappa\eta+\lambda(\sin z-\eta)
        -R\sqrt{\kappa^2+\lambda^2-2\kappa\lambda\cos z}\\
 &=z+\kappa\{\eta+\cos z(\sin z-\eta)-\sin z\,V\}
                 =:G(z).                            \tag{14}
 \end{split}
\]
The explicit choice (12) gives the last equality; it is a positive
multiplier applied to the original feasible owner.

Section 8 proves, on the whole interval,
\[
                         G(z)>\frac3{2000}z>0.       \tag{15}
\]
Together with J>=0, this proves (3) for positive owner-3 error.

## 5. Original owner 3 with negative error and an outer target

Write d=-z<0.

If Y<=0, write Y=-B. The target is outer by hypothesis. Put
q=tan(z/2), so 0<q<.366. The original projection difference is
\[
                 P_3-P_2=\sin z\{qa+b-A-qB\}.       \tag{16}
\]
Sorted containment gives qa+b<=c0(1+q). On the target outer arc,
A+qB>=c0(1+q): its concavity in B reduces the minimum to B=0 or
B=c0, and the first endpoint satisfies
\(a_0>1.414>.9(1+.366)>c_0(1+q)\).
Thus P3<=P2. The original owner-2 projection is feasible, so
Section 3.2 applies.

If Y>0 and the target is outer, (2) instead gives
\[
 a-Y-1\ge(A+1/2)\sin z-(Y+1/2)(1-\cos z)
       \ge(c_0+1/2)(\sin z+\cos z-1).               \tag{17}
\]
Feasibility forces z<1/2. Indeed the last function increases on
[0,.7], and at z=1/2 its lower Taylor bound is
\[
 (c_0+1/2)(\sin(1/2)+\cos(1/2)-1)
 >\frac{1399}{1000}\frac{17}{48}
 >\frac{83}{200}>a_0-1\ge a-Y-1.
\]
The positive reserve in the middle comparison is 3863/48000.
For z<=1/2,
\[
 \sin z+\cos z-1
 \ge z-z^2/2-z^3/6\ge\frac{17}{24}z.
\]
Therefore (17) gives
\[
 -z+\kappa(a-Y-1)
 >\left(\kappa\frac{1399}{1000}\frac{17}{24}-1\right)z
                    =\frac{49649}{2400000}z>0.      \tag{18}
\]
No marker correction is needed in this outer-target case.

## 6. Original owner 3 with negative error and a positive core target

First Y<1/2. If Y>=1/2, the universal primary lower bound
A>447/800>1/2 would give
\[
 P_3-W<a_0-1/2-(A+1/2)\sin z-\cos z
          <a_0-3/2<0,
\]
using sin z+cos z>=1. Thus the target is on its actual flat core
side and A=7/12.

The projection now gives
\[
 Y\cos z\le a-\tfrac12-\tfrac12\cos z-\tfrac{13}{12}\sin z.
                                                               \tag{19}
\]
Since Y>0, this also forces z<1/2: the right-hand constraint at
z=1/2 would require
\[
 a>\frac12+\frac12\{1-(1/2)^2/2\}
             +\frac{13}{12}\{1/2-(1/2)^3/6\}
       =\frac{283}{200}+\frac{599}{14400}>a_0.
\]
The required right side increases on [0,.7].

Eliminate Y using (19). With U=183/200>a0-1/2,
\[
 \begin{split}
 -z+\kappa(a-Y-1)+\rho J
 &\ge -z+\kappa\left\{\frac{13}{12}\tan z
                  -(a-1/2)(\sec z-1)\right\}+\rho J\\
 &\ge L(z)+\rho J,                                  \tag{20}
 \end{split}
\]
where the single degree-five polynomial is
\[
 L(z)=\left(\frac{13\kappa}{12}-1\right)z
       -\frac{\kappa U}{2}z^2+\frac{13\kappa}{36}z^3
       -\frac{47\kappa U}{200}z^4+\frac{13\kappa}{90}z^5.
                                                               \tag{21}
\]
The bounds used here, throughout [0,1/2], are
\[
 \tan z\ge z+z^3/3+2z^5/15,\qquad
 \sec z-1\le z^2/2+47z^4/200.                        \tag{22}
\]
The tangent inequality follows by integrating
\((\tan z)'=1+\tan^2z\) twice from the initial bound tan z>=z.
For the secant bound multiply its proposed upper bound by
\(C_6(z)=1-z^2/2+z^4/24-z^6/720\). The product minus one is
\[
 z^4\left\{\frac2{75}-\frac{353}{3600}z^2
                 +\frac{131}{14400}z^4-\frac{47}{144000}z^6\right\}.
\]
Dropping its positive z^4 term and bounding the negative powers
at 1/2 leaves 19793/9216000>0. Since cos z>=C6(z)>0,
this proves (22).

For 0<z<=3/10, L(z)/z is decreasing. An upper bound on its derivative
is the negative of 695971/3000000, obtained by dropping its negative
quadratic term and bounding the remaining positive powers at 3/10.
At the endpoint,
\[
                 \frac{L(3/10)}{3/10}
                          =\frac{37993057}{12000000000}>0.       \tag{23}
\]
Thus (20) is strictly positive on this first range.

On the entire interval [0,1/2], L is concave. One explicit check is
\[
 L''(z)\le-\kappa U+\frac{13\kappa}{6}z-Kz^2,
 \qquad K=\frac{10529381}{9000000}>0.
\]
The quadratic on the right increases on this interval, and its
value at 1/2 is -4287581/36000000<0. Consequently
\[
 L(z)\ge\min\{L(0),L(1/2)\}>-\frac{23}{1000},
 \quad L(1/2)+\frac{23}{1000}=\frac{236473}{576000000}>0.         \tag{24}
\]
For z>3/10, (19) forces
\[
 a>\frac12+\frac12\{1-(3/10)^2/2\}
            +\frac{13}{12}\{3/10-(3/10)^3/6\}.
\]
The square of this lower bound plus 1/2, added to (83/100)^2,
exceeds Q by 304361/64000000. The source is on its actual outer
circle, so b<33/100. Equation (6) applies and gives
\[
 L(z)+\rho J>-\frac{23}{1000}+\frac{\rho}{40}
                           =\frac9{2000}>0.          \tag{25}
\]
This completes every negative owner-3 case.

## 7. Two whole-arc concavity comparisons for the marker correction

This section verifies (5)--(7). Use the fixed rational lower
bounds in (4), together with pi>3.14159, to set
\[
 \begin{array}{ll}
 A_L=.973347,& B_L=.698179,\\
 A_M=2.059065,& B_M=1.189333,\\
 K_L=3.14159/4+.178586(.89921)+.403875(1.41457)
                                      +(A_L+B_L)/2,\\
 K_M=3.14159/4+.178586(.89921)+2.143075+(A_M+B_M)/2.
 \end{array}                                                    \tag{26}
\]
In x=a+1/2 and t=b+1/2 coordinates, the original L and M formulas
imply respectively
\[
 J\ge j_L:=K_L-A_Lx-B_Lt,
       \qquad J\ge j_M:=K_M-A_Mx-B_Mt.             \tag{27}
\]
Here x^2+t^2=Q. The L/M junction b1 is determined by a=4b;
its exact quadratic 17b1^2+5b1+1/2=Q gives
\[
                 .3246<b_1<.3247.                   \tag{28}
\]

### 7.1 Positivity and the short transverse range

On L, jL decreases with b, since
\[
 B_L-A_L\frac{.8247}{1.7984}
                  =\frac{4528858427}{17984000000}>0.
\]
At its far endpoint,
\[
 K_L-A_L(1.7988)-B_L(.8247)-.026
                 =\frac{41147091}{10^{11}}>0.        \tag{29}
\]
At b=0 the comparison is stronger:
\[
 K_L-A_L(1.91458)-B_L/2-.1404
                       =\frac{321531}{2\cdot10^{10}}>0.         \tag{30}
\]
On M, Cauchy's inequality proves jM>0 because K_M>0 and
\[
 K_M^2-Q(A_M^2+B_M^2)
             =\frac{187430744126045067609}
                     {2500000000000000000000}>0.     \tag{31}
\]
For b<=.33 on M, jM is decreasing: its derivative has the sign
of \(A_Mt/x-B_M\), and x>1.796, t<=.83 suffice. At b=.33,
x<1.797 and
\[
 K_M-A_M(1.797)-B_M(.83)-.025
                         =\frac{48581103}{5\cdot10^{10}}>0.    \tag{32}
\]
Equations (29)--(32) prove (5)--(6), including either marker at a
junction. On H, J=0 by definition.

### 7.2 The L arc in (7)

Let
\[
 R_L(t)=4\kappa\rho j_L\{r(x-1)-st\}-(1-\kappa t)^2,
                       \qquad x=\sqrt{Q-t^2}.
\]
This function is concave on the entire L interval. Here is an
explicit whole-interval verification. After expansion it has the form
\[
 R_L(t)=\alpha x+\delta xt+\gamma t^2+\nu t+\omega,
\]
where only the first three coefficients matter for curvature:
\[
 \alpha=4\kappa\rho r(K_L+A_L),\quad
 \delta=4\kappa\rho(A_Ls-B_Lr),\quad
 \gamma=4\kappa\rho(A_Lr+B_Ls)-\kappa^2.
\]
Direct rational substitution gives
\[
 \alpha>7.2,\qquad -1.01<\delta<0,
                         \qquad 2\gamma<2.9.        \tag{33}
\]
More explicitly, the three positive reserves are
1790596312813223/(6*10^16),
4301237423/(6*10^11), and
15724418239/(3*10^11), respectively.

Write
\[
 H(t)=\frac{\alpha Q+\delta t(3Q-2t^2)}{(Q-t^2)^{3/2}}.
\]
Then \(R_L''=2\gamma-H\), and
\[
 H'(t)=\frac{3Q(\delta Q+\alpha t)}{(Q-t^2)^{5/2}}.
\]
Its minimum over the L interval is attained between .5 and .55:
the only possible interior minimum is at -delta Q/alpha, and
\(1.01Q/7.2<.55\), with reserve 437/600000.
On that shorter range, \(x<1.915\), so
\[
 H(t)-2.9>
 \frac{7.2Q-1.01(.55)(3Q-.5)}{1.915^3}-2.9
                      =\frac{25260617}{112363774}>0.            \tag{34}
\]
This proves concavity without subdividing the L arc.

Both endpoint values of RL are strictly positive. At t=.5,
use (30) and a0>1.41457; the resulting lower bound is
\[
 4\kappa\rho(.1404)\{r(.91457)-s/2\}
                  -(1-\kappa/2)^2
                     =\frac{337195714927}{5\cdot10^{13}}>0.
                                                               \tag{35}
\]
At t=b1+1/2, use (28)--(29):
\[
 4\kappa\rho(.026)\{r(.7984)-s(.8247)\}
                  -(1-\kappa(.8246))^2
                      =\frac{8311162591}{750000000000}>0.      \tag{36}
\]
Concavity proves RL>0 throughout L. Also D>0 there, since its
minimum is at the far endpoint and the brace in (36) is positive.
This establishes (7) on L.

### 7.3 The M arc below the threshold in (7)

Restrict M to \(t\le1/\kappa\). The function
\[
                       j_M-(1-\kappa t)^2
\]
is concave because x>1.72 and
\[
 2\kappa^2-\frac{A_MQ}{1.72^3}
                    =\frac{6835485131}{12721120000}>0.         \tag{37}
\]
At t=1/kappa it is positive by (31). At the L/M endpoint,
\[
 j_M>.028,qquad
 .028-(1-\kappa(.8246))^2
                     =\frac{1325240439}{250000000000}>0.      \tag{38}
\]
For the first inequality, substitution in (27) with
x<1.7988 and t<.8247 leaves the positive reserve
14219249/25000000000 above .028.
Thus \(j_M>(1-\kappa t)^2\) on the whole restricted arc.

Also x>1.72 gives
\[
 D>r(.72)-s/\kappa>.23,
 \qquad r(.72)-s/\kappa-.23=\frac{6277}{3090000}>0.
\]
Finally \(4\kappa\rho(.23)-1=1059/25000>0\), so
\[
 4\kappa\rho JD>4\kappa\rho(.23)(1-\kappa t)^2
                                     \ge(1-\kappa t)^2.
\]
At t=1/kappa, strict positivity follows directly from J,D>0.
The threshold b=1/kappa-1/2 is below .471, while the M/H junction
is above .5: at b=.5 its defining relation a=7b/3 gives the
corner-square sum 34/9<Q. Thus L and this restricted M arc cover
every b occurring in (7).

## 8. One polynomial for the positive owner-3 scalar

Return to G in (14). Put
\[
 \eta_0=\frac{39921}{100000},\quad
 \varepsilon=\frac1{100000},\quad \overline R=\frac{1979}{1000}.
\]
The actual eta lies between eta0 and eta0+epsilon. The derivative
in eta of the bracket in (14) has absolute value less than z:
\[
 (1-\cos z)+\frac{\sin z\,|\sin z-\eta|}
                     {\sqrt{Q-(\sin z-\eta)^2}}
 <\left(\frac7{20}+\frac4{19}\right)z<z.             \tag{39}
\]
Also, for u=sin z-eta0,
\[
 \sqrt{Q-u^2}\le\overline R-\frac{u^2}{2\overline R}.
\]
This is the tangent inequality for the square root, followed by
its monotonicity in the chosen radius upper bound.

For odd n and even m, let Sn and Cm denote the ordinary alternating
Taylor polynomials for sine and cosine, ending at their indicated
degrees. Set
\[
 B=\overline R-
                 \frac{3/4+\eta_0^2}{2\overline R}>0.
\]
Using \(\sin^3z=(3\sin z-\sin3z)/4\) and the double-angle
identities, (39) gives the following explicit degree-eleven lower
polynomial H, on the entire interval 0<=z<=.7:
\[
 \begin{split}
 G(z)\ge H(z):={}&(1-\kappa\varepsilon)z\\
 &+\kappa\left\{
 \eta_0(1-C_8(z))+\tfrac12S_{11}(2z)-B S_9(z)
 -\frac{S_9(3z)}{8\overline R}
 -\frac{\eta_0}{2\overline R}(1-C_{10}(2z))
 \right\}.                                           \tag{40}
 \end{split}
\]
All Taylor directions are fixed by the displayed signs.
They remain valid for 3z<=2.1. H(0)=0; write P(z)=H(z)/z.
This is one degree-ten polynomial with exact rational coefficients.

For a check that controls the whole interval at once, expand at
h=7/20:
\[
 P(h+w)=\sum_{j=0}^{10} A_jw^j,
 \qquad A_j=\sum_{i=j}^{10}p_i\binom{i}{j}h^{i-j},
 \qquad P(z)=\sum_{i=0}^{10}p_i z^i.
\]
Direct expansion of the fixed formula (40) yields
\[
 A_1+\sum_{j=2}^{10}j|A_j|h^{j-1}
 =-\frac{157996420929764587366847}
          {180560793600000000000000000}< -\frac1{1250},          \tag{41}
\]
so P is strictly decreasing on [0,.7]. Its right endpoint is
\[
 P(7/10)=\frac{117912021542920719381193}
                  {75233664000000000000000000}
                          >\frac3{2000}.             \tag{42}
\]
Equations (40)--(42) prove (15). The aggregate derivative bound is
for one printed polynomial on the entire interval; it is not a
subdivision certificate or a generated row inventory.

## 9. Completion and equality

At zero error, both original high projections in (2) are a-Y.
Thus (3) follows directly from J>=0, with the stated equality
condition. Sections 3--6 handle every nonzero error, both original
high owners, and every target allowed by the theorem, with strict
inequalities. This proves the complete quarter component (3).

The exact rational comparisons in this note have been reconstructed
independently of the numerical discovery of the potential. The
mathematical proof consists of the displayed circle identities,
original weak separating projections, whole-arc concavity, and one
whole-interval polynomial. No numerical search, mesh, table oracle,
Lean source change, compilation, or CI is a premise.
