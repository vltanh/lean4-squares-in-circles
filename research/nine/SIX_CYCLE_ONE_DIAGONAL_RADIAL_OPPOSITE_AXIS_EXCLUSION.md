# A radial opposite load with an owned endpoint axis: complete exclusion

**Status: complete whole-domain hand exclusion; root and separate independent full source, geometry and exact audits of all 88 coefficients passed.**

Work in \(79/40\le R\le\sqrt{1105}/16\), with the actual alternating component \(B-W-C-U_C-T-U_B-B\). W is its sole diagonal transmitter. T has two physical circle corners, while B,C each have one. The other-port normal at at least one of B,C is a loaded side axis.

**Theorem.** This complete axis-endpoint subfamily is impossible with the three actual extras. Together with the nonaxis endpoint theorem, it excludes every exactly-one-diagonal C6 whose only radial loaded body is opposite W.

No radial concurrence is assumed to lie in its square. Every original nonnegative circle weight, actual positive pair force, physical mask, and original shared application mean is retained.

## 1. A one-sided extension of the central sandwich lemma

Write \(\sigma=1/\sqrt2\) and \(W_0=\{(x,y):|x|+|y|\le\sigma\}\). Let an interior-disjoint unit E satisfy
\[
 E\subset[-1,\sigma]\times(-\infty,0]. \tag{1}
\]
For a unit normal \(N=(u,v)\), \(0\le u\le v\), put
\[
 L_0=(1-\sigma)u+(1+\sigma)v,\qquad L_1=1+\sigma v.
\]
Then
\[
 \min_E N\cdot p\le-\min(L_0,L_1). \tag{2}
\]

Here is the complete extension of Section3 of SIX_CYCLE_ONE_DIAGONAL_CENTRAL_HOLE_EMPTY.md. Choose E's axes \(e=(A,B),f=(-B,A)\), with A,B>=0 and A²+B²=1; put \(w=A+B,\ \mu=\max(A,B)\). Its center \((x,y)\) satisfies
\[
 -1+w/2\le x\le\sigma-w/2,\qquad y\le-w/2.
\]
Its halfwidth in N is \(H_N=(uA+vB+|vA-uB|)/2\), and put \(D_E=-ux-vy+H_N=-\min_E N\cdot p\).

A separating side axis directed W_0 to E has negative vertical component. Otherwise its support at a horizontal W_0 vertex puts E wholly in x<=-sigma or x>=sigma. The available horizontal interval then has width at most1-sigma<1, impossible for a unit. The purely upward case is impossible from y<=0. Thus the four complete possibilities are W_0's southeast/southwest diagonal axes, or E's southeast/southwest side axes. Horizontal zero-denominator endpoints are absent.

The W southeast and E southeast rows use only the unchanged bound \(x\le\sigma-w/2\). The exact calculations in Sections3.1 of that source apply without any change and give \(D_E\ge L_0\).

For the W southwest row, direct substitution of \(y\le-x-\sigma-\mu\) and \(x\ge-1+w/2\) gives
\[
 D_E\ge(v-u)(-1+w/2)+v(\sigma+\mu)+H_N. \tag{3}
\]
Set \(k=u/v\). If A>=kB, the difference between the right side and L_0, divided by v, is
\[
 w+\mu-2+k(\sigma-B). \tag{4}
\]
If B<=sigma this is nonnegative, because w+mu>=2. If B>=sigma, then mu=B and (4) decreases with k; here k<=A/B. Its lower endpoint value is \(g=2B-2+\sigma A/B\ge0\). Indeed
\[
 Bg=A\left[\sigma-\frac{2AB}{1+B}\right]\ge0,
\]
using \(2AB\le1,\ B\ge\sigma,\ 1/(1+\sigma)<\sigma\). If A<=kB, necessarily B>=sigma, and the corresponding difference is \(2B-2+\sigma k\ge g\ge0\). This proves \(D_E\ge L_0\) throughout the W southwest row.

For E's southwest axis, B>0 and
\[
 D_E\ge\frac{v(\sigma\mu+1/2)}B+
 \left(\frac{vA}B-u\right)x+H_N. \tag{5}
\]
When A<=kB the coefficient of x is nonpositive, so the unchanged upper x bound applies. This is exactly the second case of Section3.2 of the cited sandwich lemma, including its endpoint-minimum derivative proof; it gives \(D_E\ge\min(L_0,L_1)\).

When A>=kB, use the new lower x bound in(5). It simplifies to
\[
 D_E\ge u(1-B)+v\left[A+\frac{1+\sigma\mu-A}B\right]. \tag{6}
\]
This is at least L_1. To prove it subtract sigma v and let theta=arg(A,B), eta=arg(u,v).

If A<=B, the remaining expression is the scalar product of N with
\[
 V=\left(1-B,\ A+\frac{1-A}B\right).
\]
Both coordinates are nonnegative. Here eta lies in [theta,pi/2]. At eta=theta this scalar product equals1; at eta=pi/2 it is at least1. It is concave on that angle interval, so it is at least1 throughout.

If A>=B, the corresponding vector is
\[
 V=\left(1-B,\ A+\frac{1-(1-\sigma)A}B-\sigma\right).
\]
Again its coordinates are nonnegative, and eta is in [pi/4,pi/2]. The second coordinate is at least \(A+\sigma/B-\sigma\ge1\). At eta=pi/4 its scalar product is also at least1. For a full algebraic check, put delta=A-B>=0 and rho=1-sigma. Then
\[
 B(V_x+V_y-\sqrt2)
 =\delta\left[w-\rho-\frac{B\delta}{\sqrt2+w}\right]\ge0,
\]
because w-rho>=sigma and \(B\delta/(\sqrt2+w)\le B\le\sigma\). Concavity again proves the full interval. This establishes(6)>=L_1 and exhausts all separating axes. Thus(2) is proved for the whole one-sided strip.

## 2. Complete endpoint cover, retaining the axis mean

Use the actual diagonal frame
\[
 B=[-a,1-a]\times[b-1,b],\quad
 C=[c-1,c]\times[e-1,e],\quad a+c=2+\sqrt2,
\]
with actual W applications \((1-a,h),(c-1,h)\), h>0. Physical uniqueness gives b,e>1/2 and the strict diagonal avoidance convention gives
\[
 b-1<h<b,\qquad e-1<h<e. \tag{7}
\]
Put K=sqrt(R²-1/4), d=K-1 and r_0=sqrt(d²+1/4). As in the nonaxis radial-opposite theorem,
\[
 91/100<d<61/60,\quad r_0<23/20,\quad a,c>83/60>r_0. \tag{8}
\]

The full radial width-one support cover forces the T applications P,Q to its two distinct inner vertices. They cannot be the same inner vertex: in T's radial frame, at \(p=d e+\varepsilon f/2\) every strict outward port \(-c_i e+\varepsilon s_i f\), \(c_i,s_i>0\), has origin moment \(\varepsilon(ds_i+c_i/2)\). Two positive pair magnitudes at that vertex would have the same strict moment sign, contrary to T's original torque equation; each circle force has zero origin moment. Original endpoint force balance makes each other normal downward. A nonaxis outward horizontal component would put the T application beyond x=-a or x=c, contradicting norm r_0. Thus every nonaxis endpoint uses its inner lower vertex. Its proper unique concurrence and original positive W force give angle strictly between45 and90 degrees, exactly as in the nonaxis radial-opposite proof.

If both endpoints own axes, both normals are (0,-1), and their original bottom-side means have horizontal separation at least \(a+c-2=\sqrt2>1\). Their T applications retain that separation, impossible for the unit inner-side chord. Therefore exactly one endpoint owns an axis. Reflect and exchange B,C to make it C.

Write the B normal \(n_B=(x,-s)\), x=cos(alpha), s=sin(alpha), pi/4<alpha<pi/2, and the original C bottom mean as
\[
 p_C=(c-1+\zeta,e-1),\qquad0\le\zeta\le1.
\]
Then
\[
 P=(1-a+x,b-1-s),\qquad Q=(c-1+\zeta,e-2). \tag{9}
\]
No endpoint value of zeta has been removed.

Let \(t=(v,u)=(\cos\phi,\sin\phi)\) point from P to Q. The strict inner-vertex support of the vertical C normal gives
\[
 0<\phi<\pi/2-\alpha<\pi/4. \tag{10}
\]
The radial T inner normal is \(N=(-u,v)\), and its exact physical vertices are \(P=-dN-t/2,\ Q=-dN+t/2\). Thus
\[
 \begin{array}{ll}
 a=1-du+v/2+x,& b=1-dv-u/2+s,\\
 c=1+du+v/2-\zeta,& e=2-dv+u/2,
 \end{array} \tag{11}
\]
and the actual diagonal span yields
\[
 x=\sqrt2-v+\zeta,\qquad 0\le\zeta<v-\sigma. \tag{12}
\]
The proper unique B concurrence gives a>b. Also, using(8),(12), u+v>1 and sigma>7/10,
\[
 c-e>-1+\sigma+(d-1/2)(u+v)>11/100>0. \tag{13}
\]
So both diagonal endpoints satisfy the geometric premises a>b>1/2 and c>e>1/2.

## 3. The B circle identity bounds the entire tilt

The B circle equality gives
\[
 d=f(x,\phi):=
 \frac{1+x+s+\frac v2(1+x)-\frac u2(1+s)}
 {1+u(1+x)+v(1+s)},\qquad s=\sqrt{1-x^2}. \tag{14}
\]
For each fixed phi in(0,pi/4), f is strictly increasing for0<x<sigma. Here is a full derivative check. Put A=1+x, B_0=1+s, a_0=1+v/2, b_0=1-u/2 and k=x/s<1. Writing H=1+uA+vB_0, the derivative numerator is
\[
 H^2 f_x=a_0+u-k(b_0+v)+(v-u+1/2)(B_0+kA)>0.
\]
The first group exceeds \((3u-v)/2\ge-1/2\); the second exceeds1/2.

At x=s=sigma its upper endpoint is
\[
 F(\phi)=\frac{1+\sqrt2+\frac12(1+\sigma)(v-u)}
 {1+(1+\sigma)(u+v)}. \tag{15}
\]
This strictly decreases with phi, because v-u decreases and u+v increases on(0,pi/4).

If u>=3/8, evaluate this bound at phi=arcsin(3/8). There
\[
 u+v=(3+\sqrt{55})/8>13/10,\qquad
 v-u=(\sqrt{55}-3)/8<9/16.
\]
The ratio(15) is therefore less than91/100: after positive denominator clearing the exact margin is
\[
 \frac{91}{100}\left[1+\frac{13}{10}(1+\sigma)\right]
 -\left[1+\sqrt2+\frac9{32}(1+\sigma)\right]
 =\frac{3247-4393\sigma}{4000}
 >\frac{3247}{96000}>0,
\]
using sigma<17/24. This contradicts d>91/100. Consequently
\[
 0<u<3/8,\qquad 0<t_0:=\tan(\phi/2)<1/5. \tag{16}
\]

## 4. The original C circle and concurrence give a rational rectangle

Keep the same original mean zeta. Put w=1-zeta. The C circle identity in(11) solves linearly for d:
\[
 d=\frac{w^2+vw+3+2u}{2(1+2v-uw)}. \tag{17}
\]
The vertical C force line has horizontal coordinate Q_x=c-1+zeta. Its original unique concurrence, also on y=h, therefore gives
\[
 h=eQ_x/c,\qquad Y:=h+1-e=1-ew/c. \tag{18}
\]

Map the complete retained domain into the one closed rectangle
\[
 t_0=X/5,\quad u=\frac{2t_0}{1+t_0^2},\quad v=\frac{1-t_0^2}{1+t_0^2},\quad
 \zeta=(v-\sigma)Z_1,\qquad0\le X,Z_1\le1. \tag{19}
\]
The actual domain is a subset by(12),(16); this is not a subdivision.

Here are polynomial definitions over Q(sqrt2). Denote the rectangle variables by X,Z_1 and put
\[
 \begin{gathered}
 t_0=X/5,\quad Z=1+t_0^2,\quad U=2t_0,\quad V=1-t_0^2,\\
 J=(V-\sigma Z)Z_1,\quad W=Z-J,\\
 N_0=W^2+VW+3Z^2+2UZ,\qquad H=2[(Z+2V)Z-UW],\\
 C_0=(2W+V)H+2N_0U,\qquad E_0=(4Z+U)H-2N_0V.
 \end{gathered} \tag{20}
\]
Then
\[
 d=N_0/H,\quad c=C_0/(2HZ),\quad e=E_0/(2HZ),\quad
 Y=(ZC_0-WE_0)/(ZC_0). \tag{21}
\]
Every cleared pole is positive on the whole rectangle. Indeed v>=12/13, 0<=u<=5/13, sigma<=w<=1, so \(H=2Z^2(1+2v-uw)\ge(64/13)Z^2>0\). Also Z>0, N_0>0 and C_0>0.

The exact scalar polynomials are
\[
\begin{split}
 P_0={}&VW E_0+C_0[UW-\sqrt2\,UZ+(\sigma-1)VZ],\\
 P_1={}&VW E_0+C_0[Z^2+(\sigma-2)VZ-(\sigma+1)UZ+UW].
\end{split} \tag{22}
\]
For the actual inner-side depth \(D=v(1+Y)+u(\sigma+\zeta)\), direct substitution gives the exact target identities
\[
 P_0=Z^2C_0(L_0-D),\qquad P_1=Z^2C_0(L_1-D). \tag{23}
\]
Both polynomials have natural bidegree(10,3).

## 5. All 88 coefficient signs, with no boxes

For a bivariate polynomial P of degree at most(n,m), define
\[
 \beta_{ij}=\sum_{k\le i,\ell\le j}[X^kZ_1^\ell]P\,
 \frac{\binom{i}{k}}{\binom{n}{k}}\frac{\binom{j}{\ell}}{\binom{m}{\ell}}. \tag{24}
\]
The exact Bernstein identity is
\[
 P=\sum_{i=0}^{n}\sum_{j=0}^{m}\beta_{ij}\binom ni X^i(1-X)^{n-i}
 \binom mj Z_1^j(1-Z_1)^{m-j}.
\]
The basis is nonnegative and sums to1 on the one rectangle.

Every entry below is an exact lower bound on1000 beta_ij for n=10,m=3. All are positive.

|i|P0,j0|P0,j1|P0,j2|P0,j3|P1,j0|P1,j1|P1,j2|P1,j3|
|---|---:|---:|---:|---:|---:|---:|---:|---:|
|0|8727|8290|7623|6778|8727|8290|7623|6778|
|1|8142|7704|7041|6206|7931|7506|6858|6036|
|2|7566|7126|6470|5648|7172|6757|6126|5329|
|3|6992|6551|5904|5097|6442|6035|5421|4649|
|4|6418|5975|5337|4549|5738|5335|4737|3989|
|5|5837|5392|4764|3997|5055|4653|4069|3346|
|6|5244|4797|4181|3436|4387|3985|3414|2714|
|7|4633|4184|3580|2859|3732|3327|2767|2091|
|8|3998|3547|2958|2262|3086|2676|2128|1475|
|9|3332|2881|2307|1639|2447|2032|1496|865|
|10|2628|2179|1624|985|1812|1394|870|263|

The exact minima, both at(i,j)=(10,3), are
\[
 \min\beta(P_0)=\frac{-71016608+57020496\sqrt2}{9765625}>\frac9{10},\qquad
 \min\beta(P_1)=\frac{-76862240+56169152\sqrt2}{9765625}>\frac14. \tag{25}
\]
The standalone exact JS checker recomputes(20)--(24), every coefficient and table comparison, both minima and strict floors, the inverse Bernstein-to-power identities, the original C circle identity, the C mean identity and both target identities(23). It uses integer/rational pairs for Q(sqrt2), deciding mixed signs by squaring positive integers. No floating-point sign is used. The formulas and table constitute a whole-domain algebraic certificate; the code is a reproducibility supplement.

Reproducibility supplements: [C6_RADIAL_OPPOSITE_AXIS_CERTIFICATES.js](C6_RADIAL_OPPOSITE_AXIS_CERTIFICATES.js) and [C6_RADIAL_OPPOSITE_AXIS_CERTIFICATES.json](C6_RADIAL_OPPOSITE_AXIS_CERTIFICATES.json).

Therefore P0,P1>0 on the whole rectangle, and positivity of the denominator in(23) gives D<L0,L1.

## 6. Actual central routing and the completion contradiction

Translate the actual W center to zero. The six contact vertices of the actual cycle are
\[
 (-\sigma,0),\ (\sigma,0),\ (\sigma+\zeta,-Y),\ Q,\ P,\ (-\sigma,-Y_B),
\]
where
\[
 Q=(\sigma+\zeta,-Y-1),\qquad P=(-\sigma+x,-Y_B-s). \tag{26}
\]
Here 0<Y,Y_B<1 and 0<=zeta<1-sigma. All vertices therefore lie in \([-\sigma,1]\times(-\infty,0]\).

The actual T inner side is the supporting line \(N\cdot p=-D\), with N=(-u,v), D as in(23). The B inner vertex lies strictly above it by \(-N\cdot n_B=ux+vs>0\). The C bottom mean lies above Q by v>0. The C diagonal application has a still larger projection than that bottom mean by u zeta+vY>0, and the B diagonal application by vY_B>0. Thus all six contact vertices lie on its upper side.

The full compact-interior winding theorem of CONTACT_RING_HOLE_AREA.md and SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md puts every whole central extra E in the same horizontal strip and upper half-plane of this line, with y<=0. It also remains interior-disjoint from the actual W. This applies to every weak/shared routing limit and the entire central free union. Reflect x to apply the proved one-sided sandwich lemma(1)--(2), now with normal(u,v). It yields D>=min(L0,L1), contradicting(23)--(25). The whole central free union is empty.

The complete geometric exterior-pocket proof of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md applies directly: the displayed parallel endpoint frames, circle equalities, strict diagonal means, a>b>1/2 and c>e>1/2 have all been proved. The original unique concurrences give h>=b(1-1/a) and h>=e(1-1/c), the latter also immediate from(18) and zeta>=0. These are exactly that separating-axis proof's endpoint premises; the mask at T enters none of its argument or certificates. Thus the original diagonal exterior pocket is empty.

Each of the other two actual exterior pockets is incident to radial T and has capacity at most one by RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md. The whole physical pocket decomposition retains all three extras, which consequently would have to fit into two pockets of total capacity at most two. This is impossible.

Together with the two-nonaxis endpoint theorem, the full side-axis cover above closes the entire physical radial-opposite one-diagonal C6 family, including original axis means at endpoints and every zero individual radial corner weight. The case with the sole radial body incident to W remains separate. No radial-concurrence containment, change of mean or force, motion, sampled angle box, Lean compilation or CI is used.
