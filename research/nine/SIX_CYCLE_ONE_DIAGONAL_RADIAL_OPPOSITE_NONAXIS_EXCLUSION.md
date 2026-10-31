# Radial opposite load with two nonaxis diagonal endpoints: complete exclusion

**Status: complete whole-domain hand exclusion; root and separate independent full source, geometry and exact-reserve audits passed.**

Work in \(79/40\le R\le\sqrt{1105}/16\), with the common selected physical certificate and the actual alternating component
\[
 B-W-C-U_C-T-U_B-B.
\]
W is the only diagonal transmitter; U_B,U_C are actual unloaded degree-two side-normal transmitters. T has two physical circle corners, B and C each one. Assume the other-port normals of B and C are both nonaxis in their common displayed square frame.

**Theorem.** This entire subfamily is impossible with its three actual completion squares. Its central free union and diagonal exterior pocket are empty; each of its two side pockets has capacity at most one.

The proof never assumes that a radial concurrence belongs to its square. The original circle weights, including zero individual weights, actual pair forces and all shared means remain fixed.

## 1. The actual endpoint and radial-vertex domain

Use the physical diagonal endpoint-frame theorem and the compatible diagonal avoidance convention. Normalize
\[
 B=[-a,1-a]\times[b-1,b],\quad
 C=[c-1,c]\times[e-1,e],\qquad
 a+c=L:=2+\sqrt2,
\]
with diagonal applications \((1-a,h),(c-1,h)\), \(h>0\). The physical uniqueness and endpoint-center signs give \(b,e>1/2\), and the diagonal applications are strict side-interior points:
\[
 b-1<h<b,\qquad e-1<h<e. \tag{1}
\]
Both circle corners have norm R.

Put
\[
 K=\sqrt{R^2-1/4},\qquad d=K-1,\qquad r_0=\sqrt{d^2+1/4}.
\]
The whole radius interval gives
\[
 91/100<d<61/60,\qquad r_0<23/20. \tag{2}
\]
The lower bound follows from \(K^2-(191/100)^2\ge101/40000>0\). Since \(a,c<K\) and \(a+c=L\),
\[
 a,c>L-K>\sqrt2-1/60>83/60>r_0. \tag{3}
\]

The complete radial width-one support cover in RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md forces both applications on T to its two distinct inner vertices. Denote them P,Q. Their norms are r_0 and their separation is exactly one. They cannot be the same inner vertex: in T's radial frame, at \(p=d e+\varepsilon f/2\) every strict outward port \(-c_i e+\varepsilon s_i f\), \(c_i,s_i>0\), has origin moment \(\varepsilon(ds_i+c_i/2)\). Two positive pair magnitudes at that vertex would have the same strict moment sign, contrary to T's original torque equation; each circle force has zero origin moment.

The original B force balance makes its other normal strictly downward, since its unique circle corner has positive height b and its W force is horizontal. A negative horizontal component would put its application at the outer lower vertex \((-a,b-1)\); reserve one would then give \(P_x<-a\), contradicting \(|P|=r_0<a\). The assumed nonaxis condition excludes a zero horizontal component. Thus its application is the inner lower vertex and its normal is \(n_B=(\cos\alpha,-\sin\alpha)\). Likewise
\[
 n_C=(-\cos\beta,-\sin\beta),\qquad
 P=(1-a,b-1)+n_B,\quad Q=(c-1,e-1)+n_C. \tag{4}
\]
Initially \(0<\alpha,\beta<\pi/2\).

The unique B concurrence is \(q_B=(-ah/b,h)\). Its proper ray and original positive W force give
\[
 Y_B=h+1-b=\frac{a-b}{a-b\cot\alpha},\qquad a-b\cot\alpha>0. \tag{5}
\]
Because \(Y_B>0\), we get a>b. More explicitly, with \(t_B=1-h/b>0\), the proper B ray has positive components \(1-at_B\) and \(1-bt_B\); the second exceeds the first. Therefore \(\alpha>\pi/4\). Reflection gives c>e and \(\beta>\pi/4\). We have proved directly
\[
 a>b>1/2,\quad c>e>1/2,\quad \pi/4<\alpha,\beta<\pi/2. \tag{6}
\]
No turn bound at T was used. Also the original unique concurrence lies in B,C, giving
\[
 h\ge b(1-1/a),\qquad h\ge e(1-1/c). \tag{7}
\]

## 2. Exact radial inner-side equations

Write the unit direction from P to Q as \(t=(v,u)=(\cos\phi,\sin\phi)\). Its first coordinate is positive, since \(Q_x-P_x=\sqrt2-\cos\alpha-\cos\beta>0\). The interior of T lies below this directed side: its inward normal has positive scalar product with both n_B,n_C, which is impossible for a normal with nonnegative vertical component. Thus the normal toward the origin is \(N=(-u,v)\), and
\[
 P=-dN-\tfrac12t,\qquad Q=-dN+\tfrac12t. \tag{8}
\]
The strict inner-vertex cones give
\[
 \beta-\pi/2<\phi<\pi/2-\alpha,\qquad |\phi|<\pi/4. \tag{9}
\]
Reflect the complete configuration and interchange B,C if needed to arrange \(u\ge0\). Thus \(v>1/\sqrt2\).

Put
\[
 x=\cos\alpha,\quad y=\cos\beta,\quad s=\sin\alpha,\quad z=\sin\beta,\quad M=x+y,\quad U=s+z,\quad\Delta=x-y.
\]
Equation(4) and the actual unit chord give
\[
 M=\sqrt2-v, \tag{10}
\]
and
\[
\begin{array}{ll}
 a=1-du+v/2+x,&b=1-dv-u/2+s,\\
 c=1+du+v/2+y,&e=1-dv+u/2+z.
\end{array} \tag{11}
\]
In particular \(M\in[\sqrt2-1,1/\sqrt2)\), \(U>\sqrt2\). Since \(s-z=-M\Delta/U\), subtracting the two circle equalities \(a^2+b^2=c^2+e^2=(d+1)^2+1/4\) gives the exact identity
\[
 u\left[d(2+M)+1+\frac U2\right]
 =\Delta\left[1+\frac v2+(dv-1)\frac M U\right]. \tag{12}
\]
For direct verification before subtracting, the B equality is
\[
 d[1+u(1+x)+v(1+s)]
 =1+x+s+\tfrac v2(1+x)-\tfrac u2(1+s),
\]
and C has u replaced by -u, x,s by y,z.

The right bracket E in(12) is positive: \(M/U<1/2\) and \(E>1-M/U>1/2\). Consequently \(\Delta\ge0\), with equality when u=0.

## 3. A whole-domain tilt estimate, with exact rational reserves

We prove
\[
 0\le u<1/6,\quad v>59/60,\quad0<y<13/60,\quad z>39/40. \tag{13}
\]
If u=0 the first part is immediate and the later estimates follow as below. Suppose u>0.

By(2), \(M>2/5\), \(U>7/5\), \(M/U<1/2\), one has
\[
 d(2+M)+1+U/2>193/50,\qquad E<181/120.
\]
Since
\[
 193/50-\frac52\frac{181}{120}=\frac{107}{1200}>0,
\]
equation(12) gives \(\Delta>(5/2)u\). Also \(\Delta<M\). The function
\[
 f(u)=\frac{\sqrt2-\sqrt{1-u^2}}u
\]
is strictly decreasing for \(0<u<1/\sqrt2\), since its derivative has the sign of \(1/v-\sqrt2<0\). At \(u=1/5\),
\[
 f(1/5)=5\sqrt2-\sqrt{24}<85/12-24/5=137/60<5/2.
\]
Therefore u<1/5.

Now \(v>39/40\), so \(M<53/120\). For a fixed M, concavity of \(r\mapsto\sqrt{1-r^2}\) gives
\[
 U\ge1+\sqrt{1-M^2}>189/100,
\]
because
\[
 1-(53/120)^2-(89/100)^2=4619/360000>0.
\]
Use \(d>91/100\), \(\sqrt2>24/17\), and the preceding bounds to obtain
\[
 d(2+M)+1+U/2>563/136,\qquad E<3/2+\frac1{60}\frac{53/120}{189/100}=20465/13608.
\]
The exact margin
\[
 \frac{563}{136}-\frac{11}{4}\frac{20465}{13608}=\frac{3697}{925344}>0
\]
gives \(\Delta>(11/4)u\). But
\[
 f(1/6)=6\sqrt2-\sqrt{35}<17/2-23/4=11/4.
\]
Therefore u<1/6. This also yields \(v^2>35/36>(59/60)^2\) with difference19/3600.

Since \(\Delta\ge0\), (10) gives \(y\le M/2<(17/12-59/60)/2=13/60\). Finally
\[
 1-(13/60)^2-(39/40)^2=7/2880>0
\]
proves \(z>39/40\), completing(13). All comparisons use the entire continuous angle interval; there is no subdivision or sampled premise.

## 4. The actual C concurrence gives a short height offset

Equations(2),(11),(13) imply
\[
 e>1-61/60+39/40=23/24,\qquad
 c<1+61/360+1/2+13/60=679/360,\qquad k:=y/z<2/9. \tag{14}
\]
By the original unique C concurrence,
\[
 Y:=Y_C=h+1-e=\frac{c-e}{c-ek}. \tag{15}
\]
The denominator is positive by its original positive W force. Now
\[
 e(7-4k)-3c>
 \frac{23}{24}\frac{55}{9}-\frac{679}{120}
 =\frac{107}{540}>0.
\]
After multiplying(15) by its positive denominator this is exactly
\[
 Y<4/7. \tag{16}
\]

## 5. The whole central region has incompatible support bounds

Translate the actual W center to the origin and put \(\sigma=1/\sqrt2\). Its six actual contact vertices, in cycle order, are
\[
 (-\sigma,0),\ (\sigma,0),\ (\sigma,-Y_C),\ Q,\ P,\ (-\sigma,-Y_B),
\]
where
\[
 P=(-\sigma+x,-Y_B-s),\qquad Q=(\sigma-y,-Y_C-z). \tag{17}
\]
Every vertex lies in \(\{|X|\le\sigma,\ Y_{\rm coord}\le0\}\). The actual T inner side is a supporting line of the entire contact polygon:
\[
 N\cdot X=-D,\qquad D=v(Y+z)+u(\sigma-y). \tag{18}
\]
Indeed \(N=(-u,v)\) and the formula follows by evaluating at Q. The B inner vertex lies strictly above this line because \(-N\cdot n_B=ux+vs>0\); the C inner vertex lies strictly above it because \(-N\cdot n_C=vz-uy>0\), by the strict T normal cone. Their two corresponding W vertices have still larger projections, by adding vY_B or vY_C.

The full compact-interior winding argument of CONTACT_RING_HOLE_AREA.md and SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md therefore puts any whole central extra E in
\[
 |X|\le\sigma,\qquad Y_{\rm coord}\le0,\qquad\min_E N\cdot X\ge-D. \tag{19}
\]
This remains true for the entire weak central free union and every genuine shared junction. The extra is interior-disjoint from the actual W.

Reflect horizontally and apply the radius-free unit-square sandwich lemma, Section3 of SIX_CYCLE_ONE_DIAGONAL_CENTRAL_HOLE_EMPTY.md. For
\[
 L_0=(1-\sigma)u+(1+\sigma)v,\qquad L_1=1+\sigma v,
\]
it gives \(D\ge\min(L_0,L_1)\).

Both reverse strict inequalities follow from our whole bounds. First \(vz-uy\le1\), so
\[
 D-L_1\le v(Y-\sigma)+\sigma u<0. \tag{20}
\]
For the last sign, \(u/v<10/59\), while
\[
 \sigma(1-u/v)>\frac7{10}\frac{49}{59}=\frac{343}{590}>\frac47>Y;
\]
the middle margin is41/4130.

Second, using z<=1 and y>0,
\[
 D-L_0\le v(Y-\sigma)+u(\sqrt2-1)
 <-\frac{59}{60}\frac9{70}+\frac16\frac5{12}
 =-\frac{359}{6300}<0. \tag{21}
\]
Here \(\sigma>7/10\), \(\sqrt2-1<5/12\). Equations(20),(21) contradict the sandwich lemma. Thus the entire central free union has capacity zero.

## 6. The original completion budget closes this subfamily

The complete separating-axis proof in Sections1--7 of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md uses only the following geometric endpoint premises: the actual displayed parallel endpoint units and diagonal W; \(a+c=2+\sqrt2\), \(a^2+b^2=c^2+e^2=R^2\); \(a>b>1/2,c>e>1/2\); the strict side-interior inequalities(1); and the two original concurrence inequalities(7). All have been proved directly here. The radial mask at T enters none of that exterior-pocket argument or its four whole-rectangle certificates. Its actual physical cap and horizontal-strip routing theorem is also mask-independent. Consequently the original diagonal exterior pocket is empty for the present family. This is direct use of that proved geometric argument, not a limit from a unique T mask.

Both remaining exterior pockets are incident to radial T. RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md therefore gives capacity at most one for each, with their original channels, means and boundary arcs. Every actual extra is either in the whole central free union or one of these three exterior pockets, by SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. There are three actual extras, but their total available capacity is at most two. Contradiction.

This closes every exactly-one-diagonal C6 with radial opposite load T and two nonaxis other-port normals at the unique diagonal endpoints. If one endpoint owns its horizontal bottom side, its original bottom-side mean remains a separate case; it has not been forced to a vertex or included by continuity. No claim is made here about a radial body incident to W. No radial-concurrence containment, altered weight, moved square, sampled angle box, Lean compilation or CI is used.
