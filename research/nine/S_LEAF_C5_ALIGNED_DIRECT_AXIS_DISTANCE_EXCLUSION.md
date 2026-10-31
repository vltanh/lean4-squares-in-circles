# The entire aligned strict-west / owned-axis family violates the actual return distance

Date: October 26, 2026.

**Status: complete analytic proof, freshly independently reviewed.** See
REVIEW_S_C5_ALIGNED_AXIS_DISTANCE_RECOVERY_BLOCK_2026_10_26.md.
This reconstruction uses a uniform distance argument; no historical
review of the missing manuscript is reused.

Keep the original S-leaf C5 load13 component A-B-V-C-U-A, its genuine
S leaf, all nine actual squares, all original positive forces, true
degrees, normals, application means, circle masks, individual weights
and both transmitter sliders. The root's third force is retained.

The actual aligned A-to-B normal is strictly west and down, and B owns
that original direct normal as a side axis. Use the complete accepted
chart and reductions in S_LEAF_C5_ALIGNED_STRICT_WEST_REDUCTION.md:

\[
\begin{gathered}
\epsilon=1/60,\quad 0<\delta<\epsilon,\quad d=1+\delta,
\quad R^2=(d+1)^2+1/4,\\
1/3<q<2,\quad 0<s<1/4,\quad c=\sqrt{1-s^2},\\
a=qs,\quad b=1-a,\quad \delta=q(1-c),
\quad a^2=2\delta q-\delta^2,\\
F=(\delta,-b),\quad M=\sqrt{q^2+1-2qs},\\
m=(-(q-\delta),-b)/M,\quad v=(b,-(q-\delta))/M,\\
B=[X,X+1]m+[Y-1,Y]v,\\
X=\frac{1-2qs+q^2(1-c)}M,\quad
T=\frac{q(1-qs)}M,\quad
Y=\sqrt{R^2-(X+1)^2}>1/2.
\end{gathered}
\tag{1}
\]

Here F is the unchanged direct contact and T is its actual transverse
coordinate. In particular this is the whole original owned mean
interval, including its permitted endpoints. The actual radial C's
unchanged return port is

\[
Q=(-dc-s/2,ds-c/2).
\tag{2}
\]

The actual reserve-one C-to-B channel requires

\[
                         |W-Q|\ge1\quad\hbox{for every }W\in B.
\tag{3}
\]

**Theorem.** The entire physical feature (1) is impossible. The proof
uses a point of the original B and does not specialize its original
return owner, mean or slider.

## 1. An actual clamped point of B

Write

\[
Q_m=Q\cdot m=\frac{d(q-s)+c/2}{M},\qquad
Q_v=Q\cdot v=\frac{-dc+(q-s)/2}{M},
\]
\[
H=Y-1-Q_v,\qquad
L=X-Q_m=\frac{N}{M},\qquad
N=1-q-c/2+s[1-q(1+c)].
\tag{4}
\]

The actual constraints imply a<13/50, because
a^2<4/60<(13/50)^2. Hence M<sqrt(5)<12/5 and the numerator
of X exceeds 1-2a>12/25, so X>1/5. Also
\[
Q_m\le|Q|=\sqrt{d^2+1/4}<6/5<X+1.
\]
Consequently the point
\[
W=\max(X,Q_m)m+(Y-1)v
\tag{5}
\]
belongs to the actual B, and
\[
                    |W-Q|^2=H^2+\max(L,0)^2.
\tag{6}
\]

There is also a uniform lower bound on H. Since c>24/25,
\[
V:=MQ_v=-dc+(q-s)/2<1/25.
\]
The actual M^2>1/9+12/25>1/4 gives Q_v<2/25. Since Y>1/2,
\[
                            H>-29/50.
\tag{7}
\]
Thus every positive upper bound for H below will also bound |H|,
provided it exceeds29/50.

## 2. One monotone comparison controls the whole two-dimensional domain

For scalar comparison only, extend (1),(4) to the connected rectangle
\[
                    1/3\le q\le2,\qquad0\le s\le1/4,
\tag{8}
\]
setting c=sqrt(1-s^2), delta=q(1-c), a=qs and d=1+delta.
No actual packing or application mean is moved by this comparison.

Throughout (8), b>=1/2 and 0<=delta<a when s>0. Therefore
rho^2=delta^2+b^2<=1, with the appropriate strictness, and
0<X<1, M^2>=q^2, Y>1/2. All radicals and denominators used in
the following differentiations are consequently positive.

Direct differentiation gives
\[
X_s=\frac qM\left[-1+\frac{qs}{c}-\frac{q^2c}{M^2}\right]<0,
\tag{9}
\]
since qs/c<25/48. As R_s>=0, this implies Y_s>0. Moreover
\[
V_s=s\left[\frac{1+q}{c}-2q\right]-\frac12<-\frac{23}{72}.
\]
Indeed the bracket decreases with q, and at q=1/3 it is less
than13/18. Since V<1/25 and q/M^2<=1/q<=3,
\[
(Q_v)_s=\frac{V_s+Vq/M^2}{M}<0,
\qquad -\frac{23}{72}+\frac3{25}=-\frac{359}{1800}<0.
\]
It follows on the entire connected rectangle that
\[
                              H_s>0.
\tag{10}
\]

Put
\[
c_0=\sqrt{15}/4,\qquad
q_* =\frac{\epsilon}{1-c_0}=\frac{4+\sqrt{15}}{15}.
\tag{11}
\]
Then 13/25<q_*<21/40 and q_*>1/2. For an actual point of (1),
(10) gives exactly the two boundary comparisons
\[
\begin{cases}
H(q,s)\le H(q,1/4),&q\le q_*,\\
H(q,s)\le H(q,s_\epsilon(q)),&q\ge q_*,
\end{cases}
\quad
s_\epsilon(q)=\sqrt{2\epsilon/q-(\epsilon/q)^2}.
\tag{12}
\]
Both comparison boundaries are inside (8). The second has
delta=epsilon. The actual delta<epsilon condition is used only in
the direction which makes this an upper bound.

## 3. The positive horizontal gap has three whole-interval bounds

We have
\[
N_q=-[1+s(1+c)]<0,\qquad M_q=(q-s)/M>0.
\]
Where N>=0, L_q<0; hence max(L,0) is nonincreasing in q on (8).
For q<=1/2,
\[
N_s=1-q(1+c)+\frac{s/2+qs^2}{c}\ge0,
\qquad M_s=-q/M<0.
\]
Thus its positive part is nondecreasing in s there. These facts give
\[
\begin{array}{c|c}
q\text{ interval}&\max(L,0)\text{ upper bound}\\ \hline
[1/3,2/5]&7/25\\
[2/5,1/2]&1/5\\
[1/2,2]&1/48.
\end{array}
\tag{13}
\]

For completeness these are fixed endpoint comparisons, not a sign
grid. The two useful bounds on c_0 are
\[
              \frac{387}{400}<c_0<\frac{31}{32}.
\tag{14}
\]
At (q,s)=(1/3,1/4), M^2=17/18>(97/100)^2 and
N=5/6-7c_0/12<1291/4800. Hence
L<1291/4656<7/25. At (2/5,1/4), M>489/500 and
N=3/4-3c_0/5<339/2000, giving L<1/5. Finally
\[
L(1/2,1/4)=5(1-c_0)/8<1/48,
\]
because 1-c_0<1/30. Monotonicity in q gives this last bound for
every q>=1/2 even though monotonicity in s was required only at q=1/2.

## 4. The entire constant-s boundary is increasing in q

Set s=1/4 and omega=1-c_0. Here
\[
3/100<\omega<1/30,\quad
M^2=q^2-q/2+1,\quad
A=1-q/2+\omega q^2,\quad X=A/M,
\]
\[
Y^2=(2+\omega q)^2+1/4-(X+1)^2,
\quad -Q_v=N_v/M,
\quad N_v=c_0+1/8-q(1/2-c_0\omega)>0.
\tag{15}
\]
On 1/3<=q<=q_*, we have
97/100<M<1007/1000 and
\[
X_q=\frac{\omega q^2(q-3/4)+(2\omega-7/8)q-1/4}{M^3}
<-1/2.
\tag{16}
\]
The numerator is at most -187/360, and
\[
\frac{187}{360}-\frac12(1007/1000)^3
 =\frac{159673913}{18000000000}>0.
\]
In particular X decreases and Y increases, independently of any
claim about H. The endpoint bounds established in section5 give
X+1>87/50 and Y<57/50 on this whole boundary. Consequently
\[
Y_q=\frac{(d+1)\omega-(X+1)X_q}{Y}>
\frac{2(3/100)+(87/50)/2}{57/50}=\frac{31}{38}.
\tag{17}
\]

Also N_v<47/50: using (14), omega<1/30 and q>=1/3 gives
N_v<35/32-7/45=1351/1440<47/50. Therefore
\[
(Q_v)_q
=\frac{1/2-c_0\omega}{M}
 +\frac{N_v(q-1/4)}{M^3}
<\frac{50}{97}+\frac{47}{50}\frac{11}{40}(100/97)^3
=\frac{728950}{912673}<\frac45.
\tag{18}
\]
The last gap is5942/4563365. Thus
\[
                              H_q>3/190>0
\tag{19}
\]
throughout the constant-s boundary, including both endpoints by
continuity. This is a whole-interval derivative statement.

## 5. Three explicit boundary values

All comparisons here use positive quantities before squaring.

At q=2/5, M^2=24/25 and
\[
489/500<M<49/50,\quad d<1013/1000,
\quad A>161/200,\quad X>23/28.
\]
It follows that Y<993/1000. Since
c(1+(2/5)(1-c)) is increasing for the c range in (14),
\[
-Q_v<\frac{(31/32)(81/80)-3/40}{489/500}
 =\frac{2319/2560}{489/500}<927/1000.
\]
The two final comparison reserves are
\[
(993/1000)^2-\{(2013/1000)^2+1/4-(51/28)^2\}
  =3631/2450000,
\]
\[
927/1000-(2319/2560)/(489/500)=1991/2608000.
\]
Hence
\[
                            H(2/5,1/4)<23/25.
\tag{20}
\]

At q=1/2, M=1 and X=1-c_0/4. The exact identities are
\[
Y^2=685/256-3c_0/2,
\quad -Q_v=3c_0/2-19/32.
\]
Using (14) gives Y<111/100 and -Q_v<55/64. The first squared
reserve is1211/160000. Therefore
\[
H(1/2,1/4)<111/100-1+55/64=1551/1600<39/40,
\tag{21}
\]
with final gap9/1600.

At q=q_*, delta=epsilon and
\[
787/1500<q_*<21/40,\quad
503/500<M<1007/1000,\quad R^2=15541/3600.
\]
Since A=1-29q_*/60>597/800,
\[
X>2985/4028>37/50,\quad Y<567/500<57/50.
\tag{22}
\]
The M comparisons have squared reserves1019/1125000 and231/250000;
the X comparison has reserve107/100700. For Y,
\[
(567/500)^2-\{15541/3600-(1+2985/4028)^2\}
 =708213149/2281610250000>0.
\]
Finally
\[
-Q_v<\frac{(61/60)(31/32)-(787/1500-1/4)/2}{503/500}
 <843/1000,
\]
where the last gap is991/2012000. Thus
\[
                           H(q_*,1/4)<977/1000.
\tag{23}
\]
These fixed radical enclosures and (16) supply the X,Y bounds used
in section4 without relying on its later conclusion (19).

## 6. A fixed-delta derivative reduces the whole remaining boundary

On the second comparison boundary, delta=epsilon is fixed and
\[
q=(a^2+\epsilon^2)/(2\epsilon),\quad b=1-a,
\quad \theta=\arctan((q-\epsilon)/b).
\]
Thus m=(-sin(theta),-cos(theta)), v=(cos(theta),-sin(theta)).
If n=(-cos(phi),sin(phi)), then
phi=2 arctan(epsilon/a) and phi_a=-1/q. With F=(epsilon,-b),
\[
X_a=-\cos\theta-T\theta_a=-T(\theta_a+1/q),
\]
\[
(Q_v)_a=(\theta_a+1/q)Q_m,
\qquad
Y_a=(X+1)T(\theta_a+1/q)/Y.
\]
Consequently
\[
H_q=\left(\theta_q+\frac{\epsilon}{aq}\right)
\left[\frac{T(X+1)}Y-Q_m\right],
\quad
\theta_q=\frac{b+(q-\epsilon)\epsilon/a}{M^2}>0.
\tag{24}
\]
Every identity differentiates the exact coupled scalar boundary.

### 6.1. A single quartic bounds the first term in the bracket

For q>=q_*>13/25,
a^2>307/18000>(13/100)^2. Thus
\[
\rho^2=b^2+\epsilon^2<(87/100)^2+1/3600<19/25,
\qquad T^2=\rho^2-X^2.
\tag{25}
\]
For every X>=0,
\[
\mathcal Q(X):=68/25-(7/5-X^2)(X+1)^2>0.
\tag{26}
\]
Indeed, writing y=X-5/8>=-5/8, exact expansion gives
\[
\mathcal Q=y^2\left[y^2+\frac92y+\frac{911}{160}\right]
 +\frac{13}{640}y+\frac{5593}{102400}.
\]
The bracket is increasing on y>=-5/8 and its left endpoint exceeds3.
Therefore
\[
\mathcal Q\ge3y^2+(13/640)y+5593/102400>0,
\]
because its minimum is53659/983040>0. Combining (25),(26),
\[
(T^2+16/25)(X+1)^2
 <(7/5-X^2)(X+1)^2
 <68/25\le(16/25)R^2.
\]
Since T,X+1,Y are positive, this is precisely
\[
                              T(X+1)/Y<4/5.
\tag{27}
\]

### 6.2. The whole tail q>=3/5 is decreasing

Here c=1-epsilon/q>=35/36 and s^2<1/18<(17/72)^2.
Also a>13/100 gives M^2<q^2+37/50. Hence
\[
Q_m>\frac{q-17/72+35/72}{\sqrt{q^2+37/50}}
=\frac{q+1/4}{\sqrt{q^2+37/50}}>4/5.
\tag{28}
\]
For the last inequality, the squared difference
(q+1/4)^2-(16/25)(q^2+37/50) increases for q>=0 and equals
37/2000>0 at q=3/5. Equations (24),(27),(28) prove
\[
                              H_q<0\quad(3/5\le q\le2).
\tag{29}
\]

### 6.3. One derivative bound covers the short connecting interval

For q_*<=q<=3/5, we have 13/100<a<3/20, q>13/25,
s<=1/4, c>24/25. Therefore
\[
d(q-s)+c/2>q+23/100+(1/60)(13/25-1/4)
=q+469/2000>q+15/64.
\]
Together with M^2<q^2+37/50 this gives
\[
Q_m>\frac{q+15/64}{\sqrt{q^2+37/50}}>3/4.
\tag{30}
\]
The squared comparison increases for q>=0 and at q=13/25 has
reserve1873/2560000>0. Further, M^2>q^2+7/10, so
\[
\theta_q<\frac{1+(3/5)(5/39)}{(13/25)^2+7/10}
=\frac{17500}{15769},\qquad
\frac{\epsilon}{aq}<\frac{125}{507}.
\]
Their sum is834125/614991<3/2, with gap176723/1229982.
If the bracket in (24) is negative then H_q<0. Otherwise
(27),(30) bound it by1/20. In either case
\[
                              H_q<3/40.
\tag{31}
\]
Since 3/5-q_*<2/25, integrating this whole-interval bound from
(23), and then using (29), proves
\[
H(q,s_\epsilon(q))<977/1000+(3/40)(2/25)
 =983/1000<99/100\quad(q_*\le q\le2).
\tag{32}
\]
For 1/2<=q<=q_*, (19),(23) already give the stronger bound977/1000.

## 7. The unchanged reserve-one channel is contradicted in every case

Use (12),(19)--(23),(32), together with (7),(13), in the exact
actual-point identity (6). The three broad intervals give
\[
\begin{array}{c|c|c|c}
q&|H|\text{ bound}&\max(L,0)\text{ bound}&1-|W-Q|^2\text{ lower bound}\\ \hline
(1/3,2/5]&23/25&7/25&47/625\\
[2/5,1/2]&39/40&1/5&3/320\\
[1/2,2)&99/100&1/48&28031/1440000.
\end{array}
\tag{33}
\]
Every reserve is positive. Thus the actual point W of the original
B has |W-Q|<1, contradicting (3). The full owned-axis family is
excluded, including its actual mean endpoints and every permissible
return feature and transmitter position.

Together with the complete original feature cover in
S_LEAF_C5_ALIGNED_STRICT_WEST_REDUCTION.md and the strict-vertex
exit S_LEAF_C5_ALIGNED_STRICT_DIRECT_VERTEX_EXCLUSION.md, this
closes the entire aligned strict-west root-normal family. The
aligned vertical root-normal family is a separate pocket argument.
No physical force, load, square or boundary weight was removed.
The proof adds no adaptive subdivisions, parameter grid or numerical
root certificate; all scalar signs and comparisons are displayed
above. No Lean compilation or CI was run.
