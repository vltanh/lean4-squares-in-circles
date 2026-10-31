# Positive end-triangle pressure with one articulation owner and one tip owner

**Status: complete hand implication; root and separate independent full hand audits passed.**
Work in
\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Let A,B,C be an actual unit-square contact triangle. The two tips
B,C are positive degree-two circle-loaded bodies; A may have other
positive neighbors. Suppose the actual AB normal n is a side axis
of A and the AC contact is a singleton lying in the relative
interior of a C side. Write m for its normal from A into C.

**Theorem.** In the compatible selected certificate,
\[
             c_A\cdot M>0,\qquad
       M=F_B+F_C,\quad F_S=2\sum_{z\text{ on }S}\lambda_z z.
\tag{2}
\]
Every physical circle-corner mask and nonnegative split of its
positive total circle load is retained. The AB contact may be a
positive-length shared side, with an arbitrary actual application
mean. The BC contact may also have a variable side mean.

Opposite or perpendicular A-owned directions are already excluded
by UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md and
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md. Parallel directions have
the pressure sign by BOWTIE_PARALLEL_PRESSURE.md. Thus it suffices
to prove (2) in the acute nonparallel case. A free articulation
vertex normal is not included in the present ownership hypothesis.

## 1. Coordinates, force equations and a support estimate

After rotation and reflection, put
\[
\begin{split}
 n&=e_x,\qquad m=(d,c),\quad k=Jm=(-c,d),\quad
    c=\sin\psi,\ d=\cos\psi,\quad0<\psi<\pi/2,\\
 A&=[Q_x-1,Q_x]\times[Q_y-1,Q_y],\\
 c_A&=Q-(1/2,1/2),\\
 C&=Q+[0,1]m+[-r,1-r]k,\quad0<r<1,\quad V=1-r.
\end{split}
\tag{3}
\]
The strict inequalities on r follow from the stated relative-side
interior AC contact. For positive AB,AC,BC magnitudes mu,nu,gamma
and the actual BC normal g directed from B into C, write
\[
 F_B=\mu e_x-\gamma g,\qquad F_C=\nu m+\gamma g,
       \qquad\beta=\mu/\gamma>0,\quad\chi=\nu/\gamma>0.
\tag{4}
\]

Here is a useful estimate that retains two physical circle corners.
If F=2 Lambda zbar is the circle-force vector of a loaded square,
put rho=|zbar|. For any square point zstar maximizing F dot x,
\[
 c_A\cdot F
   =\rho|F|-F\cdot(\bar z-c_A)
   \ge\rho|F|-F\cdot(z_* -c_A).
\tag{5}
\]
For one physical circle corner rho=R. For two, the radial-S
coordinates give rho>=sqrt(R^2-1/4). This includes zero individual
weights. The maximizing point need not be a physical circle
corner. To prove (2), we will bound the support sum strictly below
K_B|F_B|+K_C|F_C|, using a lower bound K_S<=rho_S appropriate
to each stated physical mask. In particular rho is never silently
replaced by R for a two-positive-corner average.

We will use
\[
       K_0=79/40,\quad K_1=39/20,\quad
       K_*=\sqrt{5841}/40,\qquad
       C_0=1+(c+d)/2.
\tag{6}
\]
Thus rho>=K_* for every loaded tip, while rho>=K_0>K_1 for
a tip with one physical circle corner.

## 2. The entire aligned/shared AB alternative

Suppose B has a vertical left support side at x=Q_x. Since its
side frame is then the same as A's, write
\[
             B=[Q_x,Q_x+1]\times[Q_y+h-1,Q_y+h].
\tag{7}
\]
Positive-length AB contact requires -1<h<1. A singleton at two
aligned vertices cannot have the axis e_x under the selected
strict point-normal convention, so it supplies no additional
endpoint case here.

The C point Q-rk has first coordinate strictly between Q_x and
Q_x+1 and relative height -rd in (-1,0). If h>=0, C has an open
overlap with B immediately below Q. Hence h<0. If h>-rd, the
lowest C vertex is horizontally inside B and above B's bottom,
and again their open interiors overlap. If h<-rd, the squares
are vertically separated and cannot touch. Therefore
\[
           h=-rd,\qquad T=Q-rk\in\operatorname{relint}
                       (\text{top side of }B),\qquad g=e_y.
\tag{8}
\]
This proves the BC axis without any generic choice. Every AB
application mean in the actual common segment is retained.

The force-maximizing vertices relative to c_A are
\[
       W_B=(3/2,-rd-1/2),\qquad
       W_C=(1/2,1/2)+m+Vk.
\tag{9}
\]
Indeed F_B/gamma=beta e_x-e_y and
F_C/gamma=(chi+c)m+dk. Their support sum divided by gamma is
\[
              N=\frac32\beta+C_0\chi+1+c+d.
\tag{10}
\]
For any positive beta,chi, Cauchy's inequality in the two frames
gives
\[
\begin{split}
 K_*|\beta e_x-e_y|
     &\ge\tfrac32\beta+\sqrt{K_*^2-9/4},\\
 K_*|\chi m+e_y|
     &\ge C_0\chi+cC_0+d\sqrt{K_*^2-C_0^2}.
\end{split}
\tag{11}
\]
Now sqrt(K_*^2-9/4)>59/50, C_0>=3/2 and
sqrt(K_*^2-C_0^2)>17/20, since C_0<=1+1/sqrt(2).
For the last strict comparison, use sqrt(2)<283/200 in
C_0^2<=3/2+sqrt(2).
The constant on the right of (11), minus 1+c+d, exceeds
\[
                    \frac9{50}+\frac c2-\frac{3d}{20}
                          \ge\frac3{100}>0.
\tag{12}
\]
Equations (5),(10)--(12) prove (2) for this whole aligned branch,
for every physical circle mask and all AB means.

## 3. The complete oblique B geometry and BC-owner cover

In every remaining case, B has its unique left vertex at the AB
application P. The strict point convention and the A ownership
make P a relative interior point of the A side. Write
\[
\begin{split}
 P&=Q-te_y,\quad0<t<1,\\
 u&=(b,a),\quad v=(a,-b),\quad
       a=\sin\theta,\ b=\cos\theta,\quad0<\theta<\pi/2,\\
 B&=P+[0,1]u+[0,1]v,\\
 S&=\sin(\theta-\psi),\quad D=\cos(\theta-\psi)>0.
\end{split}
\tag{13}
\]
We will allow t=1 in the estimates below; this only enlarges the
domain. The applications AB and AC are fixed singleton points.

If both tips have two physical circle corners, (2) follows directly
from RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md. Otherwise choose a tip
with one physical circle corner. If BC were a free vertex/vertex
contact, both of that tip's applications would be fixed; the
compatible selection in GENERAL_FIXED_TIP_NORMAL_SELECTION.md
removes this alternative. The coincident radial-D exception cannot
occur here: a common point of two boundary squares has norm
strictly larger than R-sqrt(2), whereas that radial-D vertex has
norm R-sqrt(2). Thus BC has a side-axis owner.

For any actual BC point T, supporting inequalities give
g dot P<=g dot T<=g dot Q, hence g_y>=0. Equality would give
g=+/-e_x. The positive choice would make P both a minimum-x and
maximum-x point of B. For the negative choice Q would maximize
x on C, although Q+epsilon m lies in C and has larger x.
Therefore g_y>0.

The C-owned possibilities are m or k. The choice m makes the
two C pair forces parallel. Parallel-force classification makes
C radial S in this side direction. Its inner side cannot face
another boundary square by C7_FORCE_POLYGON.md, Lemma2.1, and
its outer face cannot be shared with a contained unit. Thus g=m
is impossible. The B-owned possibilities with positive y are u
and -v. We now give their full cover.

### 3.1. C owns BC, with a strictly different frame

Let g=k. If S<0, the unique maximum-k B point is P, which lies
strictly below C's minimum-m support. This cannot be a BC point.
The case S=0 is a joint B/C owner and is assigned to Section3.2.
Thus S>0, and the maximum-k B point is P+u. Its exact C-side
coordinates give
\[
 \theta>\psi,\qquad
 T=P+u=Q+jm-rk,\qquad
 r=td-S,\quad j=D-tc\in[0,1),\quad V=1-td+S>0.
\tag{14}
\]

### 3.2. B owns BC

The choice g=u is impossible. If S<0, the minimum-u C point
is Q+Vk, whose x-coordinate is smaller than Q_x and so lies
outside B. If S>0, that point is Q-rk, whose u-projection from
P is ta-rS<1, below B's maximum-u side. At S=0 the whole
minimum-u C face has projection ta<1 from P, with the same
contradiction.

Hence g=-v. If S>0, its minimum on C is the outer-lower point
Q+m-rk. Matching the B minimum-v side gives
\[
        r=(tb-S)/D,\qquad
        u\cdot(T-P)=(1+tc)/D>1,
\tag{15}
\]
which is impossible. Consequently
\[
 \theta\le\psi,\quad E=-S=\sin(\psi-\theta)\ge0,
 \quad r=tb/D,\quad\lambda_0=tc/D\in(0,1],
 \quad T_0=Q-rk=P+\lambda_0u.
\tag{16}
\]
For theta<psi, T_0 is the actual singleton BC application.
For theta=psi the contact is a shared side, not an artificially
fixed point: its actual application is P+xi u with
lambda_0<=xi<=1. The formulas for r and the endpoint T_0 still
hold. Every xi in the actual shared segment is retained below.

## 4. Three exact support inequalities

The following elementary estimates will handle B with a unique
physical circle corner while leaving C's mask arbitrary.

### 4.1. A shallow C-owned separator and B's opposite corner

Suppose 0<=psi<=theta<=pi/4, and put A_0=1/2+a+b. Then
\[
 cA_0+d\sqrt{K_0^2-A_0^2}
        +\sqrt{K_0^2-C_0^2}>1+\cos(\theta-\psi).
\tag{17}
\]
Fix theta, put X=sqrt(K_0^2-A_0^2), and subtract the right side
from the left to form G(psi). Its derivative is
\[
 G'=(1/2+b-q)d+(b-X+q)c,
       \qquad q=\frac{C_0}{2\sqrt{K_0^2-C_0^2}}.
\tag{18}
\]
Here 1/2<q<1, b,d>7/10, c<3/4 and X<13/10. Thus
G'> (1/5)(7/10)-(1/10)(3/4)>0.
At psi=0, put Y=sqrt(K_0^2-9/4)>41/32. The inequality
G(0)>0 is immediate if 1+b-Y<=0. Otherwise square the positive
comparison X>1+b-Y. Its squared difference is
\[
                 2Y(1+b)-a-3b-b^2-2ab>0.
\tag{19}
\]
This is exactly the s=1/2 instance of the corner-box inequality
in BOWTIE_PARALLEL_PRESSURE.md, Section2, equations(9)--(10).
For clarity, that proof bounds
a+(7/16)b+b^2+2ab by 49813/19520<41/16 through the positive
matrix (33/16)I-[[0,1],[1,1]]. Since Y>41/32, this gives
(19) with a strict margin. Therefore (17) holds throughout.

We also need the asymmetric version
\[
 cA_0+d\sqrt{K_0^2-A_0^2}
       +\sqrt{K_*^2-C_0^2}>1+\cos(\theta-\psi)
\tag{19a}
\]
when pi/6<=psi<=theta<=pi/4. With X as above, put
Y_*=sqrt(K_*^2-9/4)>59/50. The same positive-matrix estimate
used in (19) gives
\[
 X>b-7/25.
\tag{19b}
\]
Here is the exact verification. The square of the left side,
minus (b-7/25)^2, is
\[
 K_0^2-5/4-49/625
       -\left(a+\frac{11b}{25}+b^2+2ab\right).
\]
The parenthesized expression is below
41/16+(11/25-7/16)=513/200. The remaining exact difference is
289/40000>0. Since b>7/10>7/25, this proves (19b).

We also have X<b+3/10. To verify it, use the concavity of
a+(8/5)b on theta in [0,pi/4] to bound it below by8/5,
and b^2+2ab>=1. Then
\[
 X^2-(b+3/10)^2
 =K_0^2-67/50-\left(a+\frac85b+b^2+2ab\right)
 \le K_0^2-197/50<0.
\tag{19c}
\]

Let G_* be the left side of (19a) minus its right side.
Its derivative has the same form (18), now with
q_*=C_0/(2sqrt(K_*^2-C_0^2)). Again 1/2<q_*<1:
the upper bound follows from
5C_0^2<5(3/2+283/200)<4K_*^2.
Thus (19c) and b>7/10 show that both derivative coefficients
1/2+b-q_* and b-X+q_* exceed1/5. Consequently
\[
             G_*'(\psi)>1/5,\qquad
             G_*(0)>Y_*-1-7/25>-1/10.
\tag{19d}
\]
Since pi/6>1/2, these two strict bounds prove (19a).

### 4.2. A C-owned separator and B's adjacent corner

Suppose theta-psi>pi/4. Put A_1=1/2+a. Then
\[
 cA_1+d\sqrt{K_0^2-A_1^2}
       +\sqrt{K_*^2-C_0^2}>1+D+S.
\tag{20}
\]
Indeed psi<pi/4 and a>=(c+d)/sqrt(2). Put
Y_B=sqrt(K_0^2-9/4), so 32/25<Y_B<13/10, and
Y_*=sqrt(K_*^2-9/4)>59/50. The concave function
sqrt(K_*^2-(1+s/2)^2), for 1<=s<=sqrt(2), is at least
\[
                         Y_*-\frac78(s-1).
\tag{21}
\]
To check the chord slope, Y_*<6/5 and the value at sqrt(2)
is greater than17/20, while sqrt(2)-1>2/5. These exact
comparisons give slope magnitude below7/8.

Since A_1<=3/2, the left side of (20) is at least
\[
 Y_*+7/8+c\left(-3/8+\frac{c+d}{\sqrt2}\right)
               +d(Y_B-7/8).
\tag{22}
\]
The c coefficient is greater than13/40. The positive sine-cosine
sum (13/40)c+(Y_B-7/8)d is concave on [0,pi/4], so its minimum
is at an endpoint. At0 it is Y_B-7/8. At pi/4 it is greater
than (13/40+81/200)/(3/2)=73/150>17/40>Y_B-7/8.
Thus (22) is at least Y_*+Y_B>123/50>1+sqrt(2)>=1+D+S,
proving (20).

### 4.3. A B-owned separator

For 0<=theta<=pi/4,
\[
       aA_0+b\sqrt{K_1^2-A_0^2}>6/5.
\tag{23}
\]
If aA_0>=6/5 this is immediate. Otherwise the difference after
squaring the positive quantities is
\[
\begin{split}
 &b^2(K_1^2-A_0^2)-(6/5-aA_0)^2\\
 &\quad=\frac{445}{400}+\frac a5-b-\frac{561a^2}{400}
                                    +\frac{2ab}{5}\\
 &\quad\ge\frac9{80}+\frac{3a}{5}
                     -\frac{361a^2}{400}-\frac{a^3}{5}>0.
\end{split}
\tag{24}
\]
The weak inequality uses b<=1-a^2/2 and 2a/5-1<0. The final
cubic is concave on [0,1/sqrt(2)], and its endpoint values are
9/80 and -271/800+sqrt(2)/4, both positive. This proves (23).

For any 0<=psi-theta<pi/2, E=sin(psi-theta), D=cos(psi-theta),
we have C_0>=1 and sqrt(K_*^2-C_0^2)>17/20. Hence (23) gives
\[
 aA_0+b\sqrt{K_1^2-A_0^2}
       +EC_0+D\sqrt{K_*^2-C_0^2}>1+D+E.
\tag{25}
\]
The surplus is greater than1/5-3D/20>0. No condition D>E is
needed in (25).

## 5. B has one physical circle corner: every C mask is covered

### 5.1. C-owned BC

Use (14), so g=k and theta>psi. In B coordinates,
F_B/gamma=beta e_x-k has v-component beta a+D>0.
Its u-component is beta b-S. Since B's sole physical circle
corner is parallel to F_B, this component is nonzero. There are
exactly two alternatives.

If it is positive, the unique circle corner is P+u+v. Torque
about that corner gives
\[
                         \beta(b-a)=S.
\tag{26}
\]
Thus theta<pi/4. The F_B-maximizing vertex relative to c_A is
W_B=(1/2,1/2-t)+u+v. The F_C-maximizing vertex is
W_C=(1/2,1/2)+m+Vk, since F_C/gamma=chi m+k has both own
components positive. Their support sum divided by gamma is
\[
                         N=\beta A_0+\chi C_0+1+D.
\tag{27}
\]
This identity uses only V=1-td+S; it does not use a unique
circle mask or a torque equation at C.

If C has one physical circle corner too, Cauchy's inequality,
with unit dual vectors in the fixed frames, gives
\[
\begin{split}
 K_0|\beta e_x-k|
     &\ge\beta A_0+cA_0+d\sqrt{K_0^2-A_0^2},\\
 K_0|\chi m+k|
     &\ge\chi C_0+\sqrt{K_0^2-C_0^2}.
\end{split}
\tag{28}
\]
By (17), their sum strictly exceeds N. Both means now have norm
R>=K_0, so equation(5) proves (2).

If C instead has two physical circle corners, its radial direction
is m or k: the two own components of F_C are positive. The k
direction is impossible, since g=k puts B across C's radial
inner face. Thus C is radial in m. With H as in (34),
\[
        Q=Hm+(r-1/2)k,\qquad
        c_A\cdot m=H-(c+d)/2>0.
\tag{28a}
\]
For psi<=pi/6 we have c<=1/2, d>=sqrt(3)/2>17/20 and
\[
       c_A\cdot e_x=Hd-c(r-1/2)-1/2
             >\frac9{10}\frac{17}{20}-\frac14-\frac12
              =\frac3{200}>0.
\tag{28b}
\]
Since M=mu e_x+nu m, these two positive projections prove (2)
directly in this entire range, with arbitrary C circle weights.
For psi>=pi/6 use the first line of (28), but replace K_0 by
K_* in the second line and in its square root. The asymmetric
inequality (19a) then makes
K_0|F_B|+K_*|F_C| strictly greater than the support sum.
These two constants are at most the respective mean lengths,
so (5) proves (2) here as well. This exhausts the radial C mask.

If instead beta b-S<0, the unique circle corner is P+v.
Torque about it gives
\[
                         \beta b=S-D>0.
\tag{29}
\]
Consequently theta-psi>pi/4. Use
W_B=(1/2,1/2-t)+v and the same W_C. The support sum is now
\[
                         N=\beta A_1+\chi C_0+1+D+S.
\tag{30}
\]
Replace A_0 by A_1 in the first line of (28), and use K_* in
the second line and its square root. Equation(20) bounds the
support sum strictly below K_0|F_B|+K_*|F_C|. These are valid
mean-length bounds for unique B and arbitrary C, so (5) proves
(2) for all circle masks and weight splits at C.

### 5.2. B-owned BC, including the shared-side transition

Use (16), so g=-v. Both own components of
F_B/gamma=beta e_x+v are positive; its unique circle corner is
P+u+v. With xi=lambda_0 for the singleton contact and with the
actual shared-side xi when theta=psi, torque gives
\[
                          \beta(b-a)=1-\xi\ge0.
\tag{31}
\]
Thus theta<=pi/4. This includes b=a and xi=1; no endpoint mean
has been discarded.

The C force is F_C/gamma=(chi+E)m+Dk, again with both own
components positive. Using the same opposite B corner and W_C
as above, the support sum is
\[
                         N=\beta A_0+\chi C_0+1+D+E.
\tag{32}
\]
In this identity the tangential terms cancel by r=tb/D.
For the two norms, Cauchy gives the lower bound
\[
\begin{split}
 K_1|\beta e_x+v|+K_*|\chi m-v|
 \ge{}&\beta A_0+\chi C_0\\
       &+aA_0+b\sqrt{K_1^2-A_0^2}\\
       &+EC_0+D\sqrt{K_*^2-C_0^2}.
\end{split}
\tag{33}
\]
Equation(25) makes (33) strictly greater than (32). Applying
(5), with the unique-B bound rho_B>=K_0>K_1 and the general
bound rho_C>=K_*, proves (2) for the entire B-owned branch, including every
two-corner C mask and the full shared-side interval for xi.

## 6. B has two physical circle corners and C has one

This is the only mask not yet covered in the oblique geometry:
both radial tips were already handled before the owner cover.
Put
\[
               H=\sqrt{R^2-1/4}-1,
                    \qquad9/10<H<61/60.
\tag{34}
\]
The radial direction of B is +u or +v. A negative direction
would make its AB vertex P a physical circle point, which cannot
be shared. We exclude both BC-owner branches completely.

### 6.1. B-owned BC

Here g=-v. The radial direction cannot be +v: BC would be an
inner-face contact of a radial S square with a boundary neighbor,
excluded by C7_FORCE_POLYGON.md, Lemma2.1. Hence it is +u and
\[
                            P=Hu-\tfrac12v.
\tag{35}
\]
Write E=sin(psi-theta)>=0. The actual unique C circle corner is
z_C=Q+m+Vk. By (16), with W=H+lambda_0>=H, it has B-frame
coordinates
\[
                   z_C\cdot u=W+D-E,\qquad
                   z_C\cdot v=-1/2-D-E.
\tag{36}
\]
When theta<psi, C's torque about that unique corner gives
nu V=gamma(D-E)>0, so D>E. When theta=psi, the actual shared
mean changes this torque formula, but E=0,D=1 directly. Thus
in every case 0<=psi-theta<pi/4.

The squared norm in (36), minus the B circle radius squared
(H+1)^2+1/4, is at least
\[
                       1+D+E-2H(1-D+E).
\tag{37}
\]
As a function of alpha=psi-theta in [0,pi/4], this expression is
concave: its second derivative is
-(1+2H)cos(alpha)+(2H-1)sin(alpha)<0. Its endpoint values are
2 and 1+sqrt(2)-2H, both positive by H<61/60. Thus (37)>0,
contradicting the containing circle. This also covers every
shared-side mean at alpha=0.

### 6.2. C-owned BC: exact radius and torque contradiction

Now g=k and theta>psi. The radial direction of B cannot be +u,
because its BC point T=P+u would be a physical circle point.
It is therefore +v and
\[
                              P=-\tfrac12u+Hv.
\tag{38}
\]
The unique C circle corner has m,k coordinates
\[
              X=1-D/2+HS+tc,\qquad Z=1+S/2-HD.
\tag{39}
\]
Both are positive, since F_C/gamma=chi m+k. If theta<=pi/4,
substitute c=aD-bS and use t<=1 to obtain
\[
 X\le1+(a-1/2)D+(H-b)S
        <1+\tfrac14D+\tfrac13S\le17/12.
\tag{40}
\]
Also D>=cos(theta)>7/10 and S<3/4, so
0<Z<1+3/8-(9/10)(7/10)<3/4.
Equations(39)--(40) give
\[
                 |z_C|^2<\frac{289}{144}+\frac9{16}
                       =\frac{185}{72}<\frac{39}{10}<R^2,
\tag{41}
\]
which is impossible. Hence theta>pi/4.

The unique-corner torque at C is chi=(1-j)/V. Its force
direction is chi m+k, so (39) must satisfy
\[
                     XV=(1-j)Z.
\tag{42}
\]
We prove instead that the left side minus the right side is
strictly positive throughout the whole remaining parameter domain.
Using (14),(39), this difference is the concave quadratic
\[
\begin{split}
 f(t)={}&(S+D)\,[1/2+H(1+S-D)]\\
 &+t\,[\tfrac12\cos(\theta-2\psi)
                         +H\sin(2\psi-\theta)-d]-t^2cd.
\end{split}
\tag{43}
\]
At t=0 it is positive. At t=1 its H coefficient is
\[
          (1-D)(1+2D)+cD+S(1-d)\ge0.
\tag{44}
\]
Thus H>9/10 and S+D>=1 imply
\[
 f(1)\ge B_0+(1-D)W_D,
\tag{45}
\]
where
\[
 B_0=\tfrac12(1-d)+c(9/10-d),\qquad
 W_D=9/10+9D/5-d/2-9c/10.
\tag{46}
\]
Always D>=c, so W_D>0.

If c>=1/3 and d<=9/10, then B_0>0 immediately. If c>=1/3
and d>9/10, then d<=sqrt(8/9)<19/20 and
\[
 B_0>c^2/4-c/20\ge c(1/12-1/20)>0.
\tag{47}
\]
Thus (45)>0 throughout c>=1/3.

It remains to check 0<=c<=1/3. Since theta>pi/4,
\[
                 c\le D\le D_*=(c+d)/\sqrt2.
\tag{48}
\]
The expression J(D)=(1-D)W_D is a concave quadratic in D,
so its minimum on (48) occurs at an endpoint. At D=c,
\[
             J(c)=(1-c)(9/10+9c/10-d/2)\ge4/15.
\tag{49}
\]
At D=D_*, we have D_*>7/10 and
D_*<=4/(3sqrt(2))<19/20. Consequently
\[
            J(D_*)>\frac1{20}
                     (9/10+63/50-1/2-3/10)
                     =17/250>1/30.
\tag{50}
\]
But B_0>=-c/10>=-1/30. Equations(45),(49)--(50) therefore
give f(1)>0 here too. Concavity in t now yields f(t)>0 on
[0,1], contradicting (42). This excludes the entire remaining
one-radial/one-unique C-owned branch.

## 7. Exhaustion and the precise remaining interface

Section2 treats all aligned B squares and every shared AB mean.
Otherwise B is oblique, the fixed-point selection supplies a BC
owner whenever at least one tip has a unique physical circle
corner, and Section3 lists every owner and the shared transition.
Section5 proves pressure for a unique B while retaining all C
masks. Section6 excludes both owners when only B is radial.
The two-radial mask is positive by
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md without any selection.
Thus the theorem covers its entire stated owner hypothesis.

Together with BOWTIE_TIP_OWNED_PRESSURE.md,
BOWTIE_PARALLEL_PRESSURE.md and
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md, this supplies the
pressure sign for every articulation interface whose two actual
normals have side owners. It does not assume that a remaining
free articulation vertex normal has such an owner.

In particular, a free A--C normal is removed by fixed-tip
selection when C has one physical circle corner and BC is a
singleton. Genuine residual interfaces may still have C radial
with B unique, or a positive-length shared BC segment. Such a
segment has an actual variable application mean. These interfaces
require a separate whole argument before C2.33.b0 is declared
closed. All four completion squares are retained throughout.

No pose sample, numerical certificate, Lean compilation or CI is
used in this proof.
