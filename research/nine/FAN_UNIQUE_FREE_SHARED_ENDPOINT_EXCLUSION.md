# A unique free fan endpoint cannot face a hub-owned endpoint

**Status: complete hand endpoint-family exclusion; root and separate
independent full hand audits passed.** Work throughout
\[
 R_0:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad Q_*:=\frac{1105}{256}.
\tag{1}
\]
The selected positive component is the fan with clear hub H and loaded
boundary path u_1--u_2--u_3--u_4. Every hub spoke is positive. The
endpoints have exact positive degree two; the inner path bodies retain
degree three. All four arbitrary completion squares remain.

**Theorem.** Suppose Hu_1 is a free point-only vertex/vertex contact,
u_1 has exactly one physical circle corner, and Hu_4 is owned by H.
Then this entire family is impossible. The assertion includes a
positive-length u_1u_2 shared side with every actual application mean,
all other physical corner masks, and all shared Hu_4 means.

The proof makes no new normal choice. The existing fixed-tip selection
removes the case in which u_1u_2 is a singleton, so the substantive
case below retains its actual positive-length shared side. Only the
genuine endpoint u_1 receives a degree-two body equation.
The coincident singleton exception in that selection would be a
radial-D inner vertex of norm R-sqrt(2), whereas a point shared by
two boundary squares has strictly greater norm; it is impossible here.

## 1. Complete local chart and the two possible opposite hub sides

Use the full unique-free/shared-side reduction in Section2 of
`FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md`. Its local Sections2.1--2.2
do not require the other endpoint to be a hub vertex. They give, in
orthonormal coordinates about the true circle origin,
\[
\begin{gathered}
 Q=(X,Y),\qquad u_1=Q+[0,1]^2,\\
 u_2=Q+[t,t+1]e_x+[-1,0]e_y,\qquad 0<t<1,\\
 n_1=(a,b),\qquad a\ge b>0,\qquad a^2+b^2=1,\\
 X,Y>-\tfrac12,\qquad Y>X.
\end{gathered}
\tag{2}
\]
For completeness, if the actual shared-side mean is Q+tau e_x, then
tau belongs to [t,1]. Writing the unique circle corner as
z_1=(X+1,Y+1), its actual force and torque give
\[
 \lambda(X+1)=\mu a,\quad
 \lambda(Y+1)=\mu b+\gamma,\quad
 \lambda(Y-X)=\gamma\tau,
 \qquad \lambda,\mu,\gamma>0.
\tag{3}
\]
Thus
\[
 \frac ba=\frac{Y+1-(Y-X)/\tau}{X+1}\le1.
\]
The shared-side endpoint tau=1 is retained. The cases t<0 and t=0
were excluded there respectively by the actual tangent sectors and
the exact circle-radius/endpoint-torque comparison; neither exclusion
uses a degree-two equation at u_2 or an owner premise at u_4.

Because H touches u_2 to the right of Q, its inward side axes at its
strict support vertex Q are
\[
 w=(c,-d),\qquad v=(-d,-c),\qquad
 0<c<d,\quad c^2+d^2=1,
\tag{4}
\]
and H=Q+[0,1]w+[0,1]v. Indeed strict support by (a,b) requires
ac-bd<0; together with a>=b this gives c<d. The orthogonal alternative
to v has both coordinates positive and violates the same strict
support. These are geometric side axes, not substituted force normals.

The shift in (2) is now exact:
\[
                    t=c,\qquad H\cap u_2=\{Q+w\},
                    \qquad n_2=e_x.
\tag{5}
\]
H has maximum first coordinate X+c, so physical contact requires
t<=c. If t<c, its vertex Q+w=(X+c,Y-d) is strictly inside u_2:
t<c<t+1 and 0<d<1. An interior neighborhood of that vertex would
overlap the open H interior. Hence t=c. The contact lies in the
relative interior of u_2's left side, and its normal is e_x. In
particular no third square can contain Q+w: the H quadrant and the
u_2 tangent half-plane leave only sectors strictly smaller than90
degrees.

Let P be the actual Hu_4 application, including an actual side mean.
The whole-path endpoint theorem gives |P-Q|>1. Since n_4 is an H side
axis, its side is not incident to Q, and precisely two possibilities
remain:
\[
 \begin{array}{lll}
 P=Q+w+p v,&n_4=w,&0<p\le1,\\
 P=Q+v+p w,&n_4=v,&0<p\le1.
 \end{array}
\tag{6}
\]

The first is impossible by a complete hub moment comparison. The
actual inner hub ports lie along Q--(Q+w)--P; their cyclic order is
the physical fan order. Every inner outward normal has nonpositive
moment about P. On Q+s w with normal -v the value is s-1, and on
Q+w+s v with normal w it is s-p. The intermediate vertex cone has
the same sign. Meanwhile
\[
 \det(Q-P,n_1)=p(bd-ac)-(ad+bc)<0,
\tag{7}
\]
because p<=1, a>=b and c>0. The endpoint force at P contributes zero.
This contradicts the full unloaded hub torque. The same physical
port-order justification as in the preceding fan sources applies to
actual means; a mean coinciding with P has zero moment.

We therefore retain the entire second line of (6):
\[
                       P=Q+v+p w,\qquad n_4=v.
\tag{8}
\]

## 2. Full hub force and torque bound the actual side parameter

The actual inner port u_3 lies along the H arc from Q+w through Q+w+v
to P. It cannot be at Q+w by (5), and it cannot be at Q because the
nonconsecutive boundary squares u_1,u_3 are physically disjoint. Its
normal therefore has the form
\[
                         n_3=r w+s v,
                         \qquad r,s\ge0.
\tag{9}
\]
The triangle side-normal theorem with the H-owned endpoint n_4=v
also gives s>=0. All shared mean endpoints are included: on the
terminal v-side its mean lies on the appropriate closed arc, and
coincidence with P is allowed.

Put
\[
 A=bd-ac>0,\qquad B=ad+bc>0,
 \qquad n_1=-A w-B v.
\tag{10}
\]
Let the four positive hub magnitudes be mu_i. The w coordinate of
the full force equation gives
\[
                         \mu_2c+\mu_3r=\mu_1A,
                  \qquad \mu_2\le\frac{\mu_1A}{c}.
\tag{11}
\]
Every u_3 normal has nonpositive moment about P: on the w-side it
is tau-1, at Q+w+v it is -(1-p)s, and on the v-side it is
-(tau-p). Thus the full torque about P implies
\[
             \mu_1(A-pB)+\mu_2\bigl(d(1-p)-c\bigr)\ge0.
\tag{12}
\]
No inner body equation has been replaced by an endpoint equation.

If d(1-p)-c<0, (12) requires p<=A/B. If it is nonnegative,
(11)--(12) require
\[
                         p\le\frac{Ad}{Ad+Bc}.
\tag{13}
\]
The second bound also covers the first. Indeed, putting m=A/B,
\[
 0<m\le\frac{d-c}{d+c}<1-\frac cd,
 \qquad m<\frac{md}{md+c}.
\]
The first upper bound follows by maximizing b/a<=1 in
m=(d(b/a)-c)/(d+c(b/a)). The function md/(md+c) is increasing in m.
Consequently every actual parameter in (8) satisfies
\[
                         0<p\le d(d-c).
\tag{14}
\]
This uses all four original hub forces and actual means.

## 3. The complete two-square circle equations

Write N=X+1 and M=Y+1. The unique u_1 corner gives
\[
                            N^2+M^2=R^2.
\tag{15}
\]
By (2),(5), the center of u_2 has strictly positive first coordinate.
Its farthest first coordinate is X+c+1. Its farthest second coordinate
is Y-1 for Y<=1/2 and Y for Y>=1/2. Thus its complete physical circle
mask gives precisely
\[
 Y=\begin{cases}
 \dfrac c2X+\dfrac c2+\dfrac{c^2}{4},&Y\le\tfrac12,\\[2mm]
 cX+c+\dfrac{c^2}{2}-\dfrac12,&Y\ge\tfrac12.
 \end{cases}
\tag{16}
\]
Both formulas agree at Y=1/2, which retains the two-circle-corner
mask of u_2, including either individual zero weight. Equivalently,
\[
 M=\max\left(1+\frac c2N+\frac{c^2}{4},
              \frac12+cN+\frac{c^2}{2}\right).
\tag{17}
\]
This is strictly increasing in N, while Y-X is strictly decreasing
in X on each branch, with a continuous join.

We record exact bounds for this entire domain:
\[
              \frac{12}{25}<c<\frac1{\sqrt2},
              \qquad 0<X<\frac12,\qquad X<Y<c.
\tag{18}
\]
Here are complete proofs. If c<=12/25, the transition Y=1/2 in
(16) has X=1/c-1-c/2>=253/300>1/2. Since Y-X is decreasing,
the condition Y>X forces the lower branch. There both N and M
are smaller than their value where Y=X, namely
(4+c^2)/(4-2c). This value increases with c, so
\[
 R^2<2(661/475)^2<R_0^2,
 \qquad R_0^2-2(661/475)^2=399137/14440000>0.
\]
This proves the bound on c. Equation(16) gives Y>0. If X<=0,
its lower branch gives Y<1/2 and R^2<1+9/4<R_0^2. Thus X>0.
Since Y>X and Q_*<9/2, (15) implies X<1/2.

Finally Y<c throughout the window. At the hypothetical crossing
Y=c, (16) gives circle radius squared
\[
 \begin{cases}
 (2-c/2)^2+(1+c)^2=5+5c^2/4,&c\le1/2,\\
 (1+1/(2c)-c/2)^2+(1+c)^2,&c\ge1/2.
 \end{cases}
\tag{19}
\]
Both exceed Q_*. The second decreases on [1/2,1/sqrt(2)]: if
u=1+1/(2c)-c/2, then u>4/3, u'<=-3/2 and 1+c<7/4, so its
derivative is negative. Its minimum is
21/8+3sqrt(2)/2>Q_*. Because (15),(17) increase with Y, a crossing
or a larger Y is impossible. This proves (18).

## 4. Reduction of the whole side segment to two endpoints at R_0

Put p_*=d(d-c). The squared norm of Q+v+p w is convex in p, so its
maximum for 0<=p<=p_* is at
\[
 P_0=(X-d,Y-c),\qquad
 P_*=(X-L,Y-K_0),
\tag{20}
\]
where
\[
 L=d-cd(d-c),\qquad K_0=c^3+d^3.
\tag{21}
\]
Both coordinates of both points are strictly negative. For P_0 this
follows from (18). For P_*, use c>12/25, d<22/25, hence d-c<2/5,
and cd<=1/2. These give
\[
 L>d-1/5>1/2,
 \qquad K_0\ge1/\sqrt2\ge c>Y.
\]
The bound on K_0 is the elementary convexity inequality
c^3+d^3>=1/sqrt(2) under c^2+d^2=1.

For a fixed c, (15),(17) make X,Y strictly increase with R. Decreasing
R to R_0 preserves Y>X, because Y-X decreases with X. All bounds just
proved therefore continue to hold throughout this decrease. Since
the coordinates in (20) stay negative, both endpoint norms decrease
as R increases. It is enough to prove
\[
                      |P_0|<11/20,\qquad |P_*|<11/20
                         \quad\hbox{at }R=R_0.
\tag{22}
\]
No force or contact parameter is changed in the actual packing; this
is a monotonic comparison on the enlarged scalar domain (15)--(18).

## 5. The complete interval 12/25<c<=1/2

At R=R_0, one has X>3/8. Otherwise (16) gives
Y<=13/32, so
\[
 R_0^2\le(11/8)^2+(45/32)^2<R_0^2,
 \qquad R_0^2-(11/8)^2-(45/32)^2=831/25600>0.
\]
Also Y>X. Therefore
\[
 |P_0|^2< (22/25-3/8)^2+(1/2-3/8)^2<121/400.
\tag{23}
\]
The last gap is 637/20000.

For the other endpoint, L<18/25. Indeed d<=1-c^2/2 gives
\[
 L=d(1+c^2)-c(1-c^2)
 \le1-c+c^2/2+c^3-c^4/2=:f(c).
\]
Its derivative is
(c-1/2)(-2c^2+2c+2), nonpositive on [12/25,1/2]. Hence
\[
 L\le f(12/25)=280957/390625<18/25.
\]
The function c^3+(1-c^2)^{3/2} decreases up to c=1/sqrt(2).
Thus
\[
 K_0<(12/25)^3+(22/25)^3=12376/15625<4/5.
\]
Consequently
\[
 |P_*|^2<(18/25-3/8)^2+(4/5-3/8)^2<121/400,
\tag{24}
\]
with final gap 57/20000. This proves (22) for the entire first
interval, including c=1/2.

## 6. For c>=1/2 the first endpoint is always farther at R_0

First X<77/200. Otherwise N>=277/200 and (17) gives
M>=1+N/4+1/16, implying
\[
 R_0^2\ge(277/200)^2+(1+277/800+1/16)^2
       =R_0^2+1393/640000,
\]
a contradiction.

Let K=dY-cX. The lower expression in (16) is a lower bound on Y
in both masks. Using X<77/200, we get
\[
\begin{split}
 K-p_*/2
 &>cd\left(\frac{477}{400}+\frac c4\right)
       +\frac{c^2}{2}-\frac{77c}{200}-\frac12\ge0.
\end{split}
\tag{25}
\]
To check the last sign on [1/2,1/sqrt(2)], cd is nondecreasing, its
positive coefficient is increasing, and the derivative of
c^2/2-77c/200-1/2 is positive. The minimum of the displayed right
side is therefore its value at c=1/2:
\[
 \frac{527\sqrt3-908}{1600}>0,
                  \qquad 3\cdot527^2-908^2=8723>0.
\]
Since
\[
                  |P_*|^2-|P_0|^2=p_*^2-2p_*K,
\]
equation(25) shows that P_0 is farther. It remains to bound only
P_0=(X-d,Y-c) throughout this complete second interval.

## 7. Two uniform scalar bounds for the farther endpoint

We prove
\[
                       d-X<\frac8{15},
                    \qquad c-Y<\frac{13}{100}
                         \quad (R=R_0, c\ge1/2).
\tag{26}
\]
These imply
\[
 |P_0|^2<\frac{64}{225}+\frac{169}{10000}
          =\frac{27121}{90000}<\frac{121}{400}.
\tag{27}
\]

### 7.1. The first scalar bound, with complete polynomial signs

Suppose X<=d-8/15, so N<=d+7/15. In (17) both expressions are
increasing with N. It is therefore enough to show that the two values
\[
 (d+7/15)^2+
 \left(1+\tfrac c2(d+7/15)+\tfrac{c^2}{4}\right)^2,
\]
\[
 (d+7/15)^2+
 \left(\tfrac12+c(d+7/15)+\tfrac{c^2}{2}\right)^2
\tag{28}
\]
are strictly less than R_0^2.

Parametrize c=2t/(1+t^2), d=(1-t^2)/(1+t^2). The entire interval
1/2<=c<=1/sqrt(2) has 0<t<3/7, since
t<=sqrt(2)-1<3/7. Put D=1+t^2. Subtracting the two respective
values in (28) from R_0^2 gives
\[
                  \frac{P_L(t)}{14400D^4},
                \qquad\frac{P_U(t)}{14400D^4},
\tag{29}
\]
where the following are exact polynomial identities:
\[
\begin{split}
 P_L(t)={}&233+42240(t-1/2)^2\\
 &+t^2(25636-111360t+211126t^2)\\
 &+3840t^5+148516t^6+15360t^7+37673t^8,
\end{split}
\tag{30}
\]
and
\[
\begin{split}
 P_U(t)={}&21593-42240t+18148t^2-238080t^3\\
 &+300310t^4+49920t^5+179428t^6+15360t^7+48473t^8.
\end{split}
\tag{31}
\]
The quadratic in (30) has positive leading coefficient and
discriminant -9248654944. Thus P_L(t)>0 for every t>=0.

For the other polynomial,
\[
 P_U'(t)=-42240+36296t+t^2B(t),
\]
\[
 B(t)=-714240+1201240t+249600t^2+1076568t^3
                         +107520t^4+387784t^5.
\tag{32}
\]
B is increasing for t>=0, and
\[
 B(3/7)=-1001689944/16807<0.
\]
Also -42240+36296t<0 on [0,3/7]. Hence P_U is strictly
decreasing there, while
\[
                  P_U(3/7)=825636752/5764801>0.
\tag{33}
\]
Both differences in (29) are strictly positive, contradicting
(15). This proves the first inequality in (26) without a sampled
angle or radius restriction.

### 7.2. The second scalar bound, retaining the circle-mask transition

Suppose Y<=c-13/100. In the lower mask Y<=1/2, equation(16) gives
N=2Y/c-c/2. For c<=63/100 this is at most
2-13/(50c)-c/2, which increases on [1/2,63/100]. For c>=63/100,
the bound Y<=1/2 instead gives the decreasing expression 1/c-c/2.
In both cases,
\[
                     N\le\frac{16031}{12600},\qquad M\le\frac32.
\]
But
\[
 R_0^2-(16031/12600)^2-9/4=632533/19845000>0,
\tag{34}
\]
contradicting (15).

In the upper mask Y>=1/2, the supposition requires c>=63/100 and
gives
\[
                N\le1+\frac{37}{100c}-\frac c2=:u(c),
                     \qquad M\le c+87/100.
\tag{35}
\]
The function u(c)^2+(c+87/100)^2 is strictly convex on
[63/100,1/sqrt(2)], since u>0, u''>0, and its second derivative
is 2(u')^2+2uu''+2. Its maximum is at an endpoint. At 63/100
the bound is the expression in (34). At 1/sqrt(2) it is
\[
 \frac{22857}{10000}+\frac{111}{100}\sqrt2
 <\frac{22857}{10000}+\frac{111}{100}\frac{10}{7}<R_0^2,
\tag{36}
\]
with last gap 8179/280000. This also contradicts (15). The second
inequality in (26) follows in both masks, including Y=1/2.

## 8. Whole-family contradiction

Sections4--7 prove |P|<11/20 for every actual P in (8),(14), for
the entire radius window and all physical masks of the shared
neighbor u_2. On the other hand P belongs to the circle-touching
unit u_4. The unit-square diameter gives
\[
                     |P|\ge R-\sqrt2
                     \ge79/40-\sqrt2>11/20,
\tag{37}
\]
where the last inequality is sqrt(2)<57/40. This is the desired
contradiction.

The unique-free endpoint's singleton-neighbor alternative was already
removed by the compatible fixed-tip selection. The shared-neighbor
alternative was treated here with every actual mean endpoint, and
both possible opposite hub-owned sides were covered. Thus the whole
physical-unique free endpoint family opposite a hub-owned endpoint
is excluded. The physically radial free endpoint remains separate.
No inner degree-three body received an artificial degree-two equation,
no actual normal or mean was changed, and no completion square was
discarded. The polynomial identities above are explicit hand sign
proofs; numerical optimization, Lean compilation and CI are not used.
