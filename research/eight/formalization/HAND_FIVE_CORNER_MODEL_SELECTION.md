# Global selection of the five-corner minimum

This note proves that the natural minimum in
[the five-corner model](EIGHT_SQUARE_FIVE_CORNER_MODEL.md) is attained,
has a unique angle and five points in the chosen frame, and has squared
radius \(q_*\). The definition ranges over all
\(0\le t\le\pi/4\) and arbitrary five points satisfying the five
projected spans. No coordinate window or numerical radius bracket is
part of that definition.

The proof below uses one constant-weight support on the entire large
tilt arc, the already proved single polynomial nominal stress on the
remaining arc, and the actual-envelope stationary uniqueness theorem.
It does not use the five interval-dependent stresses in
[the historical five-interval enclosure](../HUMAN_FAMILY_ENCLOSURE.md), a local root box, or a numerical
optimizer. The rational constants in Sections 3 and 4 are estimates
inside the proof, rather than conditions selecting the model.

## 1. Existence and a strict trial below radius two

Write \(e_t=(c,s)\), \(f_t=(-s,c)\), where
\(c=\cos t\), \(s=\sin t\). The five projected requirements are
\[
\begin{aligned}
 (P_2-P_1)_y&\ge2,&
 (P_2-P_3)_x&\ge3,&
 (P_3-P_4)_y&\ge2,\\
 f_t\cdot(P_4-P_5)&\ge1+s,&
 e_t\cdot(P_1-P_5)&\ge2+c.
\end{aligned}
\tag{1}
\]
At \(t=0\), the five points
\[
 \left(\frac{41}{24},-1\right),\quad
 \left(\frac{41}{24},1\right),\quad
 \left(-\frac{31}{24},\frac32\right),\quad
 \left(-\frac{31}{24},-\frac12\right),\quad
 \left(-\frac{31}{24},-\frac32\right)
\tag{2}
\]
satisfy all five requirements with equality. Their largest norm is
\[
                     R_0=\frac{\sqrt{2257}}{24}<2.
\]
Consequently the unrestricted infimum in the geometric definition
equals the minimum over the product of five closed disks of radius
\(R_0\) and the closed tilt interval. That product is compact; (1)
defines a nonempty closed subset; and the largest point norm is
continuous. The minimum is therefore attained.

We will also use the explicit rational trial in Section 4 of
[stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md).
Its four prescribed corners and its fifth corner determined by the
last two spans satisfy (1) exactly. Equations (30) and (31) of that
note prove, by five displayed positive integer differences, that all
five squared norms are strictly less than
\[
                  q_U=\frac{1957767069}{500000000}.
\tag{3}
\]
This is a finite explicitly specified trial, not an assertion about
an enclosed root. If \(\widehat q\) is the squared geometric minimum,
we have
\[
                         \widehat q<q_U<4.
\tag{4}
\]

## 2. Exact scalar reduction on the complete domain

We include the full arbitrary-point reduction to make clear that no
sorted square coordinates or active-contact assumptions are used.
It is the geometric argument in Section 1 of
[the original five-corner reduction](../FIVE_CORNER_REDUCTION.md).

Suppose (1) is feasible in a disk of radius \(R<2\), and put
\(q=R^2\), \(P_{1y}=-u\). From
\(P_{2y}\ge P_{1y}+2\), the disk bounds give
\[
                    0<u\le R,\qquad P_{2y}\ge2-u>0.
\]
Define, in sequence,
\[
\begin{aligned}
 r&=\sqrt{q-u^2},&
 U&=\sqrt{q-(2-u)^2},&
 V&=3-U,\\
 Y&=\sqrt{q-V^2},&
 v&=2-Y,&
 w&=\sqrt{q-v^2}.
\end{aligned}
\tag{5}
\]
The first two roots exist by containment of \(P_1,P_2\), and
\[
 P_{1x}\le r,\qquad P_{2x}\le U,\qquad
 P_{3x}\le U-3=-V<0.
\]
Containment of \(P_3\) now proves that \(Y\) is real and
\(P_{3y}\le Y\). Thus
\[
                 P_{4y}\le Y-2=-v<0.
\]
Containment of \(P_4\) gives \(0<v\le R\), so the last root is real.
In particular, every step is justified by the original five points;
no radical branch is merely postulated.

For \(-R\le z\le0\), the largest possible value of
\(f_t\cdot P\) at height \(P_y=z\) is
\[
                 \psi(z)=s\sqrt{q-z^2}+cz.
\]
It is strictly increasing: on the open interval,
\[
                 \psi'(z)=c-\frac{sz}{\sqrt{q-z^2}}>0,
\]
and continuity covers the endpoints. Hence
\[
 e_t\cdot P_1\le cr-su,\qquad
 f_t\cdot P_4\le sw-cv.
\]
Set
\[
 K_1=2-c(r-1)+su,\qquad K_2=1+cv-s(w-1).
\tag{6}
\]
Both are positive. The horizontal span already gives \(R\ge3/2\),
and therefore
\[
 K_1\ge3-R>1,\qquad K_2\ge1-s(R-1)>0.
\tag{7}
\]
The last two requirements in (1) imply
\[
                 e_t\cdot P_5\le-K_1,\qquad
                 f_t\cdot P_5\le-K_2.
\]
Their signs permit squaring, giving the necessary condition
\[
                F(q,u,t):=K_1^2+K_2^2-q\le0.
\tag{8}
\]

Conversely, if (5) has its nonnegative roots, \(0\le u,v\le R<2\),
and (8) holds, the points
\[
 (r,-u),\quad (U,2-u),\quad (-V,2-v),\quad
 (-w,-v),\quad -K_1e_t-K_2f_t
\tag{9}
\]
lie in the disk and satisfy all five requirements with equality.
Thus (8) is equivalent to the full arbitrary-point feasibility
problem for \(R<2\).

### 2.1. The entire position domain is one interval

For completeness, the nonempty domain occurs exactly when
\(25/16\le R<2\). Define
\[
 L=2\sqrt{R-1},\qquad
 a_R=2-\sqrt{R^2-(3-L)^2}.
\]
Its complete position domain is
\[
                             a_R\le u\le R.
\tag{10}
\]
Indeed \(U\) increases with \(u\), its maximum is \(L\), and
\(v\le R\) is equivalent to \(V\le L\), or \(U\ge3-L\).
The interval is nonempty precisely when \(2L\ge3\), which is
\(R\ge25/16\). For \(R>25/16\), all roots are positive in the
open interval; only \(w\) vanishes at the left endpoint and only
\(r\) at the right endpoint.

For each fixed \(R,t\), \(F\) is strictly convex on the full closed
interval (10). Here is an endpoint-valid proof. In the variable
\(y=-u\), the function
\[
 b(y)=\sqrt{R^2-
       \left(3-\sqrt{R^2-(y+2)^2}\right)^2}-2=-v
\]
is concave: the inner upper semicircle is concave and the outer
upper semicircle, as a function of its inner horizontal coordinate,
is increasing and concave. Also
\[
 K_1(y)=2+c-c\sqrt{R^2-y^2}-sy
\]
is strictly convex. The function
\[
 \phi(b)=1+s-s\sqrt{R^2-b^2}-cb
\]
is convex and decreasing on \([-R,0]\), so \(K_2=\phi\circ b\)
is convex. Positivity (7) and the increasing convex square function
make \(K_1^2\) strictly convex and \(K_2^2\) convex. This proves
strict convexity of \(F\), including both radical endpoints.
These are the full-domain arguments of Sections 1 and 2 of
[the analytic five-corner reduction](../HUMAN_FIVE_CORNER.md);
no global localization claim from that older note is needed here.

## 3. One constant support excludes the whole high-tilt arc

We prove directly that (1) is impossible whenever
\[
 q\le Q:=\frac{9789}{2500},\qquad
               \arcsin\frac3{10}\le t\le\frac\pi4.
\tag{11}
\]
This argument applies to arbitrary real five-point coordinates.

Choose the constant positive weights on the five spans in (1):
\[
 (a,b,d,\eta,1)=
       \left(\frac{23}{30},\frac{31}{32},\frac9{10},\frac67,1\right).
\tag{12}
\]
The weighted demand is
\[
 B(t)=B_0+\eta s+c,\qquad
 B_0=2a+3b+2d+\eta+2.
\tag{13}
\]
Collecting the five point coefficients gives
\[
\begin{aligned}
 F_1&=(c,s-a),&
 F_2&=(b,a),&
 F_3&=(-b,d),\\
 F_4&=(-\eta s,\eta c-d),&
 F_5&=(\eta s-c,-\eta c-s).
\end{aligned}
\tag{14}
\]
Disk support therefore implies
\[
 B(t)\le\sum_i F_i\cdot P_i
       \le R\sum_i\|F_i\|=R D(t),
\tag{15}
\]
where
\[
\begin{aligned}
 D(t)&=K+g_1(t)+g_4(t),\\
 K&=\sqrt{a^2+b^2}+\sqrt{b^2+d^2}+\sqrt{1+\eta^2},\\
 g_1&=\sqrt{1+a^2-2as},\qquad
 g_4=\sqrt{d^2+\eta^2-2d\eta c}.
\end{aligned}
\tag{16}
\]
Let
\[
 \rho=\frac{4947}{2500},\qquad J(t)=B(t)-\rho D(t).
\tag{17}
\]
The exact comparison
\[
                 \rho^2-Q=\frac{309}{6250000}>0
\tag{18}
\]
will turn \(J>0\) into a contradiction to (15).

### 3.1. Strict concavity on the whole allowed tilt arc

For any positive norm
\[
 g(t)=\sqrt{A^2+B^2-2AB\cos(t-t_0)}
\]
direct differentiation gives
\[
          g''+\frac g4=\frac{(A^2-B^2)^2}{4g^3}\ge0.
\tag{19}
\]
Both norms in (16) are positive everywhere, since \(a\ne1\) and
\(d\ne\eta\). The identity applies to \(g_1\) with phase
\(t_0=\pi/2\), and to \(g_4\) with phase zero.

Throughout \(0\le t\le\pi/4\),
\[
                         g_1<\frac{13}{10},\qquad
                         g_4<\frac7{10}.
\tag{20}
\]
The first follows from
\[
 \left(\frac{13}{10}\right)^2-(1+a^2)=\frac{23}{225}>0.
\]
For the second use \(c\ge1/\sqrt2\), \(\sqrt2>7/5\), and
\[
 \left(\frac7{10}\right)^2
       -\left(d^2+\eta^2-\frac75d\eta\right)
                          =\frac{31}{1225}>0.
\]
Thus \(g_1+g_4<2\) on the entire interval, not merely at its
endpoints. Moreover the concave sinusoid \(\eta\sin t+\cos t\)
is at least one: its endpoint values are \(1\) and
\(13/(7\sqrt2)>1\). Equations (19) and (20) consequently give
\[
 J''\le-(\eta s+c)+\frac{\rho}{4}(g_1+g_4)
                  <-1+\frac{\rho}{2}<0.
\tag{21}
\]
It remains to check two endpoints of the single high-tilt arc.

### 3.2. A rational upper bound on the constant part

We claim
\[
                              K<\frac{31}{8}.
\tag{22}
\]
First, \(\sqrt{a^2+b^2}=593/480\). Put
\[
 C=\frac{1267}{480},\qquad
 A=\frac{44761}{25600}=b^2+d^2,\qquad
 B=\frac{85}{49}=1+\eta^2.
\]
The exact identities
\[
 C^2-A-B=\frac{983389}{282240}>0,\qquad
 (C^2-A-B)^2-4AB=\frac{603060361}{79659417600}>0
\]
permit two positive squarings and give \(\sqrt A+\sqrt B<C\).
Adding \(593/480\) proves (22).

### 3.3. The lower endpoint of the high-tilt arc

At \(t_0=\arcsin(3/10)\), one has
\[
 s=\frac3{10},\qquad
 c=\frac{\sqrt{91}}{10}>\frac{9539}{10000},\qquad
 g_1<\frac{17}{16},\qquad g_4<\frac{271}{1000}.
\]
The three positive square reserves, in the same order, are
\[
\begin{aligned}
 \frac{91}{100}-\left(\frac{9539}{10000}\right)^2
        &=\frac{7479}{100000000},\\
 \left(\frac{17}{16}\right)^2
       -\left(1+a^2-\frac35a\right)
        &=\frac{13}{11520},\\
 \left(\frac{271}{1000}\right)^2
       -\left(d^2+\eta^2-2d\eta\frac{9539}{10000}\right)
        &=\frac{23449}{49000000}.
\end{aligned}
\]
Consequently
\[
\begin{aligned}
 J(t_0)&>
 B_0+\frac3{10}\eta+\frac{9539}{10000}
       -\rho\left(\frac{31}{8}+\frac{17}{16}+\frac{271}{1000}\right)\\
       &=\frac{124871}{105000000}>0.
\end{aligned}
\tag{23}
\]

### 3.4. The upper endpoint

At \(t=\pi/4\),
\[
 c=s=\frac1{\sqrt2}>\frac{707}{1000},\qquad
 g_1<\frac{71}{100},\qquad g_4<\frac{27}{40}.
\]
The corresponding positive reserves are
\[
\begin{aligned}
 \frac12-\left(\frac{707}{1000}\right)^2
       &=\frac{151}{1000000},\\
 \left(\frac{71}{100}\right)^2
       -\left(1+a^2-2a\frac{707}{1000}\right)
       &=\frac7{18000},\\
 \left(\frac{27}{40}\right)^2
       -\left(d^2+\eta^2-2d\eta\frac{707}{1000}\right)
       &=\frac{3393}{1960000}.
\end{aligned}
\]
It follows that
\[
\begin{aligned}
 J(\pi/4)&>
 B_0+(\eta+1)\frac{707}{1000}
       -\rho\left(\frac{31}{8}+\frac{71}{100}+\frac{27}{40}\right)\\
       &=\frac{13001}{10500000}>0.
\end{aligned}
\tag{24}
\]
Concavity (21) and the two positive endpoint values prove \(J>0\)
on the complete interval (11). But (15) and \(R\le\sqrt Q<\rho\)
would give
\[
                       J\le(R-\rho)D<0.
\]
This proves the whole high-tilt exclusion with the one constant
choice (12).

## 4. The remaining arc and the exact stationary value

### 4.1. The nominal stress applies to every canonical chain

The single polynomial stress in
[the nominal gap proof](HAND_POSITIVE_TILT_NOMINAL_GAP.md) applies
on \(0\le s\le3/10\). Its collection does not require sorted square
coordinates. To verify that interface explicitly, for the chain
(9) take the following real formal coordinates:
\[
\begin{array}{lll}
 (a_A,b_A)=(r-\tfrac12,u-\tfrac12),&
 (a_B,b_B)=(U-\tfrac12,\tfrac32-u),\\
 (a_D,b_D)=(\tfrac32-v,\tfrac52-U),&
 (a_E,b_E)=(w-\tfrac12,v-\tfrac12),\\
 (a_H,b_H)=(K_2-\tfrac12,K_1-\tfrac12),&
 b_T=U-\tfrac32,\qquad b_G=\tfrac32-K_1.
\end{array}
\tag{25}
\]
The five shifted-corner norms squared equal
\(q,q,q,q,q+F\), and the seven nominal edge projections are
exactly \(1,W,1,1,1,1,W\), where \(W=(1+c+s)/2\).
These identities follow by substituting (5) and (6).

The completed-square inequality used in that stress,
\[
 F_xa+F_yb\le m q+\frac{F_x^2+F_y^2}{4m}
                           -\frac{F_x+F_y}{2},
\tag{26}
\]
holds for all real \(a,b\) satisfying
\((a+1/2)^2+(b+1/2)^2\le q\) and every \(m>0\).
The free G and T coordinates cancel. At \(s=0\) the E force and
mass both vanish and are omitted, exactly as in the nominal proof.
Thus no chart, square containment, core, or owner assertion is
being imported into this arbitrary five-point problem.

Writing \(g(q,s)\) for that explicit stress gap, we have
\[
                  F(q,u,t)\le0\ \Longrightarrow\ g(q,s)\le0.
\tag{27}
\]
The nominal proof establishes
\[
 g(q_U,s)\ge p(s),\qquad
 g(q,s)=g(q_U,s)+(q_U-q)\mathcal M(s),
\tag{28}
\]
where \(\mathcal M\) is its positive mass sum and
\[
 p(s)=\frac{38726637}{9929687500}
       -\frac{79}{1250}s+\frac{51}{200}s^2-\frac{s^3}{100}
       -\frac{27}{100}s^4-\frac3{10}s^5.
\tag{29}
\]
Its Section 3 proves \(p>0\) on both complete intervals
\([0,1/10]\) and \([79/500,3/10]\) by direct derivative signs.
Together with Section 3 above and \(q_U<Q\), this shows that
every feasible chain with \(q\le q_U\) satisfies
\[
              \frac1{10}<\sin t<\frac{79}{500}
                         <\frac1{\sqrt{26}}.
\tag{30}
\]
In particular \(0<t<\alpha:=\arctan(1/5)\).

### 4.2. A proved radius localization, used only after definition

On \(0\le s\le1/5\), Section 3.1 of
[stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
proves
\[
                   \mathcal M(s)>1,\qquad p(s)>-\frac1{8000}.
\tag{31}
\]
For \(q_L=19577/5000\), the exact radius difference is
\[
                q_U-q_L=\frac{67069}{500000000}.
\]
Therefore (28) and (31) give
\[
 g(q_L,s)>-\frac1{8000}+(q_U-q_L)
                  =\frac{4569}{500000000}>0.
\tag{32}
\]
Since the mass is positive, (27) excludes every \(q\le q_L\)
on the remaining tilt arc as well. Combining (4), (30), and (32),
any geometric minimizer has
\[
                 q_L<\widehat q<q_U,\qquad
                 0<\widehat t<\alpha.
\tag{33}
\]
These are conclusions about the naturally defined minimum.

### 4.3. Identification and uniqueness of the minimizing angle

Sections 1 and 2 of
[stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
prove that, for every \(q\) between \(q_L,q_U\) and every
\(0\le t\le\alpha\), the actual \(F\) has a position-stationary
point with
\[
                          \frac{87}{100}<u<\frac{11}{10}.
\tag{34}
\]
All radicals are positive on that full window. By the full-domain
strict convexity proved in Section 2.1 above, this point is the
unique global position minimum on the entire natural radical
interval (10).

Canonicalize any geometric minimizer by Section 2 and then minimize
in its position variable. The resulting value of \(F\) is at most
zero. It cannot be strictly negative: at the positive radicals in
(34), continuity would preserve \(F<0\) after a sufficiently small
decrease in \(q\), producing a feasible five-point chain of
smaller radius. Hence
\[
                     F(\widehat q,\widehat u,\widehat t)=0,
                     \qquad F_u=0.
\]
The tilt is interior by (33). If \(F_t\ne0\), a small tilt change
would make \(F<0\), again permitting a smaller radius. Therefore
\[
                              F=F_u=F_t=0.
\tag{35}
\]

Section 6 of
[stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
states and applies the actual-envelope uniqueness theorem on this
whole analytic strip. Its proof uses full-domain position convexity
and strict positivity of the envelope curvature at every critical
tilt, including critical points of positive defect. Its dependencies
are the circle and Hessian estimates in
[stationary geometry](STATIONARY_GEOMETRY.md) and Section 4 of
[the stationary-family proof](../HUMAN_FAMILY_CLOSURE.md); the earlier global
interval-enclosure section of the latter is not used.
The unique stationary zero supplied there is
\((q_*,u_*,t_*)\). Thus (35) gives
\[
                 \widehat q=q_*,\qquad
                 \widehat u=u_*,\qquad
                 \widehat t=t_*.
\tag{36}
\]
This proves that the natural geometric minimum equals \(q_*\),
and every minimizing five-point realization has the same tilt.
It remains to show that canonicalization did not discard any
noncanonical realizations at equality.

## 5. Positive contact forces and rigidity of the five points

At the solution in (36), put
\[
 a=s+\frac{cu}{r},\qquad
 p=\frac{(2-u)V}{U(2-v)}.
\]
All the quantities in the denominators, and \(s,c,a,p\), are
positive. The position equation in (35) is precisely
\[
              K_1a=K_2p\left(c+\frac{sv}{w}\right).
\tag{37}
\]
Choose positive weights on the five spans:
\[
\begin{aligned}
 \lambda_1&=a,&
 \lambda_2&=\frac{aU}{2-u},&
 \lambda_3&=\frac{\lambda_2(2-v)}{V},&
 \lambda_4&=\frac{K_2}{K_1},&
 \lambda_5&=1.
\end{aligned}
\tag{38}
\]
Equation (37) is equivalent to
\[
                  \lambda_3=\lambda_4
                                  \left(c+\frac{sv}{w}\right).
\tag{39}
\]
The five resulting point forces are
\[
\begin{aligned}
 F_1&=(c,s-\lambda_1),&
 F_2&=(\lambda_2,\lambda_1),&
 F_3&=(-\lambda_2,\lambda_3),\\
 F_4&=(-\lambda_4s,\lambda_4c-\lambda_3),&
 F_5&=(\lambda_4s-c,-\lambda_4c-s).
\end{aligned}
\tag{40}
\]
For the canonical points \(P_i^*\) in (9), (38)--(39) give
\[
                             F_i=2\mu_iP_i^*,
\tag{41}
\]
where, in the same point order,
\[
 (\mu_1,\mu_2,\mu_3,\mu_4,\mu_5)=
 \left(\frac{c}{2r},
       \frac{a}{2(2-u)},
       \frac{\lambda_2}{2V},
       \frac{\lambda_4s}{2w},
       \frac1{2K_1}\right)>0.
\tag{42}
\]
Every canonical point has norm \(R_\star=\sqrt{q_*}\), because
the first four satisfy their circle equations and \(F=0\) for
the fifth. All five spans are equalities. If \(B_*\) denotes
the weighted demand for (38), we obtain
\[
                  B_*=\sum_iF_i\cdot P_i^*
                      =R_\star\sum_i\|F_i\|.
\tag{43}
\]

Now take any other feasible five points \(Q_i\) at the minimizing
angle and radius. Positive contact weights and disk support give
\[
 B_*\le\sum_iF_i\cdot Q_i
             \le R_\star\sum_i\|F_i\|=B_*.
\tag{44}
\]
Each force is nonzero. Equality in each individual disk support
therefore forces
\[
                 Q_i=R_\star\frac{F_i}{\|F_i\|}=P_i^*.
\]
Equality in the positively weighted span sum also forces each
individual span to be exact. This proves uniqueness of the
original five points, not merely uniqueness of their canonical
replacement.

### 5.1. The tilt equation is rotational balance

Differentiate the two tilt-dependent span gaps at fixed points.
Their weighted rotational balance is
\[
 [f_t\cdot(P_1-P_5)+s]
       -\lambda_4[e_t\cdot(P_4-P_5)+c]=0.
\tag{45}
\]
Substitution of (9) and \(\lambda_4=K_2/K_1\) reduces this to
\[
 K_1\bigl[s(r-1)+cu\bigr]
                 =K_2\bigl[c(w-1)+sv\bigr],
\tag{46}
\]
which is exactly \(F_t=0\). Conversely (37), (46) and the
circle equalities give the force and rotational balances above.
Thus the two stationary equations are the equilibrium conditions
of the five contacts on the common circle.

## 6. Scope of the conclusion and dependency boundary

We have proved that the natural minimization over the full interval
\(0\le t\le\pi/4\) has exactly one minimizer in the chosen frame,
with all five circles and all five projected spans active. Its
radius is the existing exact sharp value \(R_\star=\sqrt{q_*}\).
No numerical enclosure is used to define or select it.

The proof uses only the following established analytic statements:

1. The finite rational trial and the position derivative signs in
   [stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md).
2. The one polynomial stress on its entire small-tilt arc in
   [the nominal stress](HAND_POSITIVE_TILT_NOMINAL_GAP.md), with the explicit
   arbitrary-coordinate adapter (25).
3. The actual-envelope critical-point theorem summarized in Section 6
   of the stationary-existence note.

The new Section 3 supplies the missing whole high-tilt arc with one
constant support. Sections 2 and 5 supply the complete arbitrary-point
equivalence and equality rigidity. None of these statements uses
the unrestricted eight-square theorem, so the model can in turn be
used to state that theorem's sharp constant without circularity.
The assertion concerns the global minimum and the stationary zero
in the proved analytic strip. It does not assert uniqueness of
stationary solutions at arbitrary larger radii.
