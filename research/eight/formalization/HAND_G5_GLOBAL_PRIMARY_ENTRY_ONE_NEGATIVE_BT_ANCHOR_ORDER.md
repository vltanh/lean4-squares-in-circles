# Original anchor order at the one remaining aligned negative BT endpoint

## 1. Whole-domain statement

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,
 \quad K=13/12,\quad S_0=2\sqrt{Q-1}-3,
 \quad p=41/40,\quad \varepsilon=27/160000.
\tag{1}
\]
Retain a sorted true-core necessary cycle at a common
circle ceiling q<=Q and with real frame spread at most h.
H,A are nonnegative, B,D,E are nonpositive, and G has
arbitrary signed tangent. Retain the actual owners
\[
 HG,AB,TD\in\{0,2\},\qquad GA0,\quad BT3,
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
For a necessary system stated separately from an original
candidate retain the original implication HG2=>y_G<0.
Assume TD is aligned and BT2 is unavailable:
\[
             \theta_T=\theta_D<\theta_B.
\tag{3}
\]
There is no assumption on AB alignment, G's sign, either
mixed error, E's radial kind, or the radial boundary of H
or D.

**Anchor-order theorem.** Every such system satisfies
\[
                         \theta_H>\theta_D.
\tag{4}
\]
All coordinates, frames and actual witnesses remain unchanged
in this theorem. In particular, (4) is available as a barrier
at every later necessary descendant which still satisfies
(2)--(3). The proof does not reflect E's sign.

## 2. The negative-primary cut and a formal middle endpoint

Translate D's frame to zero and put
\[
 u=\theta_B-\theta_D,\qquad z=\theta_G-\theta_D,
 \qquad g=-y_G,\qquad t=y_T.
\tag{5}
\]
The actual negative BT3 comparison with aligned TD gives
\[
 0<u<.09,\qquad .1<t<.156,\qquad a_T\ge7/12,
\]
\[
 1+(t+1/2)^2+K^2+2(t+1/2)\cos u+2K\sin u<Q.
\tag{6}
\]
These are the E-independent D/T/B versions of Sections
2--3 of the
[aligned negative-GA local comparison](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md).
They use the actual unavailable BT2 and do not require a
normal sign at G.

Define the two scalar quantities
\[
 t_e=(t+1/2)\cos u+K\sin u-1/2,
 \qquad s=t_e-t.
\tag{7}
\]
Actual BT3 gives a_B>=1+t_e. Thus the original GA and AB
inequalities, together with this last inequality, have
exactly the middle-path algebra of a zero-error BT2
reference at B's existing frame, with signed tangent t_e.
This is a comparison of three inequalities. No new T
state, circle, witness, or geometric motion is asserted.
The reference frame is an original frame, so its use
does not enlarge the frame interval.

The elementary bounds sin u>=u-u^3/6 and
1-cos u<=u^2/2 imply
\[
 s\ge u\{K(1-.09^2/6)-.656(.09)/2\}
                       >\frac{21}{20}u>pu.
\tag{8}
\]
We also need the following slightly sharper tangent cap:
\[
                           t<.156-.64u.
\tag{9}
\]
To prove it, complete the square in (6):
\[
 t<T(u):=\sqrt{Q-(K+\sin u)^2}-\cos u-1/2.
\]
At zero, T(0)<.156 by positive squaring. The assertion
T'(u)<-.64, after squaring positive quantities and putting
w=sin u, is equivalent to positivity of
\[
 \begin{split}
 &(K+w)^2(1+.64^2+1.28w)-Q(w+.64)^2\\
 &=\frac{2840201}{56250000}
    -\frac{128141}{281250}w
    +\frac{401}{1500}w^2+\frac{32}{25}w^3.
 \end{split}
\tag{10}
\]
For 0<=w<=.09 its constant and linear terms alone exceed
.0094. This proves (9) on the entire interval.

Here is the precise correction used when replacing the
BT reference by (7). For either mu=1 or mu=.94,
\[
 (1-\mu)t+pu-\mu s\le(1-\mu)t_*,
 \qquad t_*=\begin{cases}.156,&\mu=.94,\\0,&\mu=1.
                        \end{cases}
\tag{11}
\]
For mu=1 this is (8). For mu=.94, (9), t+1/2<.656,
and the same Taylor bounds give an upper bound of u times
\[
 p-.94K-.06(.64)+.94(.656)\frac{.09}{2}
                           +.94K\frac{.09^2}{6}<-.0026
\tag{12}
\]
for the left side of (11) minus .06(.156).
Consequently all occurrences of u can be removed from the
middle stress below with the exact correction (11).

## 3. The actual HG contact gives a sharper positive-angle charge

Suppose for contradiction that H<=D. We first have z>0.
Indeed the original all-sign HG zero charge, aligned TD,
and the old p_0=50/49 mixed-endpoint estimate give
\[
                       g+t+p_0z>S_0+\varepsilon.
\tag{13}
\]
The HG charge is the unchanged actual inequality proved
in Section 5 of the
[signed middle-path theorem](HAND_G5_SIGNED_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md).
It uses the retained HG2 sign implication where needed.
If z<=0, apply that theorem's middle estimate (5) to the
formal reference (7), with reversed width u-z>=0:
\[
 g+t+p_0z\le S_0+\tfrac34(u-z)-s+p_0z<S_0.
\]
The last inequality uses (8) and z<=0. This contradicts
(13), and proves z>0 under the proposed H<=D assumption.

Put r=theta_D-theta_H>=0 and v=theta_G-theta_H=z+r>0.
The original HG0 inequality is
\[
                 b_H+g+a_G\sin v+y_G(1-\cos v)\ge W(v).
\]
For HG2 the additional expression is instead
a_H sin v-b_H(1-cos v), which has no larger upper bound.
On every contained sorted corner the following support
bounds therefore suffice:
\[
 \begin{array}{ll}
 a_G\sin v+y_G(1-\cos v)\le a_0\sin v,
       &0\le v\le1/2,\\
 a_G\sin v+y_G(1-\cos v)
   \le2R\sin(v/2)-\tfrac12(\sin v+1-\cos v),
       &1/2\le v\le h,
 \end{array}
\tag{14}
\]
where a_0=sqrt(Q-1/4)-1/2. The first line uses the actual
transverse floor |y_G|>=0: the unrestricted corner support
has transverse component R sin(v/2)<1/2 on this interval.
The second line is ordinary full-circle support and is
valid for either sign of y_G. For HG2, the bound a_0 sin v
holds on the whole interval and is no larger than the
second support in (14). No G sign has been imposed.

Define a lower bound for the resulting charged excess:
\[
 f(v)=\begin{cases}
 pv-k_0\sin v-\tfrac12(1-\cos v),&0\le v\le1/2,\\
 pv-2R\sin(v/2)+\sin v,&1/2\le v\le h,
 \end{cases}
 \qquad k_0=\sqrt{Q-1/4}-1.
\tag{15}
\]
Using the appropriate line of (14), add aligned TD and
the strengthened actual mixed-endpoint budget
\[
                  b_H+b_D+pr+S_0<2-\varepsilon
\]
from
[the coefficient-41/40 endpoint note](HAND_G5_GLOBAL_PRIMARY_ENTRY_STRONGER_MIXED_ENDPOINT_BUDGET.md).
This gives, on the original coordinates,
\[
                         g+t+pz>S_0+f(v)+\varepsilon.
\tag{16}
\]

The two elementary bounds needed later are
\[
 f(v)>0\quad(0<v\le h),\qquad
 f(v)>.004\quad(.04\le v\le h).
\tag{17}
\]
Here C_j and S_j denote the alternating Taylor
polynomials for cosine and sine through degree j.
For the first branch, f''=k_0 sin v-(cos v)/2<0 on
[0,1/2]. The strict sign follows already from
\[
 .914576\,S_5(1/2)<\tfrac12 C_6(1/2),
 \qquad k_0<.914576.
\]
Its values at .04 and 1/2 exceed .004 by the corresponding
degree-five upper sine and degree-six lower cosine bounds;
also f(0)=0. Concavity proves both claims on this branch.
The second branch has second derivative
\[
              \sin(v/2)\{R/2-2\cos(v/2)\}<0.
\]
Its two endpoint values exceed .004 using S_5(v/2),
S_7(v), and R<1.97878751. This proves (17) without any
subdivision or sampling of an angle interval.

If L:=z-u<0, the same reversed-middle estimate as above
and (8) give
\[
 g+t+pz\le S_0+\tfrac34(u-z)-s+pz<S_0,
\]
because 0<z<u. This contradicts (16)--(17). Hence only
\[
                         0\le L=z-u\le h
\tag{18}
\]
remains.

## 4. Exact concentration of the original A frame

Use weights 1,lambda,mu on the original GA, AB and the
formal zero BT inequality in Section 2. Choose
\[
 (\lambda,\mu)=
 \begin{cases}
 (.605,.94),&0\le L\le.04,\\
 (.59+L/2,1),&.04\le L\le h.
 \end{cases}
\tag{19}
\]
Either choice is available at L=.04. These are two
continuous scalar stresses, not an inventory of angle
boxes. Put x=theta_A-theta_G and d=theta_B-theta_A,
so x+d=-L. Define
\[
 N_a(w)=\sqrt{a^2+\lambda^2+2a\lambda\sin w},
 \qquad \phi_+(w)=\cos w+(\sin w)_+.
\]
For actual AB0, collecting the two shifted A/B circles
once each gives exactly
\[
 \begin{split}
 g+\mu t_e\le{}&R\{N_1(x)+N_\mu(d)\}
 -\tfrac12-\tfrac32\mu-\lambda
 -\phi_+(x)-\lambda\phi_+(d).
 \end{split}
\tag{20}
\]
The A force is (cos x,sin x+lambda); the B force is
(mu+lambda sin d,lambda cos d). Thus (20) includes
every half-shift and retains the actual AB owner.

The maximum of (20), for fixed L, is at A=G or A=B.
Here are whole-angle details, including A outside their
frame interval. The functions
\[
 RN_a(-w)-c\cos w,\qquad
 RN_a(w)-c(\cos w+\sin w),\qquad 0\le w\le h,
\tag{21}
\]
are strictly convex for the coefficients used here:
(a,c)=(1,1) or (mu,lambda). This follows from the
whole-interval two-angle norm lemma in Section 3 of
[the angle-concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md).
In fact every ratio of the two positive norm coefficients
is at least .605, and its bound C_0/min(a,lambda)<.762,
together with cos h>.7648, gives the negative-angle
convexity even when c is the smaller coefficient. The
positive-angle convexity is that lemma's U concavity;
increasing c adds the convex function -(c-min(a,lambda))
(cos w+sin w).

If B<=A<=G, both x,d are nonpositive. Convexity reduces
their sum to the two endpoints. If A>=G, differentiation
as A moves upward gives at most
\[
                            .72-1.2\lambda<0.
\tag{22}
\]
The first constant is the bound for the positive A term
in (21), proved by the H_1 comparison in Section 5 of
[the small-sign middle theorem](HAND_G5_GLOBAL_SMALL_WRONG_INTERMEDIATE_SIGNS.md).
For the second term, convexity reduces its derivative to h.
Writing rho=lambda/mu, one has .61<=rho<=.94 and
\[
 \sqrt{1+\rho^2-2\rho\sin h}<.820044,
 \qquad
 \frac{R\cos h}{.820044}-\sin h>1.2.
\tag{23}
\]
The squared norm is convex in rho, so its two endpoint
checks prove the first bound throughout that weight range.

If A<=B, differentiate while A moves downward. Convexity
again bounds the derivative by its h values, namely
\[
 \lambda\{C(\rho)-G(\lambda)\},
\]
\[
 C(\rho)=\frac{R\cos h}{\sqrt{1+\rho^2+2\rho\sin h}}
                         -\cos h+\sin h,
 \quad
 G(\lambda)=\frac{R\cos h}{\sqrt{1+\lambda^2-2\lambda\sin h}}
                         -\frac{\sin h}{\lambda}.
\tag{24}
\]
For the second family of (19), rho=lambda>=.61,
C(rho)<.910 and G(lambda)>.920. The first function
decreases in rho. The second is concave on [.61,1]:
if n^2=(lambda-sin h)^2+cos^2 h, its second derivative is
\[
 -\frac{R\cos h\{\cos^2h-2(\lambda-\sin h)^2\}}{n^5}
                         -\frac{2\sin h}{\lambda^3}<0.
\]
Its two endpoint lower bounds therefore suffice. For
the first family, rho=.605/.94>.64,
C(rho)<.893 and G(.605)>.911. Thus the derivative is
strictly negative in both cases. These constants follow
by positive squaring and C_6<=cos<=C_4,
S_7<=sin<=S_5 at h. This completes the two-endpoint
reduction for every original AB0 frame.

For actual AB2 the force norms are already independent
of A, namely N_1(-L) and N_mu(0). Its remaining penalty
satisfies
\[
                     \phi_+(x)+\lambda\phi_+(d)
                                      \ge\cos L+\lambda.
\tag{25}
\]
Between B and G this is concavity and lambda<=1.
Above G, the excess over x=0, divided by 2 sin(x/2),
is cos(x/2)-sin(x/2)-lambda sin(L+x/2)>0; use L+x<=h
and cos(h/2)>2 sin(h/2). Below B, concavity in d leaves
d=0 or d=h-L. The latter endpoint satisfies (25) iff
\[
 \lambda\ge J(L):=
 \frac{\cos L-\cos h}{\cos(h-L)+\sin(h-L)-1}.
\tag{26}
\]
Interpret its value at L=h by continuity. With
w=(h-L)/2,
\[
 J(L)=\sin h-(\cos h-\sin h)
                    \frac{\tan w}{1-\tan w}.
\]
Here J(0)<.576 and J'(L)<.18 throughout [0,h]. Indeed
tan(h/2)<.3661 and cos h-sin h<.121 bound the derivative
by .121(1+.3661^2)/(2(1-.3661)^2)<.18.
Both choices in (19) exceed .576+.18L on their domains.
This proves (25) for all AB2 frames, including weak ties.

## 5. The two exact scalar endpoints

Apply the correction (11) to (20) and its AB2 version.
Every original system in (18) satisfies
\[
                    g+t+pz-S_0\le\max\{M_B(L),M_G(L)\},
\tag{27}
\]
where
\[
 \begin{split}
 M_B(L)={}&R\{N_1(-L)+N_\mu(0)\}
 -\tfrac12-\tfrac32\mu-2\lambda-\cos L
 +(1-\mu)t_*+pL-S_0,\\
 M_G(L)={}&R\{N_1(0)+N_\mu(-L)\}
 -\tfrac32-\tfrac32\mu-\lambda-\lambda\cos L
 +(1-\mu)t_*+pL-S_0.
 \end{split}
\tag{28}
\]
Actual AB2 needs only M_B. For mu=1 the two norm sums
agree, and M_G<=M_B since lambda<=1.

For 0<=L<=.04, lambda=.605 and mu=.94 are constant.
Both functions (28) are convex by (21), so only their
two interval endpoints are needed. Put
\[
 R_+=1.97878751,\quad S_-=.41502562,
\]
\[
 n_{10}=1.168770722,\quad n_{\mu0}=1.117866272,
 \quad n_{1e}=1.147884100,\quad n_{\mu e}=1.097333647.
\tag{29}
\]
Positive squaring proves R<R_+, S_0>S_-, and that these
four n values are upper bounds for the respective norms
at L=0 or L=.04. Use S_7(.04) in the two negative-error
norms and C_6(.04) in the cosine terms. Direct rational
substitution gives
\[
 M_B(0)=M_G(0)<-.0008968,
 \quad M_B(.04)<-.0004271,
 \quad M_G(.04)<-.0000426.
\tag{30}
\]
Thus the whole small interval has negative middle excess.

For the entire second interval .04<=L<=.7, put
lambda=.59+L/2 and mu=1. We prove the single bound
\[
                            M_B(L)<.004.
\tag{31}
\]
Here is one exact polynomial certificate on that whole
interval. Write x=L-.29, so |x|<=.41, and define the
two positive quadratic polynomials
\[
 \begin{split}
 r_0(x)&=1.241058016+.296118308x+.065393376x^2,\\
 r_1(x)&=1.058241574-.453379807x-.332448780x^2.
 \end{split}
\tag{32}
\]
Each is greater than .816 by the coefficient norm on
|x|<=.41. Let
\[
 A=1+\lambda^2-2\lambda S_7(L),\qquad B=1+\lambda^2,
\]
\[
 E=2+2\lambda+C_6(L)+S_-+.004-pL,
\]
\[
 P(x)=2r_0r_1E-R_+\{r_1(B+r_0^2)+r_0(A+r_1^2)\}.
\tag{33}
\]
This is one degree-ten polynomial with rational
coefficients, defined explicitly by (32)--(33). If
P(x)=sum_{j=0}^{10} c_j x^j, exact coefficient arithmetic
gives
\[
 c_0>.000510,\qquad |c_1|<.000521,
 \qquad
 c_2-\sum_{j=3}^{10}|c_j|(.41)^{j-2}>.1009.
\tag{34}
\]
Hence the single completed-square estimate
\[
 P(x)>.000510-.000521|x|+.1009x^2
 \ge .000510-\frac{(.000521)^2}{4(.1009)}>.000509
\tag{35}
\]
holds on the whole interval. This is a coefficient norm
identity for one polynomial, not a collection of accepted
angle cells. The exact expressions in (32)--(34) suffice
to reproduce it by rational addition and multiplication.

Finally sqrt Z<=(Z+r^2)/(2r) for r>0, applied to the
two norms with r_0 and r_1, together with S_7<=sin and
C_6<=cos, turns (35) directly into (31). The polynomial
masses require only positivity, not an approximation or
an unproved error estimate.

## 6. Contradiction and unchanged-state scope

For 0<=L<=.04, (27)--(30) contradict (16)--(17).
For .04<=L<=h, the original HG error v=z+r satisfies
v>=z=L+u>=L>=.04. Equations (27),(31) then contradict
the strict lower bound .004+epsilon in (16)--(17).

Every case of the assumption H<=D has been excluded.
This proves (4) for both original AB owners, either
actual HG owner, arbitrary G sign subject to its original
owner implication, all four mixed-owner pairs, every
mixed-error sign, and all original weak contacts.

There was no geometric deformation and no radial lift.
The only formal reference was the scalar inequality
a_B>=1+t_e, used inside a two-circle stress with its
correction (11). The proof uses the true core only in the
genuine negative-primary cut and in the already proved
mixed-endpoint/zero-charge estimates. It therefore remains
valid at the same ceiling for all later necessary
descendants satisfying the stated hypotheses.
