# Pair separation retaining the two physical frame variables

This chapter gives necessary pair inequalities for independently oriented
physical unit squares. The inequalities retain the original signed frame
components, so a finite table may use their correlation with the same
originals' containment rows. No whole-original or packing exclusion is
claimed here.

Let the canonical frames of two originals P,T be

\[
 u_i=(a_i,b_i)=(\cos\theta_i,\sin\theta_i),\qquad
 v_i=(-b_i,a_i),\qquad |\theta_i|\le\pi/4.
\]

Put delta=|theta_P-theta_T|, so 0<=delta<=pi/2. The sum of
the two supports on any side axis of either original is exactly

\[
 R_{PT}=\frac{1+\cos\delta+\sin\delta}{2}\ge1.       \tag{1}
\]

The physical separating-axis criterion gives an actual owned unit
normal n with n dot(c_T-c_P)>=R_PT. Consequently

\[
                         |c_T-c_P|\ge R_{PT}.          \tag{2}
\]

This implication uses physical nonoverlap. Incircle separation alone
would give only the weaker right side one.

## 1. A simple rational coefficient from the largest relative angle

Suppose delta<=2 arctan z, where 0<=z<=1 is rational. Then

\[
 R_{PT}\ge1+k_0|b_P-b_T|,
 \qquad k_0=\frac{1-z}{2+z^2}.                         \tag{3}
\]

To prove this, put t=delta/2 and m=(theta_P+theta_T)/2. The
elementary difference identities give

\[
 |b_P-b_T|=2\cos m\sin t\le2\sin t,
 \qquad R_{PT}-1=\sin t(\cos t-\sin t).                \tag{4}
\]

The factor cos t-sin t decreases for 0<=t<=pi/4. At the
upper endpoint it is (1-z)/sqrt(1+z^2). Since
sqrt(1+z^2)<=1+z^2/2 and 1-z>=0, (4) yields

\[
 R_{PT}-1\ge
 \frac{|b_P-b_T|}{2}\frac{1-z}{1+z^2/2}
 =k_0|b_P-b_T|.
\]

For an enlarged angle bound with z>=1, set k_0=0 and use (1).
The aligned case delta=0 is included without division by sin t.

For signed half-angle intervals
w_P in [l_P,u_P], w_T in [l_T,u_T], with all endpoints in
(-1,1), a rational upper bound for tan(delta/2) is

\[
 z=\max\left\{
 \frac{|u_P-l_T|}{1+u_P l_T},
 \frac{|u_T-l_P|}{1+u_T l_P}\right\}.                  \tag{5}
\]

Indeed theta_i=2 arctan w_i, the largest difference of two
angles in intervals occurs at opposite endpoints, and the tangent
subtraction formula gives (5). All its denominators are positive.
The formula remains a necessary bound when the rational intervals
extend slightly beyond the physical canonical range.

## 2. A stronger coefficient for frames with the same tilt sign

If theta_P theta_T>=0, then |m|>=t. Since both are at most
pi/4, cos m<=cos t. Equation (4) therefore gives

\[
 R_{PT}\ge1+k_{\rm same}|b_P-b_T|,
 \qquad k_{\rm same}=\frac{1-z}{2},                    \tag{6}
\]

whenever tan(delta/2)<=z<=1. To check this when delta>0,
divide the two expressions in (4):

\[
 \frac{R_{PT}-1}{|b_P-b_T|}
 =\frac{\cos t-\sin t}{2\cos m}
 \ge\frac{1-\tan t}{2}\ge\frac{1-z}{2}.
\]

The case delta=0 is immediate. With only a common tilt sign and
canonicality, delta<=pi/4, and sqrt(2)-1<5/12 permits the
uniform rational choice k_same=7/24. The exact coefficient in
(6) is attained when one angle is zero and the other has
tan(delta/2)=z within the canonical range.

## 3. An exact rational coefficient on any signed half-angle box

There is a stronger rule that avoids square roots and does not require
clipping enlarged rational endpoints to the canonical range. Define

\[
 F(w,v)=\frac{1+wv-|w-v|}{2(1-wv)},
 \qquad -1<w,v<1.                                    \tag{7}
\]

For the actual physical half-angle values, the exact identity is

\[
                    R_{PT}-1=F(w_P,w_T)|b_P-b_T|.       \tag{8}
\]

For distinct angles, (8) follows from (4) and

\[
 \cos t=\frac{1+w_Pw_T}
                {\sqrt{(1+w_P^2)(1+w_T^2)}},\quad
 \sin t=\frac{|w_P-w_T|}
                {\sqrt{(1+w_P^2)(1+w_T^2)}},\quad
 \cos m=\frac{1-w_Pw_T}
                {\sqrt{(1+w_P^2)(1+w_T^2)}}.
\]

At equal angles both sides of (8) vanish, so no exceptional case is
discarded. Identity (8) is asserted for the physical canonical values;
the auxiliary function F can also be evaluated at enlarged endpoints.

**Endpoint-minimum lemma.** The minimum of F on any closed rectangle
[l,u] times [p,q] contained in (-1,1)^2 is the minimum of its
four corner values.

*Proof.* Fix v. On the two sides of w=v, differentiation gives

\[
 \frac{\partial F}{\partial w}=
 \begin{cases}
 (1+2v-v^2)/(2(1-wv)^2),&w<v,\\
 (v^2+2v-1)/(2(1-wv)^2),&w>v.
 \end{cases}                                         \tag{9}
\]

Each branch is monotone. The numerator on the left exceeds that
on the right by 2(1-v^2)>0. Thus crossing w=v can change an
increasing branch to a decreasing branch, but cannot change a
decreasing branch to an increasing branch. The continuous function
has an interval minimum at one of its endpoints, including when
one derivative is zero. Hence
F(w,v)>=min(F(l,v),F(u,v)). Symmetry in w,v applies the same
argument to each of these two endpoint functions and proves the
four-corner assertion. \(\square\)

Set

\[
 k_{\rm box}=\max\left\{0,
       \min_{w\in\{l_P,u_P\},\ v\in\{l_T,u_T\}}F(w,v)
                         \right\}.                    \tag{10}
\]

Equations (1), (8) and the lemma prove

\[
                  R_{PT}\ge1+k_{\rm box}|b_P-b_T|.     \tag{11}
\]

Every operation in (10) is rational. If enlarged endpoints make
the minimum negative, clipping the coefficient to zero is justified
by R_PT>=1. This explicitly covers the enlarged intervals with
endpoints +/-5/12; no physical orientations are removed.

For example, when both half-angle intervals are [1/10,1/5],
formula (5) gives z=5/51. The three valid coefficients are

| Rule | Coefficient |
|---|---:|
| General relative-angle bound (3) | 2346/5227 |
| Same-sign bound (6) | 23/51 |
| Exact box rule (10) | 23/49 |

Any maximum of independently applicable coefficients remains valid.
In particular the same-sign bound may be retained when an enlarged
signed box makes the general four-corner coefficient zero.

## 4. Affine necessary rows retaining b_P and b_T

Let k>=0 be any coefficient proved above. Equations (2) and (11)
imply

\[
 |c_T-c_P|^2\ge(1+k|b_P-b_T|)^2
                    \ge1+2k|b_P-b_T|.                \tag{12}
\]

Suppose proved difference intervals are
L_x<=Delta_x<=U_x and L_y<=Delta_y<=U_y. The elementary
secants give

\[
 |c_T-c_P|^2\le
 (L_x+U_x)\Delta_x-L_xU_x
 +(L_y+U_y)\Delta_y-L_yU_y=:S(\Delta).                 \tag{13}
\]

Therefore both of the following affine rows hold simultaneously:

\[
 S(\Delta)\ge1+2k(b_P-b_T),\qquad
 S(\Delta)\ge1-2k(b_P-b_T).                            \tag{14}
\]

No sign split on b_P-b_T is needed. When a coordinate interval
is a singleton, its expression in (13) still equals the exact
squared coordinate value. The intervals must be proved before
using their secants.

The b variables in (14) are the actual original frame components.
Other rows involving a_i, b_i, h_i or g_i must be necessary
conditions for these same frames. Independent interval relaxation
of some relations can weaken a contradiction search, but it cannot
justify a stronger row or change the underlying originals.

These are additional necessary inequalities for a finite hand table.
They do not provide the table's case cover, any missing bound
deduction, or a whole-Cb882 closure.
