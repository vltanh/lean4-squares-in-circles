# A coupled exclusion on the aligned-zero, E-zero branch

## 1. Exact scope

This note excludes one continuous **seven-vertex** branch by a single
global calculus argument. It keeps each vertex shared by its two
incident edges and allows arbitrary original radial states and weak
contacts. It does not establish that an arbitrary candidate cycle
reduces to this branch. In particular, arbitrary zero-edge errors,
the negative E interior, and the other quarter-owner branches remain
outside this theorem. This is not a closure of G4.

Put \(Q=9789/2500\). Suppose the candidate has the signs
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
     =(b_H,-b_G,b_A,-b_B,b_T,-b_D,0),\qquad b_i\ge0,
\]
the original bounds
\[
 a_i\ge b_i,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le Q,
\]
and, after a common frame shift,
\[
 \theta_H=\theta_G=\theta_A=\theta_B=0,
 \qquad \theta_T=\theta_D=-(\delta+\epsilon),
 \qquad \theta_E=-\epsilon,
 \qquad \delta,\epsilon\ge0,
 \quad\delta+\epsilon\le7/10.                                  \tag{1}
\]
Assume the originally feasible witnesses are transverse on the
three zero-quarter edges, are axis 0 or 1 on GA, axis 2 on BT,
axis 3 on DE, and axis 1 on EH. These are explicit hypotheses,
not owner conclusions imported from a later mismatch stage.

**Theorem.** No such candidate exists. In fact the necessary scalar
derived below is smaller than its required value by more than
\(149/500000\).

The theorem assumes no contact equality or outer-boundary equality.
The physical-gap and core-avoidance conditions may be retained;
the proof does not need them. It therefore proves an exclusion in
a larger domain of the original seven shared centers.

## 2. Eliminate the shared vertices monotonically

Define
\[
 f(b)=\sqrt{Q-(b+1/2)^2}-1/2,
 \qquad C=\sqrt{Q/2}-1/2,
 \qquad v=\sqrt{Q-1/4}-1,
\]
and, for \(0\le t\le7/10\),
\[
 u(t)=1+\tfrac12\cos t-v\sin t,
 \qquad h(t)=\sqrt{Q-u(t)^2}-1/2,
 \qquad B(t)=\min\{C,h(t)\}.                                   \tag{2}
\]
Here \(u>0\), \(u'<0\), and \(h'>0\) throughout this interval.

The actual original witnesses give
\[
\begin{split}
 b_H+b_G&\ge1,& b_A+b_B&\ge1,& b_T+b_D&\ge1,\\
 a_A-b_G&\ge1,\\
 a_B\cos(\delta+\epsilon)-b_B\sin(\delta+\epsilon)-b_T
     &\ge\frac{1+\cos(\delta+\epsilon)+\sin(\delta+\epsilon)}2,\\
 a_D+a_E\sin\delta&\ge\frac{1+\cos\delta+\sin\delta}2,\\
 a_H+a_E\sin\epsilon&\ge\frac{1+\cos\epsilon+\sin\epsilon}2.
\end{split}                                                     \tag{3}
\]
Since the unchanged E state has \(b_E=0\), containment gives
\(a_E\le v+1/2\). The last two inequalities imply
\[
             b_H\le B(\epsilon),\qquad b_D\le B(\delta).       \tag{4}
\]
The cap C uses only \(a_i\ge b_i\). The other bound in (4) uses
the lower primary coordinate in (3) and the decreasing outer
function f; it does not replace either actual primary coordinate.

Set
\[
 z(\epsilon)=f(2-B(\epsilon)),\quad
 Y(\epsilon)=\frac32-z(\epsilon),\quad
 X(\epsilon)=\sqrt{Q-Y(\epsilon)^2}-1.                          \tag{5}
\]
Successive use of the same H, G, A, and B states gives
\[
 b_G\ge1-b_H,\qquad a_A\ge2-b_H\ge2-B(\epsilon),
 \qquad b_A\le z(\epsilon),
\]
\[
 b_B\ge1-z(\epsilon),\qquad a_B\le f(1-z(\epsilon)).           \tag{6}
\]
Since both sine and cosine of \(\delta+\epsilon\) are
nonnegative, insertion of (4)--(6) into the BT inequality yields
the necessary condition
\[
 \boxed{\ B(\delta)+X(\epsilon)\cos(\delta+\epsilon)
                   -Y(\epsilon)\sin(\delta+\epsilon)
                       \ge\frac32.\ }                        \tag{7}
\]
This is a consequence of the actual seven vertices. Independently
optimized pair states have not been summed.

## 3. Reduce the scalar maximization to one small square

The increasing function h has exactly one crossing \(h(t_C)=C\)
in \(0<t_C<11/100\). For the upper endpoint, the elementary
Taylor bounds give
\[
 u(11/100)<1397/1000<1399/1000<\sqrt{Q/2}.
\]
At zero the reverse comparison follows directly from Q. Because
u is positive and decreasing, this proves the crossing statement.

Beyond \(t_C\), B is constant. If \(\epsilon>t_C\), decreasing
it to \(t_C\) leaves both quantities in (5) unchanged and
increases the left side of (7): the derivative of its trigonometric
part with respect to the sum angle is
\(-X\sin(\delta+\epsilon)-Y\cos(\delta+\epsilon)<0\).
The same argument then decreases \(\delta>t_C\) to \(t_C\).
These are comparisons of an explicitly defined scalar upper
bound, not a deformation of the original configuration.

It is enough, therefore, to maximize the uncapped function
\[
 F(e,d)=h(d)+X(e)\cos(e+d)-Y(e)\sin(e+d)                       \tag{8}
\]
on the single square \(0\le e,d\le11/100\), where in (5) we now
use \(B(e)=h(e)\). We will prove
\[
                      F(e,d)<\frac{1499702}{10^6}<\frac32.    \tag{9}
\]

## 4. Uniform derivative bounds, without subdivision

Write \(R^2=1/4+v^2\). Positive squaring gives
\[
                  1.0864<R^2<1.08645.
\]
On the interval in (8), the degree-six cosine lower bound and
degree-five sine upper bound give
\[
 1.3965<u(t)\le1.5,
 \qquad .79<h(t)<.902.                                       \tag{10}
\]
For an exact lower-endpoint check, with \(t=11/100\),
\[
 1+\tfrac12(1-t^2/2+t^4/24-t^6/720)
       -.9146(t-t^3/6+t^5/120)-1.3965
   =\frac{2693339893637}{36000000000000000}>0.
\]

Direct differentiation yields
\[
 h'(t)=\frac{u\sqrt{R^2-(u-1)^2}}{\sqrt{Q-u^2}},
 \qquad
 h''(t)=\frac{N(u)}{(Q-u^2)^{3/2}},
\]
\[
 N(u)=-u^4+u^3+2Qu^2-3Qu+Q(1-R^2).                            \tag{11}
\]
The sign of the derivative of the last expression with respect to
u is the sign of
\[
 D(u)=u^5-2Qu^3-3Qu^2+Q(4Q+3-3R^2)u-3Q^2.
\]
Put \(u=1.39+x\), \(0\le x\le.11\). Replacing \(R^2\)
by its lower bound gives the single polynomial upper bound
\[
 D(u)\le-.6997472141+.92973341x-17.546714x^2
                     +11.4898x^3+6.95x^4+x^5
       \le-.5811499606<0.                                    \tag{12}
\]
The second comparison discards the negative quadratic term and
uses \(x\le.11\) in the remaining positive terms.
Thus the expression for \(h''\) decreases with u. At \(u=1.39\),
with the lower value \(R^2=1.0864\), its numerator is
\(-258308973/10^8\), its denominator before the exponent is
\(3967/2000\), and
\[
 \left(\frac{258308973}{10^8}\right)^2
  -\left(\frac{23}{25}\right)^2
       \left(\frac{3967}{2000}\right)^3
  =\frac{673609609660729}{10^{16}}>0.
\]
Consequently \(h''<-.92\). In particular \(h'\) decreases with
t. Endpoint substitution in (11), using the two bounds on
\(R^2\), now proves
\[
                      .96<h'<1.063,\qquad h''<-.92.           \tag{13}
\]
For explicit positive-squaring reserves, the lower comparison at
\(u=1.3965,R^2=1.0864\) has reserve
\(12991715199/16000000000000\); the upper comparison at
\(u=1.5,R^2=1.08645\) has reserve
\(79833/1250000000\).

For the functions in (5), put
\[
 A=\tfrac52-h(e),\quad w=\sqrt{Q-A^2},\quad
 Y=2-w,\quad r=\sqrt{Q-Y^2}=X+1,
\]
\[
 k=\frac{Ah'}w=-Y'>0,\qquad
 l=-\frac{Ah''}w+\frac{Q(h')^2}{w^3}=Y''>0.
\]
Equations (10)--(13), with direct positive squaring, give
\[
\begin{gathered}
 .995<w<1.17,\qquad .83<Y<1.01,\qquad
 1.70<r<1.80,\qquad .70<X<.80,\\
 1.36<A/w<1.72,\qquad 1.31<k<1.83,\qquad l>3.5.               \tag{14}
\end{gathered}
For k's lower endpoint one can use
\((1.598/1.17)(.96)>1.31\); for its upper endpoint use
\((1.71/.995)(1.063)<1.83\). The final comparison follows from
\[
 l>1.36(.92)+\frac{Q(.96)^2}{1.17^3}
     =\frac{9993866}{2851875}>3.5.
\]

## 5. The Hessian has a uniform negative reserve

Let \(a=e+d\), \(c=\cos a\), \(s=\sin a\). On the whole
square, \(c>.97\) and \(0\le s\le.22\). We have
\[
 X'=Yk/r,\qquad X''=-Qk^2/r^3-Yl/r,
\]
and the mixed derivative is
\[
 F_{ed}=(k-X)c+Y(1-k/r)s
  >(.51)(.97)-1.01(1.83/1.70-1)(.22)
   =\frac{101513}{212500}>0.                                  \tag{15}
\]
The second row sum of the Hessian satisfies
\[
\begin{split}
 F_{dd}+F_{ed}
 &=h''(d)+(k-2X)c+Y(2-k/r)s\\
 &<-.92+(1.83-1.40)+1.01(2-1.31/1.80)(.22)\\
 &=-\frac{186581}{900000}<-\frac15.                           \tag{16}
\end{split}
\]
If \(k-2X\) is negative, its term is already nonpositive;
otherwise the displayed bound uses \(c\le1\).

For the first row, write
\[
 F_{ee}+F_{ed}=Jc+Ks,
\]
\[
 J=-Qk^2/r^3-Yl/r-2X+3k,
 \qquad K=2Y-l-3Yk/r<0.                                      \tag{17}
\]
Substitute the formula for l in J. The coefficient of \(-k^2\)
is
\[
 T=Q/r^3+QY/(rA^2w).
\]
The elementary cubic maximum gives
\(A^2w=(Q-w^2)w<3\): its unrestricted maximum is
\(2Q^{3/2}/(3\sqrt3)<3\), since \(4Q^3<243\).
Therefore
\[
 T>\frac{Q}{1.8^3}+\frac{Q(.83)}{1.8(3)}
      =\frac{15469883}{12150000}>1.27.
\]
The remaining negative term has magnitude at least
\[
 \frac{YA}{rw}(-h'')>
       \frac{.83}{1.8}(1.36)(.92)=\frac{32453}{56250}.
\]
Because \(-1.27k^2+3k\) decreases for \(k\ge1.31\),
\[
 J<-1.27(1.31)^2+3(1.31)-1.4-\frac{32453}{56250}
    =-\frac{2037503}{9000000}.
\]
It follows that
\[
 F_{ee}+F_{ed}<-.97\frac{2037503}{9000000}
       =-\frac{197637791}{900000000}<-\frac15.                 \tag{18}
\]
Equations (15)--(18) say that the negative Hessian is strictly
diagonally dominant with both row reserves greater than \(1/5\).
Equivalently, for every real vector \(v_0\),
\[
                  v_0^T(\nabla^2F)v_0
                              \le-\frac15|v_0|^2.            \tag{19}
\]
For example, this follows by writing the quadratic form using
\(F_{ed}(v_{0,1}-v_{0,2})^2\) and the two negative row sums.

## 6. One rational comparison point

Take \((e_0,d_0)=(37/800,13/200)\). Direct rational Taylor
comparison and positive squaring in the definitions above give
\[
 F(e_0,d_0)<1.499701,\qquad
       |F_e(e_0,d_0)|<.0004,\quad |F_d(e_0,d_0)|<.0004.        \tag{20}
\]
Here are sufficient enclosures to check the comparison without an
unprinted numerical premise:
\[
\begin{gathered}
 .914575671003890<v<.914575671003893,\\
 .838739223068485<h(e_0)<.838739223068489,\qquad
 1.019588220432744<h'(e_0)<1.019588220432749,\\
 1.075087266703917<w(e_0)<1.075087266703923,\qquad
 1.575501795700079<k(e_0)<1.575501795700093,\\
 1.749324565592893<r(e_0)<1.749324565592899,\\
 .857692434940500<h(d_0)<.857692434940507,\qquad
 1.002096426336771<h'(d_0)<1.002096426336788,\\
 .111020659871773<\sin(e_0+d_0)<.111020659871782,\\
 .993818098587702<\cos(e_0+d_0)<.993818098588286.
\end{gathered}
\]
Each sine is enclosed between its degree-eleven and degree-thirteen
alternating sums, each cosine between its degree-ten and
degree-twelve sums, and each displayed positive square root is
checked by squaring its two endpoints. Substitution in (8) and
\[
 F_e=(Yk/r-Y)\cos(e+d)+(k-X)\sin(e+d),
 \quad F_d=h'(d)-X\sin(e+d)-Y\cos(e+d)
\]
proves (20). This is one comparison point for a function whose
global curvature was already proved, not a subdivision or a
collection of contact data.

Integrating (19) along the line segment from the comparison point
to any point of the square and completing a square gives
\[
 F(e,d)\le F(e_0,d_0)+\frac52|\nabla F(e_0,d_0)|^2
          <1.499701+5(.0004)^2
          =1.4997018<1.499702.
\]
This proves (9), contradicts (7), and completes the stated branch
exclusion.

The unproved global reduction must still cover other original
quarter witnesses, nonzero zero-edge errors, and \(y_E<0\).
Neither the scalar elimination nor its strict concavity supplies
that reduction by itself.
