# A short H--D span at the aligned-HG negative-GA endpoint with TD0

## 1. Original-data statement

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,
 \quad c=\sqrt{Q/2}-1/2,\quad K=13/12,
 \quad \lambda=13/20.
\tag{1}
\]
Retain a sorted true-core necessary cycle contained at an original
squared radius \(q\le Q\), with real frame spread at most h. The
signed tangents of H,A are nonnegative, those of B,D,G are
nonpositive, and T has either sign. Suppose
\[
 \theta_H=\theta_G>\theta_A,\qquad GA1,\quad BT2,\quad TD0,
 \qquad AB\in\{0,2\},
\tag{2}
\]
with either aligned HG owner, and suppose actual GA0 is unavailable.
Then
\[
                         \theta_H-\theta_D<11/50.
\tag{3}
\]
No E state or E witness is used. No state, radius, frame or owner is
changed in this proof. In particular, (3) is available before the
contact normalization in the
[negative-GA transport theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md).
All decimals in this note are exact rational numbers.

Write \(t=\theta_H-\theta_A\). The original-data local comparisons
in Sections 2--3 of that transport theorem give
\[
              0<t<.09,\qquad b_G<.156,\qquad a_G\ge7/12.
\tag{4}
\]
These comparisons use no EH assumption. Indeed aligned HG gives
\(b_H+b_G\ge1\), sorted containment gives \(b_H\le c<.9\),
and the unavailable-GA0 comparison is
\[
 1+(b_G+1/2)^2+K^2+2(b_G+1/2)\cos t+2K\sin t<Q.
\]
Putting \(b_G+1/2>.6\) in this increasing expression gives the
short-angle cut in (4). The actual GA1 inequality also gives
\[
 a_A\ge f(t):=\tfrac12+(\tfrac32-c)\cos t+K\sin t.
\tag{5}
\]
Here \(b_G\ge1-b_H\ge1-c\) was used; (5) is an inequality on
the unchanged A coordinate.

## 2. Two norm functions and their whole-interval bounds

Define, for \(0\le z\le h\),
\[
 \begin{split}
 N(s)&=\sqrt{1+\lambda^2+2\lambda\sin s},\qquad N_0=N(0),\\
 U(z)&=\lambda(\cos z+\sin z-1)-R\{N(z)-N_0\},\\
 V(z)&=\cos z-1-R\{N(-z)-N_0\}.
 \end{split}
\tag{6}
\]
Both U and V are concave and vanish at zero. This is the
whole-interval two-angle norm lemma in Section 3 of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md),
with \((p,q)=(13/20,1)\). Its hypotheses are
\(1/2\le p/q\le1\), so they hold here.
The following particular bounds suffice:
\[
 \begin{gathered}
 U'(z)>-.72,\qquad U(z)>-.545z\quad(z>0),\\
 .64<V'(z)<1.079,\qquad V(z)>(.87\lambda/h)z\quad(z>0),\\
                         V'(.13)<1.01.
 \end{gathered}
\tag{7}
\]
The first derivative bounds and the two chord bounds follow from
concavity and the respective endpoint comparisons
\[
 U'(h)>-.72,\quad U(h)>-.545h,\quad V'(h)>.64,
 \quad V'(0)<1.079,\quad V(h)>.87\lambda.
\tag{8}
\]
Here and below a weak bound is understood at a zero argument.

For explicit rational verification, let \(C_j,S_j\) be the
alternating cosine and sine Taylor polynomials of degree j.
The elementary bounds used in (8) are
\[
 \begin{gathered}
 1.978787<R<1.978788,\quad .899214<c<.899215,\\
 1.192686<N_0<1.192687,\quad N(-h)<.7649,\\
 1.503<N(h)<1.5034,\quad N(-.13)>1.1198.
 \end{gathered}
\tag{9}
\]
Each follows by positive squaring and \(S_7\le\sin\le S_5\).
Substitute (9), \(C_6\le\cos\le C_4\), into
\[
 U'(z)=\lambda(\cos z-\sin z)-R\lambda\cos z/N(z),\qquad
 V'(z)=-\sin z+R\lambda\cos z/N(-z).
\tag{10}
\]
The resulting rational reserves in the six inequalities (8) and
\(V'(.13)<1.01\), in their displayed order, exceed
\[
                 .1437,\quad .0325,\quad .00187,
                 \quad .00058,\quad .0458,\quad .00071.
\tag{11}
\]
Thus (7) uses a few endpoint arithmetic comparisons after a
whole-interval concavity proof, with no angle subdivision.

## 3. The sorted D charge

For \(-h\le w\le h\), sorted containment gives
\[
          a_D\sin w+b_D\cos w\le c(\sin w+\cos w).
\tag{12}
\]
For nonnegative w the sorted quarter-circle support is maximized
at the diagonal, because \(\cos w>\sin w\). For negative w,
use \(a_D\ge b_D\), \(b_D\le c\), and
\(\cos w+\sin w>0\). This proves (12) also for contained
states lying inside the ceiling-Q circle.

Put \(W(w)=(1+\cos w+|\sin w|)/2\), and set
\[
                   C(w)=W(w)-c(\sin w+\cos w).
\tag{13}
\]
Then \(C(0)=1-c\), and
\[
 \begin{array}{ll}
 C'(w)>-.4,&0<w\le h,\\
 C'(w)<-1.32,&-h\le w<0.
 \end{array}
\tag{14}
\]
For the first bound, \(C'(w)=-(c-1/2)(\cos w-\sin w)\).
For the second, write \(w=-r\). The negative of the derivative is
\((c-1/2)\sin r+(c+1/2)\cos r\). This positive concave
function has its minimum at an endpoint. At zero it exceeds 1.399;
at h it exceeds 1.32 by the exact reserve
\[
 (.399214)(.6442)+(1.399214)(.7648)-1.32
                         =3646263/500000000>0.
\tag{15}
\]

## 4. The two AB owners give the same scalar lower bound

Translate A's frame to zero. Write
\[
 s=\theta_T-\theta_A,\quad d=\theta_B-\theta_A,
 \quad v=\theta_T-\theta_B=s-d,\quad w=\theta_D-\theta_T.
\tag{16}
\]
Add the necessary inequality (5), lambda times the actual AB
inequality, and the actual BT2 and TD0 inequalities. The signed
T tangent cancels exactly. Apply full-circle support only to A,B,
and the sorted estimate (12) to D.

For AB0 the A and B forces are
\[
             (1,\lambda),\qquad
             (\lambda\sin d+\cos v,\lambda\cos d+\sin v),
\tag{17}
\]
whose norms are \(N_0,N(s)\). All half-shifts and demands sum to
\[
 f(t)+1+\lambda+\lambda\{\cos d+(\sin d)_+\}
       +\cos v+(\sin v)_+ +C(w).
\tag{18}
\]
For three frames in an interval of length h, the width expression
in the middle of (18) obeys
\[
 \lambda\{\cos d+(\sin d)_+\}+\cos v+(\sin v)_+
 \ \ge\ \begin{cases}
             1+\lambda(\cos s+\sin s),&s\ge0,\\
             \lambda+\cos s,&s\le0.
           \end{cases}
\tag{19}
\]
Here is a direct sector proof. For s nonnegative and \(0\le d\le s\),
concavity gives the smaller endpoint \(d=s\). If \(d=-a\),
comparison with \(d=0\), after division by \(2\sin(a/2)\),
has the positive lower bound
\[
 (\cos h-\sin h)\cos(a/2)
       +(\sin h+\cos h-\lambda)\sin(a/2).
\]
If \(d=s+a\), comparison with \(d=s\) gives instead
\[
 \lambda(\cos h-\sin h)\cos(a/2)
       +\{\lambda(\sin h+\cos h)-1\}\sin(a/2).
\]
The second coefficient is negative, so its minimum on
\([0,h/2]\) is at h/2. That value is positive since
\(\lambda(15/16-343/1000)-343/1000=.043425>0\).

For \(s=-r\le0\), both nonpositive angles give the smaller
concavity endpoint \(d=0,v=-r\). In the remaining sectors,
\((d,v)=(a,-r-a)\) or \((-r-a,a)\), where \(r+a\le h\).
Use
\[
 \frac{\sin(r+a/2)}{\cos(a/2)-\sin(a/2)}
 \le\sin h<\lambda<1.
\tag{20}
\]
The inequality follows by replacing \(r+a/2\) by \(h-a/2\)
and expanding the sine. The half-angle differences in the two
sectors are respectively
\(\lambda(\cos(a/2)-\sin(a/2))-\sin(r+a/2)\) and
\(\cos(a/2)-\sin(a/2)-\lambda\sin(r+a/2)\).
They are nonnegative; the second sector also has the nonnegative
endpoint surplus \((1-\lambda)(1-\cos r)\). This proves (19).

For AB2 the forces are instead
\[
          (1+\lambda\sin d,\lambda\cos d),\qquad
          (\cos v,\lambda+\sin v),
\tag{21}
\]
with norms \(N(d),N(v)\), and the same demands (18). The two
angular increments are bounded below by U for a positive argument
and by V for its negative magnitude. Specifically the negative
AB increment has the extra \((1-\lambda)(1-\cos d)\), and the
positive BT increment has the extra
\((1-\lambda)(\cos v+\sin v-1)\).

Same-sign increments concentrate by concavity and U(0)=V(0)=0.
For opposite signs P,N, both totals are at most h. If \(P\le N\),
(7) gives
\[
 U(P)+V(N)-V(N-P)>(.64-.545)P\ge0.
\]
If \(N\le P\), it gives
\[
 U(P)+V(N)-U(P-N)>
                \{.87\lambda/h-.72\}N\ge0.
\]
Both coefficients are positive. Thus either AB owner gives the
same necessary inequality
\[
       f(t)+2+2\lambda-2RN_0+B(s)+C(w)\le0,
 \qquad
 B(s)=\begin{cases}U(s),&s\ge0,\\V(-s),&s\le0.\end{cases}
\tag{22}
\]
This calculation permits arbitrary AB and BT errors and either
sign of T. Weak owner ties cause no change.

## 5. Eliminate T's frame and contradict a long H--D span

Suppose \(\alpha=\theta_H-\theta_D\ge.22\), and put
\(u=\theta_A-\theta_D=\alpha-t\). By (4), \(u>.13\).
In (22), \(w=-u-s\). Its two frame-dependent terms are minimized
at \(s=-u,w=0\), as the following three derivatives show:

* for \(s\ge0\), the derivative of \(U(s)+C(-u-s)\) is
  greater than \(-.72+1.32>0\);
* for \(s=-v\), \(0\le v\le u\), the derivative of
  \(V(v)+C(v-u)\) is less than \(1.079-1.32<0\);
* for \(v\ge u\), that derivative is greater than
  \(.64-.4>0\).

Each comparison path keeps T's scalar frame between its original
value and D's, so all angles stay in the original interval. No
geometric T replacement is asserted. Consequently (22) implies
\[
 F(t,u):=f(t)+2+2\lambda+\cos u-c
          -R\{N_0+N(-u)\}\le0.
\tag{23}
\]
But V is increasing and \(u\ge.22-t\), so
\(F(t,u)\ge F(t,.22-t)\). For \(0\le t\le.09\),
\[
 f'(t)>K C_2(.09)-.601(.09)>1.024,
 \qquad V'(.22-t)\le V'(.13)<1.01.
\tag{24}
\]
Thus \(F(t,.22-t)\) increases strictly with t. At its left
endpoint,
\[
 F(0,.22)=4+2\lambda+\cos(.22)-2c
                    -R\{N_0+N(-.22)\}>.0057>0.
\tag{25}
\]
For the last exact check, \(N(-.22)<1.067147\) follows from
\[
 (1.067147)^2-\{1+\lambda^2-2\lambda S_7(.22)\}
                         =6051985769/4921875000000000>0.
\]
Using this, (9), and \(C_6(.22)\), the reserve after subtracting
.0057 in (25) is exactly
\[
                         394290029/11250000000000>0.
\tag{26}
\]
Equations (23)--(25) contradict one another. This proves (3).
In particular, whenever E's frame lies between D and H, its
positive EH angle is less than .22 and falls within the proved
short-EH1 part of the negative-GA transport theorem. The span
bound itself makes no assumption on E and supplies no conclusion
about the other actual TD owner.
