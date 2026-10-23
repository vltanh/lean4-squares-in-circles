# Positive T-primary total: signed cancellation by actual transport

## 1. Statement and the two physical projections

Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10},
 \qquad
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12,
\]
\[
 W(x)=\frac{1+\cos x+|\sin x|}{2}.                 \tag{1}
\]
Use an actual boundary-neighbor cycle as defined in
[the boundary transport theorem](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
Retain the high-GA role order H,G,A,B,T,D,E, with B and D
sorted outer states of negative signed tangent, and actual
weak BT3 and TD2 witnesses. Write
\[
 u=d_{BT},\qquad v=d_{TD},\qquad t=u+v>0.
\]
The actual real-frame spread and variation bounds imply
\[
 |u|,|v|<h,\qquad 0<t<h.                          \tag{2}
\]
The T center has sorted own-frame coordinates
\[
 (a,-y),\qquad a\ge |y|,\qquad
 (a+\tfrac12)^2+(|y|+\tfrac12)^2\le Q.
\]
With the fixed nonnegative endpoint scalars
\[
                         A=a_B,\qquad B=b_D,
\]
its two actual inequalities are exactly
\[
 \begin{split}
 A+a\sin u-y\cos u&\ge W(u),\\
 a\sin v+y\cos v+B&\ge W(v).
 \end{split}                                      \tag{3}
\]
In particular \(0\le A,B\le a_0\). No sign or radial-kind
restriction is imposed on T.

**Signed-cancellation theorem.** If \(u<0<v\), there is an
actual T-only continuous transport to
\[
             u=0,\qquad v=t,
\]
where the aligned BT2 witness is also feasible. If
\(v<0<u\), there is an actual T-only continuous transport to
\[
             u=t,\qquad v=0,
\]
where the aligned TD0 witness is also feasible.

Both original primary inequalities remain feasible throughout.
Every other center, frame and retained neighboring witness is
unchanged. At the final endpoint T is on its outer Q-circle,
the frame spread does not increase, and the total positive and
negative frame variations both decrease by the magnitude of
the original negative error. The entire signed T-primary sum
t is preserved. In particular the A/E primary totals and their
individual errors are unchanged.

The proof is local in the three actual squares, together with
the geometric continuity argument maintaining the whole
neighbor cycle. It does not use an isolated-pair scalar
surrogate, a nearest-axis tie exclusion, a numerical
certificate, or a radial-kind assumption at T.

Sections 2--3 also provide a general circle/contact entry lemma
for \(u+v>0\), without requiring opposite signs. This is useful
for the separate same-sign primary-pair transport.

## 2. Circle entry while one actual primary stays fixed

First suppose T is strictly inside its outer Q-circle. Keep its
actual frame, B and D fixed, and move its own-frame center along
\[
 a(\lambda)=a+\lambda,\qquad
 y(\lambda)=y+\lambda\tan u,\qquad \lambda\ge0.       \tag{4}
\]
All angles in this note lie in \([-h,h]\), where
\[
 \cos x>\frac34,\qquad |\sin x|<\frac{13}{20},
 \qquad |\tan x|<1.                                \tag{5}
\]
These elementary strict bounds follow, for example, from
\(C_2(h)=151/200>3/4\) and \(S_5(h)<13/20\), together
with the monotonicity of sine and cosine on the interval.

Along (4), the first left side in (3) is exactly constant.
The derivative of the second is the positive number
\[
       \sin v+\tan u\cos v=\frac{\sin t}{\cos u}>0. \tag{6}
\]
Sorting is retained, because
\[
 a(\lambda)-|y(\lambda)|
 \ge a-|y|+\lambda(1-|\tan u|).                    \tag{7}
\]
The containing-circle expression increases strictly: wherever
\(y(\lambda)\ne0\), its derivative is at least
\[
 2\{a(\lambda)+\tfrac12
       -|\tan u|(|y(\lambda)|+\tfrac12)\}>0.
\]
The same bound applies to both one-sided derivatives at zero.
The bounded containing-circle region therefore has a unique
first exit along this ray, and that exit is on its outer
Q-circle. All earlier points are contained.

The square continues to avoid the open radius-\(1/12\) disk.
Indeed its exact distance squared from the origin is
\[
 d_{\rm core}^2
   =(a-\tfrac12)_+^2+(|y|-\tfrac12)_+^2.            \tag{8}
\]
Here \(a>1/2\) by the original core avoidance. When
\(|y|>1/2\), half its derivative along (4) is at least
\[
 (a-\tfrac12)-|\tan u|(|y|-\tfrac12)>0;
\]
when \(|y|\le1/2\), the first summand alone increases.
Formula (8) is continuous at the transitions. Thus the core
distance never decreases.

This first motion may pass through interior radial states.
No G1 boundary theorem is applied there. Containment, core
avoidance and the two actual weak inequalities hold directly.
If T was already outer, omit this first motion.

More generally, either primary can be held fixed during circle
entry. Interchanging the two inequalities and replacing
\[
                    (A,B,u,v,y)\longmapsto(B,A,v,u,-y)
                                                               \tag{9}
\]
turns the second-primary version into exactly (4)--(8).

## 3. Outer-circle contact entry

On the complete sorted outer circle write
\[
 a(y)=\sqrt{Q-(|y|+\tfrac12)^2}-\tfrac12,
                         \qquad -c_0\le y\le c_0.   \tag{10}
\]
Its one-sided derivatives have absolute value at most one.
Consequently the derivatives with respect to y of the two
T contributions in (3) obey
\[
 \begin{split}
 \frac{d}{dy}\{a(y)\sin u-y\cos u\}
      &\le|\sin u|-\cos u<-\frac1{10},\\
 \frac{d}{dy}\{a(y)\sin v+y\cos v\}
      &\ge\cos v-|\sin v|>\frac1{10}.
 \end{split}                                       \tag{11}
\]
These inequalities hold on both smooth arcs and pass through
the continuous join \(y=0\).

Starting at the circle-entry state, increase y until the first
primary becomes an equality, or until the positive diagonal
\(y=a=c_0\) is reached. The second primary remains feasible.
This is the promised general circle/contact entry lemma:
every positive-total primary pair reaches an actual circle
contact or an actual positive-T diagonal, with all frames fixed.

For the signed-cancellation theorem the first error is
\(u=-s<0\). The diagonal alternative is impossible by a direct
local comparison. At the positive diagonal the first left
side in (3) is at most
\[
 A-c_0(\sin s+\cos s)
       \le a_0-c_0<1\le W(s).                      \tag{12}
\]
Here \(a_0<3/2\), \(c_0>1/2\), and
\(\sin s+\cos s\ge1\). Thus there is a unique first-primary
contact strictly before that diagonal. This argument also
applies after (9), because its first endpoint scalar is
again in \([0,a_0]\).

Every state on (10) has \(a\ge c_0>3/4\), so its square has
core distance at least \(a-1/2>1/4>1/12\). Circle containment,
sorting and core avoidance are therefore explicit throughout
the contact-entry motion.

## 4. Contact coordinates when the first error is negative

We now have \(u<0<v\), \(t=u+v>0\), T on its outer circle,
and the first inequality in (3) at equality. Keep A, B and t
fixed, and increase u from its current value toward zero.
Set \(v=t-u>0\) and
\[
 P=A-\frac12,\qquad
 X=a+\frac12,\qquad Z=|y|+\frac12,\qquad X^2+Z^2=Q. \tag{13}
\]
The endpoint bound gives
\[
                         -\frac12\le P<1.          \tag{14}
\]

### 4.1. The nonpositive-tangent arc

For \(y\le0\), put
\[
 S(u)=\cos u-P,\qquad U(u)=\sqrt{Q-S(u)^2}.
\]
The contact equation and its positive rotated companion are
\[
 X\sin u+Z\cos u=S,\qquad
 X\cos u-Z\sin u=U.
\]
Thus the complete contact arc has the explicit formula
\[
 X=U\cos u+S\sin u,\qquad
 Z=-U\sin u+S\cos u,\qquad y=\frac12-Z.             \tag{15}
\]
In this range \(-1<S\le3/2\), hence
\[
                  U^2\ge Q-\frac94>1.              \tag{16}
\]
Since \(S'=-\sin u\), differentiation gives
\[
 X'=Z\left(1+\frac{\sin u}{U}\right)>0,\qquad
 Z'=-X\left(1+\frac{\sin u}{U}\right)<0.             \tag{17}
\]
In particular y increases, a increases, and \(a-|y|=X-Z\)
increases strictly. The arc can continue until \(u=0\) or
\(Z=1/2\), with no loss of sorting. The square remains on
its outer circle.

### 4.2. The nonnegative-tangent arc

For \(y\ge0\), the contact equation instead is
\[
 Z\cos u-X\sin u=P.
\]
Put \(U=\sqrt{Q-P^2}\), now constant. The explicit contact is
\[
 X=U\cos u-P\sin u,\qquad
 Z=U\sin u+P\cos u,\qquad y=Z-\frac12.              \tag{18}
\]
A sorted nonnegative-tangent contact with \(u<0\) forces
\[
 P=Z\cos u-X\sin u
       \ge Z\{\cos(-u)+\sin(-u)\}\ge\frac12.
\]
Together with (14), this gives \(U>P\). Formula (18) has
\[
 X'=-Z,\qquad Z'=X>0,\qquad
 X-Z=(U-P)\cos u-(U+P)\sin u>0.                    \tag{19}
\]
It therefore continues to \(u=0\), with y increasing and
strict sorting throughout.

At \(y=0\), formulas (15) and (18) describe the same actual
state: \(Z=1/2\), \(X=\sqrt{Q-1/4}\), and both contact
equations reduce to
\[
                  P=\frac12\cos u-X\sin u.
\]
Thus they join continuously. Because y is increasing on both
arcs, there is at most one such join. Equations (15)--(19)
give a complete sorted contact path all the way to \(u=0\).

## 5. The opposite primary becomes strictly easier

Along the contact path the second inequality in (3) is
equivalent to
\[
                 B\ge D(u):=W(v)-a\sin v-y\cos v,
                    \qquad v=t-u>0.              \tag{20}
\]

On the nonpositive-tangent arc, (15) gives the exact formula
\[
                   D_-(u)=\frac12+\sin v-U\sin t+S\cos t.
\]
Write \(s=-u>0\) and \(r=S/U\). Sorted contact implies
\[
 U-S=X(\cos s+\sin s)-Z(\cos s-\sin s)>0,
\]
so \(r<1\). Differentiation and \(v=t+s\) yield
\[
 \begin{split}
 D_-'(u)
   &=-\cos t(\cos s-\sin s)
            +\sin t\sin s(1+r)\\
   &=-(\cos v-\sin v)-\sin t(\cos s-r\sin s)
                                      <-\frac1{10}.             \tag{21}
 \end{split}
\]
The final inequality uses (5), \(r<1\), and
\(\cos s>\sin s\). It does not require r to be nonnegative.

On the nonnegative-tangent arc, (18) gives
\[
          D_+(u)=\frac12+\cos v+\sin v-U\sin t-P\cos t.
\]
Here U and P are constant, and hence
\[
                 D_+'(u)=\sin v-\cos v<-\frac1{10}.             \tag{22}
\]
The two demands agree at the zero-tangent join. Thus D
strictly decreases over the entire contact path, including
that join. The second actual weak inequality remains feasible.

At \(u=0\), the first actual equality is \(A-y=1\). The
BT3 and BT2 projections agree at this alignment, so the
actual BT2 witness is now available. The remaining TD2
error is the unchanged positive total \(t\).

## 6. The other sign order and weak endpoints

If \(v<0<u\), apply the preceding local construction to
(9). Its new first error is v, its new second error is u,
and their total is still t. The hypotheses on the endpoint
scalars, sorted circle, containment and core avoidance are
unchanged. Reflecting the resulting actual T path back gives
\[
                           v=0,\qquad u=t.
\]
At that endpoint the TD2 and TD0 projections both equal
\(y+b_D\), so TD0 is an actual weak witness. The positive
BT3 witness is retained at error t.

If u or v is already zero, the corresponding secondary
witness is immediately available at the same original state;
there is no need for the angular transport. All statements
are compatible with original weak contacts and with a
zero-tangent T state.

## 7. Preservation of the whole geometric cycle

The first two motions keep all real frames fixed. During the
contact motion for \(u<0<v\),
\[
                   \theta_T<\theta_B<\theta_D
\]
initially, and T's frame increases only to \(\theta_B\).
After (9), the other sign order moves T's frame down only to
\(\theta_D\). Each frame path stays in the original global
frame interval. Its prescribed directed quarter offsets
remain fixed, because the own-frame center stays sorted.

The two changing neighboring squares remain disjoint from T
by the actual inequalities (3). Every other neighboring
inequality is unchanged. Sections 2--3 retain containment and
core avoidance even before T returns to the outer boundary.
The strict two-square central-band estimate in Section 2 of
[the boundary transport theorem](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md)
therefore prevents either moving consecutive center gap
from reaching zero. Lift the seven center arguments
continuously from their original cyclic order. Their
consecutive gaps remain positive and sum to \(2\pi\), so
the same one-winding cyclic order is preserved.

At the final endpoint all seven states are boundary states
again. The actual containing-circle and core conditions,
quarter word, consistent own-frame labels, frame interval,
and neighboring weak witnesses give a boundary-neighbor
cycle of exactly the original kind. No assertion about
nonconsecutive disjointness or completion to an eight-square
packing is needed. Boundary markers, if used subsequently,
are evaluated at this actual descendant state.

For \(u=-s<0\), the two changed errors initially have
positive variation \(t+s\) and negative variation s.
Their endpoint values \(0,t\) have positive variation t
and negative variation zero. Both global variations
therefore decrease by s, while the total signed sum stays
unchanged. The reflected case is identical.

This completes the actual signed-cancellation theorem. It
reduces every positive-total T-primary pair with opposite
individual signs to one positive primary and one genuine
aligned secondary, with all A/E data unchanged. The two
nonnegative-error T primaries are the separate same-sign
transport problem.

## 8. Complete high-GA join for nonnegative A/E totals

The two positive-total transports have a useful complete
consequence. Retain the original high-GA boundary-neighbor
domain, with sorted outer H,G,B,D of signed tangents
positive, negative, negative and negative, and E nonpositive.
Retain any actual weak owners in
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
\]
\[
 BT\in\{2,3\},\quad TD\in\{0,2\},\quad
 DE\in\{2,3\},\quad EH\in\{0,1\}.                 \tag{23}
\]
A, T and E may have either canonical radial kind; A and T
may have either sign.

Let the selected signed A- and E-primary totals a and e
both be nonnegative. Each total is zero when neither
primary at that role is selected, its actual error when
one is selected, and the signed sum when both are selected.
The individual errors of a paired total may have opposite
signs. Then **no such original cycle exists, with any
T-primary owner or error allocation**.

Here is the complete finite join.

* If BT2 is retained, TD0 of arbitrary error and TD2 of
  nonnegative error are excluded by
  [the nonnegative-A/E theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).
  A nonpositive TD2 is excluded by
  [the nonpositive-T-total theorem](HAND_G3_HIGH_GA_NONPOSITIVE_T_PRIMARY_TOTAL_EXCLUSION.md).
* If BT3 and TD0 are retained, a nonpositive BT3 error is
  again in the nonpositive-T-total theorem. A nonnegative
  BT3 error is excluded by
  [the positive-BT3/TD0 theorem](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
* If BT3 and TD2 are retained and their signed sum is
  nonpositive, the nonpositive-T-total theorem applies.
  If their signed sum is positive, Sections 1--7 handle
  opposite individual signs, while
  [the positive paired-T endpoint theorem](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
  handles two nonnegative individual errors. A zero
  individual error is already an actual alignment.

In the last case every resulting actual descendant has
either BT2 and positive TD2, or positive BT3 and TD0.
The A/E totals, all their actual witnesses and the high-GA
owner remain unchanged, while the necessary circle,
boundary and variation conditions remain valid. The first
two bullets therefore exclude both possible descendants.

This corollary imposes no sign on the selected T-primary
total or either of its constituent errors. It still assumes
nonnegative selected A- and E-primary totals; negative
A/E totals require their separate endpoint theorems.
