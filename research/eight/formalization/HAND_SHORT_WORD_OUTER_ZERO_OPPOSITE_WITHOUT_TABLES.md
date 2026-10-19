# All six opposite-sign outer zero-quarter owners without angle subdivisions

This note replaces ../SHORT_WRONG_WORD_OUTER_ZERO_OPPOSITE_HAND_PROOF.md.
It proves the original owners \((i,+,-,j)\), \(i\in\{0,1,3\}\),
\(j\in\{1,3\}\), on the entire domain \(|\phi|\le.7\), with corrected
cost greater than .898. All original weak separators, state boundaries,
and simultaneous owners are included.

The proof uses actual contacts and all their boundaries. No multiplier
sequence on angle intervals, sampled minimum, or coefficient table is
used. Every terminating decimal is an exact rational.

## 1. Data, alignment, and notation

Put
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad b_0=1-d,
\]
\[
 r(y)=\frac{y+1/2}{a(y)+1/2},\quad
 r'=\frac Q{(a+1/2)^3},\quad
 r''=\frac{3Q(y+1/2)}{(a+1/2)^5}.
\]
Write \(L(b)=pa(b)+qb\), \(T(B)=v a(B)+tB\).
Reflection/reversal of original axis 3 gives exactly
\[
 C=\phi+c+L(b)+T(B),\qquad
 b+A(B)\sin\phi+B\cos\phi\ge W,
\tag{1}
\]
where \(W=(1+|\sin\phi|+\cos\phi)/2\).
In original order \((0,1),(0,3),(1,1),(1,3),(3,1),(3,3)\), the six
normalized tuples \((c,p,q,v,t)\) are
\[
\begin{aligned}
0&:(-.24463,0,.94766,.13422,1.03828),\\
1&:(-.24463,.13422,1.03828,0,.94766),\\
2&:(.08753,0,.9994,-.09133,.88074),\\
3&:(.08753,-.09133,.88074,0,.9994),\\
4&:(-.45320,.51554,1.19909,-.19335,.76744),\\
5&:(-.45320,-.19335,.76744,.51554,1.19909).
\end{aligned}                                               \tag{2}
\]
Both labels increase strictly in their transverse coordinate:
\(L'=q-pr>0\), \(T'=t-vr>0\).
We use the elementary bounds
\[
\begin{gathered}
1.414575671<a_0<1.414575672,\quad
.899214065109<d<.899214065110,\quad
R<1.978788,\\
1.399<d+1/2<1.4,\quad
1.885<a(b_0)+1/2<1.886,\quad r(b_0)<.319,\\
[(a(b_0)+1/2)/(d+1/2)]^3<2.46,\quad
.26115<\rho:=1/[2(a_0+1/2)]<.262.
\end{gathered}                                               \tag{3}
\]
These follow by positive squaring.

At alignment, monotonicity reduces (1) to \(b+B=1\),
\(b\in[b_0,d]\). Its second derivative is
\(-p r'(b)-v r'(1-b)\).
Rows 0 and 1 are concave. Rows 4 and 5 are concave as well, by
\(.19335(2.46)<.51554\).
Row 2 instead has positive first derivative
\(.9994-.88074-.09133r(1-b)>.027\);
row 3 has negative first derivative
\(.88074+.09133r(b)-.9994<-.027\).
Thus all aligned minima are at the two geometric endpoints.
Direct substitution gives the common bound
\[
                              C(0)>.89809.                 \tag{4}
\]
The smallest endpoint value is greater than .8980998.

## 2. The complete negative half

Write \(\phi=-x\), \(s=\sin x,k=\cos x\).
The largest possible separating projection uses both diagonal states.
Hence every feasible negative angle satisfies
\[
 0\le x\le x_*=
 2\arctan\frac{d-1/2}{d+1/2}<.556.
\tag{5}
\]
This follows directly from
\((d-1/2)(1+\cos x)\ge(d+1/2)\sin x\).
Moreover \(b+B\ge1\), so both coordinates are at least \(b_0\).
Minimizing the increasing source label gives the exact contact
\[
 b=1/2+(A+1/2)s+(1/2-B)k.
\tag{6}
\]
It decreases strictly with \(B\). Its complete target interval has
endpoints \(B=d\) and \(b=d\).

### 2.1. Four whole contact surfaces are concave in the target

Let \(u=a(b)+1/2\), \(U=A+1/2\), \(K=k+r(B)s\),
\(l=q-pr(b)\). Differentiating (6) gives
\[
 \frac{C_{BB}}{r'(B)}
 =-p\frac{r'(b)}{r'(B)}K^2-ls-v.
\tag{7}
\]
For rows 0 and 1, this is strictly negative immediately.
For row 4, set
\(A_* = .51554(1.399/1.886)^3\).
Equation (3), \(K\ge k\), and \(l\ge .68355\) give
\[
 C_{BB}/r'(B)
 \le A_*s^2-.68355s+.19335-A_*<0.
\]
The last quadratic is convex and negative at both ends of
\([0,.645]\), so this is one whole-angle inequality.

For row 5, use two global estimates simultaneously. Put
\[
 a_* = .19335(2.46),\qquad
 b_* = \frac{.19335Q(1.886)}{1.399^3}.
\]
The first follows from \(K^2\le(k+s)^2\le1+2s\).
For the second, use
\((Uk+(B+1/2)s)^2\le Q\), by Cauchy's inequality, to get
\((r'(b)/r'(B))K^2\le Q U/u^3<Q(1.886)/1.399^3\).
Averaging the resulting two upper bounds in (7) gives
\[
 C_{BB}/r'(B)
 <(a_*+b_*)/2-.51554+(a_*-.76744)s<0.
\tag{8}
\]
Indeed the constant is less than -.016 and the coefficient of \(s\)
is negative. This replaces the former negative-angle curvature ranges.
Thus rows 0,1,4,5 minimize at one of the two diagonal contacts.

### 2.2. Both entire diagonal boundary curves

At \(B=d\), the source is
\[
 b(x)=1/2+(1/2-d)\cos x+(d+1/2)\sin x,\quad h=b'>0,
\]
\[
 h^2=2d^2+1/2-(b-1/2)^2\ge Q/2.
\]
For rows 0,1,5, \(L'\ge .76744\), so the boundary derivative
\(-1+L'h\) is positive on the whole domain.
For row 4, its third derivative divided by \(h\) is
\[
 -p r''h^2-3p r'(1/2-b)-L'.
\]
It is negative when \(b\le1/2\). When \(b\ge1/2\), the inequality
\[
 (b+1/2)h^2\ge Q/2>
 .4(Q-1)\ge(b-1/2)[a(b)+1/2]^2
\]
shows that the first negative term dominates the only possible
positive term. Thus the first derivative is concave and starts
positive at zero. The minimum is at an endpoint.

At the other boundary \(b=d\), put \(z_0=1/2-d<0\) and
\[
 Z=k+z_0,\quad Y=\sqrt{Q-Z^2},\quad
 U=Yk-Zs,\quad V=Ys+Zk,\quad f=1-s/Y.
\]
Here \(U'=-Vf,V'=Uf\), \(f>0\), and
\[
 f'=\frac{(1-Q+z_0^2)k+z_0(1+k^2)}{Y^3}<0.
\]
The cost has second derivative
\[
 -(tV+vU)f^2+(tU-vV)f'<0.
\tag{9}
\]
Both factors required positive here are indeed positive: \(U\ge V\),
\(t>\max(v,0)\); for the one negative \(v\) in these four rows,
\(tV+vU>.76744(.6)-.19335(1.886)>0\).
So this entire boundary is concave.

At zero, all boundary values have (4). At their common double-diagonal
endpoint, every tuple has
\[
 -x_*+c+(p+q+v+t)d>1.048.
\tag{10}
\]
This proves the four complete negative-half contact families.

### 2.3. The remaining two negative-half families

Rows 2 and 3 need only the single constant multiplier \(\lambda=.9994\).
Subtract it times (1). In row 2 the source remainder is zero.
In row 3 its exact outer-arc minimum is
\(S=d(p+q-\lambda)\), since \(q-\lambda\le p<0\).
The target coefficients are \(v+\lambda s,t-\lambda k\).
For row 3 they are nonnegative and hence have an endpoint minimum.
For row 2, a negative primary coefficient forces a diagonal minimum
because
\(t-v-\lambda(k+s)<.97207-.9994<0\);
a nonnegative primary coefficient instead gives both endpoints.

The axial and diagonal lower functions are
\[
\begin{aligned}
F_A&=-x+c+S+\lambda/2+va_0
          +(\lambda/2)k+\lambda(1/2+a_0)s,\\
F_D&=-x+c+S+\lambda/2+(v+t)d
          +\lambda(1/2-d)k+\lambda(1/2+d)s.
\end{aligned}
\]
Both increase on \([0,.7]\), by the endpoint minimum of their positive
sine/cosine derivative combinations. In particular their derivatives
are bounded below using \(k>.764,s<.645\) for \(F_A\), and concavity
of \((d-1/2)s+(d+1/2)k\) for \(F_D\).
Their values at zero exceed .898104. This proves both remaining
negative halves without any angle change of multiplier.

## 3. The positive-half contact domain and all its boundary costs

For \(0\le\phi\le.7\), put \(s=\sin\phi,k=\cos\phi\).
On active contact,
\[
 b=1/2+(1/2-A)s+(1/2-B)k,\qquad
 b_B=r(B)s-k<0.
\tag{11}
\]
Every positive-angle minimum is on this contact: lowering an active
source reduces cost, and an inactive zero source reduces its increasing
target coordinate until contact. The four possible state boundaries
are \(B=d,b=0,b=d,B=0\).
Let \(\phi_a\) be the event defined by
\[
 1/2+(1/2)\cos\phi_a-(a_0-1/2)\sin\phi_a=d,
 \quad .1072632<\phi_a<.1072633,
\]
and let \(\phi_0\) satisfy
\((d-1/2)(\sin\phi_0+\cos\phi_0)=1/2\).
Both are unique by monotonicity. The first exchanges the lower target
boundary from \(b=d\) to \(B=0\); the second exchanges the upper target
boundary from \(B=d\) to \(b=0\).

### 3.1. Target diagonal and zero source

At \(B=d\), the active source is
\(b=1/2-(d-1/2)(s+k)\).
Its cost derivative exceeds \(1-1.2(.4)>0\).
Any following zero-source clamped portion increases with slope 1.
Thus its minimum is at alignment.

The zero-source contact runs over \([\phi_0,.7]\). It is exactly
\[
 Z=1/2+s+k,\quad Y=\sqrt{Q-Z^2},\quad
 U=Zs+Yk,\quad V=Zk-Ys,\quad B=V-1/2.
\]
Section 2.1 of HAND_SHORT_WORD_MIXED_ZERO_COMPLETE_WITHOUT_TABLES proves
from these formulas, on the entire arc,
\[
 B'<0,\qquad -B''/(B')^2>.423.
\tag{12}
\]
This is a geometric contact lemma, independent of any core label.
The label \(T\) is increasing. If \(v\ge0\), it is concave;
if \(v<0\),
\(T''/T'<.19335(1.431)/.76744<.361\).
Thus the cost on the whole zero-source arc is strictly concave by
(12). Its initial value is the already covered target diagonal;
its six final values at .7 exceed 1.23.

### 3.2. Source diagonal

On \(0\le\phi\le\phi_a\), the source-diagonal target is
\[
 Z=s+k+1/2-d,\quad Y=\sqrt{Q-Z^2},\quad
 U=kY+sZ,\quad V=kZ-sY,
\]
with \(U'=Vf,V'=-Uf\), \(f=1-(k-s)/Y>0\).
Here \(Z<.703,Y>1.849,Y<1.886\), and
\[
 f'=(s+k)/Y-Z(k-s)^2/Y^3>
             1/1.886-.703/1.849^3>0.
\]
The cost has curvature
\[
 -(tV+vU)f^2-(tU-vV)f'<0.
\]
For negative \(v\), positivity of the first factor follows already
from \(.76744/2-.19335(1.915)>0\); all other signs are immediate.
The second factor is positive by (2)--(3).
Hence this entire boundary is concave. Its initial values have (4);
its six final values, exactly
\(\phi_a+c+(p+q)d+va_0\), exceed .89956.

### 3.3. Target axis: the two negative-p rows

On \(\phi_a\le\phi\le.7\), the target-axis source is
\[
 b=1/2+(1/2)k-(a_0-1/2)s,\qquad
 h=-b'=(a_0-1/2)k+s/2>0.
\]
It has \(.293<b\le d\), and
\[
 h^2=(a_0-1/2)^2+1/4-(b-1/2)^2
                         <1.043^2-(b-1/2)^2.
\tag{13}
\]
For rows 3 and 5, write \(j=-p>0\). Convexity of \(r(b)\) and the
two endpoint comparisons at .293 and \(d\) give
\(r(b)<.18+.92b\) on this entire interval.
Set \(A=q+.64j,B=.92j,z=b-1/2\). Then
\(L'h<(A+Bz)\sqrt{1.043^2-z^2}\).
For \(z\le0\), this is at most \(1.043A\).
For \(z\ge0\), use the square-root tangent and complete a square:
\[
 L'h<1.043A+1.043Bz-\frac{A}{2(1.043)}z^2
 \le1.043A+\frac{B^2(1.043)^3}{2A}.
\]
The last expression is less than .984 in row 3 and less than .950 in
row 5. Their cost derivatives \(1-L'h\) are therefore positive
throughout. Their initial values are covered by Section 3.2.

### 3.4. Target axis: the other four rows

Row 0 has \(L'h\le.94766(1.043)<1\), so it increases as well.
For rows 1,2,4, let \(E\) denote the target-axis cost. Then
\[
 E'=1-L'h,\qquad
 E''=-p r'h^2-L'(b-1/2),
\]
\[
 E'''/h=p r''h^2+3p r'(b-1/2)+L'>0.
\tag{14}
\]
When \(b\ge1/2\) the sign is immediate. When \(b<1/2\), use
\(r'<.788\), \(b-1/2>-.207\), and \(L'>.68355\); even after
discarding the first term, the lower bound
\(-3(.51554)(.788)(.207)+.68355\) is positive.
Thus \(E'\) is convex. In rows 1 and 2, its value at .7 is negative
(respectively less than -.00072 and -.021). Consequently it cannot
cross from negative to positive before that endpoint, and the cost
has its minimum at an angle endpoint. Both endpoints exceed .916
in row 1 and .951 in row 2.
For row 4, instead \(E''(.7)<-.15\) and \(E'(.7)>.0054\).
Equation (14) makes \(E''\) negative throughout and \(E'\) positive
throughout. Its minimum is the already covered initial state.
Thus all four positive-half state boundaries have been proved.

## 4. Every positive-half interior minimum is absent

On contact (11), let \(l=q-pr(b)\),
\(K=k-r(B)s>0\), and \(R_0=r'(b)/r'(B)\).
Its exact target curvature is
\[
 C_{BB}/r'(B)=-pR_0K^2+l s-v.
\tag{15}
\]
For row 0, if \(q s-v\le0\), the contact is concave and has no
interior minimum. If \(q s-v>0\), its derivative is
\(t-qk+(qs-v)r(B)>0\), because \(t>q\).

For row 2, the contact is strictly convex in the target. At an interior
target critical point, subtracting \(\lambda=q=.9994\) times the
separator cancels the source coordinate exactly. The minimizing target
is the corresponding full-circle support point, locally within its
actual arc. The reduced angular cost is therefore
\[
 F(\phi)=\phi+c+(q-v-t)/2+q(s+k)-RN,
 \quad N^2=v^2+t^2+q^2-2q(vs+tk).
\]
Here \(q>\sqrt{v^2+t^2}\), so
\(N''+N/4\ge0\), \(N\le q+\sqrt{v^2+t^2}\), and \(R<2\)
prove \(F''<0\) on the entire angle range. An interior reduced
minimum is impossible.

For rows 3 and 5, the right side of (15) decreases with \(B\):
\(R_0\), \(K\), and \(l\) all decrease as the target coordinate
increases and the source coordinate decreases. Hence \(C_B\) first
increases and then decreases, with no further change of shape.
Its value at the lower target endpoint is positive. If that endpoint
has \(b=d\), its target ratio is at most .319; if it has \(B=0\),
its target ratio is \(\rho<.262\). Thus row 3 has
\(C_B\ge .9994-.97207>0\), and row 5 has
\(C_B>1.19909-.51554(.319)-.96079>0\).
Such a derivative cannot create an interior minimum. These four rows
are exhausted by their already proved boundary curves.

### 4.1. A stationary projection identity for the two positive-p rows

Only rows 1 and 4 remain. Suppose both coordinates of a contact minimum
are interior. Its angular derivative vanishes. Put
\[
 z=1/2-b,\quad u=a(b)+1/2,\quad
 l=q-pr(b),\quad T=z^2+l^{-2}.
\]
Let \(U=A+1/2,V=B+1/2\), and \(S=U+V\).
The actual contact is a rotation of \((U-1,V-1)\). Angular stationarity
sets its derivative speed equal to \(1/l\). Consequently
\[
 S=(Q+2-T)/2,\quad
 U=\frac{S+\sqrt{2Q-S^2}}2,\quad r_t=V/U,
\]
\[
 C_{\phi\phi}
   =l\{z-p r'(b)/l^3\},
\quad
 C_B=t-vr_t-\frac{Q-S}{UT}
                    -(r_t-1)\frac{zl}{T}.
\tag{16}
\]
For direct verification, write
\(z=(U-1)s+(V-1)k\) and
\(1/l=(U-1)k-(V-1)s\), and solve these two projection equations
for \(K/(1/l)\). This gives the second identity in (16).

If the first expression in (16) is negative, the point is not a minimum.
Otherwise \(z\ge p r'/l^3>0\), so \(b<1/2\).
The last term of (16) is then nonnegative. Also every target satisfies
\(S\ge a_0+1>2.414575671\) and \(r_t>\rho>.26115\).

In row 1, \(l\le l(0)<1.0033\), so \(T>.993\) and
\(S<(Q+2-.993)/2\), which gives \(U>1.89\) by positive squaring.
As \(v=0\),
\[
 C_B>.94766-\frac{Q-2.414575671}{1.89(.993)}>.147>0.
\tag{17}
\]
This contradicts target stationarity.

In row 4, the function \(z-p r'/l^3\) decreases strictly with \(b\),
because \(z\) decreases, \(r'\) increases, and \(l\) decreases.
Its value at .2 is less than -.014. Thus the possible nonnegative
angular-curvature regime has \(b<.2\), and hence \(z>.3\).
Moreover \(l\le l(0)<1.065\), so
\[
 T>.09+1/1.065^2>.97165,\quad
 S<(Q+2-.97165)/2,\quad U>1.8918.
\]
Here \(v=-.19335\), so (16) gives
\[
 C_B>.76744+.19335(.26115)
          -\frac{Q-2.414575671}{1.8918(.97165)}
          >.00134>0.
\tag{18}
\]
Again target stationarity is impossible. Thus every positive-half
interior minimum has been excluded, with both actual states coupled
through their contact and circle equations.

## 5. The final-angle boundary

At the single angle \(\phi=.7\), choose, in the row order (2),
\[
 \lambda=(.94766,.96135,.9994,.93,.90362,.90362).
\]
For \(p\ge0\), use the exact concave source endpoint support
\(S_0=\min\{pa_0,(p+q-\lambda)d\}\).
For \(p<0\), use the source full-circle lower support
\(S_0=-(p+q-\lambda)/2-R\sqrt{p^2+(q-\lambda)^2}\).
The target coefficients \(v-\lambda\sin(.7)\) and
\(t-\lambda\cos(.7)\) are respectively negative and positive
in all six tuples, so its exact support is axial. Thus
\[
 C\ge .7+c+S_0+\lambda/2+va_0
       +(\lambda/2)\cos(.7)+\lambda(1/2-a_0)\sin(.7)>.923.
\tag{19}
\]
These are evaluations on the one geometric boundary angle, not an
angle cover. Positive radical brackets and adjacent alternating
sine/cosine sums verify (19) directly.

## 6. Complete compact-minimum argument and exact arithmetic

The negative half is complete by Section 2. The positive-half contact
domain is compact; all four state boundaries are covered in Section 3,
all interior minima are excluded in Section 4, alignment is (4), and
the final angle is (19). Inactive zero-source states reduce to their
contact boundary by strict target monotonicity. There are no additional
feasible endpoints or omitted contact transitions.

Hence every original family in (2) has corrected cost greater than .898
on its entire closed domain. Reflection/reversal restores the original
axis-3 owners without altering a cost or changing any other vertex label.

All fixed comparisons use the displayed tuple coefficients, the source
and target circle equations, and the two monotone boundary events.
Square-root brackets are checked by squaring positive rationals;
trigonometric endpoints use alternating Taylor sums. Machin's identity
supplies the rational bracket for \(\pi/2\) when a boundary event is
expressed through an inverse trigonometric function. The continuous
proof consists of (7)--(9), (12)--(18), and boundary monotonicity.
No former near-zero strip, complementary angle-support interval, or
numerical verifier is a premise of this theorem.
