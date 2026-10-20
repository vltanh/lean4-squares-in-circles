# A middle-path bound for reversed intermediate frames

## 1. Statement with arbitrary original AB frames

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,
 \quad R_1=\sqrt{Q-1},\quad
 S_0=2R_1-3,\quad \lambda=\frac1{R_1},\quad c_* =\frac{149}{240}.
\tag{1}
\]
Retain normal G,A,B,T signs, nonnegative sorted own-frame
coordinates, their actual corner bounds at most Q, and real
frames of total spread at most \(7/10\). Retain the original
hard owners GA0, BT2, and either transverse owner AB0 or AB2.
Let
\[
 r=\theta_T-\theta_G\ge0,
 \qquad W(z)=\frac{1+\cos z+|\sin z|}{2}.
\tag{2}
\]

**Theorem.** Regardless of the A/B frame positions,
\[
                         b_G+b_T\le S_0+c_*r.
\tag{3}
\]
No H,D,E coordinate, outer owner, or outer error occurs in this
statement. It is a necessary bound for the original middle path;
it does not assert that arbitrary AB frames have been aligned.
We prove it for AB0. Local reflected reversal gives AB2 with the
same r and the same left side.

For later use, direct squaring gives
\[
                  \frac7{12}<\lambda<\frac35<1.
\tag{4}
\]

## 2. A common AB frame can always normalize its transverse sum

Suppose A and B already share a frame \(\rho\), and their
transverse sum is at least one. This subsection does not require
any order of G and T. There is a descendant at the same frame
with sum exactly one, retaining each actual middle circle ceiling
separately.

Use the actual individual circle values \(q_A,q_B\le Q\).
Write shifted corner coordinates \(X_i=a_i+1/2\),
\(Y_i=b_i+1/2\). On each circle, the feasible sorted transverse
coordinates form an interval. A nonnegative hard angle has its
lower endpoint at \(Y=1/2\). For a negative hard angle \(-z\),
the lower endpoint is
\[
 \max(\tfrac12,m),\quad
 m=C\sin z-\sqrt{q_i-C^2}\cos z\le\sqrt{q_i}\sin z,
 \qquad C=D+\cos z+\sin z,
\tag{5}
\]
where \(D=b_G+1/2\) or \(b_T+1/2\). These are the exact
circle intersections for \(X\cos z+Y\sin z\ge C\).
The original point makes the feasible interval nonempty.

The sum of the two lower endpoints is strictly below two.
If at most one hard angle is negative, (5), \(\sqrt{q_i}<2\),
and \(z\le7/10\) bound that sum by
\(1/2+2(7/10)=19/10<2\), or by one if both are nonnegative.
If both hard angles are negative, their magnitudes x and y satisfy
\(x+y=r\le7/10\). Their lower-endpoint sum is at most
\[
 \max\{1,\tfrac12+\sqrt{q_A}\sin x,
            \tfrac12+\sqrt{q_B}\sin y,
            \sqrt{q_A}\sin x+\sqrt{q_B}\sin y\}<\frac{19}{10}.
\tag{6}
\]
The last term is below \(2(x+y)\le7/5\).

Interpolate both transverse coordinates downward inside their
actual feasible circle intervals until their sum is two. This
is possible because the original sum was at least two and (6)
is below two. Along each circle the primary increases, sorting
persists, and the hard constraint remains feasible. The hard
projection itself gives
\(a\ge1/2+1/(2\sqrt2)>7/12\), so the true core is also
retained. This proves the claimed exact normalization, including
preservation of an existing strict loss in either actual circle.

When r is nonnegative, the normalized common-frame system obeys
\[
                         b_G+b_T\le S_0+\frac25\sin r.
\tag{7}
\]
This is precisely the independent middle-pair calculation in
Section 2 of
HAND_G5_REVERSED_INTERMEDIATE_SPAN_WITH_NONNEGATIVE_OUTER_ERRORS.md.
That calculation uses no outer-edge or E assumption: the two hard
angles sum to \(-r\), their signed sine contributions are at most
\((2/5)\sin r\), and the two middle circles with transverse sum
one give \(a_A+a_B\le2R_1-1\). Since
\((2/5)\sin r\le c_*r\), (3) follows for every common frame.

## 3. The direct AB comparisons leave only one geometric sector

For AB0 write \(d=\theta_B-\theta_A\). The exact shifted
inequality is
\[
 Y_A+X_B\sin d+Y_B\cos d
                         \ge1+\cos d+(\sin d)_+.
\tag{8}
\]
The following individual comparisons in
HAND_G5_AB_ALIGNMENT_BETWEEN_ORDERED_INTERMEDIATE_FRAMES.md
do not use its final hypothesis \(\theta_G\ge\theta_T\):

- If \(d<0\), its Section 4 and the ordinary positive rotated-cap
  comparison put B at A's frame, keeping A,G,T fixed and not
  increasing B's circle. The common sum is at least one. Apply
  Section 2 above.
- If \(d>0\) and \(\theta_A\ge\theta_T\), its Section 3
  contracts the actual B circle and aligns AB with sum one.
- If \(d>0\) and \(\theta_B\le\theta_G\), the increasing
  positive A-cap comparison in the first paragraph of its
  Section 5 aligns A to B with sum one.

Thus, apart from the common case, it remains to treat
\[
            d>0,\qquad \theta_A<\theta_T,
                    \qquad \theta_B>\theta_G.
\tag{9}
\]
If \(\theta_A<\theta_G\), move A upward to G, keeping B,G,T
fixed. This is exactly the partial positive-cap move in Section 5
of the cited note: the A cap grows at rate greater than \(9/8\),
whereas the AB demand grows at rate less than \(21/20\).
Only nonnegative GA hard angles are traversed. Thus this move
also does not require an order between G and T. It preserves
both hard constraints and (8), retains the same b_G,b_T, and
keeps the new A circle at most Q.

We may consequently assume for the remaining scalar estimate that
\[
 \theta_G\le\theta_A<\theta_T,
 \qquad \theta_B>\theta_A.
\tag{10}
\]
All intermediate constructions stayed within the original frame
span. They are used only to prove a necessary bound on the
unchanged original b_G,b_T.

## 4. A single fixed positive stress

Put
\[
 z=\theta_G-\theta_A,quad w=\theta_B-\theta_T,
 \quad d=\theta_B-\theta_A,quad z+w=d-r.
\]
Add GA0, AB0, BT2 with weights \(1,\lambda,1\).
The two collected center forces are exactly
\[
 F_A=(\cos z,\lambda-\sin z),\qquad
 F_B=(\cos w+\lambda\sin d,\lambda\cos d-\sin w).
\tag{11}
\]
For any force F the actual shifted-corner support gives
\[
             F\mathbin{\cdot}(a,b)
               \le R|F|-\tfrac12(F_x+F_y).
\tag{12}
\]
No sign restriction on the force components is needed for (12).
Writing \(n=\sqrt{1+\lambda^2}=R/R_1\), direct expansion yields
\[
 |F_A|^2=n^2-2\lambda\sin z,
 \qquad |F_B|^2=n^2+2\lambda\sin(d-w).
\tag{13}
\]
The resulting necessary upper bound is
\[
\begin{aligned}
 b_G+b_T\le{}&R(|F_A|+|F_B|)-1-\cos z-\cos w\\
 &-(-\sin z)_+-(-\sin w)_+
                 -\lambda\{1+\cos d+(\sin d)_+\}.
\end{aligned}
\tag{14}
\]

Under (10), set
\[
 x=\theta_A-\theta_G\ge0,\qquad
 s=\theta_T-\theta_A>0,\qquad x+s=r.
\tag{15}
\]
The norm squares in (13) are now
\(n^2+2\lambda\sin x\) and \(n^2+2\lambda\sin s\).
The concave square-root tangent and the exact identity
\(R\lambda/n=1\) give
\[
 R(|F_A|+|F_B|)\le2Rn+\sin x+\sin s.
\tag{16}
\]
Its zero-angle base in (14) is
\(2Rn-3-2\lambda=S_0\).

## 5. B between A and T

Suppose \(\theta_B\le\theta_T\), and write
\(y=\theta_T-\theta_B\ge0\). Then
\(s=d+y\) and \(x+d+y=r\). Subtracting the base S_0
from (14) and using (16) bounds the correction by
\[
\begin{aligned}
 &(1-\cos x)+(1-\cos y)+\lambda(1-\cos d)
                    +\sin(d+y)-\sin y-\lambda\sin d\\
 &\hspace{5mm}\le
 (1-\cos x)+(1-\cos y)+\lambda(1-\cos d)
                                      +(1-\lambda)\sin d.
\end{aligned}
\tag{17}
\]
The last step follows from
\(\sin(d+y)-\sin y\le\sin d\).
For \(0\le t\le7/10\),
\(1-\cos t\le t^2/2\le(7/20)t\). Thus (4) gives
\[
 (17)\le\frac7{20}(x+y)
                      +\left(1-\frac{13}{20}\lambda\right)d
                  \le c_*(x+y+d)=c_*r.
\tag{18}
\]
This proves (3) in this sector.

## 6. B above T: its demand is worse than at T

Now let \(w=\theta_B-\theta_T\ge0\), so \(d=s+w\).
The norm terms in (16) are independent of w. The w-dependent
part subtracted in (14) is
\[
                  P(w)=\cos w+\lambda\{\cos(s+w)+\sin(s+w)\}.
\tag{19}
\]
For \(s,w\ge0\), \(s+w\le7/10\),
\[
\begin{aligned}
 P(w)-P(0)
 =2\sin(w/2)\{\lambda[\cos(s+w/2)-\sin(s+w/2)]-\sin(w/2)\}
 \ge0.
\end{aligned}
\tag{20}
\]
Here is one whole-interval proof of the braced inequality. Put
\(u=w/2\). Since \(s+u\le7/10-u\) and
\(\cos t-\sin t\) decreases, it suffices to bound
\[
 f(u)=\lambda\{\cos(7/10-u)-\sin(7/10-u)\}-\sin u,
                      \qquad0\le u\le7/20.
\]
This is
\[
 \lambda(\cos(7/10)-\sin(7/10))\cos u
 +\{\lambda(\cos(7/10)+\sin(7/10))-1\}\sin u.
\]
The first coefficient is positive and the second negative,
using \(\lambda<3/5\), \(\sin t+\cos t\le\sqrt2<3/2\).
It therefore decreases on the whole interval. At \(u=7/20\),
\[
 f(u)>\frac7{12}\left(\frac{15}{16}-\frac{343}{1000}\right)
                     -\frac{343}{1000}
       =\frac{91}{24000}>0.
\tag{21}
\]
The degree-two lower cosine and degree-five upper sine at
\(7/20\) prove the two trigonometric bounds used in (21).

Consequently (14) is no larger than its scalar value at w zero.
By (16), its correction above S_0 is at most
\[
               (1-\cos x)+(1-\lambda)\sin s
                                      +\lambda(1-\cos s)
                \le\frac7{20}x+c_*s\le c_*r.
\tag{22}
\]
This comparison does not construct a new B point; it only bounds
the exact collected support for the original B frame.

Equations (7), (18), and (22) exhaust every original AB0 case.
For AB2 exchange A with B, G with T, and reverse the frame
direction. Its owner becomes AB0, both hard inequalities retain
their displayed roles, r stays nonnegative and unchanged, and
the left side b_G+b_T is unchanged. This proves (3) for both
original witnesses, including all ties and weak contacts.

The proof uses a fixed analytic stress, two square-root tangents,
and three already proved direct AB comparisons. No state or angle
mesh, numerical acceptance result, Lean compilation, or CI is a
premise.
