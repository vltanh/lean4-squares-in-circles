# Every nearvertical endpoint-owned downward transfer retains the center cost

November 1, 2026 America/Chicago / November 2 UTC. Complete hand
derivation. No mathematical program, numerical search, Lean, Lake, or CI.
This removes the actual vertical endpoint comparison from the downward
center-cost transfer for the complete nearvertical endpoint-owned branch.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 \mu=\frac{k}{b}=\frac{23}{24},\quad T=\frac{211}{4},\quad f=\frac7{60}.
\]
For a centered physical unit square S let H_S(v) be its support
halfwidth and h_S=H_S(e_x)=H_S(e_y).

## 1. Exact statement

Let M,A,B be physical unit squares with disjoint open interiors.
M and A are contained in the centered disk of radius R_0<=r, and
\[
                              h_M<8/15.                 \tag{1}
\]
Suppose a genuine separating unit normal from M toward A is
\[
 n=(c,s),\quad s\ge|c|,\quad c^2+s^2=1,
\]
\[
             n\cdot(c_A-c_M)\ge H_M(n)+H_A(n),          \tag{2}
\]
and n is parallel to a physical side axis of M. Suppose a genuine
separator from A toward B is proportional to (1,-z), with z>=0:
\[
 (1,-z)\cdot(c_B-c_A)\ge H_A((1,-z))+H_B((1,-z)).       \tag{3}
\]
Finally suppose B lies wholly above y=f:
\[
                             y_B-h_B\ge7/60.            \tag{4}
\]
Then, for **both signs of c and every z>=0**,
\[
 \boxed{a(-x_M-h_M)+b(1/2-x_B)\le T.}                  \tag{5}
\]
The inequality is strict if R_0<r, c is nonzero, or z>0. No
actual vertical projection comparison of M and A is assumed. No
ownership assumption is imposed on the A,B normal. Disk containment
of B is not needed in this single transfer; its whole floor is used.

At equality c=z=0. In particular the endpoint separator is vertical
and the shoulder-to-central separator is horizontal. The central
square is aligned, as in the original center-cost transfer.

An outer endpoint of an actual four-chain satisfies (1), so this
theorem applies to that geometric caller. It does not address a
shoulder-owned-only or a nearly horizontal endpoint normal.

## 2. The generalized support expression

Multiply (2) by k and (3) by b, and use containment supports in
directions -a e_x-k n and -b e_x+k n+bz e_y. With
\[
 L_M(c)=\sqrt{a^2+k^2+2ak c},\qquad
 V_A(c)=|-b e_x+k n+bz e_y|,
\]
the usual support addition gives
\[
\begin{aligned}
 a(-x_M-h_M)+b(-x_B-h_B)
 \le{}&r\{L_M(c)+V_A(c)\}-bfz-P_M(c)-P_A(c)-P_B,      \tag{6}
\end{aligned}
\]
where
\[
 P_M(c)=a h_M+H_M(ae_x+kn)+kH_M(n),
\]
\[
 P_A(c)=kH_A(n)+bH_A((1,-z))+H_A(-be_x+kn+bz e_y),
\]
\[
 P_B=b\{(1+z)h_B+H_B((1,-z))\}.                      \tag{7}
\]
If R_0<r the disk-support step is strict. Equation (6) uses physical
separators (2),(3); no surrogate vertical separator has been inserted.

Set W=mu+z and L=sqrt(1+W^2). At the reference vector n=e_y,
the shoulder expression is
\[
 P_A^0=k h_A+bH_A((1,-z))+bH_A((-1,W)).                \tag{8}
\]
Define the comparison expression
\[
 U_0=r\{L_M(0)+bL\}-bfz-(a+k)-P_A^0-P_B.             \tag{9}
\]
This is an algebraic expression evaluated using the actual orientations
of A and B. It is not an auxiliary packing. The scalar proof in
`DOWNWARD_TRANSFER_WITH_CENTRAL_CENTER_COST_HAND_PROOF.md` proves
\[
                       U_0+b(h_B+1/2)\le T,            \tag{10}
\]
strictly when z>0. Specifically its three triangle candidates E,N,D
bound P_A^0/b, its two-vector inequality bounds P_B, and its complete
E,N,D scalar estimates prove (10). Those scalar estimates impose no
further geometric hypothesis. At z=0 equality in the central support
bound requires h_B=1/2.

It therefore suffices to show that the right side of (6) is at most
U_0, strictly if c is nonzero. The following comparison does so.

## 3. Exact endpoint ownership and the norm changes

Let epsilon=|c|. Since M owns n and s>=epsilon, h_M=(s+epsilon)/2.
The elementary tilt calculation in
`ENDPOINT_OWNED_OBLIQUE_UPWARD_TRANSFER_HAND_PROOF.md` gives
\[
 \epsilon<1/14,\quad s>27/28,\quad
             1-s<\frac2{55}\epsilon\quad(\epsilon>0).\tag{11}
\]
For clarity, epsilon+s<16/15 by (1); at epsilon=1/14 the left
side exceeds 16/15 because sqrt(195)>209/15. Then
(1-s)/epsilon=epsilon/(1+s)<2/55.

Evaluation in M's side frame gives
\[
 P_M(c)=
 \begin{cases}
 k+a(c+s),&c\ge0,\\
 k+as,&c<0.
 \end{cases}                                         \tag{12}
\]
The second formula uses epsilon<1/14<k/a. Concavity of the square
root, and rL_M'(0)=2k, give
\[
                         r(L_M(c)-L_M(0))\le2kc.       \tag{13}
\]
The other squared norm differs from its reference value by
\[
             V_A(c)^2-(bL)^2=-2bk c+2bkz(s-1).         \tag{14}
\]
Thus V_A(c)<=bL for c>=0. For c<0, concavity of the square root
gives the upper difference bound
\[
                         V_A(c)-bL\le k\epsilon/L.    \tag{15}
\]
The nonpositive second term in (14) has only strengthened this bound.

## 4. A signed shoulder-vertex bound for the complete orientation interval

Choose a topmost vertex w of A, and a vertex v maximizing the
direction (-1,W). For the fixed reference support (8), these give
\[
 P_A(c)\ge P_A^0+k\{cX+(s-1)Y\},
 \qquad(X,Y)=v+w.                                    \tag{16}
\]
They can be chosen to satisfy
\[
 -1\le X\le X_+(W):=\max\left\{0,\frac{W-1}{\sqrt{1+W^2}}\right\},
 \qquad 0\le Y\le\sqrt2<3/2.                         \tag{17}
\]

Here is the complete two-chirality proof. Write alpha>=beta>=0,
alpha^2+beta^2=1, h=(alpha+beta)/2, j=(alpha-beta)/2.
For the first chirality take w=(j,h). The maximizing v is (-h,j)
if W<=alpha/beta, giving X=-beta; if W>=alpha/beta, take v=w,
giving X=alpha-beta. The latter case requires W>=1, and
\[
 \alpha-\beta=
 \frac{\alpha/\beta-1}{\sqrt{1+(\alpha/\beta)^2}}
                \le\frac{W-1}{\sqrt{1+W^2}},
\]
because (u-1)/sqrt(1+u^2) increases for u>=1.
If beta=0, the first case applies directly for finite W.

For the other chirality take w=(-j,h). The maximizing v is (-h,-j)
if W<=beta/alpha, giving X=-alpha; otherwise v=w gives X=-2j.
Both are nonpositive. The possible Y values are alpha, beta, and
alpha+beta, all in [0,sqrt(2)]. Ties allow either listed choice.
This proves (17), including aligned squares and support ties.

The useful exact envelope is
\[
                       r/L+X_+(W)\le3/2\quad(W\ge\mu).
                                                               \tag{18}
\]
If mu<=W<=1, X_+=0 and
L>=sqrt(1+mu^2)=2r/3. If W>=1, the left side is
(r+W-1)/sqrt(1+W^2). Its derivative has numerator
1-(r-1)W<0, because r>2. Its maximum on that interval is
r/sqrt(2)<3/2, since Q<9/2. Both ranges prove (18).

## 5. Both horizontal signs give a positive reserve

Subtract U_0 from the right side of (6). Its difference is
\[
 r(L_M(c)-L_M(0))+r(V_A(c)-bL)
              -(P_M(c)-(a+k))-(P_A(c)-P_A^0).          \tag{19}
\]
For c>0, use (12)--(14), X>=-1 and Y<3/2 in (16).
The difference (19) is at most
\[
 -(a-3k)c+(a+3k/2)(1-s)
 < -\left(\frac{115}{16}-\frac2{55}\frac{2093}{32}\right)c
 =-\frac{529}{110}c<0.                               \tag{20}
\]

For c<0, use (12),(13),(15),(16), and X<=X_+(W). The difference
is at most
\[
 k\epsilon\{-2+r/L+X_+(W)\}+(a+3k/2)(1-s).
\]
The envelope (18) and (11) bound this strictly above by
\[
 -\left(\frac k2-\frac2{55}(a+3k/2)\right)\epsilon
                   =-\frac{7199}{1760}\epsilon<0.     \tag{21}
\]
At c=0 the expression (19) is zero. Hence the right side of (6)
is at most U_0, with a strictly positive improvement for every
nonvertical endpoint-owned normal in (2).

Add b(h_B+1/2) and use (10). This proves (5) and every asserted
strictness and equality condition.

## 6. The retained downward reserves needed by a mixed-sign caller

The same comparison also preserves the weaker-floor downward transfer
with its central orientation and height terms. Namely, keep (1)--(3),
assume only y_B-h_B>=1/10, and put
\[
 E_B^-(z)=H_B((1,-z))+(1+z)h_B-(1+z)\ge0.
\]
Then
\[
\begin{aligned}
 a(-x_M-h_M)+b(1-x_B-h_B)
 \le T-bE_B^-(z)-bz(y_B-h_B-1/10),                    \tag{22}
\end{aligned}
\]
strictly if R_0<r, c is nonzero, or z>0.

To see this directly, use f=1/10 in (6),(9), and retain the
additional term -bz(y_B-h_B-f) when using the actual y_B in the
support reduction. Instead of the two-vector center-cost estimate,
use the E,N,D scalar inequalities in
`DOWNWARD_THREE_SQUARE_CAP_FLOOR_ONE_TENTH_HAND_PROOF.md`, keeping
the exact penalty
P_B=b(1+z)+bE_B^-(z). They give (22) for the reference expression.
The comparison (19)--(21) is independent of f and unchanged; it
preserves those central terms and supplies the same strict oblique
reserve. This proves (22) without assuming a vertical M,A comparison.

## 7. Paired geometric caller

In an actual-four-chain configuration, require all seven physical
units to be interior-disjoint in the same centered disk. Both outer
endpoints satisfy h_M<8/15. Suppose the two shoulders and one central unit have the
central whole floor 7/60, and each downward shoulder-to-central
separator has the indicated horizontal sign toward the central unit.
If each physical shoulder-to-outer-main pair has an upward nearvertical
separator owned by its outer main, apply (5) on the left and its
horizontal reflection on the right. The two central centers cancel,
and the actual-four span gives
\[
 2a+b\le a(x_3-x_0-h_0-h_3)+b\le2T=2a+b.
\]
Strict subcritical containment is impossible. Positive downward
slopes or nonvertical endpoint normals are impossible at equality.

The upward owner theorem covers the other transfer signs, retaining
the common central orientation and height. In a mixed-sign pair, use
(22) on the downward side and the upward theorem's adjusted reserve
on the other side. That adjusted reserve exceeds (21/10-r) times
the upward slope for every positive slope, so it pays the complete
mixed central-height deficit exactly as in the shared-central proof.

Therefore the combination covers all signed shoulder-to-central
slopes when both matched endpoint separators are upward, nearvertical,
and owned by their outer main, the upward-transfer shoulders satisfy
their side-column premises, and the central whole floor is at least
7/60. The mixed case alone needs only the floor1/10. Mixed
actual-vertical/endpoint-owned choices are allowed independently on
the two sides. Every stated geometric premise must still be supplied.

The requirement that an endpoint owns the displayed separator is
essential to (12). An arbitrary shoulder-owned separator is not
silently substituted, nor is a nearly horizontal endpoint normal.
The global caller still has to classify or exclude those remaining
physical owner domains and the weak-chain arrangements.
