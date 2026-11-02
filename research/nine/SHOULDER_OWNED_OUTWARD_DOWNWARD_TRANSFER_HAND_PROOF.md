# A shoulder-owned outward endpoint normal retains both downward transfers

November 2, 2026 UTC. Complete hand derivation, using only displayed
support identities, elementary derivatives, and rational comparisons.
No mathematical program, numerical search, Lean, Lake, or CI.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 \mu=k/b=\frac{23}{24},\quad T=\frac{211}{4}.
\]
For a centered physical unit square S, write H_S(v) for its support
halfwidth and h_S=H_S(e_x)=H_S(e_y).

## 1. Physical premises and the two conclusions

Let an actual horizontal four-chain M0<_xM1<_xM2<_xM3 and physical
outsiders A,B have disjoint open interiors in a centered disk of radius
R_0<=r. Put M=M0 and assume x_A<=-29/60. Suppose a genuine separating
normal from M toward A is
\[
 n=(-t,s),\qquad 0\le t\le s,\qquad t^2+s^2=1,
\]
\[
 n\cdot(c_A-c_M)\ge H_M(n)+H_A(n),                    \tag{1}
\]
and n is parallel to a physical side axis of the shoulder A.
Suppose a genuine normal from A toward B is proportional to (1,-z):
\[
 (1,-z)\cdot(c_B-c_A)\ge
                   H_A((1,-z))+H_B((1,-z)),\qquad z\ge0. \tag{2}
\]
No actual vertical projection comparison of M,A is assumed, and no
ownership condition is imposed on the second normal.

There are two useful conclusions, both valid for every z>=0.

**Retained ordinary transfer.** If y_B-h_B>=1/10, put
\[
 E_B^-(z)=H_B((1,-z))+(1+z)h_B-(1+z)\ge0.
\]
Then
\[
\begin{aligned}
 a(-x_M-h_M)+b(1-x_B-h_B)
 \le T-bE_B^-(z)-bz(y_B-h_B-1/10).                   \tag{3}
\end{aligned}
\]

**Center-cost transfer.** If y_B-h_B>=7/60, then
\[
             a(-x_M-h_M)+b(1/2-x_B)\le T.             \tag{4}
\]

Both bounds are strict if R_0<r, t>0, or z>0. Horizontal reflection
gives the corresponding right-end statements. The complete
conditional paired caller is stated in Section 9.

## 2. Physical support facts already proved for this owner branch

The full two-chirality main-square calculation and physical endpoint
confinement in Sections 2--4 of
SHOULDER_OWNED_OUTWARD_UPWARD_TRANSFER_HAND_PROOF.md give
\[
 t<5/9,\qquad s>4/5,\qquad
 P_M:=a h_M+H_M(ae_x+kn)+kH_M(n)\ge k+as.              \tag{5}
\]
They apply to precisely the physical premises (1): in particular
the actual-four endpoint has h_M<8/15, the side-column premise gives
2/5<x_A-x_M<31/30, and no surrogate vertical separator is used.
We also have the stronger convenient bound
\[
                         s>83/100,                   \tag{6}
\]
directly from s^2>56/81>6889/10000; the last numerator difference is
560000-558009=1991.

Define
\[
 A(t)=\sqrt{a^2+k^2-2ak t},\quad
 B(t)=\sqrt{b^2+k^2+2bk t},\quad K(t)=r(A(t)+B(t)).
\]
The four-row rational curvature calculation there proves
\[
 K(t)\le K(0)-(k/2)t-(27/4)t^2,\quad
 K(0)=T+a+b+2k.                                      \tag{7}
\]
The resulting reserve
\[
 J(t)=(k/2)t+(27/4)t^2-(a-k)(1-s)
                 >\frac{259}{8000}t\quad(t>0)          \tag{8}
\]
is also proved there, with J(0)=0.
For A's actual orientation put
\[
 D_A=(1+\mu)h_A+H_A((-1,\mu))-(1+\mu)
                   =(1+\mu)(s-1)+t\ge0.              \tag{9}
\]
Consequently the physical two-square cap obeys
\[
 a(-x_M-h_M)+b(-x_A-h_A)\le T-bD_A-J(t).              \tag{10}
\]
These are hand-proved dependencies, including every signed support
case; this note extends them to downward second normals.

## 3. Exact support reduction for the downward normal

Write
\[
 L(t,z)=\sqrt{(1+\mu t)^2+(\mu s+z)^2}.
\]
The generalized physical support reduction, obtained by multiplying
(1) by k and (2) by b and applying disk supports, is
\[
\begin{aligned}
 a(-x_M-h_M)+b(-x_B-h_B)
 \le{}&r\{A(t)+bL(t,z)\}-bfz-P_M-P_A-P_B\\
     &-bz(y_B-h_B-f),                                 \tag{11}\\
 P_A={}&kH_A(n)+bH_A((1,-z))
                         +H_A(-be_x+kn+bz e_y),\\
 P_B={}&b\{(1+z)h_B+H_B((1,-z))\}.
\end{aligned}
\]
Here f is any whole-square floor for B. Replacing R_0 by r in
the disk-support bound is strict when R_0<r.

Because A owns n=(-t,s), its two side axes are n and (s,t).
Evaluating both absolute coordinates gives the exact formula
\[
                    P_A=k+b\{t+sz+|s-tz|\}.           \tag{12}
\]
For example, H_A((1,-z)) equals
(t+sz+|s-tz|)/2, while the last support in P_A equals
(k+b(t+sz)+b|s-tz|)/2. Thus (12) covers both sides of its
only breakpoint, z=s/t.

The sharp two-vector minimum from Section 2 of
DOWNWARD_TRANSFER_WITH_CENTRAL_CENTER_COST_HAND_PROOF.md is
\[
 z h_B+H_B((1,-z))\ge C(z)
 :=\frac{1+z+2z^2}{2\sqrt{1+z^2}}
 =\sqrt{1+z^2}+\frac{z-1}{2\sqrt{1+z^2}}.             \tag{13}
\]
For later use,
\[
 C''(z)=\frac{3(1-z)}{2(1+z^2)^{5/2}}.                \tag{14}
\]

For t>0 set R=s/t. By (5),(6),
\[
                     R>747/500>1.                    \tag{15}
\]
The symbol R in this note is the slope breakpoint, not the disk
radius R_0.

## 4. The retained ordinary transfer: only two slope values remain

Use f=1/10 in (11), retain the exact
P_B=b(1+z)+bE_B^-(z), and use (5),(12).
The scalar part of the resulting upper bound is
\[
\begin{aligned}
 G(t,z)={}&rA(t)-(k+as)+rbL(t,z)\\
         &-b\{\mu+t+sz+|s-tz|\}-(11b/10)z.             \tag{16}
\end{aligned}
\]
Thus (3) follows from G(t,z)<=T.

For each fixed t>0, the only curvature in (16), away from R,
comes from the radius norm. In fact
\[
 G_{zz}(t,z)=\frac{rb(1+\mu t)^2}{L(t,z)^3}>0
                    \quad(z\ne R).                   \tag{17}
\]
Moreover
\[
 \lim_{z\to\infty}\frac{G(t,z)}z
       =b\{r-s-t-11/10\}\le b(r-21/10)<0.              \tag{18}
\]
A convex function on [R,infinity) that tends to minus infinity is
nonincreasing: any positive secant slope would force all subsequent
secants to be positive. Therefore its maximum there is at R.
On [0,R], convexity places the maximum at 0 or R.

At z=0, (16) is exactly the scalar cap in (10), so
\[
                  G(t,0)\le T-bD_A-J(t)<T.             \tag{19}
\]
At z=R, we have L(t,R)=mu+1/t and P_A=k+b/t.
Consequently
\[
 G(t,R)=rA(t)-as+(r-2)k+
                      \frac b t\{r-1-(11/10)s\}.       \tag{20}
\]
Concavity of A gives
\[
             rA(t)\le23Q-2kt,                        \tag{21}
\]
since A(0)=23r and rA'(0)=-2k. Also
\[
 r<133/64,\qquad
 1-s=\frac{t^2}{1+s}<\frac{100}{183}t^2,\qquad
 23Q-a+(5/64)k-T=\frac{1575}{1024}.                    \tag{22}
\]
Substitution in (20) yields
\[
\begin{aligned}
 G(t,R)-T
 <\frac{1575}{1024}
  +\frac{4600}{183}t^2
  +\left(-\frac{207}{8}+\frac{495}{61}\right)t
  -\frac{189}{640t}.                                  \tag{23}
\end{aligned}
\]
Since t<5/9, the positive quadratic is at most
(23000/1647)t. Adding 495/61 gives (36365/1647)t, and
\[
 \frac{207}{8}-\frac{36365}{1647}>\frac{15}{4},
 \qquad 177\cdot1647=291519>290920=8\cdot36365.
\]
Thus
\[
 G(t,R)-T<
   \frac{1575}{1024}-\frac{15}{4}t-\frac{189}{640t}
                 <-\frac{473}{1024}<0,               \tag{24}
\]
because the product of the last two positive terms is
567/512>1, so their sum exceeds 2. This proves the retained
ordinary transfer for every t>0 and every z>=0, with the exact
central orientation and floor terms in (3).

For t=0, (1) is an actual vertical separation and the original
DOWNWARD_THREE_SQUARE_CAP_FLOOR_ONE_TENTH_HAND_PROOF.md applies.
Its strictness for z>0, together with (19),(24) and the disk-radius
step, proves every strictness assertion for (3).

## 5. The center-cost scalar and the initial slope interval

Now take f=7/60 in (11), drop the nonnegative floor excess, add
b(h_B+1/2), and use (5),(12),(13). It suffices to prove F(t,z)<=T,
where
\[
\begin{aligned}
 F(t,z)={}&rA(t)-(k+as)+rbL(t,z)\\
         &-b\{\mu+t+sz+|s-tz|\}-bfz-bC(z)+b/2.         \tag{25}
\end{aligned}
\]
At t=0 the original center-cost theorem applies directly. Assume
t>0 for the rest of the proof.

First suppose
\[
                         0\le z\le R-\mu.              \tag{26}
\]
This interval is nonempty by (15). Set W=mu+z. For A, write
h=(s+t)/2 and j=(s-t)/2. A top vertex is w=(j,h).
Since W<=R, a vertex maximizing (-1,W) is v=(-h,j).
Thus v+w=(-t,s).

Let the purely algebraic reference support be
\[
 P_A^0=kh_A+bH_A((1,-z))+bH_A((-1,\mu+z)).
\]
Using these two actual vertices as witnesses for the changed support
directions gives
\[
 P_A-P_A^0\ge k\{(-t)(-t)+(s-1)s\}=k(1-s).            \tag{27}
\]
This is a support comparison in the actual orientation of A; it
does not introduce an auxiliary packing with vertical separation.
Similarly, (5) gives P_M-(a+k)>=-a(1-s).

The norm increment
\[
                    L(t,z)-L(0,z)
\]
is nonincreasing in z. To see this, each z derivative is the increasing
function q/sqrt(1+q^2) of its vertical-to-horizontal ratio q, and
\[
          \frac{z+\mu s}{1+\mu t}\le z+\mu.
\]
Therefore
\[
 r\{A(t)-A(0)+bL(t,z)-bL(0,z)\}\le K(t)-K(0).          \tag{28}
\]

The scalar proof of the original center-cost theorem bounds the
reference expression, with P_M replaced by a+k and P_A by P_A^0,
by T for every actual orientation of A and B. It relies only on
the displayed E,N,D orientation minima and their scalar estimates.
By (27),(28), the changed expression in (25) is at most that
reference expression plus
\[
 K(t)-K(0)+(a-k)(1-s)\le-J(t)<0.                       \tag{29}
\]
This proves F(t,z)<T throughout (26), including its right endpoint.

## 6. Two explicit center-cost anchor estimates

### 6.1. The slope z=1

At z=1 the shoulder penalty is k+2bs. Put
\[
 L_*=\sqrt{1+(\mu+1)^2}=\sqrt{2785}/24,\qquad
 K_1=rk/L_*<13.
\]
The last inequality follows, for example, from r<133/64,
L_*>21/10, and
133*207*10=275310<279552=13*64*16*21.
Since L(t,1)^2=L_*^2+2mu(s+t-1), norm concavity and (21) give
\[
\begin{aligned}
 F(t,1)-F(0,1)
 &\le -2kt+K_1(s+t-1)+(a+2b)(1-s)\\
 &\le-\frac{103}{8}t+60(1-s).                        \tag{30}
\end{aligned}
\]
Here s+t-1>=0, which justifies replacing K_1 by 13.
The final expression is convex in t on [0,5/9]. Its value at zero
is zero, and its value at 5/9 is less than
\[
       -\frac{515}{72}+60\frac{17}{100}
                        =\frac{1097}{360}.            \tag{31}
\]

For the aligned shoulder at t=0, the exact E-branch expression is
\[
 F(0,1)=T-b\{\Delta_E(1)-d(1)\},
\]
\[
 \Delta_E(1)=\frac{127}{60}
                -r\frac{\sqrt{2785}-\sqrt{1105}}{24},
 \qquad d(1)=\frac{3-2\sqrt2}{2}.
\]
The elementary root bounds sqrt2785<53, sqrt1105>166/5,
sqrt2>7/5 and r<133/64 give
\[
 b\{\Delta_E(1)-d(1)\}
 >\frac{27}{2}\left(\frac{127}{60}
                           -\frac{4389}{2560}-\frac1{10}\right)
 =\frac{62667}{15360}>4.                              \tag{32}
\]
Together (30)--(32) prove
\[
                      F(t,1)<T-\frac{343}{360}.        \tag{33}
\]

### 6.2. The shoulder support breakpoint z=R

At R=s/t, (13) gives C(R)=1/t+j, with j=(s-t)/2.
The exact scalar value is
\[
 F(t,R)=rA(t)-as+(r-2)k+
                 b\left\{\frac{r-2-fs}{t}+\frac12-j\right\}.
                                                               \tag{34}
\]
By (6),
\[
 r-2-fs<\frac5{64}-\frac7{60}\frac{83}{100}
                            =-\frac{449}{24000}.
\]
Use (21),(22) and (1/2-j)=(1-s+t)/2 in (34):
\[
 F(t,R)-T<
  \frac{1575}{1024}-\frac{153}{8}t
       +\frac{5275}{183}t^2-\frac{12123}{48000t}.       \tag{35}
\]
As t<5/9,
\[
 \frac{5275}{183}t^2\le\frac{26375}{1647}t<\frac{129}{8}t,
 \qquad211000<212463.
\]
Consequently
\[
 F(t,R)-T<
  \frac{1575}{1024}-3t-\frac{12123}{48000t}
                         <-\frac{317}{5120}<0.        \tag{36}
\]
Indeed the product of the last two positive terms is
12123/16000>16/25, so their sum exceeds 8/5.

## 7. All slopes at least one

Away from R, differentiating (25) twice and using (14) gives
\[
 \frac1b F_{zz}(t,z)=
 \frac{r(1+\mu t)^2}{L(t,z)^3}
                   -\frac{3(1-z)}{2(1+z^2)^{5/2}}.    \tag{37}
\]
This is strictly positive for z>=1. Thus F is convex separately
on [1,R] and [R,infinity). Its limiting slope is
\[
 \lim_{z\to\infty}\frac{F(t,z)}z
   =b\{r-s-t-f-1\}\le b(r-2-7/60)<0.                 \tag{38}
\]
The same elementary convexity argument as in Section 4 bounds F
on the whole range z>=1 by its values at 1 and R.
Both are strictly below T by (33),(36).

## 8. The only possible gap is covered by a two-row rational table

Sections 5 and 7 leave only
\[
                        R-\mu<z<1.                   \tag{39}
\]
If this interval is nonempty, then R<1+mu=47/24, hence
\[
 t>\frac{24}{\sqrt{2785}}>\frac9{20}.
\]
The last comparison is equivalent to 230400>225585.
Also (15) gives
\[
 R-\mu>\frac{747}{500}-\frac{23}{24}
                         =\frac{1607}{3000}>\frac12.  \tag{40}
\]
Thus this possible gap lies in the rectangle
\[
                   9/20\le t\le5/9,\qquad1/2\le z\le1.
\]
It remains to show F_{zz}>0 there.

The numerator of the first term in (37) has the uniform lower bound
\[
           r(1+\mu t)^2>
                   \frac{33}{16}\left(\frac{229}{160}\right)^2.
\]
For z<=1 and t<=5/9,
\[
 \partial_t L(t,z)^2=2\mu(1-zt/s)>0,
 \qquad \partial_z L(t,z)^2=2(\mu s+z)>0.
\]
Therefore L^2 is bounded above at the upper endpoints of each row.
Use the identity
L^2=1+mu^2+z^2+2mu(t+sz), and at t=5/9 use s<5/6.
The following entirely rational table supplies the two comparisons:

| z interval | Upper L² | Upper L | Lower first term of (37) | Upper second term |
|---|---:|---:|---:|---:|
| [1/2,5/8] | 7555/1728 | 21/10 | 9/20 | 7/16 |
| [5/8,1] | 9643/1728 | 12/5 | 3/10 | 2304/7921 < 3/10 |

The L comparisons reduce to
755500<762048 and 241075<248832. The first-term comparisons are
\[
 \frac{1730553000}{3793305600}>\frac9{20},
 \qquad
 \frac{216319125}{707788800}>\frac3{10}.                \tag{41}
\]
These are obtained directly by dividing
(33/16)(229/160)^2 by (21/10)^3 and (12/5)^3, respectively.

For the last column, the function
3(1-z)/(2(1+z^2)^{5/2}) decreases on [1/2,1]:
its derivative has the sign of 4z^2-5z-1<0.
At z=1/2 its value is
\[
                 \frac{24}{25\sqrt5}<\frac{24}{55}<\frac7{16}.
\]
At z=5/8 it is less than 2304/7921, after replacing the
remaining square-root denominator by 1. Finally
23040<23763 proves that this bound is less than 3/10.
Both rows therefore give F_{zz}>0.

For each t for which (39) is nonempty, F is consequently convex
on [R-mu,1]. Its first endpoint is below T by (29), and its
second endpoint is below T by (33). It is strictly below T
throughout this interval as well.

Sections 5--8 cover every z>=0, proving (4) for t>0.
For t=0 the physical separator (1) is vertical and the established
center-cost theorem applies, strictly for z>0. The strict
disk-radius step proves the remaining stated strictness.

## 9. How this completes the outward shoulder-owned caller branch

Together with SHOULDER_OWNED_OUTWARD_UPWARD_TRANSFER_HAND_PROOF.md,
this note covers both signs and all slopes of the shoulder-to-central
separator when the matched endpoint normal is upward, nearvertical,
outward, and owned by the shoulder. The left and right endpoint
choices may be made independently.

For two downward shoulder-to-central transfers, apply (4) and its
horizontal reflection with central whole floor at least 7/60.
Their central-center terms cancel exactly. For a mixed pair, use
(3), retaining its actual E_B^- and whole-floor slack, and the
upward theorem's unchanged central E_B and top-height terms.
Its shoulder reserve exceeds (21/10-r)z for every positive upward
slope, so the shared-height argument in
SHARED_CENTRAL_ORIENTATION_AND_ALL_MIXED_SHOULDER_SIGNS_HAND_PROOF.md
applies without any additional slope restriction. For two upward
transfers use that same note's universal shared-orientation loss
and the upward theorem's reserve exceeding (1/10)min(z,1).

These substitutions also mix independently with an actual vertical
endpoint comparison or with an upward nearvertical endpoint-owned
normal covered by ENDPOINT_OWNED_OBLIQUE_UPWARD_TRANSFER_HAND_PROOF.md
and ENDPOINT_OWNED_OBLIQUE_DOWNWARD_CENTER_TRANSFER_HAND_PROOF.md.
All physical squares in the paired caller must be in the same
centered disk. The upward side-column premise and the central-floor
premise remain explicit.

This is a conditional physical endpoint-owner closure. It does not
assert that every endpoint pair has one of the covered normals.
Inward shoulder-owned endpoint normals and nearhorizontal endpoint
normals remain separate owner branches.
