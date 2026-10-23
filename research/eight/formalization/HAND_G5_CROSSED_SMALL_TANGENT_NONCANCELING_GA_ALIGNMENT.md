# The smaller crossed noncanceling tangent also reaches GA alignment

## 1. Scope and the additional capture

Put
\[
 Q=\frac{9789}{2500},\qquad p=\frac{50}{49},\qquad
 S_0=2\sqrt{Q-1}-3.
\tag{1}
\]
Retain the normal signs at H,G,A,B,T,D, either E sign, sorted
own-frame magnitudes, true core avoidance, circles at most
\(q\le Q\), and a real frame interval of length at most
\(7/10\). The retained witnesses are
\[
 HG=0,\quad GA=0,\quad BT=2,\quad TD\in\{0,2\},
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\}.
\]
Assume
\[
 \theta_A=\theta_B=\rho,\quad b_A+b_B=1,\quad
 \theta_T\le\rho\le\theta_G,\quad \theta_H<\rho,
 \qquad \frac{67}{200}\le b_A\le\frac12.
\tag{2}
\]

**Theorem.** Every such necessary system has the stronger
captures
\[
                  b_A>\frac{47}{98},\qquad
                  0<\rho-\theta_H<\frac1{100}.
\tag{3}
\]
It has a descendant at the same q with \(\theta_G'=\rho\)
and the same HG0/GA0 witnesses. H,B,T,D,E, their frames and
coordinates, and A's frame and tangent remain unchanged.
A nonzero original \(\theta_G-\rho\) creates a strict A
circle loss; inherited separate A/B losses are retained.

This extends the
[large-tangent crossed GA-alignment lemma](HAND_G5_CROSSED_NONCANCELING_LARGE_TANGENT_GA_ALIGNMENT.md).
It does not assume that the opposite outer zero has already
been aligned. The lower input \(b_A\ge67/200\) is explicit.
It does not treat HG2, which remains a separate owner branch.

## 2. The same exact scalar budget on the enlarged tangent interval

Use the notation of Sections 2--3 of the cited lemma:
\[
 \rho=0,\quad \theta_H=-r,\quad\theta_G=z,\quad
 \theta_T=-v,\qquad r>0,\quad z,v\ge0,
\]
\[
 b=b_A,\quad Y=b+\frac12,\quad Y_B=2-Y,
 \quad R=\sqrt{Q-Y^2},\quad P=R-1,
 \quad R_B=\sqrt{Q-Y_B^2},\quad P_B=R_B-1.
\tag{4}
\]
The inverse hard angle \(z_A\) is defined by
\[
                  P\cos z_A-Y\sin z_A=\frac12,
\]
and \(z_B\) by the same equation with \(P_B,Y_B\).
Let
\[
 V(z)=P\cos z-Y\sin z,\quad U(z)=P\sin z+Y\cos z,
 \quad w(z)=\sqrt{Q-V(z)^2},
\]
\[
 B(r,z,b)=\frac12+\{1-V(z)\}\cos(r+z)
                          -\{w(z)-1\}\sin(r+z),
\]
\[
 M(b)=\max_{0\le v\le z_B}
          \{P_B\cos v-Y_B\sin v+pv\}.
\tag{5}
\]
The actual mixed endpoint estimate and TD zero charge give,
exactly as in that lemma,
\[
                         B(r,z,b)+\frac12+pr-M(b)<1-S_0.
\tag{6}
\]
The comparisons here use Q only to enlarge necessary circle
bounds. Section 7 returns to the actual q.

Throughout (2), positive squaring and alternating Taylor
bounds give
\[
 .835\le Y\le1,\quad 1.7075<R<1.794,
 \qquad .195<z_A<.312.
\tag{7}
\]
For the upper angle bound, evaluate the decreasing hard
expression with \(P<.794\), \(Y\ge.835\) at .312.
For the lower bound, its inverse decreases with Y; at Y=1,
use \(P>.7075\) and evaluate at .195.

The strict concavity in z used previously still holds on
this entire larger interval. In fact, put \(T=w-U\).
The same identities give \(T>0\), \(T'<0\), \(T''>0\),
and \(T<1\), since \(Y>P\). Moreover
\[
 1-\frac{2VT}{w}>
       1-2(.794)\frac{216}{383}>0,
\tag{8}
\]
because \(U\ge.835\), \(w<1.915\).
The same differentiated formula
\[
 F''(h)=\cos h\left(1-\frac{2VT}{w}\right)
                     +\sin h(1-T+T'')>0
\]
therefore applies up to \(h=r+z_A<1.012<1.1<\pi/2\).
Thus
\[
              B(r,z,b)\ge\min\{B(r,0,b),B(r,z_A,b)\}.
\tag{9}
\]
As before, this enlarged endpoint comparison is algebraic;
it does not assert a new state outside the original frame interval.

## 3. Keep a positive reserve at the zero-transverse endpoint

Write
\[
 k=\sqrt{Q-1/4}-1,\qquad
 f(h)=ph-k\sin h-\frac12(1-\cos h).
\]
The stronger estimate needed here is
\[
                         f(h)>.007
                  \qquad(.195\le h\le1.1).
\tag{10}
\]
Here and below every terminating decimal is an exact rational.
The already proved convexity of \(f'\) on \([0,.7]\)
shows that f first increases and then decreases there.
Consequently its minimum on \([.195,.7]\) is at an endpoint.
Using \(.914<k<.915\), the alternating degree-five upper
sine and degree-six lower cosine give
\[
                         f(.195)>.007,
                         \qquad f(.7)>.00723.
\]
On \([.7,1.1]\), \(f'''>0\). The degree-four upper cosine
and degree-seven lower sine give
\[
                         f'(.7)>-.002,
                         \qquad f''(.7)>.2.
\]
Two integrations and a completed square therefore give
\[
 f(h)>.00723-.002(h-.7)+.1(h-.7)^2
                    \ge .00723-.00001>.007.
\]
This proves (10) on the whole displayed interval.

At the endpoint \(z=z_A\), the exact calculation in the
large-tangent lemma gives
\[
 B(r,z_A,b)+\frac12+pr-M(b)=1-J(b)+f(r+z_A),
\quad J(b)=pz_A+M(b)-\frac12.
\tag{11}
\]
We next prove
\[
                              J(b)<.419
                 \quad(.335\le b\le.5).
\tag{12}
\]
The positive term in (10) will make this sufficient.

## 4. The endpoint envelope J has only two intrinsic pieces

Put \(b_c=47/98\). For \(b\le b_c\), one has
\(Y_B\ge p\). The derivative of the expression maximized
in (5) starts nonpositive at v=0 and strictly decreases,
because its second derivative is \(-V_B\le-1/2\).
Hence
\[
                    M=P_B,\qquad J=pz_A+R_B-\frac32
                         \quad(.335\le b\le b_c).
\tag{13}
\]

The inverse-angle identity from Section 5 of the cited lemma is
\[
 z_{YY}=-\frac{Y}{R^3}(1+s/U)
            +\frac{c}{R^2U}(1+s/U)+\frac{sY}{R^2U^3},
\quad U=\sqrt{Q+3/4-2R},\ s=\sin z_A,\ c=\cos z_A.
\tag{14}
\]
On the whole small-tangent interval,
\(1.7<R<1.8\), \(1.03<U<1.12\), and \(s<.312\).
It follows that
\[
 z_A''<
 -\frac{.835}{1.8^3}
 +\frac{1+.312/1.03}{1.7^2\cdot1.03}
 +\frac{.312}{1.7^2\cdot1.03^3}<\frac25.
\tag{15}
\]
The first two terms in (14) also show \(z_A''>0\): their
combined numerator contains \(cR-YU\), which exceeds
\(.95\cdot1.7-1.12>0\).

Since \(R_B<1.708\), (13)--(15) give
\[
                   J''<p\frac25-\frac{Q}{1.708^3}<0.
\tag{16}
\]
At \(b=.335\), positive squaring and the hard contact give
\[
 R<1.794,\quad U<1.039,\quad z_A>.31,\quad
 \sin z_A>.305,\quad R_B>1.599.
\]
Using \(z_Y=-(1+s/U)/R\),
\[
 J'(.335)<\frac{1.165}{1.599}
                -\frac{p}{1.794}\left(1+\frac{.305}{1.039}\right)<0.
\tag{17}
\]
Thus J decreases throughout the interval in (13). At its
left endpoint, \(z_A<.312\) and \(R_B<1.6\) give
\[
                 J(.335)<p(.312)+.1
                         =\frac{41}{98}<.419,
\tag{18}
\]
with final reserve \(31/49000\).

For \(b_c\le b\le.5\), the maximizer in (5) is the free
stationary point \(U_B=p\), starting with v=0 at \(b_c\).
Here
\[
 1.695<R_B<1.708,\quad V_B<.696,\quad
                         v\le2(p-1),\quad\cos v>.999.
\]
The stationary-envelope identity
\[
 M''=-\frac{Q\cos v}{R_B^3}
                         +\frac{(V_B+\cos v)^2}{R_B^2V_B}
\]
therefore gives
\[
 M''>\frac{(.696+.999)^2}{1.708^2\cdot.696}
                                    -\frac{Q}{1.695^3}>\frac12.
\tag{19}
\]
The bound on v follows by integrating \(U_B'=V_B\ge1/2\).
The free maximum lies before its hard endpoint, since at
that endpoint \(U_B>1.117>p\).

Thus \(J''=pz_A''+M''>0\) on this short free piece. Its
maximum is at one of its two endpoints. The first is below
.419 by (18), while the already audited balanced endpoint
estimate in Section 7 of the large-tangent lemma gives
\(J(.5)<.409\). The two envelope formulas and their first
derivatives agree at \(b_c\). This proves (12).

Now (7), (10)--(12) give, at the zero-transverse endpoint,
\[
 B(r,z_A,b)+\frac12+pr-M(b)>1-.419+.007=.588.
\]
But \(S_0>.415\), so \(1-S_0<.585\). This contradicts
(6). The G-zero endpoint is excluded for the entire tangent
interval (2).

## 5. The aligned endpoint excludes tangents at or below 47/98

At z=0 put \(w_A=\sqrt{Q-(R-1)^2}\). Since \(Y\le1\),
\[
 1-P<.2925,\qquad w_A-1<.85,
 \qquad (.2925)^2+(.85)^2<(.9)^2.
\]
The last positive square reserve is \(311/160000\).
It follows by Cauchy--Schwarz that
\[
 \frac{d}{dr}\{B(r,0,b)+pr\}
     =p-(1-P)\sin r-(w_A-1)\cos r>p-.9
                                \quad(0\le r\le.7).
\tag{20}
\]
At r=0 the required H tangent is \(5/2-R\).
If \(b\le b_c\), (13) and (20) therefore give
\[
 B(r,0,b)+\frac12+pr-M(b)
     >4-R-R_B\ge4-2\sqrt{Q-1}=1-S_0.
\tag{21}
\]
The middle inequality is concavity of
\(Y\mapsto\sqrt{Q-Y^2}\) applied to Y and \(2-Y\).
This contradicts (6). Together with (9) and the excluded
G-zero endpoint, it proves the first assertion in (3)
for the original state.

## 6. The remaining crossing is below one hundredth

Now \(b_c<b\le.5\), so \(1\le Y_B<p\). The opposite
envelope has the elementary quadratic bound
\[
                   0\le M-P_B\le(p-Y_B)^2\le(p-1)^2.
\tag{22}
\]
Indeed the maximized function starts at \(P_B\), has
initial derivative \(p-Y_B\), and second derivative
\(-V_B\le-1/2\) throughout its hard interval.
Use (20), (22), and the same concavity comparison as in
(21). If \(r\ge1/100\), then
\[
 \begin{split}
 B(r,0,b)+\frac12+pr-M(b)
 &>1-S_0+\frac{p-.9}{100}-(p-1)^2\\
 &=1-S_0+\frac{1891}{2401000}>1-S_0.
 \end{split}
\tag{23}
\]
This contradicts (6). The two-endpoint comparison (9)
therefore proves the second capture in (3) for the original
state, without changing its A tangent.

## 7. Direct GA alignment at the actual q

Return to q, keep A's tangent fixed, and lift only A's
primary to its containing q-circle if necessary. By (3),
\[
                         Y>\frac{48}{49},\qquad r<.01.
\]
Use the same functions as in (4)--(5) with Q replaced by q.
Positive squaring gives
\[
 R<1.7195,\qquad z_A<.21,
                    \qquad h_{\max}=r+z_A<.22.
\tag{24}
\]
For the angle bound, the hard expression at .21 is less
than \(1/2\) already using \(P<.7195\), \(Y\ge48/49\).
The same F'' formula remains positive: \(Y>P\), and
\[
 1-\frac{2VT}{w}>
                 1-2(.72)\left(1-\frac{48/49}{1.915}\right)>0.
\]

At the endpoint \(V=1/2\), set
\[
 w_0=\sqrt{q-1/4},\quad
 U_0=\sqrt{q+3/4-2\sqrt{q-Y^2}},\quad T_0=w_0-U_0.
\]
As before, \(T_0\) decreases with Y and increases with q.
The latter derivative is positive already from
\(U_0\ge Y\ge48/49\), \(R<1.72\), \(w_0<1.915\).
Thus its maximum is at \(q=Q,Y=48/49\). At that point,
\(R<1.7195\) gives \(U_0>1.107\), and hence
\[
                              T_0<.808.
\tag{25}
\]
The endpoint derivative of F increases with both \(T_0\)
and \(w_0\). From (24)--(25),
\[
 \begin{split}
 F'(h_{\max})
 &<-.192(1-.22^2/2)
                  +.22\left(1-\frac{.808}{3.83}\right)\\
 &=-\frac{823817}{59843750}<-\frac1{100}.
 \end{split}
\tag{26}
\]
Since F''>0, the same upper derivative bound holds over
the entire z interval. Consequently
\[
                 B(r,0,b)<B(r,z,b)-z/100\qquad(z>0).
\tag{27}
\]

Construct G at the common frame with
\[
                    b_G=R-\frac32,\qquad
                    a_G=\sqrt{q-(R-1)^2}-\frac12.
\]
GA0 is an equality, and HG0 has the strict slack (27).
Here \(0\le b_G<.2195<b_A\), so \(a_G>a_A\ge1\).
Sorting, circle containment and the true core are preserved.
For z>0, lower A's primary slightly and adjust \(b_G\)
continuously to retain aligned GA0. The strict HG0 slack
persists and A's circle becomes strictly less than q.
This recreates any inherited A loss after the temporary lift.
For z=0, no lift or change is required. B and its separate
loss have never changed.

The proof uses two intrinsic envelope pieces, one inverse-angle
curvature calculation, one retained positive endpoint term,
and whole-interval derivative comparisons. It requires no
angle or state mesh, numerical acceptance premise, Lean run
or CI result.
