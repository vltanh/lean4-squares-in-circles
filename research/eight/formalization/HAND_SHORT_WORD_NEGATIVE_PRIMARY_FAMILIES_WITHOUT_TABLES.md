# All short-word opposite primary owners below a quarter turn

Every outer/outer opposite-sign primary owner
\[
 (i,\sigma,\tau,j)\in
 \{(2,-,+,2),(2,-,+,4),(4,-,+,2),(4,-,+,4),
                         (6,-,+,2),(6,-,+,4)\}
\tag{1}
\]
of \(0010111\) satisfies
\[
 C_2>.8975,\qquad C_4>.89765,\qquad C_6>.89765
\tag{2}
\]
on its entire original negative angle half
\[
 \phi=\frac\pi2-u,\qquad 0\le u\le.7.
\]
All original weak separating inequalities and simultaneous owners are
included.

The true primary separator itself forces \(u<.226\). On that entire
feasible domain, one fixed multiplier per owner leaves only a circle
support and at most two elementary endpoint functions. There is no
table, sampled-angle estimate, or state subdivision in the proof.

Every terminating decimal is an exact rational.

## 1. Geometry forces the complete angle restriction

Put
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 d=\sqrt{Q/2}-\tfrac12,\quad
 \rho=\frac{1}{2(a_0+\tfrac12)}.
\]
The two states lie on the outer arcs
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad
 A=\sqrt{Q-(B+\tfrac12)^2}-\tfrac12,\qquad 0\le b,B\le d.
\tag{3}
\]
We use
\[
\begin{gathered}
 1.414575671<a_0<1.414575672,\qquad
 .899214065109<d<.899214065110,\qquad
 R<1.978788,\qquad \rho>.26115,\\
 k=\cos u>.764,\qquad 0\le s=\sin u<.645
                                     \quad(0\le u\le.7).
\end{gathered}
\tag{4}
\]
For an original axis 2, reflect and reverse the pair. This preserves
the angle and corrected cost and converts it to source axis 4 with
normalized signs \((-,+)\). An original axis 4 needs no conversion.
In all six cases the original weak separator is therefore
\[
 a-As-Bk\ge W,\qquad W=\frac{1+k+s}{2}.
\tag{5}
\]

The expression \(As+Bk\) is concave in \(B\), so its minimum is at
\(B=0\) or \(B=d\). The diagonal value is larger because
\[
 d(s+k)-a_0s
 =dk-(a_0-d)s
 >.899214065109(.764)
             -(1.414575672-.899214065109)(.645)>0.
\tag{6}
\]
Thus \(As+Bk\ge a_0s\). Since \(a\le a_0\), feasibility implies
\[
 a_0(1-\sin u)\ge \frac{1+\cos u+\sin u}{2}.
\tag{7}
\]
The difference of the two sides is strictly decreasing on \([0,.7]\):
its derivative is
\[
 -(a_0+\tfrac12)k+\tfrac12s<0.
\]
At \(u=.226\), the alternating series gives that difference less than
\(-.0017\). Hence
\[
 0\le u<.226.
\tag{8}
\]
In particular, throughout the full feasible domain,
\[
 k>.97456,\qquad 0\le s<.22409.
\tag{9}
\]
The discarded part of the original angle half is impossible by the
actual separator, rather than omitted from a scalar cover.

## 2. Exact normalized coefficients and source-circle support

The normalized cost is
\[
 C=\frac\pi2-u+c+pa-qb-PA-tB.
\tag{10}
\]
In the order (1), the exact tuples \((c,p,q,P,t;\lambda)\) are
\[
\begin{aligned}
 {\cal T}_{2,2}&=(.6618,-.51554,1.19909,-.09133,.88074;\ .93308),\\
 {\cal T}_{2,4}&=(.6618,.09133,.88074,.51554,1.19909;\ 1.1625),\\
 {\cal T}_{4,2}&=(-.25931,0,.86884,-.19335,.76744;\ 1.00982),\\
 {\cal T}_{4,4}&=(-.25931,.19335,.76744,0,.86884;\ 1.08532),\\
 {\cal T}_{6,2}&=(-.1866,0,.94766,-.18602,.80996;\ 1.10143),\\
 {\cal T}_{6,4}&=(-.1866,.18602,.80996,0,.94766;\ 1.12741).
\end{aligned}
\tag{11}
\]
The first five coordinates are the adjacent affine role-label
difference, with the exact reflection/reversal rule
\((p,q,P,t)\mapsto(-P,t,-p,q)\) for original axis 2.
The sixth is a fixed positive multiplier for (5).

Subtracting \(\lambda\) times the separator margin gives source
expression \((p-\lambda)a-qb\). The full-circle support is
\[
 S=\frac{\lambda+q-p}{2}
              -R\sqrt{(p-\lambda)^2+q^2}.
\tag{12}
\]
The remaining target expression is
\[
 (-P+\lambda s)A+(\lambda k-t)B.
\tag{13}
\]
Consequently
\[
 C\ge\frac\pi2-u+c+S+\lambda W+
            \min_{0\le B\le d}
            \{(-P+\lambda s)A+(\lambda k-t)B\}.
\tag{14}
\]

## 3. The five nonpositive-P tuples

For every tuple except \({\cal T}_{2,4}\), \(P\le0\).
The coefficient of \(A\) in (13) is therefore nonnegative, so (13)
is concave in \(B\). It is enough to retain both arc endpoints.
Define their corresponding lower functions
\[
\begin{aligned}
 A_-(u)&=\frac\pi2-u+c+S-Pa_0+\frac\lambda2+
                         \frac{\lambda k}{2}
                          +\lambda(\tfrac12+a_0)s,\\
 D_-(u)&=\frac\pi2-u+c+S-(P+t)d+\frac\lambda2+
                                      \lambda(\tfrac12+d)(s+k).
\end{aligned}
\tag{15}
\]
Then \(C\ge\min\{A_-(u),D_-(u)\}\).

The axial scalar is increasing throughout the feasible domain:
\[
\begin{split}
 A_-'&=-1-\lambda s/2+\lambda(\tfrac12+a_0)k\\
 &>-1+.93308\{1.914575671(.97456)-.22409/2\}>.63.
\end{split}
\tag{16}
\]
The diagonal scalar is concave:
\[
 D_-''=-\lambda(\tfrac12+d)(s+k)<0.
\tag{17}
\]
Hence its minimum on \([0,.226]\) is at an endpoint.

The fixed comparisons from (11)--(12) and (4) give
\[
\begin{array}{ll}
 A_-(0)>.89758,\quad D_-(0)>.89758,
                   &\text{for }{\cal T}_{2,2},\\
 A_-(0)>.89810,\quad D_-(0)>1.016,
                   &\text{for the four edge-4/6 tuples},\\
 D_-(.226)>.9309,
                   &\text{for all five tuples}.
\end{array}
\tag{18}
\]
These are values at fixed endpoints of functions already proved
monotone or concave. The explicit radical bounds in Section 5 give a
direct rational verification. Thus (2) holds for these five original
owners.

## 4. The positive-P tuple remains axial throughout

For \({\cal T}_{2,4}\), write
\[
 X=-P+\lambda s,\qquad Y=\lambda k-t.
\]
On the whole feasible interval, (9) gives
\[
 X<-.51554+1.1625(.22409)<0.
\tag{19}
\]
The source of the exact outer-arc axial criterion is
\[
 \frac{d}{dB}(XA+YB)
  =-X\frac{B+\tfrac12}{A+\tfrac12}+Y
  \ge -X\rho+Y.
\]
By (9), (19), and \(\rho>.26115\),
\[
\begin{split}
 Y-\rho X
 &=\lambda k-t+\rho(P-\lambda s)\\
 &>1.1625(.97456)-1.19909+
           .26115\{.51554-1.1625(.22409)\}\\
 &=\frac{70158109}{160000000000}>0.
\end{split}
\tag{20}
\]
Therefore the target support is axial everywhere on the feasible
angle interval. Its cost lower bound is exactly \(A_-\) in (15).
Equation (16) still applies, and its initial value satisfies
\[
 A_-(0)>.89766>.8975.
\tag{21}
\]
This completes the sixth original owner without any angle transition.

## 5. Explicit radical and endpoint arithmetic

For the six tuples in (11), the source norms in (12) have the following
strict rational upper bounds, in that order:
\[
\begin{gathered}
 1.880509701,\quad 1.386761738,\quad 1.332148407,\\
 1.176679496,\quad 1.452999491,\quad 1.241873719.
\end{gathered}
\tag{22}
\]
Each follows simply by squaring against the exact radicand
\((p-\lambda)^2+q^2\). With \(R<1.978788\), these give
\[
 S>
 (-2.397276,\ -1.768154,\ -1.696710,\
                         -1.498695,\ -1.850634,\ -1.581731).
\tag{23}
\]
Substitution into (15), using (4) and \(\pi/2>1.570795\),
proves the initial bounds (18), (21). For the right-end diagonal
values use the alternating series at the single point \(.226\).

For example the delicate \({\cal T}_{2,2}\) diagonal initial value is
bounded below by
\[
 1.570795+.6618-2.397276+.93308+
                  (.93308+.09133-.88074)(.899214065109)
 >.89758.
\tag{24}
\]
For \({\cal T}_{2,4}\), the axial comparison is already
\[
 1.570795+.6618-1.768154+1.1625
                        -.51554(1.414575672)>.89766.
\tag{25}
\]

The original angle domain was fully accounted for in Section 1.
On the feasible remainder, the original weak owner itself supplied
every lower bound. All six original negative-half primary owners are
therefore covered, including the angle endpoint \(u=0\), state-arc
endpoints, and simultaneous separating owners.

