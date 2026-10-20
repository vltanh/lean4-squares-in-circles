# Global radial and angle capture when the three zero sources are nonpositive

## 1. Exact scope and conclusions

Work on the original G0--G2 boundary cycle at
\(Q=9789/2500\), with its established E normalization
\(y_E\le0\). Assume only the three additional weak signs
\[
                         y_H,y_A,y_T\le0.             \tag{1}
\]
The original zero owners are then all 2 by the global
zero-owner sign theorem, and their targets G,B,D have
strictly negative tangents. Every quarter owner is high:
EH0/1 would force H positive, GA0/1 would force A positive,
and BT0/1 would force T positive; DE2/3 is already global.

Write the three original zero errors as
\[
                     v=d_{HG},\quad x=d_{AB},\quad w=d_{TD},
\]
and let p be the total positive variation of the entire
closed real-frame tour. Then
\[
 \boxed{\quad \frac{21}{200}<v,x,w<\frac{31}{100},
                  \qquad p<\frac{13}{25}.\quad}       \tag{2}
\]
Every one of the seven boundary states is outer. More
precisely, their unsigned coordinates satisfy
\[
\begin{array}{c|cc|c}
 \text{roles}&a&b&\text{outer marker chart}\\ \hline
 H,A,T&>67/50&<11/50&L\\
 G,B,D&<109/100&>69/100&H.
\end{array}                                           \tag{3}
\]
E is outer without a further chart restriction.

These are global implications of (1), not a complete
exclusion of this sign branch. No owner, radial kind,
frame order, mismatch or tangent cut is added to (1).

## 2. Each negative-to-negative zero edge has positive error

The universal geometric bounds are
\[
 a<\frac{283}{200},\qquad b<\frac9{10},\qquad |d|<\frac7{10}.
\]
For any of the three zero edges write its source tangent
as \(-b\), its target tangent as \(-B\), and its source
primary as a. Its actual owner-2 inequality is
\[
       a\sin d-b\cos d+B\ge W(d),
       \qquad W(d)=\frac{1+\cos d+|\sin d|}{2}.         \tag{4}
\]
If \(d\le0\), the left side is at most B<9/10, whereas
W>=1. Thus d>0. Subtracting the width in (4), dropping
the nonpositive term \(-b\cos d\), gives the strict upper
bound
\[
 P_2-W<\frac25-\frac12\cos d+\frac{183}{200}\sin d.
                                                               \tag{5}
\]
The right side increases on \([0,7/10]\). At
\(l=21/200\), the bounds \(\cos l\ge1-l^2/2\),
\(\sin l\le l\) make it at most
\[
 \frac25-\frac12(1-l^2/2)+\frac{183}{200}l
                  =-\frac{187}{160000}<0.             \tag{6}
\]
Therefore v,x,w>l.

## 3. The G1 error gain bounds the whole positive variation

Use the previously proved complete cycle bounds
\[
 \sum_i h(|d_i|)<\Delta:=\frac{10394}{25425},
 \qquad p=\sum_i(d_i)_+=\sum_i(-d_i)_+<\frac7{10},
 \qquad h(t)=\frac{\sin t+\cos t-1}{2}.                \tag{7}
\]
The last inequality is the global total-variation theorem,
not an assumption on the present sign branch.

On \([0,7/10]\), h is increasing and concave, with h(0)=0.
The three distinguished positive arguments exceed l.
For x,y>=l and x+y<=7/10, concavity gives
\[
                       h(x)+h(y)\ge h(l)+h(x+y-l).
\]
Apply this twice to the three distinguished arguments,
then merge every other positive argument using
subadditivity. Merge all negative arguments in the same
way. Their sums remain below 7/10 by (7). The result is
\[
             \sum_i h(|d_i|)
                \ge2h(l)+h(p-2l)+h(p).                \tag{8}
\]
Here p>=3l, so every argument is nonnegative.

The right side increases with p. At p=13/25, its last two
arguments are 31/100 and 13/25. Substituting the alternating
lower polynomials
\[
 S(t)=t-t^3/6+t^5/120-t^7/5040,
 \qquad C(t)=1-t^2/2+t^4/24-t^6/720
\]
in h gives the exact positive reserve
\[
 2\frac{S(l)+C(l)-1}{2}
 +\frac{S(31/100)+C(31/100)-1}{2}
 +\frac{S(13/25)+C(13/25)-1}{2}-\Delta
 =\frac{11191360232286351419}{7289856000000000000000}>0.
                                                               \tag{9}
\]
Consequently p<13/25. Since each distinguished positive
error leaves two others greater than l, each is less than
\(13/25-2l=31/100\). This proves (2).

## 4. Both endpoints of every distinguished zero are outer

First suppose a source in (4) is core. Then a<=7/12 and
the analogue of (5) is
\[
 P_2-W<\frac25-\frac12\cos d+\frac1{12}\sin d.
\]
This increases on the interval in (2). Its degree-two and
degree-one Taylor bound at d=31/100 is
\[
 \frac25-\frac12\{1-(31/100)^2/2\}
                    +\frac1{12}\frac{31}{100}
             =-\frac{6017}{120000}<0.                 \tag{10}
\]
Thus H,A,T are outer.

If a target is core, its transverse coordinate satisfies
\(B<14/25\). The source retains the universal primary
bound a<283/200. Hence
\[
 P_2-W<\frac3{50}-\frac12\cos d+\frac{183}{200}\sin d.
\]
The same whole-interval comparison gives
\[
 \frac3{50}-\frac12\{1-(31/100)^2/2\}
                    +\frac{183}{200}\frac{31}{100}
             =-\frac{5293}{40000}<0.                  \tag{11}
\]
Thus G,B,D are outer as well. Finally the already proved
reflected zero--quarter radial theorem applies to EH2/3
followed by HG: its source E is outer. No unproved
outer-circle substitution was used in (5)--(11).

## 5. Quantitative whole-chart capture

Rearrange (4), retain \(b\ge0\), and use the interval (2):
\[
\begin{aligned}
 B&\ge\frac12+\frac12\cos d-(a-\tfrac12)\sin d+b\cos d\\
  &>1-\frac14(31/100)^2-\frac{183}{200}\frac{31}{100}
   =\frac{27693}{40000}>\frac{69}{100}.                \tag{12}
\end{aligned}
\]
For the source coordinate, the same inequality gives
\[
 b\cos d<\frac25-\frac12\cos d+\frac{183}{200}\sin d.
\]
The lower bound \(\cos d>1-(31/100)^2/2\) and the
corresponding upper bound on the right side show b<11/50.
The exact cross-product reserve is
\[
 \frac{11}{50}\{1-(31/100)^2/2\}
 -\left[\frac25-\frac12\{1-(31/100)^2/2\}
                   +\frac{183}{200}\frac{31}{100}\right]
                  =\frac{877}{500000}>0.              \tag{13}
\]

All six endpoints are now known to be on their actual outer
circles. For H,A,T, b<11/50 therefore implies a>67/50;
for G,B,D, b>69/100 implies a<109/100. The respective
positive square reserves are
\[
 Q-(67/50+1/2)^2-(11/50+1/2)^2=\frac{29}{2500}>0,
\]
\[
 (109/100+1/2)^2+(69/100+1/2)^2-Q=\frac{143}{5000}>0.
                                                               \tag{14}
\]
Their ratios are consequently below 1/4 and above 3/7,
respectively. This proves all of (3), with strict chart
membership. E's chart remains unrestricted.

Every estimate above concerns the original witnesses and
the unchanged common G1 error budget. The proof consists
of concavity, monotonicity and the displayed rational
endpoint arithmetic; it uses no state mesh, angle table,
numerical feasibility result, Lean compilation or CI.
