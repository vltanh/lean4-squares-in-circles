# AB aligns before the G and T transverse signs are fixed

## 1. Scope and the additional cap

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad q_L\le q\le Q.
\tag{1}
\]
Retain the sorted own-frame circles, true core, real frame spread
at most `7/10`, and the ordered frames
\[
 \theta_D\le\theta_A,\theta_B\le\theta_H,
 \qquad \theta_D\le\theta_E\le\theta_H.
\tag{2}
\]
H,A have positive signed tangents and B,D have negative signed
tangents; their nonnegative magnitudes are b_H,b_A,b_B,b_D.
The G and T transverse signs are arbitrary. Retain owners
\[
\begin{array}{c|rrrrrrr}
 \text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
 \text{axis}&0\text{ or }2&0&0\text{ or }2&2&0\text{ or }2&3&1.
\end{array}
\tag{3}
\]
For an original G0--G2 candidate, the global zero-owner sign
theorem says that HG2 forces the normal negative G sign and
TD0 forces the normal positive T sign. We use these already
proved restrictions. Thus the only additional cases beyond
`HAND_G5_AB_ALIGNMENT_WITH_ALL_ORDERED_OUTER_ERRORS.md` are
\[
               HG0\text{ with }y_G>0,
       \qquad TD2\text{ with }y_T<0.
\tag{4}
\]
A zero transverse coordinate is included in the normal case.
For a necessary system considered apart from an original
G0--G2 candidate, the two owner/sign restrictions just stated
are explicit hypotheses.

**AB alignment with arbitrary intermediate signs.** The AB
conclusion of that note remains valid under (1)--(4): there
is a common A/B frame in `[theta_D,theta_H]`, at the same q,
with `b_A+b_B=1`. H,D,E are unchanged. Each normal outer side
has precisely its previously proved comparison; each wrong-sign
side retains a concrete same-circle intermediate of that sign.
All changed middle points are sorted and satisfy the true core.
Earlier separate A/B circle losses survive; a nonzero original
AB difference creates a strict middle-circle loss.

The proof below supplies the missing wrong-sign cap and both
AB comparisons. It does not assume AB alignment in deriving
that cap or its estimates.

## 2. Exact wrong-sign elimination

Consider the H side of (4). Normalize A's frame to zero and put
\[
 \theta_H=\Theta\ge0,\qquad
 \theta_G=\Theta+h,\qquad z=\Theta+h.
\]
Write the actual wrong signed transverse coordinate as y>=0.
HG0 and GA0 are exactly
\[
\begin{aligned}
 b_H+a_G\sin h-y\cos h&\ge W(h),\\
 y+a_A\cos z-b_A\sin z&\ge W(z),
 \qquad W(r)=\tfrac12(1+\cos r+\sin r)
 \quad(r\ge0).
\end{aligned}
\tag{5}
\]
Necessarily h>0. If h<=0 the first left side is at most
b_H<.9, whereas its signed width is at least one. Also
\[
                              h>1/10.
\tag{6}
\]
Indeed `a_G<=sqrt(q-1/4)-1/2` gives
\[
 b_H\ge\tfrac12+\tfrac12\cos h
                 -(\sqrt{q-1/4}-1)\sin h.
\]
For `h<=1/10`, the right side is greater than
`1/2+199/400-183/2000=453/500>.9`, a contradiction.
The order and spread consequently give
\[
                        1/10<h\le z\le7/10.
\tag{7}
\]

Put c=cos h, s=sin h, and define
\[
 M=b_H-\tfrac12-s,\qquad
 Y_{\max}=Mc+s\sqrt{q-M^2},\qquad D=1-Y_{\max}.
\tag{8}
\]
With `X_G=a_G+1/2,Y_G=y+1/2`, HG0 says
\[
                 cY_G-sX_G\le M.
\tag{9}
\]
The function `cY-s sqrt(q-Y^2)` is strictly increasing.
Its inverse in (9) is the value Y_max in (8). It follows that
`Y_G<=Y_max`. The GA0 inequality therefore gives the constant
cap
\[
 (X_A-1)\cos z-Z_A\sin z\ge D,
 \qquad X_A=a_A+\tfrac12,\quad Z_A=b_A+\tfrac12.
\tag{10}
\]
Feasibility gives Y_max>=1/2, so D<=1/2. Throughout the
larger algebraic domain `0<=h<=.7`,
\[
\begin{gathered}
 -23/20\le M<2/5,\qquad \sqrt{q-M^2}>8/5,\\
 Y_{\max}<\tfrac25+\tfrac{13}{20}
                     (\tfrac{99}{50}-\tfrac34)
             =\frac{2399}{2000}<\frac65.
\end{gathered}
\tag{11}
\]
Here `cos h>=3/4`, `sin h<=13/20`, and `sqrt(q)<99/50`.
In particular `-1/5<D<=1/2` and all roots in (8) are real.

Conversely, (10) has the concrete realization
\[
 y'=Y_{\max}-\tfrac12,\qquad
 a_G'=\sqrt{q-Y_{\max}^2}-\tfrac12.
\tag{12}
\]
The HG0 inequality is an equality and GA0 is exactly (10).
This G is on its actual q-circle. Equation (11) and
`q_L-(6/5)^2>(3/2)^2` give `a_G'>1>y'`; hence it is
sorted and satisfies the true core. If the original y is
strictly positive, Y_max>1/2 and y' is strictly positive.

Reflection gives the identical cap and realization for a
wrong-sign T. Only that local outer path is reflected; E
and its two actual mixed inequalities are unchanged.

## 3. Correlation of the cap with its hard-quarter angle

For fixed b_H and q, differentiate (8), now as a function
of h. If `w_G=sqrt(q-M^2)`, then
\[
 Y_{\max}'=(w_G-c)\left(c-\frac{Ms}{w_G}\right)>0.
\tag{13}
\]
The first factor exceeds 3/5, and the second exceeds
`3/4-(2/5)(13/20)/(8/5)=47/80`. Thus D decreases with h.

For any hard angle z>=h, abbreviate c=cos z,s=sin z and
put C=D+cos z. Monotonicity and (8) give
\[
 C\ge D(z)+\cos z
 >1+\frac35c+sc-\sqrt q\,s
 \ge C_0(s,c):=1+\frac35c+sc-\frac{99}{50}s.
\tag{14}
\]
The following bounds will be used without replacing the
actual q in any cap circle:
\[
 C_0\ge\frac{1301}{2000}>0,\qquad
 C\le\frac32,\qquad \sqrt{q-C^2}>\frac{129}{100}.
\tag{15}
\]
The first bound uses `c>=3/4,s<=13/20`; the others follow
from D<=1/2 and positive squaring at q_L.

Every actual middle point satisfying (10) has
\[
\begin{aligned}
 X_A&\ge\frac{C+s/2}{c}
 >\frac35+s+\frac{1-(37/25)s}{c}\\
 &\ge\frac85-\frac{12}{25}s\ge\frac{161}{125}.
\end{aligned}
\tag{16}
\]
In the second line `1-(37/25)s>0` and c<=1 were used.
Thus `a_A>197/250>7/12`, so subsequent tangent lowering
preserves the true core.

Define the cap frontier at the actual q by
\[
 w=\sqrt{q-C^2},\quad
 X=cC+sw,\quad L(z,D)=cw-sC.
\tag{17}
\]
It satisfies `X^2+L^2=q` and (10) as an equality. The
frontier is strictly sorted whenever it is feasible. Indeed,
\[
 C_0-\frac75(c-s)
       =1-\frac45c+s(c-\tfrac{29}{50})>\frac15,
\tag{18}
\]
and `sqrt(q/2)<7/5`, `c>s`. Consequently
`C>sqrt(q/2)(c-s)`, exactly the condition X>L.
Reducing a required transverse corner below L increases
its q-circle primary and retains strict sorting.

## 4. Moving the middle frame toward its outer anchor

For a fixed wrong-sign D, direct differentiation of (17) gives
\[
 -L_z=J_q(C):=(cC+sw)\left(1-\frac{s}{w}\right).
\tag{19}
\]
We prove, on the whole feasible domain in (7),
\[
                         -L_z>11/10\quad(L\ge1/2).
\tag{20}
\]
At fixed z, J is concave in C and increases with q:
\[
 J_{CC}=-\frac{s q}{w^3}-\frac{3csqC}{w^5}\le0,
 \qquad J_q=\frac{s}{2w}+\frac{csC}{2w^3}\ge0.
\tag{21}
\]
The feasible interval is
\[
 C_0\le C\le C_{\max}:=c\sqrt{q-1/4}-s/2.
\tag{22}
\]
It suffices to bound J at these two endpoints.

At C_max put `X=sqrt(q-1/4)>19/10`. Then
\[
 J_q(C_{\max})
 =X\frac{1/2+(X-1)\tan z}{1/2+X\tan z}
 >\frac98+\frac{51}{6440}>\frac{11}{10}.
\tag{23}
\]
The fraction increases with X and decreases with tan z;
the displayed bound substitutes `X=19/10,tan z=13/15`.

At C_0 use q=q_L by (21), and put
\[
 N=q_L-C_0^2-cC_0,\qquad
 V_0=cC_0-s^2-11/10.
\]
The exact identity to prove is
\[
                     J_{q_L}(C_0)-11/10
                         =V_0+\frac{sN}{\sqrt{q_L-C_0^2}}>0.
\tag{24}
\]
For `0<=s<=3/10`, using `c>=1-(4/7)s^2` yields
\[
 V_0\ge v(s):=\frac12-\frac{49}{50}s
                       -\frac{76}{35}s^2+\frac{23}{175}s^3.
\tag{25}
\]
The cubic decreases on this interval and
`v(3/10)=353/25000>0`. Also
`C_0<=8/5-(49/50)s` and `sqrt(q_L-C_0^2)>1`.
On `1/10<=s<=3/10`, this gives
`N>=q_L-(751/500)^2-751/500>0`.
On `0<=s<=1/10`, it gives `N>=-1223/5000`, so (24)
is at least `v(1/10)-1223/50000>0`. This proves (24)
throughout the small-s range.

For `3/10<=s<=13/20`, one has
`C_0<=653/500` and
`N>=q_L-(653/500)^2-653/500>0`. If V_0>=0, (24)
already follows. Otherwise it is enough, by positive squaring,
to prove
\[
 P(s,c):=s^2N^2-(q_L-C_0^2)(11/10+s^2-cC_0)^2>0.
\tag{26}
\]
Using only `c^2=1-s^2`, write P=A(s)+B(s)c. The coefficients
in ascending powers of s are
\[
\begin{aligned}
 A={}&(-17577/4000,\ 898549/62500,\ 9018379/1000000,\\
 &-3772139/62500,\ 21053273/500000,\ 63607/3125,\\
 &-26607/1000,\ 1/5,\ 1),\\
 B={}&(20277/5000,\ -3458123/250000,\ -289107/125000,\\
 &1536861/31250,\ -5483073/125000,\ -703/250,\ 198/25).
\end{aligned}
\tag{27}
\]
Put
\[
 C_{10}(s)=1-\frac{s^2}{2}-\frac{s^4}{8}-\frac{s^6}{16}
                  -\frac{5s^8}{128}-\frac{7s^{10}}{256}.
\]
The binomial series, whose remaining positive coefficient
magnitudes decrease, gives
\[
 C_{10}-\frac{s^{12}}{25}\le\sqrt{1-s^2}\le C_{10}.
\tag{28}
\]
Indeed its first omitted coefficient is 21/1024 and its
geometric tail coefficient is at most
`(21/1024)/(1-(13/20)^2)=25/704<1/25`.

For a polynomial f expanded as `sum f_j(s-l)^j`, define
\[
 U_{l,h}(f)=f_0+\sum_{j\ge1}\max(f_j,0)(h-l)^j.
\]
Direct rational coefficient summation in (27) gives
\[
 U_{3/10,13/20}(B)
       =\frac{1202238667}{400000000}<\frac{31}{10}.
\tag{29}
\]
Thus (28), for either sign of B, gives
\[
             P\ge p(s):=A+B C_{10}-\frac{31}{250}s^{12}.
\tag{30}
\]
For completeness, the single whole-interval polynomial
comparison needed here is as follows. If
`f(s)=sum f_j(s-m)^j`, set
\[
 \mathcal U_{m,r}(f)=f_0+
       \sum_{j\text{ odd}}|f_j|r^j+
       \sum_{j\ge2\text{ even}}\max(f_j,0)r^j.
\]
For the degree-16 polynomial explicitly defined by (27),(30),
exact rational coefficient sums give
\[
\begin{array}{c|c}
 \text{quantity}&\text{bound}\\ \hline
 \mathcal U_{19/40,7/40}(p''')&<-44\\
 p''(3/10)&<-1\\
 p(3/10)&>1/10\\
 p(13/20)&>1/10.
\end{array}
\tag{31}
\]
These displayed finite sums are evaluations of the stated
polynomial, not additional geometric hypotheses. They show
that p'' decreases and is negative on the whole interval;
concavity therefore places its minimum at an endpoint.
Hence p>1/10, proving (26), (24), and (20).

## 5. Moving away from the opposite outer anchor

The other AB direction uses
\[
 g_v(C)=\cos v\sqrt{q-C^2}-\sin v\,C.
\]
For the wrong-sign side let its original hard angle be u,
and its new angle be v=u+Delta. Then
\[
 1/10<u<v\le7/10,\qquad
 D+\cos v\le C\le D+\cos u.
\tag{32}
\]
Use the sharper, radius-dependent bound in (14) at v,
`C>1+(3/5)c+sc-Rs`, where c=cos v,s=sin v,R=sqrt q.
Then
\[
\begin{aligned}
 R(-g_v')&\ge cC+Rs\\
 &\ge c+\tfrac35c^2+sc^2+Rs(1-c)\\
 &\ge\tfrac85+s-\tfrac{41}{35}s^2-\tfrac3{200}s^3
 >\tfrac85.
\end{aligned}
\tag{33}
\]
Here `c>=1-(4/7)s^2`, `1-c>=s^2/2`, `R>197/100`,
and the bracket `1-(41/35)s-(3/200)s^2` is positive up to
13/20. Thus `-g_v'>80/99>4/5`.

The correlation u>1/10 supplies the additional angular gain.
Put r=Delta/2<3/10. The inequalities
`cot r>191/60`, `sin u>.9u`, `cos u>=1-u^2/2` give
\[
 \frac{\cos u-\cos v}{1-\cos\Delta}
 =\cos u+\sin u\cot r
 >1+u(573/200-u/2)
 >1+503/2000>5/4.
\tag{34}
\]
Integrating (33) over (32) therefore gives the strict gain
\[
 g_v(D+\cos v)-g_v(D+\cos u)>1-\cos\Delta.
\tag{35}
\]
This is precisely the rotated-cap comparison needed for AB.

## 6. Complete AB comparison and strictness

For a normal-sign outer side, retain its local cap and any
crossed-frame restoration from Sections 2--4 of
`HAND_G5_AB_ALIGNMENT_WITH_ALL_ORDERED_OUTER_ERRORS.md`.
Those local arguments do not use the opposite intermediate's
sign. For a wrong-sign side use (8)--(12). Its comparison
frame lies strictly outside H or D, so a middle frame moving
between D and H cannot cross that comparison frame. Thus
the correlation h<=z needed above holds throughout the move.

For AB axis 0 put d=theta_B-theta_A. Its exact inequality is
\[
 Z_A+X_B\sin d+Z_B\cos d
                 \ge1+\cos d+(\sin d)_+.
\tag{36}
\]
If d>0, move A to B's frame. A normal cap gains more than
`(9/8)d`; a wrong-sign cap gains more than `(11/10)d` by
(20). The unchanged B circle contributes the same bound
as in the earlier AB proof,
\[
 (X_B-1)\sin d+(Z_B-1)(\cos d-1)
                  <.915d+d^2/4\le1.09d.
\tag{37}
\]
Thus the new A cap plus Z_B exceeds two, with reserve
greater than d/100 even in the new wrong-sign case.

If d<0, move B to A's frame. This goes away from its
comparison T frame. The usual rotated-circle bound is
\[
 X_B\sin d+Z_B\cos d\le g_v(D_D+\cos u).
\]
For a normal T cap the earlier comparison applies. For a
wrong-sign T cap, (35) applies with Delta=-d. In either
case (36) gives `Z_A+L(v,D_D)>2`.

In both cases keep the unmoved middle point, choose the
other tangent to make their sum one, and put its primary
strictly below but sufficiently close to its actual q-circle.
The strict cap gain absorbs this decrease and gives a strict
circle loss. Sorting and the true core follow from (16),(18)
on a wrong-sign side and from the old cap proof on a normal
side. Realize a changed wrong-sign intermediate by (12).
Apply the same local argument with the roles reversed for
AB axis 2; it leaves E untouched.

If d=0, retain both middle coordinates initially. If their
tangent sum is greater than one, lower one tangent to make
it one. Each tangent is less than .9, so the new one is
positive. Every retained hard cap has a nonpositive tangent
coefficient, and (16) or the old cap bound preserves the
primary core condition. This normalization improves its
circle and cap.

An earlier strict loss at an unmoved middle point is retained.
If that point moves, the strict AB comparison recreates a
strict loss. If d=0, no primary lift is required. Thus the
two losses are retained separately exactly as in the earlier
AB theorem. This proves the stated extension, including
the possibility that both intermediate signs are wrong.

Every estimate above is continuous on its stated domain.
The only polynomial comparison uses the explicit formulas
(27)--(31) on one whole interval. No angle mesh, sampled
minimum, state cover, numerical acceptance premise, Lean
compilation or CI is used.
