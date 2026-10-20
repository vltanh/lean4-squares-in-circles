# Negative A total with positive BT3 and arbitrary TD0

## 1. Scope and theorem

Put
\[
 Q=9789/2500,\qquad R=\sqrt Q,\qquad h=7/10.
\]
Retain the high-GA G0--G2 necessary boundary cycle with cyclic
roles H,G,A,B,T,D,E. The states H,G,B,D are sorted outer states
with signed tangents respectively positive, negative, negative,
negative; E is nonpositive and may be outer or true core. Use
the actual weak neighboring witnesses
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=3,\quad TD=0,\quad DE\in\{2,3\},\quad EH\in\{0,1\}.
 \tag{1}
\]
The selected signed A-primary total is negative, the selected
signed E-primary total is nonnegative, and the actual BT3
error is nonnegative. TD0 has arbitrary error. Retain
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.                 \tag{2}
\]
No ordering of the real frames is assumed.

**Theorem.** No such necessary cycle exists. The conclusion
holds for either radial kind of E and for both signs and
radial kinds of T, including all weak owner and angle ties.

The A-only reductions in
[the actual negative-A entry theorem](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md)
and
[the mixed negative-A transport](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md)
are independent of the retained BT owner. They use only the
two A witnesses and the actual G,A,B states, and change no
T or E inequality. Their paths and endpoints are eligible by
[the boundary-neighbor transport bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
They reduce the claimed scope either to an already excluded
nonnegative A total, or to one genuine negative A primary
with the other A edge secondary. The remaining possibilities
are exactly
\[
 \begin{array}{c|c|c|c}
  &\text{negative primary}&\text{other owner}&\text{actual data}\\\hline
  \mathrm{GA}&GA3\text{ at }-s&AB0&a_A=7/12,\ 0<y_A<39/250,\ s<1/4\\
  \mathrm{AB}&AB2\text{ at }-s&GA2&a_A=7/12,\ 0<y_A<1/2,\ s<19/50.
 \end{array}                                                   \tag{3}
\]
If a negative primary can instead be reselected secondary at
the same state, make that actual reselection first. A remaining
nonnegative selected total is covered by
[the nonnegative-A/E positive-BT theorem](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
After a transport, reapply the local entry theorem to obtain
the bounds (3); no original-marker bound is transferred without
that argument.

Write \(z=d_{BT}\ge0\), and let e be the selected signed
E-primary total. This note proves all \(e\ge0\). Sections 2--8
first prove the algebraic secondary-E reference case \(e=0\).
Sections 9--12 transfer the result to every nonnegative e.
All decimals below are exact rational numbers.

## 2. Exact positive weights and secant cancellation

Use
\[
 \eta=.293,\quad K=13/12,\quad
 c_0=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2,
\]
\[
 \sigma=R\sqrt{1+\eta^2}-(1+\eta)/2,\qquad
 f(z)=\cos z+\eta\sin z,\qquad
 W(t)=\frac{1+\cos t+|\sin t|}{2}.
\]
Choose positive k,l,m, put \(c=mf(z)\), and put \(p=l\sec s\).
Give the seven actual inequalities weights
\[
 (k,\lambda_G,\lambda_B,m,c,1,1),\qquad
 (\lambda_G,\lambda_B)=
 \begin{cases}(p,l),&\mathrm{GA},\\(l,p),&\mathrm{AB}.
 \end{cases}                                                   \tag{4}
\]
For GA3 and AB2, respectively, their actual projections give
\[
 p\{a_G-a_A\sin s-y_A\cos s\}
       =pa_G-ly_A-\frac7{12}l\tan s,
\]
\[
 p\{-a_A\sin s+y_A\cos s+b_B\}
       =ly_A+pb_B-\frac7{12}l\tan s.                           \tag{5}
\]
Thus the A tangent cancels with its other incident witness.
The actual T force is
\[
 m\{a_T\sin z-y_T\cos z\}+cy_T
       =m\sin z(a_T+\eta y_T)\le m\sigma\sin z.                \tag{6}
\]
This uses its actual corner
\((a_T+1/2,|y_T|+1/2)\) in the radius-R disk. It holds for
either sign and radial kind of T.

Write S for the sorted outer support and \(\overline S\) for
the complete-circle support:
\[
 S(f,g)=\max_{0\le b\le c_0}
 \{f(\sqrt{Q-(b+1/2)^2}-1/2)+gb\},
 \qquad \overline S(f,g)=R\sqrt{f^2+g^2}-(f+g)/2.
 \tag{7}
\]
The secondary-E reference baseline is
\[
 \begin{split}
 B_O(s,z)={}&k+\lambda_G+\lambda_B+mW(z)+c+2-m\sigma\sin z\\
 &-\overline S(1,k)-\overline S(\lambda_G,k)
       -\overline S(\lambda_B,m)-S(1,c)\\
 &+p\{W(s)-1\}+\frac7{12}l\tan s,
                 \qquad O\in\{\mathrm{GA},\mathrm{AB}\}.
 \end{split}                                                   \tag{8}
\]
At s=0 both baselines agree; call this \(B_0(z)\).
On the low interval below, \(S(1,c)=(1+c)c_0\). On the high
interval, \(c<1\), and (7) is equal to full-circle support
at (1,c): its coefficient ratio is greater than .8, so the
unconstrained optimizer lies on the sorted arc.

For all derivatives in s, put \(x=\tan s\), \(w=\sec s\).
After collecting the corner half-shifts, the entire variable
part of (8) is
\[
 F_0(s)=l\{w+Kx-R\sqrt{w^2+r^2}\},\qquad
 r=k/l\ (\mathrm{GA}),\quad r=m/l\ (\mathrm{AB}).             \tag{9}
\]
In particular
\[
 \frac{F_{0,xx}}l=(1+x^2)^{-3/2}
        -R(1+r^2)(1+r^2+x^2)^{-3/2},
\]
\[
 \frac{F_{0,s}}{l\sec^2s}
   =K+\sin s\left(1-\frac R{\sqrt{1+r^2\cos^2s}}\right).
 \tag{10}
\]
These identities are the same as in
[the negative-A angle-concentration proof](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md).
The positive-BT identity (6) changes the four fixed outer
coefficients, but not a derivative in (9)--(10).

## 3. A wider two-angle sorted-D minorant

For \(0<p\le q\), define
\[
 N_{p,q}(t)=\sqrt{p^2+q^2+2pq\sin t},
\]
\[
 U_{p,q}(t)=p\{\cos t+\sin t-1\}
             -R\{N_{p,q}(t)-N_{p,q}(0)\},
\]
\[
 V_{p,q}(t)=q(\cos t-1)
             -R\{N_{p,q}(-t)-N_{p,q}(0)\}.                   \tag{11}
\]
Put \(k_*=.68\), \(\alpha=.67\), \(C_*=1.2\), and
\[
 D_c(u,v)=c\{W(u)-1\}+W(v)-1+(1+c)c_0
                 -S(c\sin u+\cos v,c\cos u+\sin v).
\]
For \(1\le c\le C_*\), on the whole signed domain
\[
 P=(u)_++(v)_+\le h,\qquad N=(-u)_++(-v)_+\le h,
\]
we have
\[
                  D_c(u,v)\ge-\alpha P+V_{k_*,1}(N).          \tag{12}
\]

Here are the complete changes to the proof of Sections 2--5
of
[the two-angle sorted-D envelope](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md).
Its diagonal derivative bounds become
\[
 \alpha-.4C_*=.19>0,\qquad
 1.327-V_{k_*,1}'(0)>1.327-1.113>0,
\]
where \(1.113^2(1+k_*^2)>Qk_*^2\). Its interior concavity is
unchanged, because adding \(\alpha P\) is linear. The axis
derivative is at most \(\alpha-.914c<0\). The one-angle
boundary comparison \(D_c(0,-n)\ge V_{k_*,1}(n)\) uses the
same general lemma, whose hypotheses \(1/2\le k_*\le17/20\)
and \(k_*\le c\le2\) still hold.

For completeness, positivity of both force coefficients on
the entire signed rectangle is unnecessary and is not asserted
at C_*=1.2. In the quadrant \(u=-n,v=t\ge0\), one has
\(g>0\) and \(f-g=\phi'(t)-c\phi(n)\le0\), so the support
is diagonal even if f is negative. In all other quadrants f,g
are positive. For two negative angles their magnitudes have
sum at most h: each force is a positive sine interpolation
of its endpoint values, which are bounded below by
\(\cos h\) and \(1-C_*\sin h>.226\), or by
\(C_*\cos h\) and \(1-\sin h>.355\). The original ratio
and transition arguments therefore apply on every branch
where they are used.

Only the two endpoint inequalities
\[
 D_c(h,-n)+\alpha h-V_{k_*,1}(n)>0,
       \qquad 0\le n\le h,\quad c=1,C_*,                     \tag{13}
\]
remain to be certified. The following explicit replacements
in
[the sorted-D endpoint proof](HAND_G3_POSITIVE_BT3_SORTED_D_ENDPOINT_CERTIFICATES.md)
do that independently. Use
\[
 \underline c=.8992140,\quad\overline a=1.414575672,
 \quad T_0=2.392942424,
 \quad\Phi_-=C_{10}(h)+S_{11}(h),
\]
where \(T_0^2>Q(1+k_*^2)\). Define
\[
 A_c=c\Phi_-+1+(c+1)(\underline c-1/2)+\alpha h-T_0,
\]
\[
 P_c(n)=1+c^2+2cS_9(h-n),\quad H(n)=1+k_*^2-2k_*S_9(n),
\]
\[
 Z_c(n)=4A_c^2QH(n)-\{Q(P_c(n)-H(n))-A_c^2\}^2.             \tag{14}
\]
The coefficient bounds defined in Section 7 give
\[
 Z_{1.2}>.970\quad[0,h],\qquad
 Z_1'<-7.85\quad[0,3/8],\qquad Z_1(3/8)>.787.                \tag{15}
\]
For \(c=1,n\ge3/8\), the same axis support comparison has
reserve greater than .0242 and gives \(S(f,g)=a_0f\). Put
\[
 A(n)=\frac{\Phi_--1}{2}-\overline aS_9(h)
       +2\underline c+\alpha h+\frac12-T_0
       -(\overline a+1/2)C_{12}(n)+\frac12S_{11}(n).
\]
For \(Y(n)=QH(n)-A(n)^2\), write
\(Y(3/8+3/40+t)=\sum y_jt^j\). On \(|t|\le1/4\),
\[
 q=y_2-\sum_{j\ge3}|y_j|(1/4)^{j-2}>1.772,
          \qquad y_0-y_1^2/(4q)>.0279.                        \tag{16}
\]
Thus Y>0. Positive squaring proves (13) from (14)--(16),
exactly as in that endpoint proof. Concavity in c of the
actual sorted support residual extends (13) to \([1,1.2]\).
The four quadrant reductions then prove (12), including all
support-transition and zero-angle ties.

## 4. Two continuous coefficient families

For \(0\le z\le1/4\), choose
\[
 k=\frac23+\frac z{20},\qquad
 l=1.066-.16z,\qquad
 m=1.18+.1z-3.845z^2.                                       \tag{17}
\]
For \(1/4\le z\le h\), put \(t=z-.2\), \(r=z-.25\), and choose
\[
 k=.676+.2t+.9t^2-1.3t^3,\qquad
 l=1.025+.22t-.3t^2,\qquad
 m=.96-.7r+1.2r^2.                                         \tag{18}
\]
In either family \(c=m(\cos z+\eta\sin z)\).

The low family satisfies
\[
 \frac23\le k\le\frac{163}{240},\quad
 1.026\le l\le1.066,\quad .964<m<1.181,
\]
\[
 .55<k/l<2/3,\qquad .94<m/l<1.13,
 \qquad 1<c<1.2,\qquad m>k.                                \tag{19}
\]
For example \(m-.94l\) is concave and positive at both
endpoints, and \(1.13l-m=.02458-.2808z+3.845z^2\) is
positive by completing its square. The lower polynomial
\(m(C_{10}(z)+\eta S_{11}(z))\) has coefficient lower bound
1.0045. The upper polynomial \(C=m(C_{12}(z)+\eta S_9(z))\)
has \(C''<-8.80\), \(C(0)=1.18\), \(C'(0)=.44574\), so
\[
             C\le1.18+.44574^2/17.6<1.192<1.2.
\]
These are whole-interval coefficient bounds. Every ordinary
larger coefficient is less than 5/4, including either actual
secant in (3). H and B have larger-to-smaller ratio at most
1.5; G has ratio less than 5/3.

For the high family,
\[
 .6880875\le k\le.8385,\qquad
 1.03525\le l\le799/750,\qquad .8579<m\le.96,
\]
\[
 .659<k/l<.82,\quad .8<m/l<1.032,\quad m<l,
 \qquad k<c<1,
 \qquad m<.92l\quad(z\ge1/3).                              \tag{20}
\]
The extrema of k,l,m follow from their derivatives or one
quadratic completion. The difference \(k-.659l\) increases
on \(.05\le t\le.5\) and is positive at the left endpoint.
The lower polynomial for c has lower bound .8068; its
difference from k has derivative less than −.122 and right
endpoint greater than .00829. The upper polynomial for c
has second derivative greater than 1.11 and endpoint values
less than .999746 and .846796; convexity gives c<1. These
coefficient bounds use (17)--(18) directly. The restricted
bound \(m<.92l\) follows from \(m\le.91\) for \(r\ge1/12\).

For the full actual s-ranges, the high ordinary pairs,
including D, consequently satisfy
\[
 \begin{array}{c|ccc}
  &p_i/q_i&q_{\max}&q_{\min}\\\hline
  \mathrm{GA}&>.6375&<1.1&1\\
  \mathrm{AB}&>.65&<1.15&1.
 \end{array}                                                   \tag{21}
\]
For the only narrow comparison use
\(.659\cos(.25)>.659(.9689)>.6375\).
Every l in both families is greater than 1.023; this will
also be used in Section 9.

## 5. Whole-angle concentration for the reference case

The ordinary pairs are
\[
 H=(k,1),\quad G=(k,\lambda_G),\quad
 B=(\min(\lambda_B,m),\max(\lambda_B,m)),\quad D=(1,c).
 \tag{22}
\]
After deleting only the arguments −s,z from the algebraic
angular vector, its variations obey
\[
 P\le h-z,\quad N\le h-s,\quad N-P=z-s.                      \tag{23}
\]
On the low family use (12), and then
\(V_{.68,1}\ge V_{k,1}\), since k≤163/240<.68. The latter
coordinate monotonicity is proved in the sorted-D envelope.
Thus D has minorants −.67P and \(V_H(N)\). On the high
family use the full two-angle D block; its negative increment
dominates \(V_H\) because \(k<c<1\).

The separate concavity and variation concentration in Sections
3--6 of
[the negative-A angle proof](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
now leave the same intrinsic alternatives: pure U or V, a
same-block term, or a separated positive and negative term.
In the low case the two D minorants already form a separated
term. Virtual zero arguments enlarge only this scalar domain;
they are not declarations of new physical witnesses.

Here are all changed analytic bounds needed to specialize that
proof to (17)--(18). Its identities (9)--(11), norm derivative
lemmas, and same-block comparisons apply unchanged.

**Pure positive terms.** Every \(B_O(s,z)+U_i(s-z)\) increases
for s≥z in the actual cut. The unaffected GA slope is greater
than .897l, and its ordinary negative derivative costs at most
\(.6(1.42)l\). The unaffected AB slope is greater than .86l,
and its cost is at most .6l. The new D cost .67 is smaller
than both available absolute slopes. For the affected GA
pair use exactly equations (32)--(34) of the cited proof,
since \(.55<k/l<.85\). For affected AB, if \(l\sec s<m\)
the derivative is at least \(l(K+1-R)>0\); otherwise
\(.8<m/l\le\sec(.38)<1.08\), so its same positive-square
comparison (35)--(36) applies. Thus all pure positive terms
reduce to s=z.

**Low pure negative terms.** On \(0\le s\le z\le1/4\),
\(V_B\ge V_H\): the universal chord bound gives
\(V_B(t)\ge(87/70)(.964)t>1.186t\ge V_H(t)\).
For G, keep k fixed and increase its larger coefficient q
from 1. If \(u=\sin t\le1/4\) and \(q/k\le5/3\), the
coordinate derivative used in that proof has
\[
 \frac{k^2(k-qu)}{(k^2+q^2-2kqu)^{3/2}}
       \ge\frac{63}{136\sqrt{34}}.
\]
Consequently
\[
 \partial_q V_{k,q}(t)
 \ge t\left\{\frac{63R}{136\sqrt{34}}\frac{95}{96}-\frac18\right\}>0;
\]
even replacing R by 1.97 and \(\sqrt{34}\) by 6 leaves
a reserve greater than .0255. Thus \(V_G\ge V_H\) as well.

For the basic ratio \(r\le1.13\), (10) gives
\(F_{0,xx}/l<-.31\) on \(x\le.256\). At x=0 this follows
by squaring after maximizing the expression over r. That
maximization is valid because, with \(A=1+r^2\),
\[
 \frac{d}{dA}\frac{A}{(A+x^2)^{3/2}}
       =\frac{x^2-A/2}{(A+x^2)^{5/2}}<0;
\]
thus (10) increases with r throughout this domain. The upper
envelope obtained at r=1.13 decreases through .256, by
\[
 (1+1.13^2+.256^2)^5
     >Q(1+1.13^2)^2(1+.256^2)^5.
\]
The norm derivative bounds of the cited proof give
\[
 \frac{d^2}{dx^2}V_H(z-s)
 \le-\frac{31}{32}+.569+.512(1.186+.25(.569))<.281.
\]
Hence \(B_O+V_H(z-s)\) is strictly concave in x, with
curvature less than \(-.31(1.026)+.281<-.037\). It reduces
to s=0 or s=z.

**Low saturation.** The same-block comparisons immediately
remove H and B. For the remaining G term, its affected GA
derivative has the same exact formula as equation (47) of
the cited proof. With \(r=k/l<2/3\), \(x<.256\), its norm
derivative is less than 1.6: the numerator coordinate is
less than .766, the other exceeds .5704, and
\[
 1.6^2(.766^2+.5704^2)-Q(.766)^2=.037505336>0.
\]
The normalized remaining derivative exceeds
\(K+.6442-1.6>.127\). This also treats an affected separated
negative-G term.

For AB we use the slightly wider basic-ratio assertion
\[
                r\ge.94,\ s\le.38\quad\Longrightarrow\quad
                         F_{0,s}>1.03l.                       \tag{24}
\]
Indeed, for \(y=\sin s\le.371\), positive squaring gives
\[
 \frac R{\sqrt{1+.94^2(1-y^2)}}<1.442+.4y^2.
\]
The squared difference is concave in \(y^2\), and its two
endpoint values exceed .00109 and .0333. By (10), (24)
reduces to positivity of
\(K-1.03-.442y+1.03y^2-.4y^3\). At \(y=1/4+v\), this is
bounded below by
\[
 .000958333333333333-.002v+.6816v^2> .0009568.
\]
The displayed truncated constant is a rational lower bound
for the exact constant \(23/24000\).
For the AB same-block G term, the norm bounds at ratio 2/3
are \(C_0/l<.51,D_0/l<1.10\), so its derivative divided
by l is greater than
\(1.03+.3145-1.10-.51(.25)=.117\).

For separated terms use the universal
\(U_i(t)\ge-.545q_it\) and the common bound \(q_i<5/4\).
It also pays the D cost since \(.545(5/4)=.68125>.67\).
Only negative H or G remains. The AB-G slope is positive
because \(V'_{2/3,1}(.32)<.93<1.03\); the AB-H slope is
greater than \(1.03(1.026)-1.032>0\). The GA-H slope uses
the unchanged bound \(F_{0,s}>.996\), valid for
\(k\ge2/3,l>1.023\), while \(V_H'(.45)<.964\).
Thus all remaining low saturated terms minimize at s=0.

**High interval.** Sections 9--12 of the cited angle proof
apply directly with (20)--(21). Treat D as an ordinary fourth
pair in their saturation comparisons, then discard its pure
negative alternative by \(V_D\ge V_H\). Their pure-positive
argument has already been checked above. The affected GA
and AB pure-negative curves have variable part
\[
 l\{(K+\sin z)x-R\sqrt{(x+r\cos z)^2+(1-r\sin z)^2}\},
\]
which is concave; here m<l, so the additional AB branch of
that proof is not needed. The unaffected GA curvature uses
\(k/l<.82\), \(x<.256\), and \(q/l<1.1\). The unaffected
AB curvature uses \(m/l<1.032\), and \(m/l<.92\) once
\(x>.35\) forces \(z>1/3\). All their margins remain valid.
They reduce to s=0, the equal-angle scalar s=z, or the actual
GA and AB cut endpoints 1/4 and .38. No actual A state at
an artificial equal-angle endpoint is asserted.

## 6. The fourteen reference scalar obligations

Let \(\phi(t)=\cos t+\sin t\) and put
\[
 M_G(z)=k\{\phi(h-z)-1\}+l(\cos h-1)
            -R\{N_{k,l}(-z)-N_{k,l}(0)\}.
\]
The preceding concentration leaves, on the low interval,
exactly
\[
 \begin{gathered}
 B_0+V_H(z),\qquad B_0+M_G(z),\\
 B_0-.68125(h-z)+V_H(h),\qquad
 B_0-.68125(h-z)+V_G(h),\qquad B_{\mathrm{GA}}(z,z).
 \end{gathered}                                                \tag{25}
\]
The GA equal-angle baseline is the smaller one, because m≥k
and the increment of \(\sqrt{p^2+r^2}\) as p increases
decreases with r. On the high interval the obligations are
\[
 B_0+V_i(z)\ (i=H,G,B),\qquad
 B_{\mathrm{GA}}(z,z),\quad B_{\mathrm{AB}}(z,z),              \tag{26}
\]
\[
 B_{\mathrm{GA}}(1/4,z)+V_i(z-1/4)\ (i=H,B),
 \qquad
 B_{\mathrm{AB}}(.38,z)+V_i(z-.38)\ (i=G,H).                  \tag{27}
\]
The latter AB cut curves are used only on [.38,h]. The other
high curves are certified on [1/4,h]. Every expression in
(25)--(27) is strictly positive by the explicit certificates
below.

## 7. Explicit polynomials and coefficient conventions

Use the already proved rational upper constants
\[
 \overline R=1.978787508,\quad \overline a=1.414575672,
 \quad\overline\sigma=1.415477291,
 \quad\overline c=.899214066.                                 \tag{28}
\]
Let \(C_j,S_j\) denote the ordinary cosine and sine Taylor
polynomials ending in degree j. On [0,h],
\(C_{10}\le\cos\le C_{12}\) and
\(S_{11}\le\sin\le S_9\).

For a polynomial \(P(x)=\sum p_jx^j\) on [0,b], define
\[
 a_{j0}=4^{-j}\binom{2j}{j},\qquad
 a_{jr}=2\,4^{-j}\binom{2j}{j-r}\quad(1\le r\le j),
 \qquad b_r=\sum_jp_jb^ja_{jr}.
\]
Its whole-interval coefficient bounds are
\[
             b_0-\sum_{r>0}|b_r|\le P\le b_0+\sum_{r>0}|b_r|.
 \tag{29}
\]
This is just the shifted Chebyshev identity and \(|T_r|\le1\).
It introduces no angular subdivisions.

For the low family put
\[
 I=2k+3l+5/2-\overline c
   +m\{1+(3/2-\overline c)C_{10}(z)
       +(1/2+\eta(1-\overline c)-\overline\sigma)S_9(z)\},
\]
\[
 (P_H,P_G,P_B)=(1+k^2,k^2+l^2,l^2+m^2).
 \tag{30}
\]
For the high family put
\[
 I=2k+3l+3+m\{1+2C_{10}(z)
                 +(1/2+3\eta/2-\overline\sigma)S_9(z)\},
\]
\[
 (P_H,P_G,P_B,P_D)
  =(1+k^2,k^2+l^2,l^2+m^2,1+\{m(C_{12}(z)+\eta S_9(z))\}^2).
 \tag{31}
\]
The H,G,B ordered pairs at s=0 are \((k,1),(k,l),(m,l)\)
whenever their pure term is used; the high family has m<l.

To build \(B_0+V_i(a)\), replace \(P_i\) by
\(P_i-2p_iq_iS_{11}(a)\) and add \(q_i(C_{10}(a)-1)\) to I.
For the low M curve use i=G,a=z but instead add
\(k\{C_{10}(h-z)+S_{11}(h-z)-1\}+l(C_{10}(h)-1)\).
For the two low separated curves use a=h and also subtract
\(.68125(h-z)\).

For an equal-angle or cut curve, multiply its scalar by
\(\cos s>0\). Replace I by
\[
 C_{10}(s)(I-l)+l+KlS_{11}(s),                               \tag{32}
\]
and every squared norm by \(C_{12}(s)^2P_i\), except that
the affected G or B norm becomes respectively
\[
                    l^2+k^2C_{12}(s)^2,
       \qquad       l^2+m^2C_{12}(s)^2.
\]
Here I−l>0. At an unaffected cut with a=z−s, further subtract
\(2C_{10}(s)^2p_iq_iS_{11}(a)\) from its squared norm and add
\(C_{12}(s)q_i(C_{10}(a)-1)\) to (32). The sign of the last
parenthesis explains the upper cosine factor.

For the low curves use native variable x=z. For the high
curves use x=z−1/4, except that AB-cut curves use x=z−.38.
For each resulting squared norm P, set
\[
 w=([P]_{\le3}-P(0))/P(0),\qquad
 r=\rho[1+w/2-w^2/8+w^3/16]_{\le3}.                          \tag{33}
\]
The following rational constants specify all masses. The low
default vector in H,G,B order is
\[
 (1.201850425155,1.257298868386,1.590206275928).
\]
For the low separated H curve replace its H constant by
.765171567774; for the separated G curve replace its G
constant by .815568741219. Other low constants are unchanged.
For the high pure H,G,B curves use the default vector
\[
 (1.213863422159,1.243063542284,1.411857840755,1.414033763977)
\]
and replace the one rotated constant respectively by
1.064421563117, 1.092123719510, or 1.225390819604.
For the high GA equal and both GA cut curves use
\[
 (1.176127347990,1.231351623317,1.367966599597,1.370074878635).
\]
For the high AB equal curve use
\[
 (1.176127347990,1.204419707095,1.391737262208,1.370074878635).
\]
For both AB cut curves use
\[
 (1.151745317104,1.193219895370,1.339697088381,1.263457367714).
\]
Every mass exceeds .76 on its whole interval by (29).
No root-approximation assertion about a mass is needed.
For the resulting nonradical A and squared norms define
\[
 \mathcal N=2A\prod_i r_i
   -\overline R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.             \tag{34}
\]
The positive-mass inequality \(\sqrt P\le(P+r^2)/(2r)\)
makes the corresponding scalar, or its positive cosine
multiple, at least \(\mathcal N/(2\prod r_i)\).

## 8. Positivity of all fourteen reference numerators

For low M and the separated H,G curves, the direct bounds
(29) for \(\mathcal N\) exceed respectively
\[
                         .063,
             \qquad      .178,
             \qquad      .175.                               \tag{35}
\]
The two tight low curves require only one power-tail argument.
Write \(\mathcal N(1/4-w)=\sum a_jw^j\), and define
\[
                T=\sum_{j\ge4}\max(-a_j,0)(1/4)^{j-4}.
\]
For the H curve, exact rational coefficient evaluation gives
\[
 a_0>.0010535,\quad a_1>-.045810,
 \quad a_2>1.11878,\quad a_3>8.50670,\quad T<42.969.
\]
The concave quadratic \(a_2+a_3w-Tw^2\) has both endpoint
values greater than .5598. Hence
\[
 \mathcal N>.0010535-.045810w+.5598w^2>.000116.                \tag{36}
\]
For the GA equal curve,
\[
 a_0>.0016043,\quad a_1>.07459,
 \quad a_2>1.08458,\quad a_3>8.78451,\quad T<53.944.
\]
The same endpoint comparison gives
\[
 \mathcal N>.0016043+w(.07459-.091w)>.0016043
                     \qquad(0\le w\le1/4).                   \tag{37}
\]
The strict final assertion includes w=0 by the strict constant
bound. These are two complete power-tail certificates; no
Bernstein coefficient inventory is used.

For the high interval let n(x) be the numerator in its native
variable. Direct (29) or its application to
\(q(x)=(n(x)-n(0))/x\) gives the following complete bounds:

| Curve | Whole-interval certificate |
| --- | --- |
| H pure | n(0)>.001263, q>.053 |
| G pure | n(0)>.01115, q>.119 |
| B pure | n>.259 |
| GA equal | n(0)>.001041, q>.020 |
| AB equal | n>.0287 |
| GA cut, H | n(0)>.001041, q>.442 |
| GA cut, B | n(0)>.001041, q>.505 |
| AB cut, G | n>.0337 |
| AB cut, H | n>.0349 |

All quotients here are exact polynomials. Equations
(30)--(34), followed by (29), reproduce each bound. The
numerator degrees are 21 for the first four low curves, 34
for low GA equal, 37 for high pure and cut curves, and 61
for high equal curves. Equations (35)--(37) and the nine
high bounds prove every scalar in (25)--(27) strictly positive.
This completes the secondary-E reference exclusion for every
negative A alternative in (3), including the algebraic s=0
and z=0 limits.

## 9. The shorter E total: \(0\le e\le s\)

For the actual flat-core A its exact increase in demand minus
projection from zero to −r is
\[
 g(r)=K\sin r-B(1-\cos r),\qquad
 B=y_A+1/2\ (\mathrm{GA}),\quad B=1/2-y_A\ (\mathrm{AB}).
\]
The actual entry cuts give \(B<.656\) in GA. In AB the
actual inequality gives \(y_A\ge1-b_B>.1\), hence \(B<.4\).
The signed E comparison supplies its single lower charge j(e).
The exact whole-domain gain lemma in
[the shorter-E transfer proof](HAND_G3_NEGATIVE_A_PRIMARY_DOMINATES_SHORTER_E_TOTAL.md)
states, for every \(l\ge1.023\),
\[
 l\sec(s-e)\{g(s)-g(s-e)\}+j(e)\ge0.                        \tag{38}
\]
Its proof uses only these two A cuts and the actual E charge;
it makes no use of the BT or TD owner. Both families
(17)--(18) have the required l bound.

Take the reference weights of Sections 2--8 at \(s'=s-e\)
and unchanged z. In this one actual weighted sum, replacing
the negative A argument by −s' contributes exactly the first
term of (38), while deleting the selected E arguments costs
at most j(e). The remaining reference force is precisely (8)
and its ordinary blocks. If the E arguments have negative
variation n, their positive variation is e+n. Deleting them
and replacing −s by −s' removes e+n from both variations,
and preserves total signed sum zero. Thus the reference
concentration applies, with s' inside its actual cut.
Its strict positivity and (38) contradict the actual weighted
inequalities. This closes every \(e\le s\), including e=s.

## 10. The longer E total: gain and angle reduction

Now suppose e≥s. The sharp actual GA contact cut and the AB
inequality, proved in Section 2 of
[the longer-E transfer proof](HAND_G3_NEGATIVE_A_PRIMARY_WITH_LONGER_E_TOTAL_EXCLUSION.md),
give the common lower gain
\[
 g_*(s)=K\sin s-(.656-.63s)(1-\cos s),\qquad
                         0\le s\le M:=19/50.                  \tag{39}
\]
It is strictly concave, with \(g_*''<-.31\). The sharp GA
cut uses only the actual G,A projections, so remains valid
with BT3. The E charge j(e) is unchanged.

If \(z+e\le L:=1/6\), use the small-total positive-BT
weights at \(z+e-s\), whose two A multipliers equal one.
The exact gain comparison from the same longer-E proof is
\[
                    g_*(s)+j(e)\ge j(e-s)+s/600.               \tag{40}
\]
Indeed \(g_*(s)>s\) and \(j'(u)>-599/600\) on [0,L].
After deleting the negative A argument and the E arguments,
the remaining total is \(-z-e+s\); their variations lie in
the positive-BT small-total concentration domain. Its strict
scalar theorem at virtual E total e−s, strengthened by (40),
gives the contradiction.

It remains that \(L\le z+e\le h\). Use the two large-total
families from the positive-BT theorem, at its parameters
\(\theta=z\) and e. For z≥L put x=z−L and use
\[
 k=.6692+.5218x-.5956x^2+.4216x^3+.28e,
\]
\[
 l=1+.0175x-1.0932x^2+1.278x^3+.25e,
 \quad m=1.0163-.0209x-1.1486x^2+1.4069x^3+.25e.             \tag{41}
\]
For z≤L put x=L−z and use
\[
                  k=.6692-.10x+.28e,
      \qquad l=1+.25e,
      \qquad m=1.0163+.25e.                                  \tag{42}
\]
Put c=mf(z), and now give both A edges the equal multiplier l.
Let \(B(z)\) denote the full-circle baseline at s=0, namely
(8) with S replaced by \(\overline S\) also at D.
The already proved balanced four-block concentration of the
positive-BT theorem, and its \(V_D\ge V_H\) comparison, leave
only
\[
       F_i(s)=B(z)+lg_*(s)+j(e)+V_i(z+e-s),\qquad i=H,G,B.
 \tag{43}
\]
Indeed the actual remaining variations are
\(P\le h-z-e,N\le h-s,N-P=z+e-s\); enlarging to
\(P\le h-(z+e-s),N\le h\) is permitted. The coefficients
are held fixed while s varies. Each \(F_i\) is concave on
\([0,\min(e,M)]\), by (39) and concavity of V. Its s=0
endpoint is already positive by the positive-BT theorem.
The endpoint \(s=\min(e,M)\) is certified next.

## 11. Twelve explicit longer-E endpoint numerators

Write \(d=h-L=8/15\), \(D=d-M=23/150\). The four intrinsic
domains, with native variables x,y, are

| Domain | z | e | s | Native domain |
| --- | --- | --- | --- | --- |
| TE | L+x | y | e | x,y≥0, x+y≤d |
| TC | L+x | M+y | M | x,y≥0, x+y≤D |
| RE | L−x | x+y | e | 0≤x≤L, 0≤y≤M−x |
| RC | L−x | M+y | M | 0≤x≤L, 0≤y≤D+x |

TE proves a harmless algebraic extension beyond e≤M; only
that subdomain is used for the actual endpoint. In each row
use (41) or (42), put \(\delta=z+e-s\), and define
\[
 J(u)=\frac{C_{10}(u)-1}{2}+(1/2-\overline a)S_9(u),
 \qquad G(u)=KS_{11}(u)+(.656-.63u)(C_{10}(u)-1).
\]
The proved E support bounds give
\[
 j_e^-=
 \begin{cases}
 J(e)-.002e^4,&\mathrm{TE},\mathrm{TC},\\
 J(e),&\mathrm{RE},\\
 J(e)-.029e^4,&\mathrm{RC}.
 \end{cases}                                                   \tag{44}
\]
Use
\[
 C=m(C_{12}(z)+\eta S_9(z)),\qquad
 q_B^+=\begin{cases}l+.15(d-x),&\mathrm{TE},\mathrm{TC},\\m,&\mathrm{RE},\mathrm{RC}.
 \end{cases}
\]
The positive-BT family bounds give
\(q_B^+\ge\max(l,m)\). Start with
\[
 A=2k+3l+3+m\{1+2C_{10}(z)
            +(1/2+3\eta/2-\overline\sigma)S_9(z)\}
                          +j_e^-+lG(s),
\]
\[
 (P_H,P_G,P_B,P_D)=(1+k^2,k^2+l^2,l^2+m^2,1+C^2).           \tag{45}
\]
For index H,G,B respectively, add to A
\[
 (C_{10}(\delta)-1),\qquad l(C_{10}(\delta)-1),
                   \qquad q_B^+(C_{10}(\delta)-1),
\]
and replace its squared norm by
\[
 P_H-2kS_{11}(\delta),\qquad P_G-2klS_{11}(\delta),
                   \qquad P_B-2lmS_{11}(\delta).              \tag{46}
\]

Define the cubic masses by (33), now truncating by total
degree in x,y. For TE,RE the default rho vector is
\[
              (1.203257512,1.203257512,1.425785990,1.451171531),
\]
and the replaced H,G,B constant is respectively
1.107155480, 1.107155480, 1.302177104. For TC,RC the default
vector is
\[
              (1.265525725,1.341857056,1.560132267,1.523913613),
\]
and the replaced constant is respectively
1.159403846, 1.232394077, 1.424873143. For G in TE and TC
only, make the additional exact changes
\[
                    r_G\leftarrow r_G-x^3/4,
            \qquad  r_D\leftarrow r_D+x^3/4.                  \tag{47}
\]
All masses exceed respectively .70,1.07,1.10,1.03 on
TE,TC,RE,RC. Define the numerator by (34) with these four
masses. Its degree is 39 on TE,TC and 35 on RE,RC. Each
endpoint (43) is at least its numerator divided by twice
the positive mass product.

For explicit bivariate coefficient bounds, use the same
\(a_{ij}\) as in (29). For a triangle of side b, substitute
\(x=bu(1-v),y=buv\). For a trapezoid
\(0\le x\le L,0\le y\le A+Bx\), substitute
\(x=Lu,y=(A+BLu)v\). Expand exactly, then apply (29)
in each of u,v on [0,1]. The lower and upper bounds are
the constant tensor coefficient minus or plus the sum of
the absolute values of all other tensor coefficients.
Use b=d,D for TE,TC and (A,B)=(M,−1),(D,1) for RE,RC.
This specifies a single whole-domain transform in each case.

## 12. Longer-E positivity and final assembly

On TE write
\(\mathcal N(x,y)=\mathcal N(x,0)+yH(x,y)\). In index order
H,G,B the whole-domain upper bounds for H_y are
\[
                           -.70,\quad-.55,\quad-.50.
\]
The lower bounds for \(H(x,d-x)\) are respectively
\[
                            .011,\quad .083,\quad .123.
\]
Thus every quotient H is positive. The three base polynomials
\(\mathcal N(x,0)\) are identically the already positive
triangle base polynomials in Section 7 of the positive-BT
theorem: (39) vanishes at e=s=0, and all masses, including
(47), agree there. This proves TE positivity.

On TC the direct whole-triangle numerator lower bounds are
\[
                            .013,\quad .032,\quad .265.
\]
On RE the whole-trapezoid upper bounds for
\(\mathcal N_{xx}\) are respectively −6.7,−7.2,−11.1.
At fixed y, concavity reduces x to
\([0,\min(L,M-y)]\)'s endpoints. The one-variable lower
bounds on the resulting three intrinsic edges are

| Index | x=0, 0≤y≤M | x=L, 0≤y≤M−L | y=M−x, 0≤x≤L |
| --- | ---: | ---: | ---: |
| H | .00135 | .01489 | .02681 |
| G | .00134 | .01489 | .02681 |
| B | .2979 | .01489 | .02680 |

Every edge is positive. Finally, on RC write
\(\mathcal N(x,y)=\mathcal N(x,0)+yH(x,y)\). The whole-domain
lower bounds for H are .854,1.184,3.443, and the base
polynomials on [0,L] all exceed .02209. Thus all RC numerators
are positive as well. Every bound in this section is obtained
by the explicit coefficient transform following (47); no
coefficient-row inventory or angular subdivisions are used.

These twelve certificates prove the second endpoint of (43).
Its first endpoint was already positive. Concavity proves
(43) strictly positive at the actual s, contradicting the
weighted neighboring inequalities. Equation (40) covers its
remaining small-total range, and Section 9 covers e≤s.
Sections 2--8 include all reference endpoints and all actual
A cuts. Together these prove the theorem for every selected
nonnegative E total, including outer E.

The proof uses the actual weak witnesses, actual circles and
flat-core data, and preserves both variation bounds under
every prior A-only transport. The artificial angle endpoints
occur only inside lower scalar expressions. No local T-only
conversion is assumed, and no numerical optimization,
sampled minimum, state mesh, Lean compilation, or CI result
is a premise of the proof.
