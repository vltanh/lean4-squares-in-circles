# Positive GA1, a sole positive E primary, and a positive T primary

## 1. Complete actual domain

All terminating decimals denote exact rational numbers. Put
\[
 Q_1=1957767069/500000000,\qquad R=\sqrt{Q_1},\qquad h=.7,
 \qquad a_0=\sqrt{Q_1-1/4}-1/2.
\tag{1}
\]
H,A have positive tangent and B,D have negative tangent. In the
DE regime below E has nonpositive tangent; in the EH regime E
may have either tangent sign. Every square is sorted and contained at a
common ceiling at most Q1. Thus
\[
 (a_i+1/2)^2+(|y_i|+1/2)^2\le Q_1,\qquad a_i\ge |y_i|.
\tag{2}
\]
G and T may have either tangent sign. No radial-kind assumption is
needed for any square in this note.

Retain actual HG2 and GA1, with GA error x nonnegative, and either
actual AB0 or AB2. Retain one of these actual E regimes:
\[
 \begin{array}{c|cc|c}
 &DE&EH&\text{nonnegative primary error}\\ \hline
 \mathrm{EH}&2&1&e=d_{EH}\ge0\\
 \mathrm{DE}&3&0&e=d_{DE}\ge0.
 \end{array}
\tag{3}
\]
Retain one of these actual T regimes:
\[
 \begin{array}{c|cc|c}
 &BT&TD&\text{nonnegative primary error}\\ \hline
 \mathrm{TD}&2&2&z=d_{TD}\ge0\\
 \mathrm{BT}&3&0&z=d_{BT}\ge0.
 \end{array}
\tag{4}
\]
All remaining errors may have arbitrary signs. The seven errors
sum to zero, and both variations are at most h. These hypotheses
include all zero-angle witness ties. Write
\[
                              t=x+e+z\le h.
\tag{5}
\]

**Theorem.** No system satisfying (2)--(5) exists.

This proves the positive-T extensions of both
[the EH1/TD0 theorem](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md)
and [the DE3/TD0 theorem](HAND_G5_POSITIVE_GA1_POSITIVE_DE3_WITH_TD0_EXCLUSION.md).
It covers both actual T signs, both actual G signs, both AB owners,
and the complete signed ordinary-angle domain. In particular it
applies to outer E, and includes the signed-E endpoint of a
paired-E reduction when the surviving primary is EH1. It does not assume a reduction of a paired E
primary to (3); that is a separate geometric input.

The proof moves no square. Its scalar companion,
[the whole-rectangle polynomial proof](HAND_G5_SOLE_E_POSITIVE_T_POLYNOMIAL_CERTIFICATES.md),
gives explicit rational polynomials and one uniform coefficient
bound. There is no angle mesh or sampled-angle premise.

## 2. Coefficients and the two tilted T forces

First select one of the following base families using t. The
letters K,L,C are base coefficients, not angles.
\[
\begin{array}{c|c|c|c|c|c}
\text{family}&t\text{ interval}&K&L&C&g\\ \hline
\mathrm{EH}_0&[0,.2]&.86265+.55t+.3t^2&.50521+.823t+.7t^2&K+.3t&.32\\
\mathrm{EH}_1&[.2,.35]&.983+.10w-.3w^2&.698+.9w-w^2&1.045+.65w-1.5w^2&.31\\
\mathrm{EH}_2&[.35,.7]&1.017-.02t&.70+.36t&1.13&.27+.08t\\
\mathrm{DE}_0&[0,.35]&1.06-.1t&.565+.75t&.903+.65t&.32\\
\mathrm{DE}_1&[.35,.7]&1.07-.12t&.77+.20t&1.13&.30+.05t
\end{array}
\tag{6}
\]
Here w=t−.2 in the second row. Either adjacent family is valid at
a common endpoint. Now set
\[
 k=K+.06z,\qquad l=L-.23z,\qquad c=C-.53z,
 \qquad \eta=.25+.33t,
\]
\[
 n=k(\cos x+g\sin x),\qquad
 m=c(\cos z+\eta\sin z).
\tag{7}
\]
All weights are positive. For EH0 and EH1 use respectively
\[
 \epsilon=.262+.267t+.1t^2,\qquad \epsilon=.319+.2w,
 \qquad p=\cos e+\epsilon\sin e.
\tag{8}
\]
For EH2 put p=1. For the DE families put \(\lambda=1.25\).

Give HG,GA,AB the weights n,k,l. Give BT,TD the weights (m,c)
in the TD regime and (c,m) in the BT regime. Give DE,EH the
weights (p,1) in the EH regime and (1,lambda) in the DE regime.

Write \(g_G=-y_G\), which is signed. The actual HG2 and GA1
inequalities are
\[
 a_H\sin u+b_H\cos u+g_G\ge W(u),\qquad
 a_A+a_G\sin x-g_G\cos x\ge W(x),
 \quad W(v)=(1+\cos v+|\sin v|)/2.
\tag{9}
\]
Their G force is exactly
\(k\sin x(a_G+g g_G)\). The actual T force is respectively
\[
 c\sin z(a_T-\eta y_T),\qquad
 c\sin z(a_T+\eta y_T).
\tag{10}
\]
For any nonnegative v define
\[
 \sigma_v=R\sqrt{1+v^2}-(1+v)/2,
 \qquad C_v(s)=1+2\cos s+(1+2v-R\sqrt{1+v^2})\sin s.
\tag{11}
\]
Replacing a signed tangent by its absolute value and using (2)
bounds (9)'s G force by \(k\sigma_g\sin x\), and either force
in (10) by \(c\sigma_\eta\sin z\). This explains why neither
G nor T needs its normal sign.

In the EH regime write bE=-yE, allowing either sign. The E force is
\(\sin e(a_E+\epsilon b_E)\) for the first two families.
For EH2 it is \(a_E\sin e+b_E(1-\cos e)\). In the DE regime
it is
\[
              a_E\sin e+b_E(\cos e-\lambda)\le a_0\sin e.
\tag{12}
\]
The last bound uses sorted nonnegative magnitudes and
\(\cos e-\lambda\le0\).

If bE is negative in the EH regime, its force is at most
a0 sin e. This axis support is no larger than the complete-circle
upper support used above, by applying Cauchy--Schwarz at the
axis point (a0+1/2,1/2). For the split in the next section, use
this axis bound first: its sine-curvature coefficient is .915,
which improves the .935 used for a nonnegative bE. In the high
family it gives the same bound -.5 cos e+.915 sin e. Thus both
the split inequalities and every endpoint scalar remain valid
for either E sign in the EH regime.

## 3. Reduce the G/E split while retaining z

Fix t,z and all ordinary angles and anchor coordinates. The
coefficients k,l,c,g,eta and epsilon are now fixed. Only x,e vary,
with x+e=t−z. Perform this reduction before maximizing the four
anchor supports.

The two residual bounds used in the original sole-E proofs are
\[
\begin{split}
 M_H&=W(u)-a_H\sin u-b_H\cos u>-.065,\\
 M_D&=W(v)-a_D\cos v-b_D\sin v>-.415.
\end{split}
\tag{13}
\]
They hold for every signed ordinary angle in [−h,h] and every
sorted contained anchor. The first uses diagonal support in a
transverse direction; the second uses radial support. In
particular, their validity does not depend on which T regime in
(4) is present.

For EH0 and EH1 the second derivative in the G/E split is at most
\[
 k\{- .435\cos x+.956\sin x\}
                  -.085\cos e+1.081\sin e.
\tag{14}
\]
Here x+e≤.35 and k≥.862. Its two endpoint upper bounds are less
than −.084 and −.154. For EH2 the corresponding bound is
\[
 k\{- .435\cos x+.961\sin x\}
                  -.5\cos e+.915\sin e.
\tag{15}
\]
Now \(1.003\le k\le1.045\), so its endpoint upper bounds are
less than −.22 and −.20. For DE the same expression has .957
instead of .961, and \(.986\le k\le1.06\); both endpoint bounds
are less than −.19. These constants follow from
\(\cos h>.7648\), \(\sin h<.6443\), and the positive-square
tilt bounds in the original EH and DE notes.

At fixed x+e each displayed expression is a linear combination
of sin x and cos x. Division by the positive cosine makes its
sign affine in tan x. Its two negative endpoint bounds therefore
make it negative everywhere; the expression itself is convex
and is bounded above by its endpoint maximum. The complete
relaxed split is strictly concave. It suffices to consider the
two full triangular faces
\[
 \mathrm{GT}:\quad x=t-z,\ e=0,
 \qquad
 \mathrm{ET}:\quad x=0,\ e=t-z,
 \qquad 0\le z\le t.
\tag{16}
\]
The dependence of the weights on z in (7) is retained throughout.
There is no concavity claim in z.

## 4. Actual ordinary blocks and their full signed envelope

After (16), the zero-ordinary-error coefficient pairs are
\[
\begin{array}{c|cccc}
 &H&A&B&D\\ \hline
\mathrm{EH,TD}&(1,n)&(k,l)&(l,m)&(p,c)\\
\mathrm{EH,BT}&(1,n)&(k,l)&(l,c)&(p,m)\\
\mathrm{DE,TD}&(\lambda,n)&(k,l)&(l,m)&(1,c)\\
\mathrm{DE,BT}&(\lambda,n)&(k,l)&(l,c)&(1,m).
\end{array}
\tag{17}
\]
For a sorted pair a≤b use
\[
\begin{split}
 U_{a,b}(s)&=a(\cos s+\sin s-1)
       -R\{\sqrt{a^2+b^2+2ab\sin s}-\sqrt{a^2+b^2}\},\\
 V_{a,b}^{\nu}(s)&=\nu(\cos s-1)
       -R\{\sqrt{a^2+b^2-2ab\sin s}-\sqrt{a^2+b^2}\}.
\end{split}
\tag{18}
\]
Use the following valid negative coefficients and mixed-block enlargements:
\[
\begin{array}{c|cccc|c}
 &\nu_H&\nu_A&\nu_B&\nu_D&\text{possible mixed blocks}\\ \hline
\mathrm{EH,TD}&n&l&m&p&B\\
\mathrm{EH,BT}&n&l&l&\max(p,m)&D\\
\mathrm{DE,TD}&\lambda&l&m&c&H,B\\
\mathrm{DE,BT}&\lambda&l&l&m&H.
\end{array}
\tag{19}
\]
An AB0 angle belongs to B and an AB2 angle to A. Enlarging B to
permit both ordinary angles in the TD regime is harmless. An
anchor can have no ordinary argument for a particular owner
choice (notably D in the DE/TD row); retaining its zero ordinary
block as an additional single-angle block only enlarges the
scalar domain. No extra actual witness is claimed.
The listed single-angle negative coefficients lie between the
smaller and larger pair coefficients. In a mixed block the
negative coefficient may be enlarged to the larger coefficient.
In particular m≥l whenever B is mixed.

All pair ratios are at least 1/2. The single-angle functions are
concave, and the two-angle functions are separately concave, by
[the continuous scalar envelope](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).
The norm-curvature bound there is less than .762 times the
smaller coefficient, whereas \(\cos h>.7648\). Concentrating
the ordinary positive and negative allocations leaves the four
pure charges \(V_i(t)\), same-block alternatives at the listed
mixed blocks, and separated alternatives
\[
 U_i(P)+V_j(h),\qquad P=h-t.
\tag{20}
\]
The universal positive bound is
\[
                     U_i(P)\ge-.545q_{\max}P,
\tag{21}
\]
where qmax is an upper bound for every pair coefficient.

The following exact ranges are useful. Here ratio means the
smaller pair coefficient divided by the larger.
\[
\begin{array}{c|c|c|l}
\text{family}&\text{ratio lower}&q_{\max}&\text{additional bound}\\ \hline
\mathrm{EH}_0&.585+.3t&1.05&\text{every larger coefficient}>.862\\
\mathrm{EH}_1&.65&1.11&\text{every larger coefficient}>.923\\
\mathrm{EH}_2&.72&1.131&\text{every smaller coefficient}>.745\\
\mathrm{DE}_0&H,D:\ .72;\ A:\ .533;\ B:\ .625+.27t&1.25&
 l\ge.565;\ l/k\le.81;\ \min(H,D)\ge.903;\ \max(B)\ge.903\\
\mathrm{DE}_1&.72&1.25&\text{every smaller coefficient}\ge.749.
\end{array}
\tag{22}
\]
They are rational polynomial inequalities after the elementary
Taylor bounds. The companion proves them by the same explicit
whole-rectangle coefficient formula as its scalar inequalities.
For orientation, the only tight EH0 A comparison is
\[
 l-(.585+.3t)k\ge
 .00055975-.022645t+.3415t^2-.09t^3>0.
\tag{23}
\]
The final inequality follows by replacing the last two terms by
.3235t² and completing the square. The tilted T coefficient is
at least c because eta−tan(t/2) is concave and positive at both
ends of [0,h]. Also m<1.131: in the high families,
\[
 m\le(1.13-.53z)(1+.481z)
       =1.13+.01353z-.25493z^2<1.131.
\tag{24}
\]

### 4.1 Same-block alternatives

For a pair ratio r the difference between its same-block term
at (P,h) and its pure term at t is at least
\[
                  b\{r(\phi(P)-1)+\cos h-\cos t\},
       \qquad \phi(s)=\cos s+\sin s.
\tag{25}
\]
For EH0 take r=.585+.3t. The bracket is positive at zero; its
derivative is concave and positive at 0 and .2, since its third
derivative is
\(-.9\phi(h-t)+r\phi'(h-t)-\sin t<0\).
For EH1 take r=.65: the bracket is convex and decreasing on
[.2,.35] and is positive at .35. For DE0, H has ratio at least
2/3 and B has ratio at least .625. The latter constant gives a
positive bracket on [0,.35]. Indeed, for
\[
 f(t)=.625\{\phi(h-t)-1\}+\cos h-\cos t,
\]
one has \(f''>.058\), \(f'(.35)<-.0298\), and
\(f(.35)>.00188\), by the alternating Taylor bounds in the
companion. Hence f decreases to a positive minimum. This is
also the same comparison used in the original DE note.
All high-family mixed ratios exceed 2/3, so the general
same-block comparison applies. Thus no same-block alternative
is smaller than its pure charge.

### 4.2 Separated alternatives

Write \(V_r=V_{r,1}^{1}\). Its derivative increases with r,
and it is concave in its angle. Fixed-angle positive squaring gives
\[
 .862\,\frac{V_{.585}(h)-V_{.585}(.2)}{h-.2}>.605,
 \qquad
 .923\,\frac{V_{.65}(h)-V_{.65}(.35)}{h-.35}>.7.
\tag{26}
\]
The first two rows of (22) therefore give, for every actual index,
\(V_j(h)-V_j(t)>.605P\) and \(>.7P\), respectively. Both
coefficients exceed .545 times their listed qmax.

For ratios between .72 and 1, one has
\[
                         (V_{a,b}^{b})'(s)>a
                         \quad(0\le s\le h).
\tag{27}
\]
Concavity reduces this to s=h. It then follows by positive
squaring from the whole-interval quartic inequality
\[
 Q_1 r^2(.7648)^2-(r+.6443)^2(1+r^2-2r(.6442))>.0829
                   \quad(.72\le r\le1).
\tag{28}
\]
This handles all high families and the DE0 H,D indices.

For DE0 A, put r=l/k. Concavity, \(.533\le r\le.81\), and
\(l\ge.565\) give
\[
 (V_A)'(s)\ge(V_A)'(h)
 >.565\{- .6443+1.978770865(.7648)/.785\}>.72.
\tag{29}
\]
Here \(1+r^2-2r\sin h<.785^2\) throughout the stated ratio
interval, by convexity in r and its two endpoints.
For DE0 B, the final one-variable comparison needed is
\[
 .903\{V_{.625+.27t}(h)-V_{.625+.27t}(t)\}>.7(h-t),
                         \qquad 0\le t\le.35.
\tag{30}
\]
The companion gives an explicit two-positive-square polynomial
proof of (30). Since \(.7>.545(1.25)\), (29)--(30) and the
stronger H,D bounds handle every DE0 separated index. Combining
(20)--(30), the entire signed ordinary-angle envelope is at least
\[
                              \min_{i\in\{H,A,B,D\}}V_i(t).
\tag{31}
\]

## 5. The four pure scalar inequalities on each whole face

Let the four pairs in (17) be \((a_i,b_i)\), with either ordering.
Set
\[
 B=kC_g(x)+cC_\eta(z)+2l+J(e)
                   -R\sum_i\sqrt{a_i^2+b_i^2},
\tag{32}
\]
where
\[
 J(e)=
 \begin{cases}
 C_\epsilon(e),&\mathrm{EH}_0,\mathrm{EH}_1,\\
 3+\sin e-2R\sin(e/2),&\mathrm{EH}_2,\\
 1+\frac12\cos e+(\frac12-a_0)\sin e+\frac32\lambda,
                                      &\mathrm{DE}_0,\mathrm{DE}_1.
 \end{cases}
\tag{33}
\]
These are the actual weighted-force identities after (9)--(12)
and the four full shifted-circle supports. The unrotated norm
for the chosen negative index cancels exactly with its increment.

For its scalar lower bound, retain the first three actual
coefficients in (19) and replace \(\nu_D\) by 1.131. This is
valid by (22)--(24), because \(\cos t-1\le0\). Thus define
\[
\begin{split}
 F_i={}&kC_g(x)+cC_\eta(z)+2l+J(e)+\widehat\nu_i(\cos t-1)\\
 &-R\!\sum_{j\ne i}\sqrt{a_j^2+b_j^2}
       -R\sqrt{a_i^2+b_i^2-2a_ib_i\sin t}.
\end{split}
\tag{34}
\]
The companion proves the uniform strict bound
\[
                         F_i>1/10000
\tag{35}
\]
for each family in (6), each T owner in (4), both faces in (16),
and all four indices. Its proof is a single explicit rational
polynomial construction on the full rectangle
\(t\in[a,b],\ 0\le z/t\le1\), with a rigorous analytic remainder.
At t=0 the value is independent of the auxiliary ratio z/t.

Equations (31), (34) and (35) make the weighted sum of the actual
necessary inequalities strictly contradictory on both faces.
The fixed-z concavity in Section 3 proves the same contradiction
for every split x+e+z=t. This proves the theorem, including all
weak ties, at the actual containment ceiling Q1.

## 6. The both-secondary E endpoint

If the E owners are instead actual DE2 and EH0, with both
errors arbitrary, the positive-T rows (4) are excluded for
either E sign as well. Use Section 3 of
[the all-secondary E gate](HAND_G5_POSITIVE_GA_OUTER_E_SECONDARY_E_ALL_T_OWNERS.md):
the two E weights are equal and their signed tangent forces
cancel exactly. Their actual rotations remain ordinary at D
and H. Its positive G/T split proof and PV scalar certificate
use only sorted containment, so no outer/core equality is
needed for this corollary. The larger strict ceiling Q there
contains the present Q1 domain.

Thus for either positive T owner the E alternatives with no
primary or with one nonnegative primary are fully covered:
both-secondary permits either E sign, sole EH1 permits either
E sign, and sole DE3 retains the hypothesis \(y_E\le0\).
A positive DE3/EH1 pair and a sole DE3 with positive E tangent
still require their actual endpoint join; neither is silently
identified with these strict sole-primary domains.
