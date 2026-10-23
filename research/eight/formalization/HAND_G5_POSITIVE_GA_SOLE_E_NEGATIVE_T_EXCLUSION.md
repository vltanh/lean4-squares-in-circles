# Positive GA1, a sole nonnegative E primary, and a negative T primary

## 1. Actual domain and exact conclusion

All terminating decimals in this note are exact rational numbers. Put
\[
 q_L=19577/5000,\qquad Q_1=1957767069/500000000,
 \qquad R=\sqrt{Q_1},\qquad h=.7,\qquad K=13/12,
\]
\[
 a_0=\sqrt{Q_1-1/4}-1/2,\qquad
 c_0=\sqrt{Q_1/2}-1/2<.9.
\tag{1}
\]
Fix one actual common ceiling \(q_L\le q\le Q_1\), in the
boundary-neighbor domain of the
[boundary bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
H,A have positive tangent and B,D have negative tangent. They
are the sorted outer anchors at q. G,T may have either tangent
sign and either radial kind; E may be core or outer. In particular,
every actual state satisfies
\[
 (a_i+1/2)^2+(|y_i|+1/2)^2\le q\le Q_1,
 \qquad a_i\ge |y_i|.
\tag{2}
\]
The true-core or outer alternative for T is used below; arbitrary
interior T states are not added to the theorem's domain.

Retain actual HG2, GA1 with error \(x\ge0\), and either actual
AB0 or actual AB2. Retain one of these E regimes:
\[
\begin{array}{c|cc|c|c}
 &DE&EH&\text{primary error}&\text{E tangent}\\ \hline
 \mathrm{EH}&2&1&e=d_{EH}\ge0&\text{either sign}\\
 \mathrm{DE}&3&0&e=d_{DE}\ge0&y_E\le0.
\end{array}
\tag{3}
\]
Retain one of these T regimes:
\[
\begin{array}{c|cc|l}
 &BT&TD&\text{errors}\\ \hline
 \mathrm{TD}&2&2&d_{TD}=-s\le0,\quad d_{BT}\text{ arbitrary}\\
 \mathrm{BT}&3&0&d_{BT}=-s\le0,\quad d_{TD}=0.
\end{array}
\tag{4}
\]
All other errors have arbitrary signs. Their sum is zero and
both variations are at most h. The actual boundary consequence
has strict variation bounds; the closed enlargement suffices.
Write
\[
                         t=x+e\in[0,h].
\tag{5}
\]

**Theorem.** No necessary cycle satisfying (2)--(5) exists.

The theorem covers both actual G signs, both AB owners, every
ordinary-angle sign allocation and all weak zero-angle ties.
The DE regime retains its stated sign restriction on E. No
reflection is used to remove that restriction. The BT regime
really assumes TD alignment.

Only same-state owner reselection is used. There is no geometric
motion in the proof and no equality inference from changing an
intermediate square. The contradiction is strict at Q1. The
[scalar companion](HAND_G5_SOLE_E_NEGATIVE_T_SCALAR_CERTIFICATES.md)
contains explicit rational polynomials on complete intervals.

## 2. Genuine negative primaries and the positive weights

If TD0 is already available in the TD regime, use it and apply
the existing
[EH sole-primary theorem](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md)
or [DE sole-primary theorem](HAND_G5_POSITIVE_GA_OUTER_E_SOLE_DE_AND_SECONDARY_EXCLUSION.md),
with the [signed-coordinate extension](HAND_G5_SOLE_E_POSITIVE_GA_SIGNED_COORDINATE_EXTENSIONS.md).
Likewise, if BT2 is available in the BT regime, the same theorems
apply with its aligned TD0. At s=0 the relevant secondary is
identical to the retained primary projection, so this also deals
with both weak zero-angle cases.

Suppose henceforth that s>0 and the corresponding secondary is
unavailable. The local proofs in Sections 4--5 of the
[core-E entry note](HAND_G5_POSITIVE_GA_HG2_CORE_E_COMPLETE_EXCLUSION.md)
use only B,T,D, their actual q and the retained T witnesses.
They use no E hypothesis and give
\[
\begin{array}{c|c|c}
 &\text{actual T state}&\text{negative error}\\ \hline
 \mathrm{TD}&a_T=7/12,\quad0<y_T<.415&0<s<.3\\
 \mathrm{BT}&a_T=7/12,\quad.1<y_T<.156&0<s<.09.
\end{array}
\tag{6}
\]
For clarity, in the first row BT2 bounds \(y_T<a_0-1<.415\),
and TD2 at error −s forces \(b_D+y_T>1\). If T were outer
at q, the shifted-circle comparison gives
\[
 \frac{a_T-a_D}{b_D-y_T}
 \ge\frac{b_D+y_T+1}{a_T+a_D+1}>\frac12>\tan(s/2),
\]
so the actual TD0 projection exceeds TD2 at the same states.
Otherwise T is on the true flat core. Its TD2 slack is less than
\(.4-.085\cos s-K\sin s\), which decreases and is negative
at s=.3. In the second row aligned TD0 gives \(y_T>.1\).
The actual BT contact-vector comparison, with BT2 unavailable,
puts T on its flat core and gives
\[
 Q_1>1+K^2+(y_T+1/2)^2
             +2\{(y_T+1/2)\cos s+K\sin s\}.
\]
The right side, at \(y_T+1/2=.6\) and s=.09, already exceeds
the larger ceiling Q of that local comparison. This proves (6)
at the original q; no q anchor has been replaced by a Q1 anchor.

Use exactly the sole-E coefficient families. They are collected
here to fix every parameter of the proof:
\[
\begin{array}{c|c|c|c|c|c}
 \text{family}&t\text{ interval}&k&l&c&g\\ \hline
 \mathrm{EH}_0&[0,.2]&.86265+.55t+.3t^2&.50521+.823t+.7t^2&k+.3t&.32\\
 \mathrm{EH}_1&[.2,.35]&.983+.10w-.3w^2&.698+.9w-w^2&1.045+.65w-1.5w^2&.31\\
 \mathrm{EH}_2&[.35,.7]&1.017-.02t&.70+.36t&1.13&.27+.08t\\
 \mathrm{DE}_0&[0,.35]&1.06-.1t&.565+.75t&.903+.65t&.32\\
 \mathrm{DE}_1&[.35,.7]&1.07-.12t&.77+.20t&1.13&.30+.05t.
\end{array}
\tag{7}
\]
Here \(w=t-.2\) in the second row. Either adjacent family may
be used at a common endpoint. Put
\[
 n(x)=k(\cos x+g\sin x),\qquad \lambda=1.25.
\tag{8}
\]
For EH0 and EH1 respectively, put
\[
 \eta=.262+.267t+.1t^2,\qquad \eta=.319+.2(t-.2),
 \qquad p(e)=\cos e+\eta\sin e.
\tag{9}
\]
For EH2 put p=1. The DE regime has no p tilt: its DE weight
is 1 and its EH weight is lambda.

Give HG,GA,AB weights n,k,l. Give BT,TD weights
\[
                    (c,c\sec s)\quad\text{in TD},
 \qquad             (c\sec s,c)\quad\text{in BT}.
\tag{10}
\]
Give DE,EH weights (p,1) in EH and (1,lambda) in DE. Every
weight is positive. The two signed T forces cancel exactly
apart from the known flat coordinate \(a_T=7/12\).

Write \(g_G=-y_G\), allowing either sign. The actual G force is
\[
                  k\sin x(a_G+g g_G)
                 \le k\sigma_g\sin x,
 \qquad \sigma_v=R\sqrt{1+v^2}-(1+v)/2.
\tag{11}
\]
The bound follows by replacing \(g_G\) with its absolute value
and using (2). In EH write \(b_E=-y_E\), allowing either sign.
The E force is \(\sin e(a_E+\eta b_E)\) for the first two
families and \(a_E\sin e+b_E(1-\cos e)\) for EH2. For
\(b_E\ge0\), use the same circle support as in the parent
theorem. For \(b_E<0\), first use the axis upper bound
\(a_0\sin e\). It has the same or better split curvature, and
is no larger than the parent circle upper bound at the endpoints.
In DE, \(b_E\ge0\) and the E force is
\[
           a_E\sin e+b_E(\cos e-\lambda)\le a_0\sin e.
\tag{12}
\]

Fix t,s, the ordinary errors and the actual H,A,B,D coordinates.
Perform the x/e split before maximizing these four supports.
The new coefficients in (10) are fixed in this split. Therefore
the second derivatives are exactly those bounded in the parent
sole-E proofs: the only varying anchor residuals are still
\[
 W(u)-a_H\sin u-b_H\cos u>-.065,
\]
\[
 W(\delta)-a_D\cos\delta-b_D\sin\delta>-.415,
 \qquad W(v)=(1+\cos v+|\sin v|)/2.
\tag{13}
\]
The full relaxed expression is strictly concave on \(x+e=t\),
with upper second-derivative bounds −.08, −.20 and −.19 in
the low/middle EH, high EH and DE families respectively. The
signed-E axis argument above only improves those bounds.
Consequently it suffices to prove positivity at
\[
                      E:(x,e)=(0,t),\qquad
                      G:(x,e)=(t,0).
\tag{14}
\]
This is scalar concavity on the complete split interval. It does
not assert an actual endpoint packing.

## 3. The exact sorted D baseline and the two negative gains

For positive f,g let S(f,g) be the support over the sorted
contained region
\[
 a\ge b\ge0,\qquad(a+1/2)^2+(b+1/2)^2\le Q_1.
\]
Let
\[
 \overline S(f,g)=R\sqrt{f^2+g^2}-(f+g)/2
\tag{15}
\]
be the full-circle upper support. Since \(b\le c_0<.9\),
for every \(g_2\ge g_1\) one has
\[
              S(f,g_2)-S(f,g_1)\le .9(g_2-g_1).
\tag{16}
\]
This follows directly by taking the supremum of the linear
functions fa+gb; it does not require differentiability of S.

In TD the zero-ordinary-angle D force changes from (p,c) to
\((p,c\sec s)\), with p=1 in DE. The exact gain relative to
the sorted baseline is
\[
 G_D(s)=c\{(\sec s-1)/2+K\tan s\}
                  -S(p,c\sec s)+S(p,c).
\tag{17}
\]
The threshold half-shifts in (17) are part of the identity.
By (16),
\[
              G_D(s)\ge c\{K\tan s-.4(\sec s-1)\}>1.05cs
                    \quad(0<s\le.3).
\tag{18}
\]
Here is a short exact whole-interval proof. The inequalities
\(\tan s\ge s+s^3/3\) and \(\cos .3>191/200\) give
\(\sec s-1<(100/191)s^2\). After division by s, the reserve
over 1.05 is at least
\[
       \frac1{30}-\frac{40}{191}s+\frac{13}{36}s^2>0,
\tag{19}
\]
because its leading coefficient is positive and its
discriminant is \(-42253/9849870<0\).

In BT use full-circle support at B. Its zero ordinary pair
changes from (l,c) to \((l,c\sec s)\). The exact gain is
\[
 G_B(s)=cF_{l/c}(s),\qquad
 F_r(s)=\sec s+K\tan s-R\sqrt{\sec^2s+r^2}
                                  -1+R\sqrt{1+r^2}.
\tag{20}
\]
All families have \(l/c\ge.585\). For \(s\le.09\), positive
squaring gives
\[
 \frac{R}{\sqrt{1+.585^2(1-.09^2/2)^2}}<1.712.
\]
Thus
\[
 F_r'(s)=\sec^2s\left\{K+\sin s
           \left(1-\frac R{\sqrt{1+r^2\cos^2s}}\right)\right\}
       \ge K-.712s.
\]
Since \(K-.356(.09)>1.05\), integration proves
\[
                         G_B(s)>1.05cs\quad(0<s\le.09).
\tag{21}
\]
In both regimes write
\[
                              \ell=1.05c.
\tag{22}
\]

We also retain part of the difference between the full-circle
and sorted D baselines. In EH1, \(1\le p<1.06\), \(c<1.11\)
and \(c\ge p\); in EH2, p=1,c=1.13. Sorting then gives
\[
 \overline S(p,c)-S(p,c)
 =R\left\{\sqrt{p^2+c^2}-\frac{p+c}{\sqrt2}\right\}
 >.32(c-p)^2
\tag{23}
\]
unless c=p, where the weak inequality holds. Rationalizing
shows that its coefficient of \((c-p)^2\) is
\[
 \frac{R}{2\{\sqrt{p^2+c^2}+(p+c)/\sqrt2\}}.
\]
Both terms in braces are below 1.535 in EH1 and below 1.509
in EH2; positive squaring gives \(R/(4\cdot1.535)>.32\).
Set
\[
 J_0=.32(c-p)^2\quad\text{in EH1 and EH2},
 \qquad J_0=0\quad\text{in EH0 and both DE families}.
\tag{24}
\]
In (24), p is its value at the endpoint (14). This correction
is introduced after the split, so no curvature claim about J0
is needed. The use of S at Q1 is an upper support inequality
on the original contained states, not a motion of their q anchors.

## 4. Ordinary blocks after a negative primary

For a positive pair \(a\le b\), put
\[
\begin{split}
 U_{a,b}(v)&=a(\cos v+\sin v-1)
       -R\{\sqrt{a^2+b^2+2ab\sin v}-\sqrt{a^2+b^2}\},\\
 V_{a,b}^{\nu}(v)&=\nu(\cos v-1)
       -R\{\sqrt{a^2+b^2-2ab\sin v}-\sqrt{a^2+b^2}\},\\
 H(a,b;v)&=R\{\sqrt{a^2+b^2}-\sqrt{a^2+b^2-2ab\sin v}\}.
\end{split}
\tag{25}
\]
The old pairs, products and available negative coefficients at
each endpoint are
\[
\begin{array}{c|c|c|c}
 &\text{pairs }H,A,B,D&\text{negative coefficients}&\text{indices used}\\ \hline
 \mathrm{EH}&(1,n),(k,l),(l,c),(p,c)&n,l,c,\max(p,c)&H,A,B,D\\
 \mathrm{DE}&(\lambda,n),(k,l),(l,c),(1,c)&\lambda,l,c& H,A,B.
\end{array}
\tag{26}
\]
Write \(V_i\) for these old functions. D has no ordinary error
in either DE regime of (4): both its incident selected directions
are primary or aligned. It is therefore absent from the DE
index set. In EH1 and EH2, \(\nu_D=c\).

An AB0 ordinary error belongs to B, whereas an AB2 error belongs
to A. The possible actual mixed blocks are precisely
\[
\begin{array}{c|cc}
 &\mathrm{TD}&\mathrm{BT}\\ \hline
 \mathrm{EH}&B&\text{none}\\
 \mathrm{DE}&H,B&H.
\end{array}
\tag{27}
\]
Allowing B two arguments also in the AB2 case is a harmless
enlargement. No other one-angle block is given a mixed pair.

### 4.1 The modified B block

In BT, B has only the AB ordinary argument, and its changed pair
is \((l,c\sec s)\). Its actual negative coefficient is l.
The gain H in (25) increases in either coefficient whenever the
coefficient ratio exceeds \(\tan(v/2)\). This follows directly
by differentiating and positive-sided squaring: the relevant
sign is that of \(2r-\sin v(1+r^2)\).
Here
\[
 \frac{l}{c\sec s}\ge .585(1-.09^2/2)>.58>\tan(h/2).
\]
Consequently its negative charge is at least the old \(V_B\):
the norm gain only increases, and replacing its negative
coefficient l by the larger c only lowers the charge.
Its positive charge is bounded below by the usual U for its
changed pair. This pair still has ratio greater than 1/2.

### 4.2 The one-angle D block relative to its exact sorted baseline

Only EH has a remaining D argument, the actual DE2 error delta.
Put \(q=c\sec s\) in TD and q=c in BT. The increment relative
to S(p,q) is
\[
 \Delta(\delta)=p\{W(\delta)-1\}
        +S(p,q)-S(p\cos\delta,q+p\sin\delta).
\tag{28}
\]
If \(q\ge p\), both supports for \(\delta\ge0\) are diagonal,
and hence
\[
             \Delta(\delta)=-(c_0-.5)p
                   (\cos\delta+\sin\delta-1)\ge-.4p\delta.
\tag{29}
\]
For \(\delta=-v\le0\), the quantity in (28) increases with q
on \([p,\infty)\): the baseline slope is c0 and the final
support slope is at most c0. At q=p the final force is in the
full-circle part of the sorted arc. Indeed its ratio is
\((1-\sin v)/\cos v=\tan(\pi/4-v/2)>.46\), above the
axis cutoff. Thus
\[
                        \Delta(-v)\ge pV_{1,1}^{1}(v).
\tag{30}
\]
If \(q<p\), the baseline support is full-circle interior in
all our ranges. Bounding the final support by full-circle
support gives the usual one-angle U bound. Its negative charge
is at least the old \(V_D\), because q has increased from c,
H is coordinatewise increasing along that path, and its actual
negative coefficient p is at most \(\max(p,c)\).

In every EH family and every \(0\le v\le h\),
\[
                         pV_{1,1}^{1}(v)\ge V_A(v).
\tag{31}
\]
Here p≥1. To verify (31), first note that \(V_{1,1}^{1}\ge0\)
from \(H(1,1;v)\ge(R/\sqrt2)\sin v\) and
\(\tan(h/2)<.3661<R/\sqrt2\). At fixed product, the
radical difference H decreases with the sum of the squares,
so
\[
                       H(k,l;v)\le\sqrt{kl}\,H(1,1;v).
\]
Also k+l<2 and
\[
                   \frac{1-l}{1-\sqrt{kl}}\le2.2.
\tag{32}
\]
For k≤1 the stronger bound 2 follows immediately. In EH2 use
\(\sqrt{kl}\le(k+l)/2\) and
\(2.4-2.2k-.2l=.0226-.028t>0\). Finally
\[
 \frac{H(1,1;v)}{1-\cos v}
      \ge\frac R{\sqrt2}\cot(v/2)
      >\frac{1.398}{.3661}>2.2
\]
for v>0. These comparisons prove (31), including v=0 by continuity.

Thus a valid negative envelope for the modified D block, for
either sign of q−p, is
\[
                          \min\{V_D(v),V_A(v)\}.
\tag{33}
\]
Both functions are concave and vanish at zero, so their minimum
is concave. The two possibilities in (33) are already included
in the index set (26); no new pure scalar is introduced.

## 5. The full signed angular envelope

After removing x,e and the one negative T primary, let P,N be
the positive and negative ordinary variations. They satisfy
\[
                   N-P=t-s,\qquad P\le h-t,\qquad N\le h-s.
\tag{34}
\]
The single-angle U and V functions are concave. The actual
two-angle blocks in (27) are separately concave, as in
[the continuous scalar-envelope proof](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md).
All their ratios are at least 1/2. For a one-angle negative
coefficient between the pair coefficients, the norm-curvature
upper bound \(.762\min(a,b)\) and \(\cos h>.7648\) give the
same conclusion. The replacement (33) and the linear positive
bound (29) are concave as well.

Concentrate each sign into one of its originally occupied
blocks. At fixed P,N this is the usual concave simplex endpoint
argument. Then vary P with N=P+t−s. Concavity leaves only:

- a pure negative charge \(V_i(t-s)\) when \(s\le t\);
- a pure positive charge at s−t when \(s\ge t\);
- a same-block mixed term at a block in (27), or a separated
  term \(U_i(h-t)+V_j(h-s)\).

The D negative alternative is interpreted using (33). These
are the entire continuous sign domain; no angle grid is used.

The following positive budgets cover all ordinary blocks,
including the changed B and D blocks:
\[
\begin{array}{c|ccccc}
 \text{family}&\mathrm{EH}_0&\mathrm{EH}_1&\mathrm{EH}_2&\mathrm{DE}_0&\mathrm{DE}_1\\ \hline
 \gamma&.57225&.608&.619&.68125&.68125.
\end{array}
\tag{35}
\]
Every positive charge is at least −gamma times its angle.
Use the universal \(U\ge-.545b v\). For a changed B, use
\(\sec s\le\sec .09<(1-.09^2/2)^{-1}\). The largest
coefficients are respectively below 1.05, \(1.11\sec .09\),
\(1.13\sec .09\),1.25,1.25. For D with q≥p use (29);
with q<p its largest coefficient is p, below 1.05 in EH0
and 1.06 in EH1. In every family
\[
                                  \ell>\gamma.
\tag{36}
\]
In EH0 there is also the angle-independent lower bound −.408
for every positive charge. For an ordinary or changed full-circle
U this is the parent tangent bound with largest coefficient
less than 1.05; for (29) the stronger lower bound −.294 suffices.

### 5.1 Same-block saturation for either sign of the net angle

Write P=h−t,N=h−s. A mixed block has positive coefficient
a and negative coefficient b, with a≤b; enlarging the negative
coefficient to b is a valid lower bound.
If \(w=t-s\ge0\), its difference from its own pure \(V(w)\)
is
\[
                     a(\cos P+\sin P-1)
                              +b\{\cos(P+w)-\cos w\}.
\tag{37}
\]
This decreases with w for P+w≤h. Since w≤t, it is at least
the same-block correction with s=0 proved in the parent EH/DE
notes, for exactly the family (7) and total t. Those corrections
are nonnegative for all the mixed blocks (27).

If \(z=s-t\ge0\), its difference from its pure positive U(z)
is
\[
             a\{\cos P+\sin P-\cos z-\sin z\}
                                  +b(\cos N-1).
\tag{38}
\]
For z+N=P≤h the ratio of the first braces to \(1-\cos N\)
is at least \(\cot(h/2)-1\). One sees this by writing it as
\((\cos(P-N/2)-\sin(P-N/2))/\sin(N/2)\): it is minimized
first at P=h and then at N=h. Thus (38) is nonnegative whenever
\[
                 a/b\ge\frac{\tan(h/2)}{1-\tan(h/2)}<.578.
\tag{39}
\]
Every actual mixed block has ratio at least .585. Therefore all
same-block saturations dominate a pure charge of the appropriate
sign, including both equality endpoints.

### 5.2 Separated saturation in the middle and high families

The parent whole-interval derivative bounds give
\[
 (V_i)'(v)>.674b\quad\text{in EH1 and EH2},
 \qquad (V_i)'(v)>.80b\quad\text{in DE1}.
\tag{40}
\]
The larger coefficients b are at least .983,1,.986 respectively.
The products .674(.983),.674 and .80(.986) exceed the matching
gamma in (35). A minimum of two functions with this lower
slope has the same lower-slope property, so (40) also covers
the D replacement (33).

If s≤t, integrate (40) from t−s to h−s. This gives at least
gamma(h−t), which pays for the separated positive charge.
If s≥t, integrate from zero: the separated sum is at least
\(-\gamma(s-t)\). Thus all separated alternatives in these
three families are bounded by the claimed pure envelope or
the stated positive linear envelope.

### 5.3 Low-family comparison on the entire far negative interval

For saturation in either low family, \(N=h-s\ge.4\) by (6).
Every actual negative charge on \([.4,h]\) dominates
\[
                            V_B(v)=V_{l,c}^{c}(v).
\tag{41}
\]
The modified B and D comparisons in Section 4 reduce this
claim to the old indices in (26). Here are full interval
proofs for those indices, since comparison only at h would
not suffice after removing a negative primary.

In EH0, H and D have both product coordinates at least those
of (.86265,1), and negative coefficient at most 1.05. The
coordinate-monotonicity criterion following (25) applies along
these coefficient paths. The resulting concave function
\[
                        H(.86265,1;v)-1.05(1-\cos v)
\]
has value greater than .791 at h, so it exceeds 1.13v.
Meanwhile
\[
 V_B(v)\le1.045V_{.669,1}^{1}(v)
               <1.151v-.125v^2\le1.101v\quad(v\ge.4).
\tag{42}
\]
The derivative at zero in this bound is less than 1.151 by
positive squaring. Its second derivative is less than −.25,
using \(1.045\{-\cos h+.762(.669)\}<-.25\).

For A in EH0 use c−l>.346, c−k≤.06 and
\[
                   0\le\partial_qH(q,l;v)<.4v
                 \quad(k\le q\le c,\ 0\le v\le h).
\tag{43}
\]
Then
\[
 V_A(v)-V_B(v)>.346(1-\cos v)-.024v>.044v
                             \quad(.4\le v\le h).
\tag{44}
\]
The ratio \((1-\cos v)/v\) increases on this interval, so
the last assertion follows from the upper Taylor bound for
cos .4.

In DE0 the parent fixed radical inequality \(V_H(h)>.9636\)
and concavity give \(V_H(v)>1.376v\). On the other hand
\(V_B'(0)<1.324\), so \(V_B(v)<1.324v\). If k≥c,
coordinate monotonicity immediately gives \(V_A\ge V_B\).
Otherwise c−l≥.303, c−k≤.1055 and
\[
                   0\le\partial_qH(q,l;v)<.53v
                 \quad(k\le q\le c,\ 0\le v\le h),
\tag{45}
\]
give
\[
 V_A(v)-V_B(v)\ge.303(1-\cos v)-.055915v>.0038v
                              \quad(.4\le v\le h).
\tag{46}
\]

For completeness, (43) and (45) have short exact algebraic
certificates, rather than a pointwise numerical premise. The
integrand of \(\partial_qH(q,l;v)\), with r=l/q and z=sin w,
is
\[
               R\frac{r^2(r-z)\sqrt{1-z^2}}
                       {(1+r^2-2rz)^{3/2}}.
\tag{47}
\]
Its derivative in r has the sign of
\(r\{3r-2z-2r^2z+rz^2\}>0\) on
\(.585\le r\le.81\), \(0\le z\le.6443\). The braces
decrease in z and are concave in r; their two r endpoints
at z=.6443 are positive. In EH0 use r≤.72; in the part
of DE0 with k<c use r≤.81. Squaring the positive upper
endpoint of (47) reduces to positivity of
\[
 T_{r,L}(z)=L^2(1+r^2-2rz)^3
                         -Q_1r^4(r-z)^2(1-z^2).
\tag{48}
\]
For r=.72,L=.4 its whole-interval Chebyshev coefficient norm
on [0,.6443] is greater than .00114. For r=.81,L=.53, put
\(T'(z)=b_0+b_1v+b_2v^2+b_3v^3\), v=z−.4. Then
\[
 q_2=b_2+.4|b_3|<-.987,\qquad
                    b_0-b_1^2/(4q_2)<.001.
\]
Thus T′<.001 throughout [0,.6443], and
\[
                 T(z)\ge T(.6443)-.001(.6443)>.0367.
\tag{49}
\]
The coefficient formula is reproduced in the scalar companion.
This proves (43),(45) over the complete angle interval.

Now suppose s≤t. Concavity of the fixed function VB gives
\[
                  V_B(h-s)-V_B(t-s)\ge V_B(h)-V_B(t).
\tag{50}
\]
The parent exact chord inequalities on the entire coefficient
families are
\[
 V_B(h)-V_B(t)>.43\quad\text{in EH0},\qquad
 V_B(h)-V_B(t)>.7(h-t)\quad\text{in DE0}.
\tag{51}
\]
Together with −.408 in EH0 and −.68125(h−t) in DE0,
they pay for every separated positive charge. The result is
at least VB(t−s), hence at least the minimum of the pure
charges in (26).

If s≥t, fixed radical comparisons and concavity give
\[
 V_B(N)>.66N\quad\text{in EH0},\qquad
 V_B(N)>.75N\quad\text{in DE0}.
\tag{52}
\]
For (52), use homogeneity and respectively
\[
 \frac{.86265}{h}V_{.585,1}^{1}(h)>.66,
 \qquad \frac{.903}{h}V_{.625,1}^{1}(h)>.75.
\]
Both constants exceed their gamma. Hence the separated sum
is at least −gamma(s−t). This completes all low-family
saturations, including the changed D support.

### 5.4 The resulting scalar reduction

Sections 5.1--5.3 prove that the total ordinary contribution
plus its negative-primary gain is bounded below by
\[
 \begin{cases}
 \ell s+\displaystyle\min_iV_i(t-s),&0\le s\le t,\\[2mm]
 \ell s-\gamma(s-t)\ge\ell t,&s\ge t.
 \end{cases}
\tag{53}
\]
Each \(V_i\) is concave. For fixed t the first line is the
minimum of finitely many concave functions of s. We may now
enlarge its scalar range to \(0\le s\le.3\), even in the
BT regime: the actual BT estimates were proved using s<.09
before this purely scalar enlargement. No hypothetical long
BT primary or long B secant is being asserted.

For t≤.3, the new endpoint is s=t, giving \(\ell t\).
For t≥.3, it is s=.3, giving
\( .3\ell+V_i(t-.3)\). The other endpoint s=0 is precisely
the existing sole-E pure scalar domain. In EH0 its canonical
VB comparison at t is the one proved in its parent note.

## 6. Exact endpoint scalars and conclusion

Let \(B_E(t),B_G(t)\) be the full-circle zero-ordinary baselines
in Section 5 of the two parent sole-E notes, with the same
families (7). The scalar companion repeats them explicitly.
After (14), (17)--(24) and (53), only the following additional
inequalities are required:
\[
                B_\varepsilon(t)+J_0(t)+\ell(t)t>0
                 \qquad(0\le t\le.3),
\tag{54}
\]
\[
 B_\varepsilon(t)+J_0(t)+.3\ell(t)+V_i(t-.3)>0
                 \qquad(.3\le t\le h),
\tag{55}
\]
where \(\varepsilon=E,G\), each family's actual interval is
retained, and i ranges over H,A,B,D in EH and H,A,B in DE.
There are 34 intrinsic univariate polynomials. Their companion
gives a common positive-mass construction and a single
whole-interval coefficient-norm rule: 33 numerators have
lower norm bound greater than .00058; the remaining numerator
has positive constant greater than .0033 and positive first
quotient with lower norm bound greater than .476. These are
exact rational identities, with explicitly bounded Taylor error.
Thus every scalar in (54)--(55) is strictly positive.

The old s=0 scalars are positive by the parent theorems; J0
is nonnegative. Concavity in s therefore makes each endpoint
(14) strictly positive for every actual negative T magnitude.
The strict x/e split then makes the relaxed weighted expression
positive at the original x,e. The positive weighted sum of the
retained actual witnesses requires that same expression to be
nonpositive. This contradiction proves the theorem.

All witnesses survive as stated, including their weak ties and
every ordinary signed frame difference. The only preliminary
owner changes select a secondary that is already feasible at
the same original states. The proof therefore excludes equality
directly at the original ceiling; it does not appeal to loss of
radius on a changed G or T state. No sampled state, numerical
optimizer, angle mesh, Lean compilation or CI is a proof premise.
