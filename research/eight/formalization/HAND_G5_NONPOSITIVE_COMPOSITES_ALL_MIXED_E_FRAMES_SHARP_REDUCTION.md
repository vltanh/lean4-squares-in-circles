# Negative outer composites are sharp for every retained mixed owner and every E frame

## 1. The necessary system and the sharp conclusion

Put
\[
 Q=\frac{9789}{2500},\qquad q_L=\frac{19577}{5000},
 \qquad Q_1=\frac{1957767069}{500000000},\qquad K=\frac{13}{12}.
\tag{1}
\]
Let H,A,B,D,E have the normal signed tangents: positive at
H,A and negative at B,D,E. Write their nonnegative magnitudes
as \(a_i\ge b_i\ge0\). Retain the true central exclusion and
their actual corner bounds
\[
                  (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{2}
\]
The common A/B frame lies between D and H. Put D at frame
zero and H at frame \(\alpha\), and let
\[
 t,u,e_H,e_D\ge0,\qquad
 \alpha=t+u+e_H+e_D\le7/10,\qquad b_A+b_B=1.
\tag{3}
\]
The two retained outer composites are
\[
\begin{aligned}
 b_H&\ge \frac12+C_A\cos e_H+K\sin e_H,\\
 C_A&=1-(a_A-\tfrac12)\cos t+(b_A+\tfrac12)\sin t,\\
 b_D&\ge \frac12+C_B\cos e_D+K\sin e_D,\\
 C_B&=1-(a_B-\tfrac12)\cos u+(b_B+\tfrac12)\sin u.
\end{aligned}
\tag{4}
\]
An error equal to zero gives the usual aligned composite.
These are exactly the true-core HG0 and TD2 composites for
remaining negative noncanceling errors. No physical-gap or
nonneighbor assertion about a comparison intermediate is assumed.

Let E's frame be any \(\delta\) in the original real-frame
interval, with
\[
 \epsilon=\alpha-\delta,\qquad
 \alpha-7/10\le\delta\le7/10,\qquad
 \widehat W(x)=\frac{1+\cos x+|\sin x|}{2}.
\]
Retain either witness in each row pair:
\[
\begin{array}{c|l}
 DE2&a_D\cos\delta+b_D\sin\delta+b_E\ge\widehat W(\delta)\\
 DE3&a_D+a_E\sin\delta+b_E\cos\delta\ge\widehat W(\delta)\\
 EH0&a_H\cos\epsilon+b_H\sin\epsilon-b_E\ge\widehat W(\epsilon)\\
 EH1&a_H+a_E\sin\epsilon-b_E\cos\epsilon\ge\widehat W(\epsilon).
\end{array}
\tag{5}
\]
The needed radial input for E is the following alternative:
\[
             a_E\le7/12
       \quad\hbox{or}\quad
             a_E\ge\max\{b_H,b_D\}.
\tag{6}
\]
A true core boundary representative satisfies the first
alternative. A sorted E on the common containing circle
satisfies the second, since its primary is at least
\(\sqrt{q/2}-1/2\) and both sorted endpoint tangents are at
most that value. Thus (6) includes the usual true-core/outer
radial boundary input. The weaker formulation also remains
valid if a working circle ceiling is subsequently enlarged
while the H,D,E coordinates stay fixed.

**Sharp terminal theorem.** Every system (2)--(6) has
\(q\ge q_*\). At equality,
\[
 e_H=e_D=0,\qquad \delta=0,
\tag{7}
\]
and its original five anchors have the unique stationary
values and canonical hard split of the aligned hard-class
theorem. All original mixed-owner ties are included.
Any separate strict A/B corner loss is retained by this
terminal argument and is incompatible with equality.

This theorem removes the E-order and mixed-owner hypotheses
from the nonpositive-composite terminal. It does not produce
the preceding common A/B frame or the two composites (4).

Since \(q_L<q_*<Q_1<Q\), a q above \(Q_1\) already proves
the strict conclusion. If q is below \(q_L\), enlarge only
the working ceiling to \(q_L\). Conditions (3)--(6) and all
actual coordinates persist. A contradiction at that ceiling
excludes the original system. We may therefore use
\[
                              q_L\le q\le Q_1
\tag{8}
\]
in the circle constructions below. At equality there is no
enlargement.

## 2. Uniform non-E bounds and the remaining negative error

Section 5 of
[the negative-core transport](HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md)
uses only (2)--(4). It gives
\[
\begin{gathered}
 a_A,a_B>11/10,\qquad .335<b_A,b_B<.665,\\
 b_H+a_A\ge2+\frac{167}{200}\sin(t+e_H),\qquad
 b_D+a_B\ge2+\frac{167}{200}\sin(u+e_D),\\
 a_H+a_D<1.9968-.718\sin\alpha<2,\qquad
                          0\le\alpha<27/100.
\end{gathered}
\tag{9}
\]
No E sign, owner, frame, or coordinate enters these estimates.
In particular, \(a_A,a_B<1.294\): the squared reserve is
\[
                  1.794^2+.835^2-Q=\frac{61}{10^6}>0.
\]
Consequently
\[
 b_H,b_D>\frac{353}{500},\qquad
 a_H,a_D<\frac{11}{10},\qquad b_H,b_D<\frac9{10}.
\tag{10}
\]
For the primary upper bound, a primary at least \(1.1\)
together with a tangent greater than .7 would give corner
square greater than \(1.6^2+1.2^2=4>Q\).

Apply the small-transverse negative transport to every side
with middle tangent at most \(1/2\). For example, if
\(b_A\le1/2\), it replaces \(t,e_H\) by \(t+e_H,0\) at
the same H,A coordinates; at \(e_H>0\) its aligned composite
has slack greater than \(e_H/150\). The barrier proof applies
directly to (4), which is its exact scalar input. The
reflected statement treats the D side.

Thus at most one error remains positive, and it is on a
side whose middle tangent is greater than \(1/2\).
All five anchor coordinates, all circle values, \(\alpha\),
and both mixed witnesses are unchanged. A positive error
removed here supplies strict middle-circle loss by a small
primary decrease, as in Section 8 of
[the nonpositive sharp theorem](HAND_G5_NONPOSITIVE_OUTER_OWNERS_SHARP_REDUCTION.md).
The bounds in (9) leave strict room for sorting and the core.
That primary decrease preserves (4) and the unchanged AB sum.
The other retained strict A/B losses remain separate.

## 3. A core E is excluded, and a nonnegative mixed error supplies its primary witness

The true core condition and sorting give
\[
                         a_E>\frac{447}{800}.
\]
Suppose the first alternative of (6) holds. The coefficient
comparisons in Section 3 of
[the aligned all-mixed theorem](HAND_G5_ALIGNED_CHAIN_ALL_MIXED_OWNERS_SHARP_REDUCTION.md)
use only
\[
 a_E\le7/12,\quad b_E\le a_E,\quad
 a_H,a_D>1/2,\quad b_H,b_D<.9,\quad
 |\delta|,|\epsilon|\le.7.
\]
They therefore apply here without change. Each original
owner in (5) gives its corresponding inequality
\[
 a_D+b_E\ge1-\tfrac12\sin\delta,\qquad
 a_H-b_E\ge1-\tfrac12\sin\epsilon.
\]
Adding, and using \(\delta+\epsilon=\alpha\),
\[
 a_H+a_D
 \ge2-\sin(\alpha/2)\cos((\delta-\epsilon)/2)
 \ge2-\sin(\alpha/2).
\tag{11}
\]
But \(\cos(\alpha/2)>.99\), since
\[
                1-\frac{.135^2}{2}-.99=\frac{71}{80000}>0.
\]
The difference between the last bound in (11) and the
primary-sum upper bound in (9) is
\[
 .0032+\{1.436\cos(\alpha/2)-1\}\sin(\alpha/2)>0;
\tag{12}
\]
the coefficient is greater than \(10541/25000\).
This also excludes \(\alpha=0\). The first alternative of
(6) is impossible.

We may therefore use \(a_E\ge\max\{b_H,b_D\}\).
For \(\epsilon\ge0\), the exact projection difference is
\[
 P_{EH1}-P_{EH0}
 =(a_H+b_E)(1-\cos\epsilon)+(a_E-b_H)\sin\epsilon\ge0.
\tag{13}
\]
For \(\delta\ge0\), it is
\[
 P_{DE3}-P_{DE2}
 =(a_D-b_E)(1-\cos\delta)+(a_E-b_D)\sin\delta\ge0.
\tag{14}
\]
If \(a_D-b_E<0\), sorting gives
\(a_E-b_D\ge b_E-a_D\), while
\(\sin\delta\ge1-\cos\delta\). Otherwise both terms in
(14) are nonnegative directly.

Thus an E between D and H already has the actual primary
DE3 and EH1 witnesses, without changing any anchor.
Sections 3--8 of the nonpositive sharp theorem then apply
directly to (3)--(4) and these two witnesses. They give the
claimed lower bound, preserve separate A/B/E circle losses,
and force the canonical data at equality.

It remains to handle E outside the endpoint interval.
Only one of its mixed errors can be negative.

## 4. The primary mixed-owner E-order argument extends to this chain

First suppose that both DE3 and EH1 are feasible, with
arbitrary E frame. If \(\alpha=0\), their sum cancels both
E coordinates and gives \(a_H+a_D\ge2\widehat W(\delta)\ge2\),
contrary to (9). Suppose henceforth that \(\alpha>0\).

Every feasible E outside \([D,H]\) has primary greater than
one. Indeed, put
\[
 \omega=\alpha/2,\quad \zeta=|\delta-\epsilon|/2,\quad
 c=\cos\omega,\ s=\sin\omega,\ m=\cos\zeta+\sin\zeta.
\]
The original frame spread gives
\(0<\omega<.135\), \(\omega<\zeta<.7<\pi/4\), and
\(m\ge c+s\). The exact mixed sum and (9) give
\[
 2s a_E m>cm-1+1.436sc.
\]
The same monotonicity in m as in Section 3 of
[the E-order theorem](HAND_G5_E_ORDER_FROM_ALIGNED_NON_E_CHAIN.md)
therefore yields
\[
 a_E>\frac{1.218c-.5s}{c+s}
 >\frac{1.218(.99)-.5(.135)}{1.135}>1.
\tag{15}
\]
The numerator minus denominator in the final comparison is
\(83/25000>0\). Thus sorting and core boundaries remain
strict on every outside portion.

The two-contact identities in Sections 4--7 of that E-order
theorem depend only on the primary mixed equations, the
strict inequalities \(a_E>b_E\), \(\alpha>0\), and the
frame spread less than \(\pi/4\). They apply verbatim here.
Above H, decreasing E's frame toward H strictly lowers its
corner, and increases its tangent at a two-contact point.
Below D with positive tangent, increasing E's frame toward D
strictly lowers its corner. The same one-contact directions
exclude all other outside minima.

Here are the endpoint exclusions needed for those arguments.
An E at \(\epsilon=0\) is impossible for every remaining
non-E alternative from Section 2:

* If both negative errors have vanished, the aligned
  epsilon-zero exclusion applies.
* If the H side retains a positive \(e_H\), then \(b_A>1/2\).
  From (9),
  \(b_H\ge5/2-\sqrt{Q-1}\), so the H circle gives
  \[
  a_H\le\sqrt{6\sqrt{Q-1}-8}-\frac12<1.
  \tag{16}
  \]
  The last comparison follows from
  \(Q<2257/576\), with reserve \(1009/360000\).
  But EH1 at zero error gives \(a_H\ge1+b_E\ge1\).
* If the D side retains a positive \(e_D\), then \(b_B>1/2\).
  Reflect the necessary system and use the signed-E
  DE-alignment stress in
  [the large-transverse negative endpoint theorem](HAND_G5_NEGATIVE_HG_LARGE_TRANSVERSE_DE_ALIGNMENT_EXCLUSION.md).
  Its inputs are precisely (3)--(4), \(\alpha<.27\), the
  opposite aligned side, and the two mixed equations at
  this endpoint. Its E support explicitly permits the
  reflected signed tangent, and its ceiling is \(Q_1\).

Consequently the compact E minimization above H cannot end
at its only possible boundary \(\epsilon=0\); E above H
is impossible. At \(b_E=0\), reflecting a below-D system
turns it into an above-H system of exactly the same form.
The tangent sign remains zero and the negative composites
interchange. Thus a transverse-zero E below D is impossible.
The compact minimization below D must therefore reach
\(\delta=0\), with a strict E-circle decrease.

This proves the full primary E-order reduction on the present
larger chain. It retains H,A,B,D and every separate A/B
circle loss. The resulting primary ordered system joins
Section 3. Its strict E loss excludes equality.

## 5. A rotated EH0 witness above H reaches the excluded endpoint

Suppose \(\epsilon=-x<0\) and \(\delta=\alpha+x>0\).
Equation (14) supplies DE3. If EH1 is also feasible,
Section 4 already excludes this branch. Retain EH0.

Put
\[
 a=a_E,\quad b=b_E,\quad b'=a_H-1,\quad
 A_H=a_H-\frac12,\quad B_H=b_H+\frac12.
\]
The exact EH0 inequality is
\[
                 b'-b\ge A_H(1-\cos x)+B_H\sin x.
\tag{17}
\]
In particular
\[
             0\le b<b'<.1,\quad A_H>.5,\quad B_H>603/500.
\tag{18}
\]
At fixed b, first raise E's primary to its q-circle if
necessary. DE3 improves because \(\delta>0\), and EH0
does not use that primary. This produces a sorted true
outer E on the working circle and leaves all non-E data
unchanged.

Write
\[
 a_q(y)=\sqrt{q-(y+1/2)^2}-1/2,\qquad
 M_\alpha(y)=(a_q(y)-1/2)\sin\alpha+(y-1/2)\cos\alpha.
\]
For \(b\le y\le b'\), its primary corner exceeds \(9/5\):
\[
                    q_L-(3/5)^2-(9/5)^2=1577/5000>0.
\]
Thus
\[
 M_\alpha'(y)
 >1-\frac{.27^2}{2}-\frac{.27}{3}
 =\frac{87}{100}+\frac{71}{20000}.
\tag{19}
\]
For the old angular coefficient retain the cosine factor:
\[
 (a-.5)\cos\alpha-(b-.5)\sin\alpha
 \le\frac{183}{200}\cos\alpha+\frac12\sin\alpha
 <\frac{127}{125}.
\tag{20}
\]
The expression in the middle increases on \([0,.27]\),
since its derivative is greater than \(9389/40000\).
At .27 its quartic-cosine and quintic-sine upper bounds
leave the exact reserve
\[
 \frac{127}{125}
 -\frac{183}{200}\left(1-\frac{.27^2}{2}+\frac{.27^4}{24}\right)
 -\frac12\left(.27-\frac{.27^3}{6}+\frac{.27^5}{120}\right)
 =\frac{313363763}{400000000000}>0.
\]
Also \(M_\alpha(b)\ge-1/2\). Combining (17)--(20),
using \(\tan(x/2)<3/8\), gives
\[
\begin{aligned}
 M_\alpha(b')-M_{\alpha+x}(b)
 &>\left(\frac{87}{100}\frac{603}{500}
                      -\frac{127}{125}\right)\sin x
                    -\frac{13}{200}(1-\cos x)\\
 &>\frac{1769}{200000}\sin x>0.
\end{aligned}
\tag{21}
\]
Place E at H's frame with coordinates
\((a_q(b'),b')\). EH1 at zero error is an equality and
DE3 has strictly improved. This is the epsilon-zero system
excluded in Section 4. When \(\alpha=0\), the two endpoint
equations instead give \(a_H+a_D\ge2\) immediately.
Thus E above H is impossible for either original EH owner.

## 6. A rotated DE2 witness below D has a decreasing contact curve

Suppose \(\delta=-x<0\) and \(\epsilon=\alpha+x>0\).
Equation (13) supplies EH1. If DE3 is also feasible,
Section 4 gives the required strict E-order descent.
Retain DE2 for the remaining branch.

Put
\[
 A_D=a_D-\frac12,\quad B_D=b_D+\frac12>\frac{603}{500},
 \qquad b(z)=\frac12-A_D\cos z+B_D\sin z.
\tag{22}
\]
The original DE2 inequality is \(b_E\ge b(x)\).
At the fixed original frame, raise E's primary to its
working q-circle and then lower its tangent to
\(\max\{0,b(x)\}\) along that circle. DE2 is preserved
and EH1 improves. If the tangent is zero, go to Section 7.

Otherwise decrease z from x with tangent \(b(z)>0\)
until the first of \(z=0\) or \(b(z)=0\). Put
\[
\begin{gathered}
 K_z=A_D\sin z+B_D\cos z>0,\\
 Y=b(z)+\frac12=1-A_D\cos z+B_D\sin z,\qquad
 X=\sqrt{q-Y^2},\qquad U=X-K_z.
\end{gathered}
\tag{23}
\]
The tangent decreases during this motion; the primary
increases, and sorting and the true core remain valid.
All changing frames stay between the original E and D.
The EH1 margin is
\[
 J(z)=a_H-\frac12+(X-1)\sin(\alpha+z)-Y\cos(\alpha+z).
\]
Its exact derivative, as in the aligned all-mixed proof, is
\[
 J'(z)=(U-1)\cos(\alpha+z)+\frac{YU}{X}\sin(\alpha+z).
\tag{24}
\]
Also
\[
 U\le\frac{\sqrt q-B_D-\sin z}{\cos z}
 <g(z):=\frac{773/1000-\sin z}{\cos z}.
\]
The quadratic comparison
\[
 \frac45s^2-\frac{773}{1000}s+\frac15
 \ge\frac{42471}{3200000}>0
\]
gives \(g'<-4/5\). Hence
\[
               U<\frac{773}{1000}-\frac45z,
 \qquad \frac{773}{1000}-\frac45z>0\quad(0\le z\le.7).
\tag{25}
\]

The larger span \(\alpha<.27\) is handled by retaining
a bound on the actual ratio \(Y/X\). Sorting on the q-circle
gives \(X\ge\sqrt{q/2}>1399/1000\), since
\[
                         q_L/2-(1399/1000)^2=499/10^6>0.
\]
By (10),
\[
 Y<.794+1.4z+.103z^2
 \le.794+1.4721z
 <1.399(.6+1.1z).
\tag{26}
\]
The last constant and linear reserves are \(227/5000\)
and \(167/2500\). Thus \(Y/X<.6+1.1z\).

If \(U\le0\), (24) is negative directly. If \(U>0\), use
\(\cos(\alpha+z)>3/4\), \(\sin(\alpha+z)\le\alpha+z\),
and (25)--(26). They give the whole-interval bound
\[
\begin{aligned}
 \frac{J'(z)}{\cos(\alpha+z)}
 &<\left(\frac{773}{1000}-\frac45z\right)
       \left[1+\frac43\left(\frac35+\frac{11}{10}z\right)
                         \left(\frac{27}{100}+z\right)\right]-1\\
 &=-\frac{938}{15625}-\frac{12073}{250000}z
                    +\frac{1327}{7500}z^2-\frac{88}{75}z^3<0.
\end{aligned}
\tag{27}
\]
For the final sign, discard the nonpositive cubic term.
The remaining quadratic is convex and has endpoint values
\[
             -\frac{938}{15625},\qquad
             -\frac{53543}{7500000}
             \quad\hbox{at }0,\ 7/10.
\]
It is negative throughout the interval. Thus EH1 strictly
improves as z decreases, without an angular subdivision.

If the curve reaches zero, its tangent is \(1-a_D\ge0\).
DE3 at zero error is an equality and EH1 has strict slack.
For \(\alpha>0\), a sufficiently small primary decrease
of E preserves both contacts, sorting and the core and
records strict E-circle loss. The primary ordered terminal
in Section 3 then applies and excludes equality. If
\(\alpha=0\), the endpoint mixed sum contradicts (9).

It remains to exclude a zero E tangent reached before D.

## 7. The zero-tangent endpoint uses only an aligned small-B side

At this endpoint E has tangent zero, primary
\(\sqrt{q-1/4}-1/2\), and frame \(-z\), where \(z>0\).
EH1 is feasible, and DE2 gives
\[
              (a_D-\tfrac12)\cos z-(b_D+\tfrac12)\sin z
                            \ge\frac12.
\tag{28}
\]
In particular \(a_D>1\).

If \(b_B\ge1/2\), the D-side version of (16) would instead
give \(a_D<1\), using only \(b_D+a_B\ge2\).
Therefore \(b_B<1/2\). Section 2 already aligned this
side, so \(e_D=0\). The H side may retain its large
negative error.

We may now use exactly the D/T move from Section 7 of the
aligned all-mixed theorem; its proof is local to the
already-aligned B/D side. For completeness, put
\[
 L_q(s,d)=\cos s\sqrt{q-(d+\cos s)^2}
                         -\sin s(d+\cos s),\qquad
 Y_D=b_D+\frac12,\quad Y_0=\sqrt{q-9/4}.
\]
Equation (28) gives \(Y_D\le L_q(z,1/2)\).
The positive-cap rate \( -\partial_sL_q>9/8\), together
with \(Y_D>1.206\) and \(Y_0<1.291\), yields \(z<.08\).
On this interval the radical exceeds 1.29 and the cap
primary corner is at least 1.5. The exact derivative then
gives the stronger rate
\[
 -\partial_sL_q>
 \frac32\left(1-\frac{.08}{1.29}\right)
 =\frac{121}{86}>\frac75.
\tag{29}
\]
The squared radical reserve is
\(q_L-9/4-1.29^2=13/10000\).
Consequently \(Y_0-Y_D>(7/5)z\).

Keep H,A,B,E and their frames fixed. Move D to E's frame
and set
\[
                    a_D'=1,\qquad b_D'=Y_0-\frac12.
\tag{30}
\]
Its circle is q and it is strictly sorted. The actual B
coordinates have
\[
 V_B(s)=(a_B-\tfrac12)\cos s-(b_B+\tfrac12)\sin s,
 \qquad
 |V_B'(s)|\le\sqrt{q-2a_B}
 <\sqrt{Q-11/5}<\frac43.
\tag{31}
\]
The final squared reserve is \(1399/22500\).
The old aligned composite gives \(V_B(u)\ge2-Y_D\).
Equations (29)--(31) therefore yield
\[
                         V_B(u+z)>2-Y_0+\frac z{15}.
\tag{32}
\]
The new B/D composite is strictly feasible. An actual
comparison T, if desired, has frame D', primary \(7/12\)
and tangent \(1-b_D'\); it is a sorted true-core point
with circle below \(q_L\).

The new total span is \(\alpha+z\), the unchanged original
H/E frame difference, so it is at most .7. E agrees with
D', has tangent zero, and satisfies DE3 with equality.
EH1 and the entire H-side negative composite are unchanged.
This is precisely the system excluded by
[negative-error E-zero deletion](HAND_G5_NEGATIVE_OUTER_E_ZERO_ERROR_DELETION.md),
which permits either or both negative outer composites
and the whole angular interval up to .7. Thus the endpoint
cannot occur. No alignment of the remaining large H-side
error has been inferred.

## 8. Sharpness and the original anchors

Section 3 excludes the core alternative and resolves every
inside E. Sections 4--5 exclude every above-H E. An E below
D either has the primary descent from Section 4 or the
rotated contact descent from Section 6; both reach a primary
ordered E with strict E-circle loss. Section 7 excludes
the only possible earlier endpoint.

These arguments prove the sharp lower bound for the whole
necessary system (2)--(6). All four non-E anchors remain
fixed during every E descent. The D move is used only in
an outright contradiction. A temporary E primary lift in
Sections 5--6 is not attributed to an original center:
Section 5 ends in exclusion, while Section 6 creates a
new strict E-circle loss at its ordered endpoint.

At equality, a nonzero small-tangent negative error would
have supplied a strict A/B loss in Section 2. The primary
ordered sharp theorem retains that loss and has positive
circle masses on all five anchors, so it is impossible.
An original outside E is likewise impossible by the
strict loss or exclusions above. The original E is
therefore already inside, and its original mixed
witnesses imply DE3/EH1 by (13)--(14).

Reapply the nonpositive composite sharp theorem to the
original five anchors, with any surviving large negative
error. Its canonical terminal forces that error to zero,
the original E split to \(\delta=0\), and all five original
anchor vectors to their stationary values. This proves
(7) without identifying any constructed anchor with its
predecessor. Every separate strict A/B circle loss is
excluded by the same final positive circle masses.

The only new scalar estimates here are the enlarged
outside-primary reserve, the single EH0 endpoint
comparison, and the whole cubic derivative bound (27).
They are exact rational and Taylor inequalities. No
numerical samples, angle table, state mesh, Lean run, or
CI result is a premise.
