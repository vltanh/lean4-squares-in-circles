# The entire middle/high frame-pair entry by hand

This proves the strengthened M/H entry **.8926** in the four-type frame
table, for both ordered types, all signs, and every retained separating
axis. No frame-concentration hypothesis is used. The strengthened value
is needed in the odd seven-walk budget in
[FOUR_TYPE_HAND_COVERAGE_INVENTORY.md](FOUR_TYPE_HAND_COVERAGE_INVENTORY.md).

Every terminating decimal below is an exact rational number. Computation
is unnecessary for the continuous argument: the only finite arithmetic
is displayed endpoint comparisons and five specified polynomial rows.
The optional JavaScript file replays those comparisons with integers.

## 1. Diagonal coordinates and unchanged potentials

Put \(Q=9789/2500\), \(\mathcal R=\sqrt{2Q}\), and
\[
 u=.089293,\quad v=.480179,\quad k=1.534906,\quad q=.045313,
 \qquad \gamma=.8926.
\]
In the original coordinates the outer boundary is
\((a_{\rm old}+1/2)^2+(b_{\rm old}+1/2)^2=Q\).
For each signed state rotate its frame toward the nearest diagonal:
\[
 a=a_{\rm old}+b_{\rm old},\qquad
 b=a_{\rm old}-b_{\rm old},\qquad
 \sigma=-\sigma_{\rm old}.
\]
The new positive arc is
\[
 (a+1)^2+b^2=2Q.                                      \tag{1}
\]
The relative tangent angle changes from
\(\alpha_{\rm old}=\sigma_{\rm old}\arctan(b_{\rm old}/a_{\rm old})\)
to \(\alpha=\alpha_{\rm old}-\sigma_{\rm old}\pi/4
=\sigma\arctan(b/a)\).
The folded positive label is \(\ell=\pi/4-\ell_{\rm old}\), so
\[
 \alpha-\sigma\ell
 =\alpha_{\rm old}-\sigma_{\rm old}\ell_{\rm old}.        \tag{2}
\]
Thus the potential at each vertex is exactly unchanged, and the
quarter-periodic width penalty is unchanged as well.

The H arc has \(0\le b/a\le2/5\); the M arc has
\(2/5\le b/a\le3/5\). Denote their successive endpoints by
\[
 (a_0,0),\quad (a_1,b_1),\quad (a_2,b_2),
 \qquad a_0=\mathcal R-1,\quad b_1=.4a_1,\quad b_2=.6a_2.
\]
The folded labels are
\[
 \ell_H=u(a-a_0)+vb,\qquad
 \ell_M=c_M-ka+qb,\qquad c_M=\pi/4+2.143075.             \tag{3}
\]
They increase with \(b\), because
\[
 a'(b)=-r(b),\quad r(b)=\frac b{a+1},\quad a''(b)<0,
 \qquad \ell_H'=v-ur>0,\quad \ell_M'=kr+q>0.            \tag{4}
\]

Substitution in (1), squaring, and \(3.14159<\pi<355/113\)
give all the following rational brackets:
\[
\begin{array}{c|c}
 \mathcal R&(2.79842813,2.79842814)\\
 a_1&(1.71322294,1.71322295)\\
 a_2&(1.62343405,1.62343407)\\
 \ell_H&[0,.321454)\\
 \ell_M&(.32988,.48080)\\
 r_H&[0,.253)\\
 r_M&(.252,.372).
\end{array}                                           \tag{5}
\]
In particular,
\[
\begin{gathered}
 a_1+b_1<2.399,\quad a_2+b_2<2.598,\\
 a_1-b_1>1.027,\quad a_2-b_2>.649.
\end{gathered}                                        \tag{6}
\]
The physical center radii are below \(1.306\) on H and \(1.35\)
on M, since their squares equal \(Q-a-1/2\).

For a source and target with signs \(\sigma,\tau\), let
\[
 \phi=\delta+\alpha_t-\alpha_s,\qquad
 h(\phi)=\frac{|\sin\phi|+|\cos\phi|-1}{2}.
\]
Here the earlier whole-domain center-gap lemma gives \(\delta>.76\).
We must prove
\[
 {\cal C}=\phi-.18h(\phi)+\sigma\ell_s-\tau\ell_t
 >\gamma.                                             \tag{7}
\]

## 2. Complete angle and separating-axis reductions

Alternating arctangent sums give
\[
 \arctan(.6)<.541,\qquad \arctan(.4)<.381,
 \qquad \phi>-.162.                                   \tag{8}
\]
If \(\phi\le0\), the center gap can exceed .76 only for
\((\sigma,\tau)=(+,-)\). In the folded frame the retained source
normals consist of the central normal \((-1,+1)/\sqrt2\)
and one extra normal. The central separator is
\[
 a+\sigma b+D A-\tau C B\ge W_2,
 \quad D=\sin\phi-\cos\phi,\quad C=\sin\phi+\cos\phi,
 \quad W_2=1+|\sin\phi|+|\cos\phi|.                     \tag{9}
\]
For \(-.162<\phi\le0\), its margin is at most
\[
 \max(a+b)-1-(\min(A-B)+1)\cos(.162).
\]
It is negative in both ordered cases: use respectively
\((\max(a+b),\min(A-B))<(2.598,\cdot)\),
\(\min(A-B)>1.027\), and \((2.399,.649)\), together with
\(\cos(.162)\ge1-.162^2/2\).

For source sign \(+\), the extra normal is \((+1,+1)/\sqrt2\).
Its separating projection is at most the target center radius minus
the source's original transverse coordinate. In M/H this is
less than \(1.306-.3246<1\); in H/M it is
less than \(1.35-.513<1\). Therefore this extra axis never separates.

For source sign \(-\), the extra normal is \((-1,-1)/\sqrt2\).
When \(0\le\phi\le\pi/2\), twice its separating projection is at most
\[
 \max(a+b)-\min(A-B)<2,
\]
by (6). To see this directly, its expression is
\(a+b-CA-\tau DB\); here \(C\ge1\) and \(|D|\le1\).
For \(\pi/2\le\phi\le1.71\) only the sign pair \((-,+)\)
needs further attention, as the direct bounds below handle the others.
In that remaining case \(D>0,\ C>.85\), and the expression is at most
\[
 2.598-.85(1.623)<2.
\]
This extra axis is also impossible. Thus every nontrivial case uses
(9), with \(\phi>0\).

We use \(0\le .18h<.0378\). The following tails already prove (7):
\[
\begin{array}{c|c|c}
 \text{ordered types and signs}&\text{tail begins}&
                  \text{lower bound for the cost}\\ \hline
 MH,HM:\ (+,-)&.61&.61-.0378+.32988>\gamma\\
 MH:(+,+),\ HM:(-,-)&.93&.93-.0378+.32988-.321454>\gamma\\
 MH:(-,-),\ HM:(+,+)&1.42&1.42-.0378-.48080>\gamma .
\end{array}                                           \tag{10}
\]
The function \(h\) is \(1/2\)-Lipschitz and \(h(\pi/2)=0\).
For every sign pair and \(\phi\ge1.71\),
\[
 {\cal C}\ge .91\phi+.09\pi/2-.48080-.321454
 >.89521755>\gamma.                                   \tag{11}
\]
No later angle remains uncovered.

Reflection followed by reversal preserves (7), the center gap and
\(\phi\), changes the ordered signs to \((-\tau,-\sigma)\), and
exchanges target and source separating axes. Since both ordered type
pairs are treated below, all retained target axes are covered too.

## 3. A support formula and the complete first-quadrant cover

Write \(\ell_i=c_i+p_i a+q_i b\), with
\[
 (c_H,p_H,q_H)=(-ua_0,u,v),\qquad(c_M,p_M,q_M)=(c_M,-k,q).
\]
For \(x=\phi>0,\ s=\sin x,\ c=\cos x\), subtract
\(\lambda\ge0\) times the margin of (9). This proves
\[
\begin{split}
 {\cal C}\ge F={}&x-.09(W_2-2)+\lambda W_2
                   +\sigma c_i-\tau c_j\\
 &+\min_i(U_s a+V_s b)+\min_j(U_t A+V_t B),             \tag{12}\\
 U_s={}&\sigma p_i-\lambda,\qquad
 V_s=\sigma(q_i-\lambda),\\
 U_t={}&-\tau p_j-\lambda D,\qquad
 V_t=\tau(\lambda C-q_j).
\end{split}
\]
The full circle (1) gives the lower support
\[
 \min(Ua+Vb)\ge-U-\mathcal R\sqrt{U^2+V^2}.             \tag{13}
\]
This is valid even if its minimizing point is outside the physical arc.
If \(U\ge0\), the functional is concave in \(b\), so its minimum
on an arc is at an endpoint. If \(U<0,V\ge0\), it increases and its
minimum is at the first endpoint. Other endpoint choices are justified
by the derivative \(-Ur+V\).

In the table, \(a\) means the first endpoint of the indicated arc,
\(b\) the last endpoint, \(a,b\) both separate endpoint expressions,
and \(o\) the full-circle lower support (13).
Put \(x_-=\pi/2-.02,\ x_+=\pi/2+.02\).
Every interval includes its endpoints.

| Types | Signs | Impossible initial interval | Remaining interval and multiplier | Source / target support | Scalar proof |
|---|---|---|---|---|---|
| MH | ++ | \(x\le.7\) | \([.7,.93],\lambda=.35\) | \(a/o\) | concavity |
| MH | +- | \(x\le.1\) | \([.1,.61],\lambda=.55\) | \(o/b\) | endpoint minimum |
| MH | -- | \(x\le.9\) | \([.9,1.2],\lambda=.4\) | \(a,b/b\) | increasing |
| MH | -- | as above | \([1.2,1.42],\lambda=.4\) | \(a,b/o\) | concavity |
| MH | -+ | \(x\le1.2\) | \([1.2,1.3],\lambda=.4\) | \(a,b/a\) | endpoint minimum |
| MH | -+ | as above | \([1.3,x_-],\lambda=.4\) | \(a,b/o\) | concavity |
| MH | -+ | as above | \([x_-,x_+]\) | exact contact | Section 5 |
| MH | -+ | as above | \([x_+,1.71],\lambda=.4\) | \(a,b/o\) | increasing |
| HM | ++ | \(x\le1.1\) | \([1.1,1.42],\lambda=.5\) | \(o/a\) | endpoint minimum |
| HM | +- | \(x\le.1\) | \([.1,.42],\lambda=.66-.4x\) | \(o/b\) | polynomial row 1 |
| HM | +- | as above | \([.42,.61],\lambda=.43\) | \(a/o\) | polynomial row 3 |
| HM | -- | \(x\le.4\) | \([.4,.6],\lambda=.64-.365x\) | \(o/b\) | polynomial row 2 |
| HM | -- | as above | \([.6,.7],\lambda=.42\) | \(o/o\) | polynomial row 4 |
| HM | -- | as above | \([.7,.93],\lambda=.4\) | \(o/o\) | polynomial row 5 |
| HM | -+ | \(x\le1.3\) | \([1.3,x_-],\lambda=.4\) | \(o/a,b\) | endpoint minimum / concavity |
| HM | -+ | as above | \([x_-,x_+]\) | exact contact | Section 5 |
| HM | -+ | as above | \([x_+,1.71],\lambda=.4\) | \(o/a,b\) | increasing |

Here is a direct verification of every initial barrier. In each case
the maximum possible margin of (9) on the indicated first-quadrant
interval is \(K+A\sin x-B\cos x\). It increases, and its value
at the listed right endpoint is negative.

| Types/signs | Right endpoint | \(K\) | \(A\) | \(B\) |
|---|---:|---|---|---|
| MH++ | .7 | \(a_2+b_2-1\) | \(a_0-1\) | \(a_0+1\) |
| MH+- | .1 | \(a_2+b_2-1\) | \(a_1+b_1-1\) | \(a_1-b_1+1\) |
| MH-- | .9 | \(a_1-b_1-1\) | \(a_1+b_1-1\) | \(a_1-b_1+1\) |
| MH-+ | 1.2 | \(a_1-b_1-1\) | \(a_0-1\) | \(a_0+1\) |
| HM++ | 1.1 | \(a_1+b_1-1\) | \(a_1-b_1-1\) | \(a_1+b_1+1\) |
| HM+- | .1 | \(a_1+b_1-1\) | \(a_2+b_2-1\) | \(a_2-b_2+1\) |
| HM-- | .4 | \(a_0-1\) | \(a_2+b_2-1\) | \(a_2-b_2+1\) |
| HM-+ | 1.3 | \(a_0-1\) | \(a_1-b_1-1\) | \(a_1+b_1+1\) |

For the maximum, \(a+\sigma b\) uses the last endpoint when
\(\sigma=+\) and the first when \(\sigma=-\).
The target expression \(DA-\tau CB\) decreases when \(\tau=+\)
and increases when \(\tau=-\): its derivative is \(-Dr-\tau C\),
where \(r<1,\ C\ge1,\ |D|\le1\). This verifies that the table
bounds entire arcs, including the endpoint states.

The support choices in the main cover have the following justifications.

* In MH++, the source derivative is
  \((k+.35)r+q-.35>(k+.35)(.252)+q-.35>0\).
* In MH+-, \(u-.55D>0\) and \(v-.55C<0\), so the H target
  functional decreases up to .61.
* In every MH negative-source row, \(U_s=k-.4>0\), so both
  M endpoints suffice. In MH-- on \([.9,1.2]\), the H target
  decreases. When \(U_t\ge0\), this is immediate from \(V_t<0\).
  When \(U_t<0\), its derivative is at most
  \[
  v-.253u-.4(.747\sin x+1.253\cos x)<0.
  \]
  The positive trigonometric sum is concave; both endpoint comparisons
  at .9 and 1.2 are strict.
* In MH-+ on \([1.2,1.3]\), \(U_t<0\) and
  \(V_t\ge.4(\sin1.3+\cos1.3)-v>0\); use the first H endpoint.
* In HM++, \(U_t=k-.5D>0\). Its target derivative is positive,
  because on \([1.1,1.42]\)
  \[
  V_t-rU_t\ge .5C(1.42)-q
       -.372[k-.5D(1.1)]>0.
  \]
* In HM+- on \([.1,.42]\), the M target derivative is at most
  \[
  .372k+q-\lambda(1.372\cos x+.628\sin x)<0.
  \]
  Use \(\lambda\ge.492,\ \cos x>.91,\ \sin x>.099\).
* In HM-- on \([.4,.6]\), the same target derivative is negative.
  The product \(\lambda(1.372\cos x+.628\sin x)\) decreases:
  its derivative is at most \(-.365+.494(.095)<0\).
  Here the parenthesis is above one and its derivative is below .095.
  At .6 its value, with \(\lambda=.421\), is still above
  \(.372k+q\).
* In HM+- on \([.42,.61]\), the H source has \(U_s=u-.43<0\)
  and \(V_s=v-.43>0\); use its first endpoint.
* In HM-+, \(U_t=k-.4D>0\), so both M endpoints suffice.

All unspecified entries in the cover use the unconditional support
(13). Thus no physical support condition has been inferred from a
numerical minimizer.

## 4. The scalar endpoint arguments

When the target support is a fixed endpoint \((A,B)\), and \(\lambda\)
is constant, the nonconstant part of (12) in the first quadrant is
\[
 x+A_*\cos x+B_*\sin x,\quad
 A_*=\lambda(1+A+\tau B)-.09,\quad
 B_*=\lambda(1-A+\tau B)-.09.                           \tag{14}
\]
The source support in each such row is independent of \(x\).

If \(A_*>0,B_*<0\), then the derivative of the second derivative
is positive. The first derivative is therefore convex. If its value at
the right endpoint is negative, the scalar has no interior minimum.
These three strict comparisons hold for MH+-, MH-+ on \([1.2,1.3]\),
HM++, and the first M endpoint in HM-+ before \(x_-\).
For MH-- on \([.9,1.2]\), \(A_*^2+B_*^2<1\), so the scalar
increases. For the last M endpoint in HM-+ before \(x_-\), both
coefficients in (14) are positive, so the scalar is concave.

After the quarter turn, the cosine coefficient in (14) becomes
\[
 A_*=\lambda(A+\tau B-1)+.09.
\]
For both M endpoint expressions in HM-+, its square plus \(B_*^2\)
is less than one, so both scalars increase on \([x_+,1.71]\).

For the target-H full-circle rows, write
\[
 N_\tau^2=(\tau u+\lambda D)^2+(\lambda C-v)^2.
\]
The full-circle scalar has, apart from a constant,
\[
 x+(2\lambda-.09)\sin x-.09\cos x-\mathcal R N_\tau.
                                                               \tag{15}
\]
Direct differentiation gives the useful exact identity
\[
 N_\tau''+\frac{N_\tau}{4}
 =\frac{(u^2+v^2-2\lambda^2)^2}{4N_\tau^3}\ge0.         \tag{16}
\]
The norm is nonzero since \(u^2+v^2\ne2\lambda^2\).
It increases on each interval below; differentiating its squared norm
reduces this assertion to the indicated positive sine/cosine comparison.

| Row | \(\lambda,\tau\) | Left endpoint | Norm upper bound | Norm increasing because |
|---|---|---:|---:|---|
| MH++ | .35,+ | .7 | \(N(.93)<.17\) | \((u+v)\sin .7>(v-u)\cos .7\) |
| MH-- late | .4,- | 1.2 | \(N(1.42)<.3\) | \((v-u)\sin1.2>(u+v)\cos1.2\) |
| MH-+ before | .4,+ | 1.3 | \(N(\pi/2)<.497\) | \((u+v)\sin1.3>(v-u)\cos1.3\) |

In each row, with left endpoint \(l\) and displayed norm bound \(n\),
\[
 (2\lambda-.09)\sin l>.09\cos l+\mathcal R n/4.
\]
Equations (15)--(16) therefore imply strict concavity on the whole
stated interval.

For MH-+ after \(x_+\), the scalar has the trigonometric term
\(.71(\sin x-\cos x)\). Here
\[
 N\ge.4958,\quad C>.85,\quad-\cos x<.14,\quad \sin x\le1.
\]
Consequently
\[
 F'\ge1+.71(.85)
 -\frac{\mathcal R(.4)[(v-u)(.14)+u+v]}{.4958}>0.        \tag{17}
\]
This establishes the last monotonicity claim in the cover.

For completeness, the following are lower numerators of all endpoint
costs used here. **Every integer is divided by \(10^8\)**.
They follow from (5), (12)--(13), \(3.14159<\pi<355/113\),
and the alternating Taylor bounds \(S_{11}\le\sin x\le S_{13}\),
\(C_{14}\le\cos x\le C_{12}\). At \(x_\pm\), use the angle .02
and the exact addition formulas. All numerators exceed \(89260000\).

| Scalar and support choice | Endpoint(s) | Lower numerator(s) |
|---|---|---|
| MH++ | .7, .93 | 106776723, 109518743 |
| MH+- | .1, .61 | 100633212, 93010614 |
| MH-- early, source first | .9 | 90998251 |
| MH-- early, source last | .9 | 91050397 |
| MH-- late, source first | 1.2, 1.42 | 92638138, 91540882 |
| MH-- late, source last | 1.2, 1.42 | 92690284, 91593028 |
| MH-+ early, source first | 1.2, 1.3 | 94038756, 92983950 |
| MH-+ early, source last | 1.2, 1.3 | 94090902, 93036096 |
| MH-+ before, source first | 1.3, \(x_-\) | 92926922, 89593095 |
| MH-+ before, source last | 1.3, \(x_-\) | 92979068, 89645241 |
| MH-+ after, source first / last | \(x_+\) | 90050494, 90102640 |
| HM++ | 1.1, 1.42 | 109685494, 91852287 |
| HM-+ before, target first | 1.3, \(x_-\) | 96455485, 89750524 |
| HM-+ before, target last | 1.3, \(x_-\) | 98084916, 89958817 |
| HM-+ after, target first / last | \(x_+\) | 89913160, 89803102 |

## 5. Exact contact across the quarter turn

The ordinary separated supports lose too much at this point. Retain the
contact equation instead. This section treats both ordered pairs with
signs \((-,+)\) on \(|x-\pi/2|\le.02\).

Fix the M state. Enlarge the H arc, for this lower-bound argument only,
to \(0\le B\le.8\). On this larger arc
\[
 A+1>2.68,\quad A(.8)<1.682,\quad r_H<.3,\quad
 \ell_H'=v-ur_H>0.                                    \tag{18}
\]
Also
\[
 .9998\le s\le1,\quad |c|\le.02,\quad
 .9798\le C,D\le1.02,\quad 2\le W_2\le2.02.
\]
Before the quarter turn \(C\ge1,D\le1\); afterwards
\(C\le1,D\ge1\).

For an M source and H target, define the contact root \(B(x)\) by
\[
 (a_M-b_M)+D A_H-C B=W_2.                              \tag{19}
\]
The left side decreases with \(B\). Its margin at zero is positive,
using
\[
 .649+.9798a_0>2.02;
\]
at .8 it is negative, using
\[
 1.028+1.02(1.682)-.9798(.8)<2.
\]
Hence there is a unique root in the enlarged arc. Every physically
feasible H target has transverse coordinate no greater than this root,
and therefore no larger H label. Thus its cost is at least the
contact cost.

Before the quarter turn, implicit differentiation gives
\[
 B'=A_H+1-\frac{2c}{C+Dr_H}>2.64.
\]
The derivative of the contact cost is at most
\[
 1.09-(v-.3u)(2.64)<0.                                \tag{20}
\]
After the quarter turn,
\[
 B'=\frac{C(A_H-1)+DB}{C+Dr_H}
 <\frac{1.616}{.9798}.
\]
Its cost derivative is at least
\[
 .91-v(1.616)/.9798>0.                                \tag{21}
\]

For an H source and M target, the contact equation is
\[
 a_H-b_H=W_2-D A_M+C B_M.                             \tag{22}
\]
It too has one root in \(0<b_H<.8\): the zero endpoint comparison is
\[
 a_0>2.02-.9798a_2+1.02b_2,
\]
and the .8 endpoint comparison follows from
\[
 1.682-.8<2-1.02(1.714)+.9798(.685).
\]
Every feasible H source has transverse coordinate below the root, so
again its cost is bounded below by the contact cost.

Before the quarter turn,
\[
 b_H'=\frac{CA_M+D(B_M+1)}{1+r_H}
 >\frac{.9798(3.398)}{1.3}.
\]
Its cost derivative is negative, since
\[
 (v-.3u)\frac{.9798(3.398)}{1.3}>1.09.
\]
After the quarter turn,
\[
 b_H'=\frac{C(A_M-1)+DB_M}{1+r_H}<1.7085,
 \qquad .91-v(1.7085)>0,
\]
so the contact cost increases. For each fixed M state, both ordered
contact costs are therefore minimized at \(x=\pi/2\).

At the quarter turn put \(d=a_M-b_M\). The H contact has
\(a_H-b_H=2-d\). Solving (1) gives the exact cost
\[
\begin{split}
 J(d)={}&\pi/4-2.2122495+ua_0+.5946665d\\
       &+.7447965\sqrt{4Q-(d+1)^2}
        -.284736\sqrt{4Q-(3-d)^2}.                    \tag{23}
\end{split}
\]
Here \(d\in[d_2,d_1]\), where \(d_i=a_i-b_i\).
The first radical is below 3.6 and the second exceeds 3.18.
Twice differentiation and
\[
 \frac{.744}{3.6^3}>\frac{.285}{3.18^3}
\]
show that \(J''<0\) on this entire interval. Hence only its endpoints
remain. The exact rational lower comparisons are
\[
 J(d_1)>\frac{2248043490506707}{2500000000000000}
       >.89921,
\]
\[
 J(d_2)>\frac{8927379093572303}{10000000000000000}
       >.89273>\gamma.                               \tag{24}
\]
This closes the full quarter strip, in both orders, without a dual gap.

## 6. Five fixed polynomial inequalities

Let \(S_j,C_j\) be the sine and cosine Taylor polynomials truncated at
degree \(j\). In the intervals used below,
\[
 S_7\le\sin x\le S_9,\quad C_{10}\le\cos x\le C_8,
 \qquad \sin x\le S_5,\quad C_6\le\cos x.
\]
All follow immediately from the alternating remainder estimates.

Use the lower and upper endpoint superscripts from (5), and set
\[
 c_M^-=3.14159/4+2.143075,\qquad
 L_{Mb}^-=c_M^--ka_2^++qb_2^-.
\]
For rows 1 and 2, take respectively
\[
 (\sigma,\lambda,[l,h])=(+1,.66-.4x,[.1,.42]),
 \quad(-1,.64-.365x,[.4,.6]).
\]
Put
\[
\begin{split}
 A(x)&=\lambda(1+a_2^--b_2^+)-.09,\\
 B(x)&=\lambda(1-a_2^+-b_2^+)-.09,\\
 T(x)&=x+.09+L_{Mb}^--\gamma+2\lambda-\sigma u\mathcal R_\sigma
             +A(x)C_6(x)+B(x)S_5(x),\\
 V(x)&=(\lambda-\sigma u)^2+(\lambda-v)^2,\\
 P(x)&=T(x)^2-2QV(x),                                \tag{25}
\end{split}
\]
where \(\mathcal R_+=\mathcal R^+\) and
\(\mathcal R_-=\mathcal R^-\).
Here \(A>0,B<0\), and \(T>.05\) in row 1 and \(T>.64\)
in row 2. The latter bounds follow even after dropping the nonnegative
cosine term and using \(S_5(x)\le x\). Thus \(P>0\) implies
the corresponding support scalar exceeds \(\gamma\).

For row 3 use \(\lambda=.43,\ [l,h]=[.42,.61]\), and
\[
 K=.09+c_M^-+k+\lambda-\lambda a_0^+-\gamma.
\]
For rows 4 and 5 use respectively
\((\lambda,[l,h])=(.42,[.6,.7])\) and \((.4,[.7,.93])\).
Choose the rational upper square-root bound
\[
 n_s=\frac{\lfloor10^{10}
       \sqrt{(u+\lambda)^2+(v-\lambda)^2}\rfloor+1}{10^{10}},
\]
verified by squaring, and put
\[
 K=.09+c_M^-+k+2\lambda+u\mathcal R^-
             -\mathcal R^+ n_s-\gamma.
\]
For each of rows 3--5 define
\[
\begin{split}
 T(x)&=x+K+(2\lambda-.09)S_7(x)-.09C_8(x),\\
 V(x)&=k^2+q^2+2\lambda^2
       +2\lambda[(k-q)S_9(x)-(k+q)C_{10}(x)],\\
 P(x)&=T(x)^2-2QV(x).                                \tag{26}
\end{split}
\]
Here \(T>0\), already from \(l+K-.09>0\).
The target-M norm squared is bounded above by \(V\), so
\(P>0\) again proves the required scalar inequality.

For a polynomial \(P\) on \([l,h]\), expand
\(P(l+(h-l)y)=\sum c_jy^j\).
Its Bernstein coefficients in degree \(n\) are
\[
 b_k=\sum_{j=0}^k c_j\frac{\binom kj}{\binom nj}.
                                                               \tag{27}
\]
The Bernstein basis is nonnegative and sums to one.
The following are strict lower numerators of every coefficient;
**divide each integer by \(10^8\)**.

| Row | Interval | Polynomial / basis degree | All coefficient lower numerators |
|---|---|---|---|
| 1 | [.1,.42] | 14 / 14 | 16425573, 14694001, 13058820, 11525877, 10099227, 8781206, 7572516, 6472316, 5478331, 4586958, 3793384, 3091710, 2475074, 1935778, 1465421 |
| 2 | [.4,.6] | 14 / 20 | 2790748, 2431170, 2097554, 1789715, 1507438, 1250488, 1018601, 811493, 628858, 470370, 335684, 224438, 136252, 70733, 27473, 6052, 6038, 26991, 68459, 129986, 211107 |
| 3 | [.42,.61] | 16 / 16 | 1993448, 2363210, 2711713, 3040020, 3349187, 3640262, 3914285, 4172290, 4415303, 4644341, 4860415, 5064530, 5257681, 5440858, 5615045, 5781215, 5940339 |
| 4 | [.6,.7] | 16 / 16 | 566759, 745406, 922183, 1097234, 1270698, 1442715, 1613426, 1782968, 1951483, 2119106, 2285977, 2452232, 2618009, 2783444, 2948672, 3113829, 3279051 |
| 5 | [.7,.93] | 16 / 16 | 5120799, 5999068, 6880379, 7766355, 8658605, 9558729, 10468314, 11388938, 12322168, 13269562, 14232666, 15213020, 16212155, 17231593, 18272847, 19337427, 20426832 |

Row 2 uses the same degree-14 polynomial expressed in degree 20.
Degree elevation uses only the identity
\[
 b^{(n+1)}_k=\frac{k}{n+1}b^{(n)}_{k-1}
                  +\left(1-\frac{k}{n+1}\right)b^{(n)}_k.
\]
No interval subdivision or sampling is involved. Substituting
(25)--(26) into (27) verifies all 87 positive coefficients.

## 7. Conclusion and arithmetic record

Sections 2--6 cover both ordered arcs, all four signs, all admissible
relative frame angles, both retained source axes, and their target-axis
images. The arc endpoints and all angle cuts are included. Therefore
\[
 \boxed{\delta-\frac9{50}h(\phi)+\psi_j-\psi_i>.8926}
\]
for the entire M/H entry. This closes all 16 ordered source-axis
branches of that unordered entry.

The optional replay
[verify_mid_high_whole_pair_hand.mjs](verify_mid_high_whole_pair_hand.mjs)
uses exact BigInt fractions and fixed Taylor/square-root brackets.
It verifies 225 strict rational comparisons, including 87 Bernstein
coefficient bounds and all 28 scalar endpoint values. The continuous
argument is the one above, with no numerical optimization premise.
The replay output is
[mid_high_whole_pair_hand_arithmetic.json](mid_high_whole_pair_hand_arithmetic.json).

This is one complete frame-table entry. It does not by itself close the
remaining frame entries, exceptional words, or global candidate capture.
\(\square\)
