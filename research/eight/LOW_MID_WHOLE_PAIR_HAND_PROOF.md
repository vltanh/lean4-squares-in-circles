# Low/middle whole-pair hand proof

## 1. The assertion and geometry

This proves the complete \(L/M\) frame-table entry
\[
 \delta-\frac9{50}h+\psi_j-\psi_i>.9005
 \tag{1}
\]
for consecutive exterior boundary states of either order, with every
genuine separating axis. The upstream hand common-point lemma gives
\(.76<\delta<3\pi/4\); no frame-span conclusion is assumed here.

Throughout \(Q=9789/2500\), \(R=\sqrt Q\), \(\beta=.18\), and every
terminating decimal is an exact rational. Put
\[
 a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\quad
 r=(b+1/2)/(a+1/2),\quad a_0=\sqrt{Q-1/4}-1/2.
\]
Then \(a'=-r\), \(r'=Q/(a+1/2)^3>0\). The arcs are
\[
 L:0\le b/a\le1/4,\qquad M:1/4\le b/a\le3/7.
\]
Write their common cut \((a_l,b_l)\), \(b_l=a_l/4\), and the upper
\(M\) endpoint \((a_h,b_h)\), \(b_h=3a_h/7\). The labels are
\[
 \begin{aligned}
 L&=\mu(a-a_0)+qb,& \mu&=.403875,&q&=1.089065,\\
 M&=c_M+pa+vb,&c_M&=-2.143075,&p&=1.489593,\quad v=1.580219.
 \end{aligned}
 \tag{2}
\]
Both labels increase and are concave as functions of \(b\).

Let \(\sigma,\tau\) be the signs of the source and target frame-to-center
angles \(\alpha_i,\alpha_j\). The actual centers in their own square
frames are \((a,-\sigma b)\), \((A,-\tau B)\). Set
\[
 \phi=\delta+\alpha_j-\alpha_i,\quad s=\sin\phi,\quad c=\cos\phi,\quad
 h=(|s|+|c|-1)/2,\quad W=1+h.
\]
The cost and retained source margins are
\[
 {\cal C}=\phi-\beta h+\sigma\ell_s-\tau\ell_t,\qquad
 M_f=\sigma b+As-\tau Bc-W,\quad
 M_e=a-Ac-\tau Bs-W.
 \tag{3}
\]
The hand cap/backward-axis reductions leave these two source axes and
their reflected-reversed target images. Reflection followed by reversal
preserves \(\phi,{\cal C}\) and changes ordered signs to
\((-\tau,-\sigma)\). Thus both orders and all source signs below give
complete coverage.

### 1.1. Root and angle bounds

Direct squaring in the circle equations gives
\[
 \begin{array}{c|cc}
 &\text{lower}&\text{upper}\\ \hline
 a_0&1.414575670&1.414575672\\
 a_l&1.298747247&1.298747249\\
 a_h&1.199256060&1.199256062
 \end{array}
 \qquad R<1.978788.
 \tag{4}
\]
Consequently
\[
 \begin{gathered}
 .30682<L(a_l,b_l)<.30683,\quad
 .3046<M(a_l,b_l)<.30461,\quad
 .4555<M(a_h,b_h)<.455511,\\
 .261<r_L<.459,\qquad .458<r_M<.597,\qquad 0\le\beta h<.0378.
 \end{gathered}
 \tag{5}
\]
The alternating arctangent bounds give
\[
 .24<\arctan(1/4)<.245,\qquad \arctan(3/7)<.405.
\]
All \(\phi\) are positive. Useful sign-dependent lower bounds are:

| order | \(++\) | \(+-\) | \(-+\) | \(--\) |
|---|---:|---:|---:|---:|
| \(L\to M\) | .76 | .11 | 1 | .35 |
| \(M\to L\) | .35 | .11 | 1 | .76 |

For \(++\) in \(L\to M\), and \(--\) in \(M\to L\), the common cut
makes the angular difference nonnegative, giving the stated .76
without rounding it down.

The following direct tails will repeatedly finish a case:

| cost signs/order | sufficient \(\phi\) |
|---|---:|
| \(L\to M,++\) | 1.4 |
| either order, \(+-\) | .64 |
| \(L\to M,--\), or \(M\to L,++\) | .95 |
| either order, \(-+\) | 1.71 |
| \(M\to L,--\) | 1.4 |

Each follows from (5). The smallest displayed tail, for example, is
\(1.4-.455511-.0378=.906689>.9005\).

## 2. Source minimization and the polynomial support lemma

Subtract any \(\lambda\ge0\) times a true margin in (3).
The source contribution is
\[
 F_s=\sigma\ell_s-\lambda\sigma b\quad(f),\qquad
 F_s=\sigma\ell_s-\lambda a\quad(e).
 \tag{6}
\]
The following simple facts select its minimum.

* On \(L\), \(L-.945b\ge-.00001\). It is concave, so check its two
  endpoints using (4).
* On \(L\), \(-L+.98b\ge-.00004\). Indeed
  \(L'(0)<.984\) and \(L''<-.22\), giving
  \(L-.98b\le.004b-.11b^2\le .004^2/.44<.00004\).
* On \(L\), \(-L+b\ge0\), since \(L'\le L'(0)<1\).
* On \(M\), \(M-\lambda b\) is minimized at the upper endpoint if
  \(\lambda\ge.8\), and at the lower endpoint if \(\lambda=.797\).
  Concavity reduces this to the endpoint comparisons
  \[
  .797<
  \frac{M(a_h,b_h)-M(a_l,b_l)}{b_h-b_l}<.8.
  \]
* On \(M\), \(-M+\lambda b\) is minimized at the lower endpoint for
  \(\lambda\ge1\): its derivative is
  \(pr+\lambda-v\ge .458p+1-v>0\).
* The source primary functional \(-L-.9a\) is minimized at the upper
  \(L\) endpoint; \(-M-\lambda a\) is minimized at the upper \(M\)
  endpoint for \(\lambda=.94,1\). Their derivatives are bounded above
  by \((\mu+.9)(.459)-q<0\) and \((p+1)(.597)-v<0\).

For a target functional, the circle bound is
\[
 UA+VB\ge-(U+V)/2-R\sqrt{U^2+V^2}.
 \tag{7}
\]
If \(U\ge0\), the functional is concave on an arc and its minimum is
at an endpoint. If \(U<0\), its derivative \(-Ur+V\) increases with
\(r\), selecting an endpoint whenever it has the required sign there.

We now record eight explicit polynomial bounds used later. All have
positive target sign. Write the target label as \(c_T+p_TA+q_TB\).
For \(T=L\), replace \(c_T=-\mu a_0\) by the adverse rational value
\[
 \bar c_L=-\mu(1.414575670);
\]
for \(T=M\), use \(\bar c_M=c_M\). Let \(F_s^-\) be the source lower
bound in the table below, and define
\[
 A(\phi)=\phi+\beta/2+F_s^--\bar c_T+(p_T+q_T)/2+\lambda/2.
\]
The full-circle lower bound is
\[
 F=A+B_s s+B_c c-RN,
 \tag{8}
\]
where the coefficients are:

| axis | quadrant | \(B_s\) | \(B_c\) | \(N^2\) |
|---|---|---|---|---|
| \(f\) | I | \(\lambda-.09\) | \(-.09\) | \(p_T^2+q_T^2+\lambda^2+2\lambda(p_Ts-q_Tc)\) |
| \(f\) | II | \(\lambda-.09\) | \(-\lambda+.09\) | same |
| \(e\) | I | \(-.09\) | \(-.09\) | \(p_T^2+q_T^2+\lambda^2-2\lambda(p_Tc+q_Ts)\) |
| \(e\) | II | \(-.09\) | \(-\lambda+.09\) | same |

Let \(S_m,C_m\) be Taylor polynomials through degree \(m\). Define
\(T(\phi)\) from \(A-.9005+B_s s+B_c c\) by using \(S_7\) for the
positive sine coefficient on \(f\), \(S_9\) for the negative sine
coefficient on \(e\), and \(C_8\) for every negative cosine coefficient.
Define \(V(\phi)\) by replacing \(s,c\) in \(N^2\) by \(S_9,C_{10}\)
on \(f\), and \(S_7,C_{10}\) on \(e\). These choices give
\[
 F-.9005\ge T-R\sqrt V,\qquad
 P:=T^2-QV.
 \tag{9}
\]
All multipliers below are positive; every replacement has the stated
direction. Positivity of \(T,P\) proves the desired strict bound.

| row | target, axis, quadrant | interval for polynomial | \(\lambda\) | \(F_s^-\) | lower bound for every Bernstein coefficient of \(T\) |
|---|---|---|---|---|---:|
| 1 | \(M,f,I\) | [.76,1.4] | .945 | −.00001 | 4 |
| 2 | \(M,f,I\) | [1,1.58] | .98 | −.00004 | 5 |
| 3 | \(M,f,II\) | [1.57,1.71] | .98 | −.00004 | 5 |
| 4 | \(L,f,I\) | [.4,.79] | \(1.146-.335\phi\) | \(.4555-.513966884\lambda\) | 1 |
| 5 | \(M,e,I\) | [1.5,1.58] | .9 | \(-.30683-1.298747249\lambda\) | 3 |
| 6 | \(M,e,II\) | [1.57,1.71] | .9 | same | 3 |
| 7 | \(L,e,I\) | [1.3,1.58] | .94 | \(-.455511-1.199256062\lambda\) | .5 |
| 8 | \(L,e,II\) | [1.57,1.71] | .94 | same | .8 |

A polynomial may be checked on a rational interval slightly larger than
its actual quadrant. The overlap \([1.57,1.58]\) contains \(\pi/2\);
the physical support formula is used only in its named quadrant.

Here are strict lower bounds for all Bernstein coefficients of \(P\)
on the indicated interval. Divide every integer by \(10^6\).

| row | Bernstein degree | coefficient lower numerators |
|---|---:|---|
| 1 | 16 | 298611, 278811, 258892, 239202, 220081, 201865, 184883, 169463, 155931, 144612, 135834, 129926, 127221, 128056, 132775, 141727, 155267 |
| 2 | 16 | 286934, 263872, 241970, 221471, 202620, 185660, 170838, 158401, 148603, 141698, 137948, 137617, 140977, 148304, 159880, 175992, 196933 |
| 3 | 16 | 183687, 269849, 356678, 444166, 532306, 621092, 710515, 800569, 891246, 982538, 1074437, 1166936, 1260028, 1353703, 1447954, 1542774, 1638153 |
| 4 | 18 | 50244, 46802, 43299, 39758, 36203, 32659, 29150, 25702, 22343, 19100, 16001, 13079, 10363, 7888, 5689, 3800, 2262, 1113, 394 |
| 5 | 18 | 747732, 735914, 723910, 711721, 699347, 686789, 674049, 661128, 648026, 634744, 621285, 607648, 593835, 579847, 565684, 551349, 536841, 522163, 507315 |
| 6 | 18 | 536389, 548221, 559794, 571110, 582174, 592988, 603556, 613881, 623966, 633814, 643429, 652813, 661971, 670904, 679617, 688111, 696391, 704459, 712319 |
| 7 | 18 | 117881, 125949, 132444, 137371, 140737, 142549, 142814, 141541, 138738, 134417, 128586, 121256, 112440, 102148, 90394, 77191, 62552, 46492, 29025 |
| 8 | 18 | 38888, 40901, 42846, 44725, 46539, 48289, 49976, 51602, 53168, 54675, 56123, 57515, 58851, 60132, 61359, 62533, 63655, 64726, 65746 |

The Bernstein basis is nonnegative and sums to one. Thus these eight
fixed rows prove \(T>0,P>0\) on the whole stated intervals, by finite
binomial expansion. In particular, row 4 covers its entire delicate
interval with one polynomial.

## 3. All secondary-axis cases

### 3.1. \(L\to M\)

For signs \(++\), use \(\lambda=.945\), the source floor \(-.00001\),
and polynomial row 1 on \([.76,1.4]\); then use the direct tail.

For signs \(+-\), the same source floor applies. The target coefficients
are \(U=p-\lambda s>0\), \(V=v-\lambda c>0\), so it suffices to use
each \(M\) endpoint \((A_j,B_j)\), label \(E_j\). The scalar bound is
\[
 F_j=\phi+\frac{\lambda+\beta}{2}+E_j-.00001
       -( \lambda A_j-C_\lambda)s+(C_\lambda-\lambda B_j)c,\qquad
 C_\lambda=(\lambda-\beta)/2.
 \tag{10}
\]
Its derivative is positive because
\[
 (\lambda A_j-C_\lambda)^2+(C_\lambda-\lambda B_j)^2<1.
\]
At \(\phi=.11\), both endpoint values exceed .94. This covers through
.64, where the direct tail starts.

For signs \(-+\), use \(\lambda=.98\), the source floor \(-.00004\),
and rows 2–3 from \(\phi=1\) through 1.71.

For signs \(--\), use \(\lambda=1\) and the source floor zero.
Both target coefficients \(p-s,v-c\) are positive, so again only
endpoints are needed. Formula (10) holds with no .00001 loss and
\(\lambda=1\). Its derivative is positive by the same squared-amplitude
test, and both values at \(\phi=.35\) exceed 1.01. The direct tail
starts at .95.

### 3.2. \(M\to L\), signs \(++\)

The secondary margin for \(\phi\le.4\) satisfies
\[
 M_f<.014+.915s-.5c
 \le .014+.915(.4)-.5(1-.4^2/2)<0.
\]
Thus \(\phi>.4\). On \([.4,.79]\), row 4 applies. Its multiplier is
at least \(1.146-.335(.79)>.8\), so the selected source upper endpoint
is valid throughout.

For \(.79\le\phi\le.95\), choose \(\lambda=.797\). The source minimum
is the lower \(M\) endpoint. The target minimum is the upper \(L\)
endpoint: its derivative there is bounded above by
\[
 \lambda(.459\sin\phi+\cos\phi)+.459\mu-q<0.
\]
The left side decreases after .79, and at .79 it is already negative
using \(\sin .79<.711,\cos .79<.704\).
The two endpoints have the same coordinates \((a_l,b_l)\), so the
remaining scalar is
\[
 F=\phi+\frac{\lambda+\beta}{2}+M(a_l,b_l)-L(a_l,b_l)-\lambda b_l
 +(C_\lambda-\lambda a_l)s+(C_\lambda+\lambda b_l)c.
\]
Its derivative is positive since
\[
 (\lambda a_l-C_\lambda)^2+(C_\lambda+\lambda b_l)^2<1.
\]
At .79 the adverse substitutions (4)–(5) give \(F>.9006\).
The direct tail closes \(\phi\ge.95\).

### 3.3. \(M\to L\), signs \(+-\)

Choose \(\lambda=.945\), selecting the upper \(M\) endpoint. On the
target \(L\) arc, \(V=q-\lambda c>0\). If \(U=\mu-\lambda s\ge0\),
the functional is concave; if \(U<0\), its derivative is positive.
Thus the two \(L\) endpoints suffice.

For target endpoint \((A_j,B_j)\), label \(E_j\), the scalar is
\[
 F_j=\phi+\frac{\lambda+\beta}{2}+M(a_h,b_h)-\lambda b_h+E_j
 -( \lambda A_j-C_\lambda)s+(C_\lambda-\lambda B_j)c.
\]
Both values at \(\phi=.11\) exceed .917. Moreover \(F_j'>-.029\)
uniformly, because
\[
 (\lambda a_0-C_\lambda)^2+C_\lambda^2<1.029^2.
\]
Therefore on \([.11,.64]\),
\[
 F_j>.917-.029(.64-.11)=.90163>.9005.
\]
The direct tail finishes the case.

### 3.4. \(M\to L\), signs \(-+\)

Choose \(\lambda=1.5\). The source minimum is the lower \(M\) endpoint.
Use the full-circle target support. It has the form
\[
 F=\phi+C+1.41s-.09c-RN\quad(I),\qquad
 F=\phi+C+1.41(s-c)-RN\quad(II),
\]
where
\[
 C=.84-M(a_l,b_l)+1.5b_l+\mu a_0+(\mu+q)/2,
 \qquad N^2=\mu^2+q^2+2.25+3(\mu s-qc).
\]
The norm identity
\[
 N''+N/4=(\mu^2+q^2-2.25)^2/(4N^3)>0
\]
gives concavity on both relevant quadrants. On \([1,\pi/2]\),
\(N\le N(\pi/2)<2.2\), so
\[
 F''<-1.41(.84)+.09(.55)+1.1<0.
\]
In quadrant II, \(RN/4<R(1.5+1.162)/4<1.41\), again giving \(F''<0\).
The endpoint estimates are
\[
 \begin{array}{c|ccc}
 \phi&1&\pi/2&1.71\\\hline
 N\text{ upper}&1.7&2.194&2.3\\
 F\text{ lower}&1&.97&1
 \end{array}
\]
and close the whole interval \([1,1.71]\).

### 3.5. \(M\to L\), signs \(--\)

Take \(\lambda=1\). The source minimum is the lower \(M\) endpoint.
For \(.76\le\phi\le1.4\), the target coefficients are
\(\mu-s<0,q-c>0\), so the minimum is the axial \(L\) endpoint. The
scalar bound is
\[
 F=\phi+.59-M(a_l,b_l)+b_l-(a_0-.41)s+.41c.
\]
At .76 it exceeds .97. Its derivative is \(>-.09\), because
\((a_0-.41)^2+.41^2<1.09^2\). Thus
\(F>.97-.09(.64)=.9124>.9005\) throughout.
The direct tail starts at 1.4.

## 4. All primary-axis cases

The primary margin is independent of the source sign. Since all labels
are nonnegative, proving the cost with source sign negative proves
both source signs. We therefore have four cases.

### 4.1. \(L\to M\), negative target

For \(0<\phi\le.95\),
\[
 M_e<.915-1.699c+.014s<0.
\]
For \(\phi>.95\), the lower cost \(\phi-\beta h-L+M\) is already
\(>.9005\) by the direct tail.

### 4.2. \(L\to M\), positive target

For \(0<\phi\le1.5\),
\[
 M_e<.915-1.699c-.8246s<0.
\]
The positive trigonometric sum is concave, so check 0 and 1.5;
both exceed .915. For \(\phi\ge1.5\), select \(\lambda=.9\).
The source minimum is the upper \(L\) endpoint, and polynomial rows
5–6 prove the bound through 1.71, followed by the direct tail.

### 4.3. \(M\to L\), negative target

For \(0<\phi\le1.1\),
\[
 M_e<.799-1.798c<0.
\]
On \([1.1,1.4]\), take \(\lambda=1\), selecting the upper \(M\)
endpoint. The target coefficients \(\mu+c,q-s\) are positive, so only
its two endpoints are needed. Their scalars are
\[
 F_j=\phi+.59-M(a_h,b_h)-a_h+E_j+(.41-B_j)s+(.41+A_j)c.
\]
They are concave on this interval because both trigonometric
coefficients are positive. All four endpoint comparisons, at 1.1
and 1.4, give \(F_j>1.01\). The direct tail closes larger angles.

### 4.4. \(M\to L\), positive target

For \(0<\phi\le1.3\),
\[
 M_e<.799-1.798c-.5s<0.
\]
Again the trigonometric sum is concave, and its two endpoints suffice.
For \(\phi\ge1.3\), use \(\lambda=.94\), selecting the upper \(M\)
endpoint. Polynomial rows 7–8 close through 1.71; then use the tail.

## 5. Coverage and arithmetic

Section 3 covers all eight ordered secondary sign cases.
Section 4 covers both source signs for each of the four ordered
primary cases. The reflected-reversed images cover all remaining
target axes. The closed intervals overlap at every change of formula;
none relies on an omitted orientation regime.

The standalone verify_low_mid_whole_pair_hand.js checks **305 strict
exact rational comparisons**, including all eight fixed polynomial
rows and their positive square-root comparison factors. It uses
integer fractions, finite Taylor sums and binomial expansion. The
continuous reduction and its coverage are given above.

Therefore the complete \(L/M\) entry is \(>.9005\).
