# Wrong word 0010111: all mixed quarter-one pairs

## Statement and scope

Every mixed core/outer entry of the rational role table on a quarter-one
edge of the word `0010111` has corrected cost

\[
 C>\frac{449}{500}=.898>\frac{17953}{20000}=.89765.
 \tag{1}
\]

This is a hand proof on the whole continuous state domains. It covers
**96 raw branches**: the allowed signs on edges 2, 4, 5, and 6, both
radial orders, and all four separating axes left by the exterior cap
and forward-gap lemmas. Its scalar checks are a fixed endpoint table,
four explicit polynomial inequalities on one full interval, and one
common contact-curvature polynomial. There is no optimizer-completeness
assumption, adaptive subdivision, or interval-tree premise.

The companion `verify_short_all_mixed_one_hand.js` evaluates 390 fixed exact
rational comparisons and prints every small table. It also regenerates
the normalized coefficients below from the original integer role
labels, checks their transcription, and counts the complete raw cover.
Its output is `short_all_mixed_one_hand_arithmetic.json`.
The earlier `SHORT_WRONG_WORD_ALL_MIXED_ZERO_HAND_PROOF.md` covers the
56 mixed zero-quarter branches. Together the two notes close **every
mixed C/O entry** of this wrong-word table. Neither note asserts its
outer/outer or core/core entries.

## 1. Coordinates and the finite cover

All terminating decimals in this note are exact rationals. Put

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 a_c=\frac7{12},\quad d_c=\frac12+\frac{\sqrt2}{24},\quad
 d=\sqrt{Q/2}-\frac12,\quad a_0=\sqrt{Q-\frac14}-\frac12.
 \tag{2}
\]

The outer boundary is

\[
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\qquad 0\le b\le d.
 \tag{3}
\]

The core boundary is the side \(a=a_c,\ 0\le b\le1/2\), followed by
the circle arc

\[
 (a-\tfrac12)^2+(b-\tfrac12)^2=\frac1{144},\qquad
 \frac12\le b\le a,\quad a\ge d_c.
 \tag{4}
\]

A source center in its own frame is \((a,-\sigma b)\), and the target
center is \((A,-\tau B)\). Let \(\phi\) be the lifted target-frame angle
minus the source-frame angle. The present four edges have

\[
 p_0-.7\le\phi\le p_0+.7,\qquad p_0=\frac\pi2.
 \tag{5}
\]

The full proof supplies (5) from the common frame interval, and supplies
the axis reduction from the exterior cap and common-point lemmas.
Write \(s=\sin\phi,\ c=\cos\phi\) and

\[
 W=\frac{1+s+|c|}{2}.
\]

The retained axes, in the numbering of the global role table, are

| Axis | Separation inequality |
|---:|---|
| 1, source \(+f\) | \(\sigma b+A s-\tau Bc\ge W\) |
| 2, target \(+e\) | \(-a c+\sigma b s+A\ge W\) |
| 3, target \(+f\) | \(a s+\sigma b c-\tau B\ge W\) |
| 4, source \(-e\) | \(a-Ac-\tau Bs\ge W\) |

The original signed role label is
\(\ell_i(a,\sigma b)=c_i+p_i a+\sigma q_i b\).
The exact integer coefficients are those in
`short_hand_labels.json`; the checker embeds the entire table.
Its pair cost is \(C=\phi+\ell_i-\ell_{i+1}\).

Reflection followed by reversal preserves \(\phi\) and \(C\). It sends
\((\sigma,\tau)\) to \((-\tau,-\sigma)\), sends each role label
\((c,p,q)\) to \((-c,-p,q)\), and takes the two target axes to the
corresponding source axes. Thus it suffices to prove the two source
axes for the following normalized rows:

\[
\begin{array}{ll}
\mathcal C:& C=\phi+c_*+\sigma g b-pA-\tau qB,
                 \qquad C\longrightarrow O,\\[2mm]
\mathcal O:& C=\phi+c_*+pa+\sigma qb-\tau gB,
                 \qquad O\longrightarrow C.
\end{array}
\tag{6}
\]

In the two tables below, all four numeric columns are integer
numerators with common denominator \(100000\). The index is only a
reference to a specific explicit row; it carries no extra hypothesis.
The `rev` column records the reflection/reversal just described.


### Normalized core-to-outer rows

| Index | Edge | rev | Signs | c* | p | q | g |
|---:|---:|:---:|:---:|---:|---:|---:|---:|
| 0 | 2 | no | −− | -39186 | -33147 | 113360 | 113855 |
| 1 | 2 | yes | ++ | 12917 | -9133 | 88074 | 62750 |
| 2 | 2 | no | −+ | 80483 | 51554 | 119909 | 113855 |
| 3 | 2 | yes | −+ | -6772 | -9133 | 88074 | 104729 |
| 4 | 4 | no | −− | -25682 | -20967 | 83048 | 104073 |
| 5 | 4 | yes | ++ | -24510 | -19335 | 76744 | 95269 |
| 6 | 4 | no | −+ | 1449 | 0 | 86884 | 104073 |
| 7 | 4 | yes | −+ | -25931 | -19335 | 76744 | 99195 |
| 8 | 4 | no | +− | -3767 | -20967 | 83048 | 58829 |
| 9 | 4 | yes | +− | 5267 | 0 | 71553 | 95269 |
| 10 | 4 | no | ++ | 23364 | 0 | 86884 | 58829 |
| 11 | 4 | yes | −− | 3846 | 0 | 71553 | 99195 |
| 12 | 5 | no | −− | 19687 | 18602 | 80996 | 95269 |
| 13 | 5 | yes | ++ | 21928 | 20967 | 83048 | 99173 |
| 14 | 5 | no | −+ | 21731 | 21826 | 83472 | 95269 |
| 15 | 5 | yes | −+ | 20507 | 20967 | 83048 | 95324 |
| 16 | 5 | no | +− | 21108 | 18602 | 80996 | 99195 |
| 17 | 5 | yes | +− | -5203 | 0 | 86884 | 99173 |
| 18 | 5 | no | ++ | 23152 | 21826 | 83472 | 99195 |
| 19 | 5 | yes | −− | -6624 | 0 | 86884 | 95324 |
| 20 | 6 | no | −+ | 7651 | 0 | 94766 | 99173 |
| 21 | 6 | yes | −+ | -21837 | -18602 | 80996 | 108816 |
| 22 | 6 | no | ++ | 9072 | 0 | 94766 | 95324 |
| 23 | 6 | yes | −− | -23881 | -21826 | 83472 | 108816 |

### Normalized outer-to-core rows

| Index | Edge | rev | Signs | c* | p | q | g |
|---:|---:|:---:|:---:|---:|---:|---:|---:|
| 0 | 2 | no | −− | 12917 | 9133 | 88074 | 62750 |
| 1 | 2 | yes | ++ | -39186 | 33147 | 113360 | 113855 |
| 2 | 2 | no | −+ | -6772 | 9133 | 88074 | 104729 |
| 3 | 2 | yes | −+ | 80483 | -51554 | 119909 | 113855 |
| 4 | 4 | no | −− | -24510 | 19335 | 76744 | 95269 |
| 5 | 4 | yes | ++ | -25682 | 20967 | 83048 | 104073 |
| 6 | 4 | no | −+ | -25931 | 19335 | 76744 | 99195 |
| 7 | 4 | yes | −+ | 1449 | 0 | 86884 | 104073 |
| 8 | 4 | no | +− | 5267 | 0 | 71553 | 95269 |
| 9 | 4 | yes | +− | -3767 | 20967 | 83048 | 58829 |
| 10 | 4 | no | ++ | 3846 | 0 | 71553 | 99195 |
| 11 | 4 | yes | −− | 23364 | 0 | 86884 | 58829 |
| 12 | 5 | no | −− | 21928 | -20967 | 83048 | 99173 |
| 13 | 5 | yes | ++ | 19687 | -18602 | 80996 | 95269 |
| 14 | 5 | no | −+ | 20507 | -20967 | 83048 | 95324 |
| 15 | 5 | yes | −+ | 21731 | -21826 | 83472 | 95269 |
| 16 | 5 | no | +− | -5203 | 0 | 86884 | 99173 |
| 17 | 5 | yes | +− | 21108 | -18602 | 80996 | 99195 |
| 18 | 5 | no | ++ | -6624 | 0 | 86884 | 95324 |
| 19 | 5 | yes | −− | 23152 | -21826 | 83472 | 99195 |
| 20 | 6 | no | −+ | -21837 | 18602 | 80996 | 108816 |
| 21 | 6 | yes | −+ | 7651 | 0 | 94766 | 99173 |
| 22 | 6 | no | ++ | -23881 | 21826 | 83472 | 108816 |
| 23 | 6 | yes | −− | 9072 | 0 | 94766 | 95324 |


## 2. Elementary support and curvature rules

The following rules will be used without changing their domains.

* The outer-circle support is
  \[
  xa+yb\ge-\frac{x+y}{2}-R\sqrt{x^2+y^2}.
  \tag{7}
  \]
  If \(x<0,y>0\), the exact outer-arc minimum is \(x a_0\):
  the derivative in \(b\) is \(-x(b+1/2)/(a+1/2)+y>0\).

* On the core side, an affine function reaches its minimum at an
  endpoint. On the core corner, if its \(a\)-coefficient is nonnegative,
  it is concave in \(b\), so again only the join and diagonal endpoints
  matter. If both coefficients are negative, the whole-circle lower
  support
  \[
  \frac{x+y}{2}-\frac1{12}\sqrt{x^2+y^2}
  \tag{8}
  \]
  is valid on the full core: the side minimum is at its join, which
  belongs to this circle. If \(x<0,y\ge0\), the core minimum is \(x a_c\).

* If \(N^2=p^2+q^2+\lambda^2+
  2\lambda(p\sin\phi-q\cos\phi)\), direct differentiation gives
  \[
  N''+\frac N4=\frac{(p^2+q^2-\lambda^2)^2}{4N^3}\ge0.
  \tag{9}
  \]
  Every use below has \(N>0\); indeed
  \(p+\lambda\sin\phi>0\). Also \(N'>0\), because
  \(p\cos\phi+q\sin\phi>0\). The latter follows row by row from
  \(q(.764)-|p|(.645)>0\).

The fixed scalar comparisons use

\[
 .8992<d,\quad1.4145<a_0<1.415,\quad
 .5589<d_c<.559,\quad
 \sin\phi>.764,\quad|\cos\phi|<.645.
 \tag{10}
\]

These statements follow by squaring rational root brackets and the
alternating sine/cosine series at \(7/10\). The checker proves
\(3.141592653589793238<\pi<3.141592653589793239\) by the Machin identity,
then uses this enclosing rational interval in its fixed endpoint
comparisons.

For source-primary separation (axis 4), the source sign does not occur
in the separation inequality. For each role with two source signs,
\(\ell_i(a,b)>\ell_i(a,-b)\) on both boundary curves. To check this
directly, the difference is \(c+pa+qb\), its derivative in \(b\) is at
least \(q-|p|>0\), and its value at \(b=0\) is positive. The checker
prints the eight endpoint and eight derivative comparisons for roles
3--6. Reflection preserves this comparison. Thus the 48 primary rows
reduce to 28 rows with negative source sign.

The retained negative-source indices, in either normalized table, are

\[
\begin{array}{c|l}
\tau=+&2,3,6,7,14,15,20,21\\
\tau=-&0,4,11,12,19,23.
\end{array}
\tag{11}
\]

## 3. Core source, source-secondary separation: all 24 rows

Subtract \(\lambda\) times
\(\sigma b+A\sin\phi-\tau B\cos\phi-W\ge0\) from (6).
The core coefficient is \(\sigma(g-\lambda)b\).
The two outer coefficients are

\[
 X=-p-\lambda\sin\phi,\qquad
 Y=\tau(\lambda\cos\phi-q).
 \tag{12}
\]

### 3.1 Negative target sign

Take \(\lambda=g\). Then \(X<0,Y>0\), and (7) is replaced by the exact
axial support \(Xa_0\). This gives

\[
 F=\phi+c_*-pa_0+\frac g2+\frac g2|\cos\phi|
                  -g(a_0-\tfrac12)\sin\phi.
 \tag{13}
\]

On the upper half \(F'>1\). On the lower half,

\[
 F'\ge1-g\sqrt{\frac14+.915^2}.
\]

The following three strict comparisons, applied to the ten indicated
table rows, complete this class. The third column is a lower bound for
(13) at \(\phi=p_0-.7\).

| Range of \(g\) | Lower bound for \(F'\) | Left endpoint |
|---|---:|---:|
| \(g\le.954\) | \(0\) | .921 |
| \(.954<g\le1\) | −.043 | .940 |
| \(g>1\), hence \(g<1.139\) | −.19 | 1.038 |

The possible losses on an interval of length .7 are respectively zero,
less than .0301, and less than .133. Every resulting lower bound
exceeds .898.

### 3.2 Positive target sign

The chosen multipliers below have \(\sigma(g-\lambda)\ge0\), so the
remaining core term can be discarded. If the source sign is negative,
feasibility forces \(\phi>1\) on the lower half: dropping its negative
\(b\)-term and the negative target-\(B\) term gives the necessary cap

\[
 (a_0-\tfrac12)\sin\phi-\tfrac12\cos\phi-\tfrac12\ge0,
\]

whose left side is increasing and is negative at \(\phi=1\).

Applying (7) gives

\[
\begin{aligned}
 F_-&=\phi+c_*+\frac{\lambda+p+q}{2}
                      +\lambda\sin\phi-RN,\\
 F_+&=\phi+c_*+\frac{\lambda+p+q}{2}
                      +\lambda(\sin\phi-\cos\phi)-RN.
\end{aligned}
\tag{14}
\]

Here the minus/plus subscript means the lower/upper half of (5).
For each row use the four fixed intervals

\[
[\ell,1.25],\ [1.25,p_0],\ [p_0,p_0+.3],\
[p_0+.3,p_0+.7],
\]

where \(\ell=1\) for negative source sign and \(\ell=p_0-.7\)
for positive source sign. By (9), on a lower-half interval \([u,v]\),

\[
 F_-''\le-\lambda\sin u+\frac R4N(v)<0.
\]

On an upper-half interval replace \(\sin u\) by
\(\sin u-\cos u\). The latter is increasing on this strip. Thus both
envelopes are strictly concave on every listed interval, and their
minima occur among its endpoints. The next table gives the exact
multipliers, a strictly smaller lower bound for all endpoint values,
and a positive lower bound for every concavity reserve
\(\lambda s(u)-RN(v)/4\). These are fixed comparisons of (14).


| Index | λ | Endpoint lower bound | Concavity reserve |
|---:|---:|---:|---:|
| 1 | .6275 | 0.971666925212 | 0.043223934 |
| 2 | 1.13855 | 0.898112380949 | 0.040333968 |
| 3 | 1.115 | 0.898109783924 | 0.346527583 |
| 5 | .95269 | 0.905454212610 | 0.307940880 |
| 6 | 1.04073 | 0.898101165491 | 0.278762372 |
| 7 | 1.0853 | 0.898112641104 | 0.404204131 |
| 10 | .58829 | 0.966781061546 | 0.002316070 |
| 13 | .99173 | 0.907728025328 | 0.134250134 |
| 14 | .95269 | 0.898109171714 | 0.167489021 |
| 15 | .95324 | 0.898103109402 | 0.172292622 |
| 18 | .99195 | 0.907600249820 | 0.129602390 |
| 20 | 1.1014 | 0.898104085447 | 0.284319862 |
| 21 | 1.1274 | 0.898107125855 | 0.410401258 |
| 22 | .95324 | 0.905428851015 | 0.178866103 |


## 4. Outer source, source-secondary separation: all 24 rows

Take \(\lambda=q\), so the source transverse term cancels. Its remaining
lower bound is \(m=pd\) when \(p\ge0\), and \(m=pa_0\) when \(p<0\).
The core coefficients are

\[
 u=-q\sin\phi,\qquad v=\tau(q\cos\phi-g).
\]

Every row has \(g>q(.645)\). For negative target sign the core minimum
is its axial endpoint, giving

\[
 F=\phi+c_*+m+\frac q2+\frac q2|\cos\phi|
                          -\frac q{12}\sin\phi.
 \tag{15}
\]

Its derivative is positive, since
\(q<1.2\) and \(1-1.2\sqrt{1/4+1/144}>0\).
Its left endpoint exceeds 1.381 for every applicable row.

For positive target sign both core coefficients are negative. Rule
(8) gives

\[
\begin{aligned}
 F_-&=\phi+c_*+m+\frac{q-g}{2}+q\cos\phi-\frac N{12},\\
 F_+&=\phi+c_*+m+\frac{q-g}{2}-\frac N{12},\\
 N^2&=q^2+g^2-2qg\cos\phi.
\end{aligned}
\tag{16}
\]

Here \(|N'|\le\min(q,g)\), by either of the two vector representations
of this distance. Thus \(F_+\) is increasing. On the lower half, if
\(q\le.95\), then \(F_-'>-.03\), and its left value is greater than
1.103. If \(q>.95\), then \(F_-'>-.3\), and its left value is greater
than 1.424. Both continuations over length .7 stay well above .898.
This proves every row in this class.

## 5. Core source, source-primary separation: all 24 rows

By the sign comparison in Section 2, only the fourteen rows in (11)
remain. Their source sign is negative.

### 5.1 Positive target sign

There is no feasible lower-half state. Indeed
\(a-Ac-Bs-W\le1/12-(A+1/2)c-(B+1/2)s<0\)
there. On the upper half write \(\phi=p_0+x\).
The necessary cap

\[
 \frac1{12}+(a_0-\tfrac12)\sin x-\frac12\cos x\ge0
\]

is negative at \(x=.4\) and increasing before it. Thus \(x>.4\).
Take \(\lambda=1.6\). The core support for
\(-\lambda a-gb\) is (8), and the outer coefficients
\(\lambda\cos\phi-p<0\), \(\lambda\sin\phi-q>0\)
give the exact axial support. Therefore

\[
 F=p_0+x+c_*-\frac g2-\frac{\sqrt{1.6^2+g^2}}{12}
       -pa_0+.8\cos x-1.6(a_0-\tfrac12)\sin x.
 \tag{17}
\]

This is decreasing on \([.4,.7]\), since
\(.8(.389)+1.6(.9145)(.764)>1\).
For all eight rows its value at .7 exceeds 1.216.

### 5.2 Negative target sign

Set \(\lambda=q/\sin\phi\), cancelling the target transverse term.
Let \(P=pa_0\) for \(p\ge0\), and \(P=pd\) for \(p<0\). Core support
and the appropriate bound on \(A\) give

\[
\begin{aligned}
 F_-={}&\phi+c_*-\frac g2-P+\frac q2
       +q(d+\tfrac12)\cot\phi
       -\frac1{12}\sqrt{g^2+q^2\csc^2\phi},\\
 F_+={}&\phi+c_*-\frac g2-P+\frac q2
       +q(a_0-\tfrac12)\cot\phi
       -\frac1{12}\sqrt{g^2+q^2\csc^2\phi}.
\end{aligned}
\tag{18}
\]

The first expression decreases. Multiplying its derivative by
\(\sin^2\phi\) bounds it above by

\[
 1-\cos^2\phi-q(d+\tfrac12)+\frac q{12}\cos\phi
 \le1-1.399q+\frac{q^2}{576}<0.
\]

The last inequality is checked for each of the six exact \(q\)'s.
The common quarter value in (18) exceeds 1.28 in every row. For the
upper-half continuation, the possible change from that value is at
least

\[
 x-1.134(.915)\tan x-\frac{1.134}{12}(\sec x-1),
 \qquad0\le x\le.7.
\]

This is concave, vanishes at zero, and exceeds −.21 at .7.
Thus every upper-half value exceeds 1.07, completing this class.

## 6. Outer source, positive core target: all source-primary rows

Again keep the eight negative-source rows in (11). Put

\[
 S(\lambda)=\frac{\lambda-p+q}{2}
                 -R\sqrt{(\lambda-p)^2+q^2}.
 \tag{19}
\]

This is the full-circle source support after subtracting
\(\lambda(a-Ac-Bs-W)\).

### 6.1 Lower half

A core-corner target is impossible: \(A\ge d_c,B\ge1/2\) would require

\[
 a\ge\frac12+(d_c+\tfrac12)\cos\phi+\sin\phi
       \ge\frac32>a_0.
\]

The target is therefore on the side \(A=a_c\).
Even with \(B=0\), the cap
\(a_0-1/2-(13/12)\cos\phi-(1/2)\sin\phi\)
is negative at 1.12 and increasing before it. Hence \(\phi>1.12\).

For each chosen positive constant \(\lambda\), only the two side
endpoints matter. Their lower envelopes are

\[
 F_a=\phi+c_*+\lambda W+S(\lambda)+\lambda a_c\cos\phi,
 \qquad
 F_b=F_a+\frac{\lambda\sin\phi-g}{2}.
 \tag{20}
\]

Both are strictly concave on the lower half. The next fixed table
checks their values at both endpoints of each listed interval.
Its union covers \([1.12,p_0]\) for every applicable row.


| Index | Interval | λ | Lower bound for both envelopes |
|---:|---|---:|---:|
| 2 | [1.12,1.25] | 1.3 | 0.978583703 |
| 2 | [1.25,π/2] | 1.115 | 0.898109783 |
| 3 | [1.12,1.25] | 1.4 | 0.982827762 |
| 3 | [1.25,π/2] | 1.13855 | 0.898112380 |
| 6 | [1.12,1.25] | 1.3 | 0.973793319 |
| 6 | [1.25,π/2] | 1.0853 | 0.898112641 |
| 7 | [1.12,1.3] | 1.3 | 0.957894154 |
| 7 | [1.3,1.4] | 1.1 | 0.919700340 |
| 7 | [1.4,π/2] | 1.04073 | 0.898101165 |
| 14 | [1.12,1.3] | 1.2 | 0.913507945 |
| 14 | [1.3,1.4] | 1.06 | 0.900485162 |
| 14 | [1.4,1.45] | 1.01 | 0.898485672 |
| 14 | [1.45,1.51] | .96 | 0.898257746 |
| 14 | [1.51,π/2] | .95324 | 0.898103109 |
| 15 | [1.12,1.3] | 1.2 | 0.913258669 |
| 15 | [1.3,1.4] | 1.06 | 0.900321608 |
| 15 | [1.4,1.45] | 1.01 | 0.898367386 |
| 15 | [1.45,1.51] | .96 | 0.898312067 |
| 15 | [1.51,π/2] | .95269 | 0.898109171 |
| 20 | [1.12,1.25] | 1.3 | 0.979112440 |
| 20 | [1.25,π/2] | 1.1274 | 0.898107125 |
| 21 | [1.12,π/2] | 1.1014 | 0.898104085 |


### 6.2 Upper half

For each row retain its final multiplier from the preceding table.
It satisfies \(g\le\lambda\le1.14\). The core bounds
\(A\le a_c,\ B\le d_c\) give, with \(\phi=p_0+x\),

\[
 C\ge F_a-d_c\max(0,g-\lambda\cos x).
 \tag{21}
\]

At \(x=0\) the correction vanishes. The one-sided derivative of the
right side is at least

\[
 1-1.14\left(1.059(.645)+\frac1{12}\right)>0.
\]

Thus it stays above its quarter value, which is already greater than
.898. This proves the whole positive-target primary class.

## 7. Outer source, negative core target: straight side

Only the six negative-target indices in (11) remain. On the core side
\(A=a_c\), the two endpoint envelopes are

\[
 F_a=\phi+c_*+\lambda W+S(\lambda)+\lambda a_c\cos\phi,
 \qquad
 F_b=F_a+\frac{g-\lambda\sin\phi}{2}.
 \tag{22}
\]

For a fixed positive \(\lambda\), both are concave on the lower half.
For indices 0 and 11, the following four rows therefore finish the
whole side interval.


| Index | Interval | λ | Lower bound |
|---:|---|---:|---:|
| 0 | [π/2−.7,1.1] | 1.11 | 0.928395026 |
| 0 | [1.1,π/2] | .958 | 0.921302267 |
| 11 | [π/2−.7,1.1] | 1.11 | 0.928347895 |
| 11 | [1.1,π/2] | .958 | 0.931779418 |


For the other four rows, set \(\lambda=g/\sin\phi\), cancelling \(B\).
The two envelopes in (22) then coincide, and simplify to

\[
 F=\phi+c_*+\frac g{\sin\phi}
    +\frac{-p+q+g}{2}+\frac{13g}{12}\cot\phi
       -R\sqrt{(g/\sin\phi-p)^2+q^2}.
 \tag{23}
\]

Here is a direct polynomial proof of \(F>.898\) on the whole lower
half. It uses the slightly larger rational interval
\(I=[.87,1.571]\). Let

\[
\begin{aligned}
 S_-&=x-\frac{x^3}{6}+\frac{x^5}{120}-\frac{x^7}{5040},\\
 S_+&=S_-+\frac{x^9}{362880},\\
 C_-&=1-\frac{x^2}{2}+\frac{x^4}{24}-\frac{x^6}{720}
              +\frac{x^8}{40320}-\frac{x^{10}}{3628800},\\
 A&=c_*+\frac{-p+q+g}{2}-.898,\\
 T&=(x+A)S_-+g+\frac{13g}{12}C_-.
\end{aligned}
\tag{24}
\]

The coefficient \(x+A\) is positive throughout \(I\).
The alternating series give \(S_-\le\sin x\le S_+\) and
\(C_-\le\cos x\). Define

\[
 V=g^2-2gp\,S_\diamond+(p^2+q^2)S_+^2,\qquad
 S_\diamond=\begin{cases}S_-,&p\ge0,\\S_+,&p<0.\end{cases}
 \tag{25}
\]

Then \(T\) is at most the nonradical term in
\((F-.898)\sin x\), and \(V\) is at least its squared radical
argument. Consequently \(T>0\) and \(T^2-QV>0\) imply (23).

For completeness, Appendix A lists positive lower bounds for every
degree-20 Bernstein coefficient of \(T^2-QV\) on \(I\).
The respective minimum Bernstein coefficients of \(T\) exceed

\[
\begin{array}{c|rrrr}
\text{index}&4&12&19&23\\ \hline
\min\operatorname{Bern}(T)&1.992945571&2.607227219&
2.621943521&2.393531686.
\end{array}
\tag{26}
\]

Thus all four inequalities hold on the entire interval, without
partitioning it or locating a minimizing point.

## 8. Outer source, negative core target: corner

### 8.1 The late part \(1.2\le\phi\le p_0\)

Take the single multiplier \(\lambda=.85\) in all six rows. The
coefficient of the core coordinate \(A\) is nonnegative, so its
corner functional is concave in \(B\). Its minimum is at the join
\((a_c,1/2)\) or diagonal \((d_c,d_c)\). Put

\[
 G=\phi+c_*+\lambda W+S(\lambda).
\]

The corresponding lower envelopes are

\[
 F_j=G+\lambda a_c\cos\phi+\frac{g-\lambda\sin\phi}{2},
 \qquad
 F_d=G+d_c\{\lambda(\cos\phi-\sin\phi)+g\}.
 \tag{27}
\]

The first is concave. The second is increasing, because its derivative
is bounded below by

\[
 1-.85\sqrt{(d_c+\tfrac12)^2+(d_c-\tfrac12)^2}>0.
\]

Their fixed endpoint values at \(1.2,p_0\) exceed .903 in all six
rows. This proves the late corner part.

### 8.2 The early part: reduce the whole corner to its endpoints

Fix \(p_0-.7\le\phi\le1.2\). The source-primary contact forces

\[
 a\ge h(B):=W+A(B)\cos\phi-B\sin\phi.
\]

Define the continued outer label

\[
 L(a)=pa-q\left(\sqrt{Q-(a+\tfrac12)^2}-\tfrac12\right).
 \tag{28}
\]

For each of the six rows, throughout the enlarged range
\(1.32\le u=a+1/2\le1.7\),

\[
 -.263<\frac pq<.253,\qquad q>.767,\qquad L'(a)>0.
 \tag{29}
\]

The ratio \(u/\sqrt{Q-u^2}\) is increasing, so the same positive-derivative
bound continues up to the actual outer axial endpoint. In particular,
even if \(h(B)<d\), monotonicity gives
\(L(a)\ge L(h(B))\) for every feasible outer source. Thus a valid
contact lower bound on the entire corner is

\[
 \phi+c_*+L(h(B))+gB.
 \tag{30}
\]

We now prove (30) strictly concave in \(B\). Put
\(t=\sqrt{Q-u^2}\). Direct differentiation of (28) gives

\[
 \frac{L''}{L'}=
 \frac{Q}{t^2\{u+(p/q)t\}}
 \le\frac Q{D(u)},\qquad
 D(u)=(Q-u^2)\{u-.263\sqrt{Q-u^2}\}.
 \tag{31}
\]

On \([1.32,1.7]\), \(D\) is strictly concave:

\[
 D''=-6u+.789\frac{Q-2u^2}{\sqrt{Q-u^2}}<0.
\]

Indeed \(t>1.01\), and
\(6(1.32)>.789\{Q-2(1.32)^2\}/1.01\).
The core contact \(u=h(B)+1/2\) decreases in both \(B\) and \(\phi\).
Its endpoint values and four comparisons of (31) give

| Frame interval | Range of \(u\) | Bound on \(L''/L'\) | Lower bound for \(\cos\phi\) |
|---|---|---:|---:|
| \([p_0-.7,1.05]\) | \([1.47,1.7]\) | \(<2.8\) | \(>.497\) |
| \([1.05,1.2]\) | \([1.32,1.54]\) | \(<2.12\) | \(>.362\) |

To verify the third column, concavity makes it enough to check
\(2.8D(1.47)>Q,\ 2.8D(1.7)>Q\), or respectively
\(2.12D(1.32)>Q,\ 2.12D(1.54)>Q\).
No intermediate points are required.

On the core corner \(A''\le-12\) and
\(|h_B|\le\sin\phi+\cos\phi\le\sqrt2\). Therefore

\[
 \frac{d^2}{dB^2}\{L(h(B))+gB\}
 =L''h_B^2+L'\cos\phi\,A''
 <L'\{2K-12c_0\}<0,
 \tag{32}
\]

using either \((K,c_0)=(2.8,.497)\) or \((2.12,.362)\).
This proves that the whole early corner has its minimum at its join
or diagonal. It removes the convex-hull loss that would result from
taking the full core-circle support in this regime.

### 8.3 A common strong-convexity bound for the two endpoint curves

For either endpoint write

\[
\begin{array}{c|ccc}
 & A_* & B_* & b_C\\\hline
\text{join}&13/12&0&1/2\\
\text{diagonal}&d_c+1/2&d_c-1/2&d_c
\end{array}
\]

and set

\[
 u=1+A_*\cos\phi-B_*\sin\phi,\qquad h=u-\frac12.
\]

The endpoint contact cost is

\[
 H(\phi)=\phi+c_*+ph
       -q\left(\sqrt{Q-u^2}-\frac12\right)+gb_C.
 \tag{33}
\]

Both endpoints satisfy \(K=A_*^2+B_*^2>1.12479\).
Writing \(k=p/q\), direct differentiation gives

\[
 \frac{(Q-u^2)^{3/2}}q H''
 =Q\{K-(u-1)^2\}-u(u-1)(Q-u^2)
           -k(u-1)(Q-u^2)^{3/2}.
 \tag{34}
\]

Define the explicit polynomials

\[
\begin{aligned}
 E(u)&=Q\{1.12479-(u-1)^2\}-u(u-1)(Q-u^2),\\
 A(u)&=\frac{.65}{.767}+.253(u-1),\\
 P(u)&=E(u)^2-A(u)^2(Q-u^2)^3.
\end{aligned}
\tag{35}
\]

Their positive Bernstein coefficient bounds on the single interval
\([1.32,1.7]\) appear in Appendix B. Since \(E,A,P>0\), equations
(29), (34), and (35) prove

\[
 H''>.65
 \tag{36}
\]

on every early endpoint curve. Notice that this is one curvature
proof for all twelve curves, not twelve separate localization claims.

At an interior reference \(r\), (36) gives the global lower bound

\[
 H(\phi)\ge H(r)+H'(r)(\phi-r)+.325(\phi-r)^2
 \ge H(r)-\frac{H'(r)^2}{1.3}.
 \tag{37}
\]

If \(r=p_0-.7\) and \(H'(r)>0\), the function is increasing, so its
left value suffices. The next table checks exactly these twelve
fixed comparisons. Each displayed completed lower bound exceeds .898.


| Index | Endpoint | Reference | Bound after (37) |
|---:|---|---:|---:|
| 0 | join | 1.17 | 0.926218794285 |
| 0 | diag | 1.075 | 0.898114752900 |
| 4 | join | 1.149 | 0.907692992851 |
| 4 | diag | 1.047 | 0.898117048798 |
| 11 | join | 1.061 | 0.931511617684 |
| 11 | diag | 0.962 | 0.898101173344 |
| 12 | join | π/2−.7 | 0.906056905970 |
| 12 | diag | π/2−.7 | 0.898108602258 |
| 19 | join | π/2−.7 | 0.905928100610 |
| 19 | diag | π/2−.7 | 0.898110957785 |
| 23 | join | 1.148 | 0.907547595798 |
| 23 | diag | 1.056 | 0.898107383461 |


## 9. Negative core target: the whole upper half

The six remaining upper-half cases admit a short common bound.
Take \(\lambda=g\). The core coefficients are

\[
 u=g\cos\phi\le0,\qquad v=g(1-\sin\phi)\ge0.
\]

Its exact minimum is the axial endpoint, so \(F_a\) from (22) applies.
At the quarter it exceeds .905 in all six rows. With
\(\phi=p_0+x\), its derivative is at least

\[
 1-1.139\left(\frac{.645}{2}+\frac1{12}\right)>0.
\]

This proves the whole upper half and completes Section 8's corner
cases as well as Section 7's side cases.

## 10. Assembly and strictness

Sections 3 and 4 prove both secondary radial orders for all 48
normalized rows. The source-sign comparison reduces the 48 primary
rows to the fourteen cases in each radial order; Sections 5--9 prove
all 28 of those. Reflection/reversal in Section 1 restores the target
axes with the same cost and same frame interval. Therefore all
96 raw mixed quarter-one cases satisfy (1).

All reductions use lower bounds on the actual SAT-feasible domain.
Where a state domain is enlarged, the proof explicitly bounds the
larger domain; the only contact reduction uses the monotonicity and
concavity calculations (28)--(32). The finite endpoint tables therefore
form a complete continuous proof, independent of how the coefficients
or reference points were originally discovered.

## Appendix A. Four whole-interval polynomial inequalities

For a polynomial \(P\) of degree \(n\) on \([l,h]\), write
\(x=l+(h-l)t\) and

\[
 P(x)=\sum_{j=0}^n b_j\binom nj t^j(1-t)^{n-j}.
\]

Positive \(b_j\)'s imply \(P>0\) on the closed interval. Each entry in
the following table is a rational lower bound for the corresponding
coefficient of \(T^2-QV\) from (24)--(25), on
\([87/100,1571/1000]\). The polynomials are defined explicitly in
(24)--(25); the table is obtained by expanding and using the binomial
basis change, without a root solver.


| Coefficient | Index 4 | Index 12 | Index 19 | Index 23 |
|---:|---:|---:|---:|---:|
| 0 | 0.087761718 | 0.023669927 | 0.023077246 | 0.116718622 |
| 1 | 0.076372425 | 0.019498424 | 0.018871884 | 0.100653502 |
| 2 | 0.066130524 | 0.017336319 | 0.016694673 | 0.086207892 |
| 3 | 0.057132592 | 0.017144668 | 0.016506323 | 0.073531210 |
| 4 | 0.049449803 | 0.018837727 | 0.018220144 | 0.062729408 |
| 5 | 0.043124449 | 0.022281198 | 0.021700312 | 0.053861444 |
| 6 | 0.038166855 | 0.027291202 | 0.026760870 | 0.046936421 |
| 7 | 0.034552735 | 0.033634036 | 0.033165518 | 0.041911459 |
| 8 | 0.032221092 | 0.041026752 | 0.040628238 | 0.038690371 |
| 9 | 0.031072701 | 0.049138593 | 0.048814784 | 0.037123187 |
| 10 | 0.030969245 | 0.057593307 | 0.057345053 | 0.037006581 |
| 11 | 0.031733135 | 0.065972328 | 0.065796336 | 0.038085200 |
| 12 | 0.033148051 | 0.073818817 | 0.073707428 | 0.040053920 |
| 13 | 0.034960215 | 0.080642516 | 0.080583564 | 0.042561003 |
| 14 | 0.036880391 | 0.085925382 | 0.085902125 | 0.045212131 |
| 15 | 0.038586603 | 0.089127914 | 0.089119056 | 0.047575271 |
| 16 | 0.039727545 | 0.089696108 | 0.089675901 | 0.049186306 |
| 17 | 0.039926624 | 0.087068937 | 0.087007361 | 0.049555355 |
| 18 | 0.038786595 | 0.080686258 | 0.080549291 | 0.048173691 |
| 19 | 0.035894723 | 0.069997029 | 0.069746986 | 0.044521166 |
| 20 | 0.030828372 | 0.054467720 | 0.054063677 | 0.038074023 |


## Appendix B. The common endpoint-curvature polynomials

All entries are rational lower bounds for the Bernstein coefficients on
\([33/25,17/10]\) of the three explicit polynomials in (35).

**E, degree 4:**

\(b_{0}\ge3.085310604\), \(b_{1}\ge2.614595484\), \(b_{2}\ge2.111708044\), \(b_{3}\ge1.635361324\), \(b_{4}\ge1.265119724\).

**A, degree 1:**

\(b_{0}\ge0.928417627\), \(b_{1}\ge1.024557627\).

**P, degree 8:**

\(b_{0}\ge0.672348963\), \(b_{1}\ge0.522477124\), \(b_{2}\ge0.404904695\), \(b_{3}\ge0.332908541\), \(b_{4}\ge0.310357819\), \(b_{5}\ge0.330469984\), \(b_{6}\ge0.376840965\), \(b_{7}\ge0.428113442\), \(b_{8}\ge0.468109775\).

Each displayed lower bound is positive. The two endpoint substitutions for
\(D\), the twelve reference comparisons, and the rest of the fixed scalar
arithmetic are printed by the companion checker. Every square-root
bound is verified by integer squaring, and every trigonometric bound
comes from an alternating series with an explicit tail sign.

