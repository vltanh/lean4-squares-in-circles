# A further contraction from the same coarse pair table

This is a hand consequence of the completed coarse mismatch inequality.
It uses no additional pair table, state restriction, multiplier, or selected
contact owner. Put

\[
 \gamma=\frac{89727}{100000},\qquad \beta=\frac{99}{5000},\qquad
 h(x)=\frac{\sin x+\cos x-1}{2}\quad(0\le x\le2/5).
\]

Let \(x_i=|d_i|\) on the five charged edges and
\(S=\sum_i x_i\). The original coarse theorem has already proved
\(S<2/5\) and, by summing its full-SAT pair bounds,

\[
        2\pi>7\gamma+\beta\sum_i h(x_i).                 \tag{1}
\]

**Corollary.** The same hypotheses imply

\[
                 \boxed{S<\frac{109}{400}=.2725.}          \tag{2}
\]

For \(0\le x\le2/5\), the elementary bounds
\(\cos x\ge1-x^2/2\) and \(\sin x\le x\) imply
\(\cos x-\sin x\ge13/25>0\). Thus h is strictly increasing.
It is concave because \(h''=-(\sin x+\cos x)/2<0\), and h(0)=0.
For S>0, concavity therefore gives, separately for every i,

\[
 h(x_i)\ge\frac{x_i}{S}h(S),\qquad
                    \sum_i h(x_i)\ge h(S).              \tag{3}
\]

The case S=0 already satisfies (2). If instead
\(S\ge t=109/400\), (1)--(3) and monotonicity give

\[
                         2\pi>7\gamma+\beta h(t).        \tag{4}
\]

On this interval alternating Taylor sums give

\[
 h(t)\ge P(t):=
 \frac t2-\frac{t^2}4-\frac{t^3}{12}+\frac{t^4}{48}
 +\frac{t^5}{240}-\frac{t^6}{1440}-\frac{t^7}{10080}.
\]

One exact rational substitution is

\[
7\gamma+\beta P(109/400)-\frac{710}{113}
=\frac{3469086670939846509033}
        {1036779520000000000000000000}>0.                 \tag{5}
\]

Together with \(2\pi<710/113\), this contradicts (4), proving (2).

For a simpler, slightly weaker endpoint the same substitution gives

\[
7\gamma+\beta P(11/40)-\frac{710}{113}
=\frac{2123678636485607}{103677952000000000000}>0,
\]

so \(S<11/40\) also follows directly. The stronger endpoint (2) may
be used as a declared frame range in a subsequent conditional pair table.
The two mixed, uncharged frame differences retain their previously proved
range unless a separate argument constrains them.

The companion `verify_coarse_mismatch_concavity_strengthening.py` expands
the displayed polynomial from the Taylor sums and checks both substitutions
with exact fractions. The preceding concavity argument proves the whole
continuous implication; no numerical root finding is needed.
