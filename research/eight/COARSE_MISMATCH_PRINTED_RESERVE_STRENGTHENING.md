# Using the printed pair reserves: S < 13/50

This supplements the first coarse candidate mismatch theorem without
changing its rational pair table or its hypotheses. The fixed table
already gives a strictly positive lower bound for every cost polynomial.
Retaining a small part of those printed reserves yields

\[
                         \boxed{S<13/50=.26.}             \tag{1}
\]

The roles, charged edges, labels, and constants remain

\[
 (H,G,A,B,T,D,E),\quad I=\{0,2,3,4,5\},\quad
 \gamma=89727/100000,\quad\beta=99/5000.
\]

Only the original G/T/E tangent bounds are assumed. In particular, no
additional owner, H or D tangent, or narrower initial frame domain is
used here.

## 1. Seven lower constants already contained in the fixed table

For each input row the compact report supplies the minimum of all the
Bernstein coefficient lower bounds of each cost polynomial. Therefore
that minimum bounds the cost polynomial on its entire closed angle
interval. When two endpoint costs occur, take the smaller of their two
lower bounds. Taking a minimum over every row belonging to a fixed
original edge gives the following exact table:

| Edge | Minimum printed cost reserve, in units 10^-14 | Retained increase c_i, in units 10^-6 |
|---:|---:|---:|
| 0 | 1539796384 | 15 |
| 1 | 1387463060 | 13 |
| 2 | 1885909004 | 18 |
| 3 | 1251076023 | 12 |
| 4 | 1539189132 | 15 |
| 5 | 2347069107 | 23 |
| 6 | 642432521 | 6 |

Each minimum in the middle column is strictly larger than the retained
increase in its last column. The supporting pair proof has the form

\[
 \phi-\beta_i h(\phi)+L_i-L_{i+1}-\gamma
 \ \ge\ \min_j F_{{\rm row},j}(x),
\]

where each of the row's one or two fixed support polynomials is at least
the printed reserve. Hence the same already proved table gives, on every actual
retained separator,

\[
             \phi_i-\beta_i h(\phi_i)+L_i-L_{i+1}
                    >\gamma+c_i.                         \tag{2}
\]

No polynomial is recomputed or replaced in this step. The complete
original state and angle cover remains the cover for (2). The choice of
one label per vertex remains consistent. The seven added constants sum to

\[
                            \sum_i c_i=51/500000.          \tag{3}
\]

## 2. One concavity argument and one rational comparison

The original coarse theorem already supplies S<2/5. On this interval
\(h(x)=(\sin x+\cos x-1)/2\) is concave, increasing, and vanishes
at zero. Consequently

\[
 \sum_{i\in I}h(|d_i|)\ge h(S).
\]

For S>0 this follows by applying concavity to each
\(|d_i|=(|d_i|/S)S+(1-|d_i|/S)0\), then summing.
The case S=0 already satisfies (1).

If S reaches \(t=13/50\), summing (2) therefore gives

\[
                2\pi>7\gamma+51/500000+\beta h(t).
\]

Alternating lower Taylor sums imply

\[
 h(t)\ge P(t):=
 \frac t2-\frac{t^2}4-\frac{t^3}{12}+\frac{t^4}{48}
 +\frac{t^5}{240}-\frac{t^6}{1440}-\frac{t^7}{10080}.
\]

The exact substitution

\[
 7\gamma+\frac{51}{500000}+\beta P(13/50)-\frac{710}{113}
 =\frac{9154605884982919}{494375000000000000000}>0
\]

contradicts \(2\pi<710/113\), proving (1).

The companion `verify_coarse_mismatch_printed_reserves.py` binds the
unchanged input and compact-report hashes, reconstructs all seven minima
from the complete fixed row list, and checks the displayed rational
arithmetic. The original full coefficient replay and independent domain
review remain the justification for the underlying pair polynomials.
