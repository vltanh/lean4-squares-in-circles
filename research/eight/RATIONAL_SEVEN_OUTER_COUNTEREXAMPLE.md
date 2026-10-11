# Exact eight-square packing below radius two with seven outer centers

**Status.** An explicit **rational** construction, not a numerical
near-feasible output. The eight squares have pairwise disjoint *closed*
sets and lie strictly inside the disk with squared radius `397/100`.
Exactly one of them contains the disk origin in its open interior;
the other seven all have center norm strictly greater than one.
This disproves any attempt to force a near-center exterior *center*
from the weak ceiling `R<2`. It is **not** a counterexample to the
smaller proposed sharp radius, since `397/100>R_hat^2`.

## 1. Rational centers and rational orthonormal frames

For `i=1,...,7`, let the square center be `p_i=(X_i,Y_i)/1000`.
For a rational parameter `h_i=H_i/1000` set

    e_i=((1-h_i^2)/(1+h_i^2), 2*h_i/(1+h_i^2)),
    f_i=(-e_i.y,e_i.x).

Thus `e_i,f_i` is an **exact** rational orthonormal frame.
The square is the convex hull of
`p_i+(epsilon*e_i+eta*f_i)/2`,
for `epsilon,eta in {-1,1}`.
The seven triples `(X_i,Y_i,H_i)` are

| i | X_i | Y_i | H_i |
|---|---:|---:|---:|
| 1 | 1390 | 0 | -48 |
| 2 | 739 | 1072 | -48 |
| 3 | -404 | 1219 | -237 |
| 4 | -1335 | 508 | -184 |
| 5 | -1111 | -645 | -148 |
| 6 | -196 | -1399 | -48 |
| 7 | 856 | -958 | -48 |

The eighth square, numbered 0, has center `p_0=(0,0)` and frame
`e_0=(4/5,3/5)`, `f_0=(-3/5,4/5)`. It contains the disk origin
strictly.

## 2. Exact finite inequalities, with hand-checkable witnesses

For any frame `(e_i,f_i)`, the farthest squared vertex norm is

    Q_i=|p_i|^2+1/2+|p_i dot e_i|+|p_i dot f_i|.

The following column lists a *strict upper bound* on `100000*Q_i`,
obtained by substitution of the rational coordinates:

| i | strict upper bound on 100000 Q_i |
|---|---:|
| 0 | 50001 |
| 1 | 394885 |
| 2 | 396609 |
| 3 | 396532 |
| 4 | 396914 |
| 5 | 396605 |
| 6 | 396807 |
| 7 | 396593 |

All eight entries are less than `397000`, giving `Q_i<397/100<4`.

For a pair `i<j` and unit vector n belonging to the axes of either
square, the **exact** separating margin is

    g_ij(n)=|n dot(p_j-p_i)|
        -[|n dot e_i|+|n dot f_i|
          +|n dot e_j|+|n dot f_j|]/2.

If some such margin is positive, a separating line lies strictly
between the closed squares. The table below supplies one axis n and
an integer N for every one of the 28 pairs, with the exact claim

    g_ij(n)>N/10000.                                    (1)

| Pair | Axis | N | Pair | Axis | N |
|---|---|---:|---|---|---:|
| 0,1 | e1 | 1772 | 0,2 | e0 | 280 |
| 0,3 | f0 | 471 | 0,4 | e4 | 2386 |
| 0,5 | e0 | 768 | 0,6 | f6 | 2049 |
| 0,7 | f0 | 736 | 1,2 | f1 | 47 |
| 1,3 | e3 | 10034 | 1,4 | e1 | 16465 |
| 1,5 | e1 | 13391 | 1,6 | f1 | 5444 |
| 1,7 | f1 | 47 | 2,3 | e2 | 49 |
| 2,4 | e2 | 8958 | 2,5 | f5 | 10906 |
| 2,6 | f2 | 15491 | 2,7 | f2 | 10094 |
| 3,4 | f3 | 51 | 3,5 | f5 | 9108 |
| 3,6 | f6 | 14392 | 3,7 | e3 | 9561 |
| 4,5 | f5 | 49 | 4,6 | f6 | 6745 |
| 4,7 | e4 | 14547 | 5,6 | e5 | 56 |
| 5,7 | e7 | 8993 | 6,7 | e6 | 49 |

Every N is positive, indeed at least 47. The assertions in both
tables are finite **rational inequalities**, not angle
approximations: each e_i has rational entries, so multiplying
each comparison by the positive product of its `1+h_i^2`
denominators clears all fractions. As an illustrative lower margin,
the smallest of the listed numerical lower bounds is `47/10000`,
already larger than `1/250`. The full formula above gives a
straight arithmetic audit for any chosen row. No qualitative
continuity or computer-minimum assumption is involved.

Finally, direct squares of the seven displayed integer center
coordinates give `|p_i|^2>3/2>1` for every `1<=i<=7`.
Therefore all seven exterior centers are outer. This completes the
construction and its finite verification.

## 3. Consequence for the unrestricted n=8 argument

The presence of a central square below R=2 does **not** imply the
presence of any additional center of norm below one. The branch with
seven outer centers is geometrically genuine, although this
particular construction has strict pair gaps and is not an optimal
contact cycle. Consequently it is invalid to eliminate the
seven-outer possibility merely by cardinality, by asserting that
a second inner center must exist at every radius below two, or by
confusing an exterior square with an outer-center square.

The sharp n=8 radius remains open: this construction has squared
radius `397/100`, while the known tilted candidate uses
`R_hat^2 approx 3.915534`. It supplies no improved upper bound.
