# The diagonal D boundary has an exact nearest-axis recoding

## 1. Scope

Retain the actual seven-cycle with roles
\[
 (H,G,A,B,T,D,E),\qquad k=(0,1,0,1,0,1,1),
\]
common real frame lifts of spread less than \(7/10\), and
signed own-frame coordinates \((a_i,-y_i)\). Assume the already
proved original owner restrictions BT,DE in \(\{2,3\}\).
In particular \(y_B<0\) and \(y_D<0\). The assertion below
requires no frame order, mismatch bound, radial-kind choice,
or sign assumption on A,T,H,G.

Suppose D is at its actual nearest-axis tie:
\[
                 a_D=b_D=-y_D>0.                 \tag{1}
\]
Then choosing its other nearest axis, followed by a cyclic
relabeling, preserves the actual squares and gives another
canonical seven-cycle with the same quarter word. This is a
representation change at an actual tie, not a deformation of
the packing or a replacement of a circle by a comparison point.

In the branch
\[
                 GA\in\{2,3\},\qquad EH\in\{0,1\},
                                                        \tag{2}
\]
the resulting cycle has the four normal quarter-owner classes
\[
          GA\in\{0,1\},\quad BT,DE\in\{2,3\},
                         EH\in\{0,1\}.           \tag{3}
\]
These classes survive the usual reflection normalization of
its new E sign. Any separately proved reduction for that
normal-owner class therefore applies at the diagonal boundary
of (2), with exactly its other stated entry hypotheses.

This note does not prove a transport of an arbitrary D to (1),
and does not import a frame-order conclusion into (3).

## 2. The coordinate and quarter-word identities

Increase D's canonical directed frame by \(\pi/2\). The same
physical center, formerly \((a_D,+b_D)\), has new own-frame
coordinates \((b_D,-a_D)\). Thus
\[
       a_D^{\rm new}=b_D,
       \qquad y_D^{\rm new}=a_D>0.                \tag{4}
\]
Equation (1) makes (4) sorted and admissible at the other
nearest-axis representative. The physical square, its farthest
corner radius, its true-core distance and its radial kind are
unchanged. The real frame lift modulo \(\pi/2\) is also
unchanged; only its recorded quarter offset changes.

Consequently the TD quarter increment increases from zero to
one and the DE increment decreases from one to zero. All other
increments remain fixed. In the old role order the new word is
\[
                         (0,1,0,1,1,0,1).        \tag{5}
\]
Use the new cyclic role list
\[
 (H',G',A',B',T',D',E')=(D,E,H,G,A,B,T).          \tag{6}
\]
Starting at H' in (5) gives \((0,1,0,1,0,1,1)\), as claimed.
The real frame errors are merely permuted. Every original
physical center gap and every originally retained separating
axis are preserved.

## 3. All affected original-owner formulas

Let \(d\) be the retained TD error. Its two original zero
projections are
\[
\begin{aligned}
 P_{TD,0}&=y_T+a_D\sin d+b_D\cos d,\\
 P_{TD,2}&=a_T\sin d+y_T\cos d+b_D.
\end{aligned}                                      \tag{7}
\]
After (4), these are respectively the quarter projections
\[
\begin{aligned}
 y_T+a_D^{\rm new}\cos d+y_D^{\rm new}\sin d,
 \qquad
 a_D^{\rm new}+a_T\sin d+y_T\cos d.
\end{aligned}
\]
Thus old TD0 becomes new EH0 and old TD2 becomes new EH1.

For the retained DE error e, its original high-quarter
projections are
\[
\begin{aligned}
 P_{DE,2}&=a_D\cos e+b_D\sin e-y_E,\\
 P_{DE,3}&=a_D+a_E\sin e-y_E\cos e.
\end{aligned}                                      \tag{8}
\]
Under (4), these are the zero projections with owners 2 and 0,
respectively. This gives the complete affected-owner map:

| Old edge and owner | New edge and owner |
|---|---|
| TD0 | EH0 |
| TD2 | EH1 |
| DE2 | HG2 |
| DE3 | HG0 |

All other edge formulas are unchanged and only their role
names change:

| Old edge | New edge |
|---|---|
| EH | GA |
| HG | AB |
| GA | BT |
| AB | TD |
| BT | DE |

These are identities of the original projections. The common
width \((1+\cos d+|\sin d|)/2\) is unchanged, so weak contacts
and ties between original witnesses are retained exactly.

Under (2), the second table and the global BT restriction give
(3) immediately. In particular the new normal signs supplied
by the quarter and zero--quarter implications are consistent:
H' is positive by (4), A'=old H is positive by old EH0/1,
B'=old G is negative by old GA2/3, and D'=old B is negative.
The T'=old A and E'=old T signs are not assumed.

## 4. Normalize the new E sign without changing the normal classes

If \(y_{E'}\le0\), no further change is needed. Otherwise
reflect the whole physical configuration and reverse the cyclic
role order, as in the G2 reflection normalization. The role
permutation is
\[
       H'\leftrightarrow D',\quad
       G'\leftrightarrow T',\quad
       A'\leftrightarrow B',\quad E'\mapsto E'.
\]
Every transverse sign changes. For quarter owners the exact
reflected-reversal map is \(0\leftrightarrow2\),
\(1\leftrightarrow3\), while the two zero owners exchange.
The quarter edges GA and BT exchange, as do DE and EH.
It follows that the four classes in (3) are preserved. The
new E sign is now nonpositive.

No radius or circle slack is spent by either representation
change. In an equality argument all original physical centers,
frames and weak contacts are still available.

## 5. The all-high diagonal boundary

If old GA and EH both have high owners, the first recoding gives
\[
 GA',BT',DE'\in\{2,3\},\qquad EH'\in\{0,1\}.
                                                        \tag{9}
\]
When old \(y_T\le0\), (9) is already normalized. It is the
high-GA, low-EH branch, with H'>0, irrespective of old H's sign.

When old \(y_T>0\), reflection to normalize E' turns the high
GA' owner in (9) into a low BT owner. All states remain
canonical because the only nearest-axis change was made at
(1). This contradicts the global BT-owner theorem. Hence the
all-high diagonal boundary necessarily has old \(y_T\le0\)
and reduces to (9).

## 6. Exact scope off the diagonal

The physical coordinate, projection and word identities
(4)--(8) remain true without (1). Their only canonical-state
failure is then at H'=old D:
\[
                a_{H'}=b_D<a_D=b_{H'}.           \tag{10}
\]
Its shifted corner circle and true-core geometry remain exact,
but it is outside the sorted cone required by the canonical
downstream statements. Those statements may not be applied to
(10) unless that additional domain extension is proved.

In particular the standard positive-half marker formula must
not be substituted at this unsorted state. If one needs only
the original G1 edge charges during a representation change,
the signed marker at this state changes by \(\pi/2\), just as
its canonical angle does; this keeps its physical potential
\(\psi=\alpha-\ell\) fixed. That bookkeeping preserves the
original charge identities, but does not by itself prove any
of the standard sorted-chart marker inequalities at (10).

The established consequence here is the exact diagonal-boundary
reduction. The remaining global task is a valid transport to
that boundary or a separately justified treatment of (10).
