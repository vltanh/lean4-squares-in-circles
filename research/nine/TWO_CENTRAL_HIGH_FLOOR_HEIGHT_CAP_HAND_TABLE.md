# Two high-floor central squares have center heights below 273/200

November 2, 2026. Complete physical theorem and finite exact table.
Numerical direction checks preceded the cover. The cover has passed an
independent exact Fraction replay. No Lean or CI is used.

Put \(Q=1105/256\), \(l=29/60\), \(\rho=91/60\), and
\(H=273/200\).

## 1. Statement and complete center routing

**Theorem.** Let A,B be original physical unit squares with disjoint open
interiors, all corners in the closed centered Q-disk, both center
x-coordinates in \([-l,l]\), and both whole floors at least one tenth.
Then both center heights are strictly less than H. Orientations and
physical separator owners are arbitrary.

Suppose the conclusion fails. Label the higher-center unit A, so
\(Y=y_A\ge H\), and put \(Z=y_B\le Y\). Their centers are both at
least three fifths high, because every projection halfwidth is at least
one half. The upper-column separation theorem therefore gives horizontal
center gap greater than l. Inside \([-l,l]\), this forces opposite
strict horizontal signs. Reflect horizontally to write

\[
 x_A=x>0,\qquad x_B=-w<0,\qquad 0<x,w\le l.
\]

The actual displacements \(D=x+w\), \(V=Y-Z\) satisfy

\[
 0<D\le2l<1,\qquad 0\le V<\rho-3/5=11/12<1.
\tag{1}
\]

For every genuine separating normal from B toward A, both components must
be positive. If either component were nonpositive, its center projection
would be less than one by (1), whereas each original unit contains its
centered radius-one-half disk and their support sum is at least one.
This accounts for all signed normals before choosing a physical owner.

## 2. Four original-frame charts

For each square j in {A,B}, choose its near-horizontal side vector as

\[
 u_j=(1,\epsilon_j t_j)/d_j,\qquad
 v_j=(-\epsilon_j t_j,1)/d_j,\qquad
 d_j=\sqrt{1+t_j^2},
\]

where \(0\le t_j\le1\), \(\epsilon_j\in\{-1,1\}\). Define
\(a_j=1/d_j\), \(b_j=t_j/d_j\),
\(h_j=(a_j+b_j)/2\), \(k_j=(a_j-b_j)/2\).
These four choices of \((\epsilon_A,\epsilon_B)\) cover both arbitrary
original chiralities. Aligned and diagonal boundary frames are included,
even when represented in more than one chart.

The original upper A corners give

\[
 Y\le U_\epsilon(x,t_A):=\min\left\{
 \sqrt{Q-(x+\epsilon k_A)^2}-h_A,
 \sqrt{Q-(x+h_A)^2}+\epsilon k_A,\rho\right\}.
\tag{2}
\]

For \(\epsilon=1\), the two retained corners have offsets
\((k_A,h_A)\), \((h_A,-k_A)\); for \(\epsilon=-1\), their offsets
are \((-k_A,h_A)\), \((h_A,k_A)\). Thus (2) uses actual corners of
the same original frame in its chart. All radicals are positive throughout
the root rectangle below.

The lower original B whole floor gives \(Z\ge h_B+1/10\). Therefore

\[
             D\le D_0:=x+l,
 \qquad V\le V_0:=U_{\epsilon_A}(x,t_A)-h_B-1/10.
\tag{3}
\]

Each physical unit has exactly one side-normal direction in the closed
positive quadrant, up to the harmless aligned/diagonal duplications:

\[
 n_j=(a_j,b_j)\quad(\epsilon_j=1),\qquad
 n_j=(b_j,a_j)\quad(\epsilon_j=-1).
\tag{4}
\]

The separating-axis theorem and the positive-sign reduction (1) imply
that one of these two original normals separates the pair. Their common
support sum in either owner's unit direction is exactly

\[
 \sigma=\frac12\left(1+
 \frac{1+\epsilon_A\epsilon_Bt_At_B+
        |\epsilon_Bt_B-\epsilon_At_A|}{d_Ad_B}\right).
\tag{5}
\]

This follows from the dot product and determinant of the two original side
vectors: each owner contributes one half, and the other contributes half
the sum of the absolute cosine and sine of their relative angle. The
cosine numerator is nonnegative over the stated charts, including its
possible zero endpoint.

Consequently every original counterexample must satisfy simultaneously

\[
 U_{\epsilon_A}\ge H,
 \qquad \max\{n_A\cdot(D_0,V_0),n_B\cdot(D_0,V_0)\}\ge\sigma.
\tag{6}
\]

The relaxation in (3) is valid for these positive normals. It does not
choose a different A frame for the two corner and two pair conditions.
No condition on B's corners is needed for this necessary system.

## 3. The complete exact cover

Every physical possibility in (6) lies in one of the four chart copies of

\[
 (x,t_A,t_B)\in[0,29/60]\times[0,1]\times[0,1].
\tag{7}
\]

`two_central_height_cap_cover.json.gz` contains four complete midpoint
binary trees over (7). At each leaf, either the interval upper bound for U
is strictly below H (`circle`), or both pair-axis interval upper bounds
are strictly below the interval lower bound for sigma (`pair_axes`).

| Upper chirality | Lower chirality | Circle rows | Pair-axis rows | Total rows |
|---:|---:|---:|---:|---:|
| -1 | -1 | 5331 | 41441 | 46772 |
| -1 | 1 | 1082 | 6723 | 7805 |
| 1 | -1 | 525 | 723 | 1248 |
| 1 | 1 | 1283 | 1392 | 2675 |
| **All four** | | **8221** | **50279** | **58500** |

There are no unresolved leaves. Every internal node has both children,
which share their midpoint face. The root faces and every frame boundary
are included. Every chart and every node is checked once by the verifier.

The producer uses outward 64-bit integer dyadic intervals. The independent
standalone verifier `verify_two_central_height_cap.py` implements exact
Fraction arithmetic with outward 64-bit square-root bounds, recomputes
(2)--(6), and imports no producer, evaluator, or interval library. Its
support computation reconstructs the relative-frame dot product and
determinant before division by their positive common denominator.

The saved replay `two_central_height_cap_fraction_replay.json` reports PASS
on all 58,500 strict leaves, maximum depth 32. The certificate SHA256 is
`d7c7ad1d87422c7c258beb3547c5d3d2218958ae86da54dce2b36c5a3eec347f`.
The report records an exact positive Fraction reserve for every chart.
These complete covers contradict (6) and prove the theorem.

## 4. Scope

This is a two-original-square geometric theorem. It assumes no actual
four-chain, selected cone chain, side occupancy, frame equality, or contact
pattern. The only external geometric input beyond circle containment and
the rectangle separating-axis theorem is the accepted five-row
upper-column separation theorem. It adds no occupancy or mask closure by
itself. A caller must derive the two original whole-floor hypotheses.
