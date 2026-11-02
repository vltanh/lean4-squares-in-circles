# Two low inner mains exclude a lower central outsider

November 2, 2026. Complete physical statement, analytic reduction, and a
finite exact table. A numerical direction check preceded the certificate;
no optimizer output is a proof premise. No Lean or CI.

Set

\[
 Q=1105/256,\quad l=29/60,\quad \rho=91/60,
 \quad g=15/31,\quad c_1=3/5,\quad c_2=119/310.
\]

## 1. The complete statement

Retain four original physical unit squares forming an actual horizontal
projection chain in the closed Q-disk. Suppose its two inner main centers
satisfy

\[
                         y_1\le-3/5,\qquad y_2\le-119/310.
 \tag{1}
\]

There is no distinct original central unit square F with

\[
                    |x_F|\le l,\qquad y_F<\min(y_1,y_2),
 \tag{2}
\]

whose open interior is disjoint from both inner mains. No side outsider,
short-chain comparison, or additional square is assumed. All orientations
and all physical separating-axis owners are included. Horizontal reflection
exchanges the two height thresholds; vertical reflection gives the
corresponding upper-central exclusion.

## 2. A complete two-variable reduction

Reflect vertically and write \((X,Y)\) for the reflected center of F.
The actual-four bounds give

\[
 -31/60<x_1<-l,\qquad l<x_2<31/60,
 \qquad g_i=1/(4h_i)>g.
 \tag{3}
\]

Section 2 of `ACTUAL_FOUR_MIXED_FULL_SIDES_LOWER_CENTRAL_EXCLUSION.md`
uses only the first height inequality of (1) and the left inner main to
prove

\[
                   1/3<X\le l,\qquad Y>3/5+g.
 \tag{4}
\]

That proof remains strict if \(y_1=-3/5\): its strict geometric margins
come from (3), \(g_i>g\), and \(\sqrt Q<133/64\). Thus (4) includes
every putative F in (1)--(2), not merely an added positional cell.
The universal center bound also gives \(Y<\rho\), and in particular
\(Y>X\ge0\).

Write the unsigned components of the one original F frame as

\[
 a\ge b\ge0,\quad a^2+b^2=1,\quad
 t=b/a\in[0,1],\quad
 a=(1+t^2)^{-1/2},\quad b=ta,
 \quad h=(a+b)/2,\quad k=(a-b)/2.
 \tag{5}
\]

### 2.1. An upper bound from the original F corners

Both possible frame chiralities imply

\[
 Q\ge\max\{(X+h)^2+(Y+k)^2,
                  (X-k)^2+(Y+h)^2\}.
 \tag{6}
\]

For the chirality with upper vertices \((X+h,Y+k)\) and
\((X-k,Y+h)\), this is direct. The other chirality has the corner
\((X+k,Y+h)\). Its squared norm exceeds the second expression in
(6) by \(4Xk\), and exceeds the first by
\(2(h-k)(Y-X)\). Both quantities are nonnegative by (4)--(5).
Consequently every original F obeys

\[
 Y\le U(X,t):=\min\left\{
 \sqrt{Q-(X+h)^2}-k,
 \sqrt{Q-(X-k)^2}-h,
 \rho\right\}.
 \tag{7}
\]

All square roots in (7) are positive over the complete root rectangle
\([1/3,l]\times[0,1]\).

### 2.2. A lower bound from the right inner main

Retain the aligned square of halfwidth g inside the original M2. Let D
and V be the horizontal and positive vertical center gaps from it to F.
By (3)--(4),

\[
 D<31/60-X<g,\qquad V\le Y-c_2.
\]

Put \(\delta=g-31/60+X>0\). Horizontal coordinate separation is
impossible. Vertical coordinate separation requires \(V\ge g+h\).
For an F-owned side separator, replacing both signed components by their
absolute values can only increase its center projection. Thus its vertical
clearance is at least one of

\[
 g+\frac{1/2+b\delta}{a},\qquad
 g+\frac{1/2+a\delta}{b}.
\]

The second is no smaller than the first when \(b>0\); their difference
has positive numerator \((a-b)/2+\delta(a^2-b^2)\). If \(b=0\),
only the coordinate alternatives remain. Every original separator therefore
implies

\[
 Y\ge L(X,t):=c_2+g+
       \min\left\{h,\frac{1/2+b\delta}{a}\right\}.
 \tag{8}
\]

This is a relaxation of the original pair, uniformly in its main center,
main frame, F frame chirality, and separator owner.

### 2.3. Necessary alternatives from the left inner main

Retain its aligned square of halfwidth g. Its center gaps are bounded by
\(D<X+31/60\) and \(V\le Y-c_1\). Put

\[
 d=X+31/60-g,\qquad v=U(X,t)-c_1-g.
\]

By the four separating-axis alternatives, disjointness requires at least
one of

\[
 d-h\ge0,\qquad v-h\ge0,\qquad
 ad+bv-1/2\ge0,\qquad bd+av-1/2\ge0.
 \tag{9}
\]

As in Section 2.2, taking absolute components includes every sign and both
chiralities. The one original F orientation is retained in all of (7)--(9).

## 3. The finite exact cover

The root rectangle is precisely

\[
                  (X,t)\in[1/3,29/60]\times[0,1].
 \tag{10}
\]

`two_low_mains_central_cover.json` is a complete midpoint binary cover of
(10). It has 615 nodes and 308 leaves, maximum depth 14. The leaf rules are:

| Rule | Rows | Exact strict rejection |
|---|---:|---|
| `right_circle` | 242 | the lower endpoint of L exceeds the upper endpoint of U |
| `left_axes` | 66 | all four interval upper bounds in (9) are negative |

Closed sibling boxes share their midpoint faces. Every internal node has
both children, every node is reached exactly once, and there are no omitted
or unresolved boxes. Thus root faces, the aligned and diagonal frames, and
all limiting separator contacts are covered.

The producer uses rational intervals and outward 64-bit square-root
bounds. The independent verifier `verify_two_low_mains_central.py` uses a
separately implemented 64-bit integer dyadic interval class, reconstructs
every box from the root and tree, and recomputes (7)--(9). It imports no
producer, producer evaluator, or interval library. Rational endpoints are
rounded outward, multiplication and division use integer directed rounding,
and square roots use `isqrt` with an upward correction. Every acceptance
comparison is an integer comparison, interpreted exactly over denominator
\(2^{64}\).

The saved replay is `two_low_mains_central_dyadic_replay.json`. It reports
PASS on all 308 leaves, with least positive rational reserve

\[
                    \frac{276834140688067}{18446744073709551616}>0.
\]

The certificate SHA256 is
`335b6b93fbf15886dc4be240f364fcf8737cb1a9ccbfcdff438b92df7b686346`.
The two rejection rules exhaust (10), so (1)--(2) are impossible.

## 4. Application to a low opposite-side outsider

Suppose now the main chain is also a center-cone chain, its left inner
main satisfies \(y_1<-3/5\), and an original right-side outsider R is
above M2 with \(y_R<3/5\). The main cone lower bound and physical
clearance give \(y_R>-113/600\). If \(y_R<7/16\), the endpoint
inset gives \(x_R<\zeta=2211/4000<49/80\). If
\(7/16\le y_R<3/5\), the same endpoint's radius-one-half disk
comparison gives \(x_R<49/80\); see
`LOW_SIDE_UNIT_FORCES_SAME_SIDE_CENTRAL_FLOOR.md` Sections 2--3.

Since \(x_R\ge l\) and \(x_2\in(l,31/60)\), their horizontal
center gap is below \(31/240<15/31<g_2\). The radius-one-half disk
inside R avoids the actual M2 aligned inset, so its positive vertical
center gap is at least \(g_2+1/2>61/62\). Hence

\[
                 y_2<3/5-61/62=-119/310.
\tag{11}
\]

The theorem consequently excludes every original central outsider below
both mains. This closes the entire low-R branch of the full-left-bottom,
one-upper/one-lower central occupancy without imposing a selected
short-chain edge. It is a standalone original-square lemma; it does not
claim closure of the remaining `(2,2,1)` branches or the whole `000/11` mask.
