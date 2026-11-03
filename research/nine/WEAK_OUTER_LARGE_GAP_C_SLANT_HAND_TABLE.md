# A slanted bound for C excludes the right-lower original pocket

Complete hand reduction and finite rational table, with full exact replay
and a fresh independent replay of all eight closed orientation roots.

November 3, 2026. Computer-assisted discovery followed by the complete
physical argument and exact rational table below. No Lean, Lake, or CI.

## 1. Exact original scope and the conclusion

Retain the full original-nine `001/00` predicate, with main originals
A,B,C,D and actual short-chain originals E,F,G, at closed

\[
 Q=1105/256,\quad r=\sqrt Q<133/64,\quad \rho=91/60,
 \quad a=46,\quad b=27/2,\quad T=211/4.
\]

Normalize the common vertical reflection so that

\[
 d=x_D-x_C\ge v=y_D-y_C\ge2/3,
 \qquad d<h_C+h_D.                                   \tag{1}
\]

The strict weak bit in (1) is retained as an original premise, even
where a necessary linear row later relaxes it to a closed inequality.
The theorem is

\[
                  \boxed{\ y_C+\frac78x_C< -\frac7{32}.\ }       \tag{2}
\]

Only unchanged C,D,G center variables and physical frames appear in
the table. Necessary original-chain inequalities retain the role of
the other selected originals. The two unselected physical squares
remain unrestricted members of the original predicate.

The expanded low-gap hand theorem through 2/3 is a separate result.
It supplies the complementary domain when this theorem is used in a
full-mask argument; it is not needed to prove (2) under (1).

### 1.1. The bound puts C inside a useful fixed unit disk

The original horizontal localization below gives

\[
                         29/60<x_C<4/5.              \tag{3}
\]

Equation (2) implies

\[
 y_C<-77/120<-5/8,
 \quad 0<\rho+y_C<\frac{623}{480}-\frac78x_C.        \tag{4}
\]

The lower inequality uses the original center-radius bound. The upper
affine expression is positive throughout (3). The quadratic

\[
 f(p)=p^2+\left(\frac{623}{480}-\frac78p\right)^2
\]

is convex, so its maximum on `[29/60,4/5]` is at an endpoint. The exact
endpoint reserves are

\[
 1-f(29/60)=\frac{11}{14400},\qquad
 1-f(4/5)=\frac{23}{9216}.
\]

Thus (2) proves the useful strict region bound

\[
              y_C<-5/8,\qquad x_C^2+(\rho+y_C)^2<1. \tag{5}
\]

### 1.2. No additional original can lie below C on the right

Suppose another original H has `x_H>=0` and `y_H<=y_C`. Put
`p=x_C`, `q=-y_C`, and write its center as `(u,-w)`. Then
`p>=29/60`, `q>=5/8`, `u>=0`, and `w>=q`. Every original center
has norm less than rho. Distinct physical unit squares have center
distance at least one: their open radius-1/2 center disks are contained
in their original interiors.

If `u<=p`, then

\[
 |c_H-c_C|^2\le p^2+(\rho-q)^2<1
\]

by (5), contradicting physical separation. If `u>=p`, write
`z=u-p>=0`, `t=w-q>=0`. Separation gives `z^2+t^2>=1` and
`z+t>=1`. Since p and q are both at least 29/60,

\[
\begin{aligned}
 u^2+w^2
 &=p^2+q^2+z^2+t^2+2pz+2qt\\
 &\ge(29/60)^2+(5/8)^2+1+2(29/60)(z+t)\\
 &\ge(89/60)^2+(5/8)^2
   =\rho^2+93/320>\rho^2,
\end{aligned}
\]

again impossible. This proves the complete implication

> Under (1), no other original H has `x_H>=0` and `y_H<=y_C`.

No H orientation, auxiliary chain link, or classification is assumed.
The finite table therefore needs only three original angles.

## 2. Necessary localization from the original chains and physical caps

Write `g_i=1/(4h_i)` for the aligned contained-inset halfwidth. The
original physical inset theorem, the first two actual main links, and
the original A/E cap give

\[
\begin{gathered}
 d\ge g_C+g_D,\qquad d\ge v\ge2/3,\qquad d<h_C+h_D,\\
 x_C>h_C-1/60,\qquad
 a(x_C-h_C)+b(x_G-h_G)\ge27/4.                        \tag{6}
\end{gathered}
\]

The last inequality follows by substituting
`-x_A-h_A>=1+h_C-x_C` and `-x_E-h_E>=1+h_G-x_G` into the physical
left cap. These two substitutions are precisely the original actual
main and short-chain comparisons.

The complete localization in
`WEAK_OUTER_LARGE_GAP_SHORT_ENDPOINT_ORDER_HAND_TABLE.md` further gives

\[
\begin{gathered}
 x_D>4/3,\qquad x_C-h_C<5/64,\qquad x_G-h_G>101/432,\\
 x_D-x_G<1459/1728<1,\qquad x_G-x_D<11/60,\qquad y_G>y_D.
                                                               \tag{7}
\end{gathered}
\]

Its lower-gap hypothesis `v>=7/30` is satisfied here. For the bound
on C's right edge, containment and (6) give
`x_C-h_C<=r-(h_D+g_D)-(h_C+g_C)<=r-2<5/64`.
Together with `h_C>=1/2` this yields the lower bound in (3); the upper
bound follows from `h_C<=1/sqrt(2)` and
`(4/5-5/64)^2-1/2=2161/102400>0`.

Every usable original D/G separating normal is upward: a normal with
nonpositive vertical component has projection on `c_G-c_D` strictly
below one by (7), while the physical support sum is at least one.
Both owners and both original chiralities remain available.

### 2.1. Original D/G insets must separate vertically

Put `S=h_D+h_G` and `K_0=3187/1728=133/64-101/432<2`.
Containment and (7) give

\[
 x_D-x_G<K_0-S<2-S\le g_D+g_G.
\]

The last inequality is the sum of `h_i+g_i>=1`. In the reverse
direction, `x_G-x_D<11/60<1/sqrt(2)<=g_D+g_G`. Thus
`|x_D-x_G|<g_D+g_G`.

The unchanged physical squares contain aligned open squares of these
halfwidths. Since their original interiors are disjoint, the insets
must be separated along at least one coordinate. Horizontal separation
has just been excluded, so (7) fixes the vertical sign and proves

\[
                         y_G-y_D\ge g_D+g_G.          \tag{8}
\]

This is especially useful near aligned frames, where its lower bound
is one. It introduces no new physical separator-owner assumption.

We also retain the independently proved affine clearance

\[
 y_G-y_D>\frac78(h_D+h_G)-\frac{41}{120}.             \tag{9}
\]

For completeness, the unit center distance and `|dx|<K_0-S` give
`dy>sqrt(1-(K_0-S)^2)`. The square of this bound exceeds the square of
the positive affine expression on `1<=S<=10/7`: their difference is
a concave quadratic with endpoint reserves `198911/74649600` and
`7595279/3657830400`. This is the hand lemma in
`WEAK_OUTER_NUMERIC_AFFINE_DG_CLEARANCE.md`.

### 2.2. Keep the same D width in the right cap and its tilt toll

For the canonical D components alpha,beta, the inherited universal
physical cap gives

\[
 a(x_D-h_D)+b(x_G-h_G)+4\beta\le T.                   \tag{10}
\]

For nonnegative D tilt, the signed cap also gives the same inequality
with toll sigma, where `sigma/a=(23/32)beta-(1-alpha)`.
The upward-owned-normal premise is supplied by (7). The signed cap
has no upper bound on v and is independent of the present conclusion.
The two toll inequalities are imposed separately, never added.

Subtracting the last inequality of (6) from either right cap cancels
the same original G width and proves

\[
                       d+h_C-h_D+\tau/a\le1.         \tag{11}
\]

The exact width/toll combinations are

\[
 h_D-4\beta/a=\alpha/2+19\beta/46,
 \qquad h_D-\sigma/a=1-\alpha/2-7\beta/32.
\]

These correlated expressions, rather than independent width/toll
extrema, are used in the interval rows below.

## 3. Eight complete original-orientation roots

Represent each unchanged original by

\[
 u_i=(1,t_i)/\sqrt{1+t_i^2},\quad
 w_i=(-t_i,1)/\sqrt{1+t_i^2},\quad -1\le t_i\le1.
\]

Take all eight closed sign boxes for `(t_C,t_D,t_G)`, with each
coordinate in `[-1,0]` or `[0,1]`. These cover every original frame,
including all shared aligned and diagonal faces.

The contrary domain is the single closed half-plane

\[
                         y_C+\frac78x_C\ge-\frac7{32}.           \tag{12}
\]

There is no horizontal partition, quadratic replacement, or additional
angle. The same six original center coordinates
`X=(x_C,y_C,x_D,y_D,x_G,y_G)` occur in every row and leaf.

## 4. Necessary physical rows on an angle box

Let `[h_i^-,h_i^+]` be an outward halfwidth enclosure and put
`g_i^-=1/(4h_i^+)`. The necessary horizontal intervals are

\[
\begin{aligned}
 h_C^- -1/60\le x_C\le
 \min\{\rho-g_C^- -g_D^-,\ 133/64-1-g_C^-,\ h_C^++5/64\},\\
 \max\{4/3,h_C^- -1/60+g_C^-+g_D^-\}\le x_D
       \le\min\{\rho,133/64-h_D^-\},\\
 h_G^-+101/432\le x_G\le\min\{\rho,133/64-h_G^-\}.
\end{aligned}                                        \tag{13}
\]

For a nonnegative horizontal lower bound L, one outward-quadrant
original corner has increments `(h,k)` or `(k,h)`, where
`k^2=1/2-h^2`. Therefore a necessary symmetric vertical interval is
given by

\[
 |y_i|\le\min\left\{\rho,
 \max\left(
 \sqrt{(Q-(L+h_i^-)^2)_+}-k_i^-,\
 \sqrt{(Q-(L+k_i^-)^2)_+}-h_i^-
 \right)\right\},                                    \tag{14}
\]

with a downward radical bound for
`k_i^-=sqrt(max(0,1/2-(h_i^+)^2))`. This retains both original
chiralities. Clipping a negative radicand to zero only enlarges the
necessary set.

The half-plane (12) increases C's lower y endpoint to at least
`-7/32-(7/8)*x_C^+`. Define

\[
 \delta=\max\{g_D^-+g_G^-,\ (7/8)(h_D^-+h_G^-)-41/120\}.
\]

Using already valid endpoints in this order, increase `y_D^-` to
`y_C^-+2/3`, decrease `y_D^+` to `y_G^+-delta`, decrease `y_C^+`
to `y_D^+-2/3`, and increase `y_G^-` to `y_D^-+delta`.
Every step follows from (1), (8), or (9).

Let M be an outward upper bound on
`alpha/2+19beta/46` over D's original interval. In the absolute slope
s this is `(23+19s)/(46sqrt(1+s^2))`; its maximum is at the point of
the absolute-slope interval nearest `19/23`. For a nonnegative D
interval let K be a lower bound for `alpha/2+7beta/32`. This positive
linear combination is concave in its canonical angle, so its minimum
is at an endpoint. These formulas are evaluated with exact outward
rational radicals.

Put

\[
 U=\min\{31/30,1-h_C^-+M\},
\]

also intersecting with `2-h_C^- -K` when the signed cap applies.
Then (1) and (11) give both `d<=U` and `v<=U`.

### 4.1. Circle support, same-original normals, and cap rows

Each original contributes the necessary circle rows

\[
 p x_i+q y_i\le\sqrt{Q(p^2+q^2)}-H_i^-(p,q),         \tag{15}
\]

for all primitive nonzero vectors in `[-4,4]^2`, and all coordinate
swaps/sign choices of `(32,9)`, `(128,35)`, `(128,37)`, `(24,23)`,
`(96,91)`, `(32,31)`. The additional directions tighten the outer
polygon near the aligned endpoint contact directions; they place no
new assumption on a physical orientation.

A separate block uses the 128 rational unit vectors obtained, for
`k=0,...,32`, from all coordinate-sign choices of

\[
 p_k=\frac{1024-k^2}{1024+k^2},\qquad
 q_k=\frac{64k}{1024+k^2}.
\]

The identity `p_k^2+q_k^2=1` is exact. Their necessary rows are
`p_k*x_i+q_k*y_i<=sqrt(Q)-H_i^-(p_k,q_k)`. These additional directions
remove the broad angular gaps left by the first support polygon.
They are appended as a whole three-original block after the existing
rows, preserving every earlier multiplier index. There are 96 original
integer-direction rows and 128 appended unit-direction rows per original;
parallel or duplicate necessary rows cause no difficulty.

The basic linear rows are (6), the closed weak relaxation, `G>=D`,
both horizontal bounds in (7), and the contrary half-plane (12).
One fixed dummy row is `0<=0`.

Separator nodes consider the unchanged physical pairs in the order
C/D, D/G, C/G. Every original signed owner remains covered. For C/D
the completed strict weak-cone sign theorem
`WEAK_OUTER_NUMERIC_CONE_SEPARATOR_SIGNS.md` excludes `-u` and `-w`,
retains `+u`, and retains `+w` exactly when the owner's angle interval
contains a negative point. A closed negative interval may harmlessly
retain its zero endpoint. For D/G only nonpositive vertical normals
are omitted, by (7). No C/G owner or sign is omitted.

The C/D omission uses the **original strict weak bit**, even though a
linear row is its closed relaxation. No theorem excluding the changed
actual-link boundary is asserted.

Signed normal coordinates are enclosed outward. Replacing a normal by
the midpoint of its coordinate intervals on the `2^-30` grid incurs an
explicit interval-product error. The difference intervals use the same
center boxes, intersected with

| Pair | Additional necessary difference bounds |
|---|---|
| C/D | `g_C^-+g_D^-<=dx<=U`, `2/3<=dy<=U` |
| D/G | `-1459/1728<=dx<=11/60`, `dy>=delta` |
| C/G | `dy>=2/3+delta` |

An empty intersected interval is recorded as an explicit contradiction;
it is never used as if nonempty in an error estimate.

The single-square support minima and owned-pair support minima use the
exact endpoint/sign-change formulas proved in the accepted G-order
table. Projection-sign intervals have concave positive sine/cosine
support expressions. In particular the endpoint owned-pair requirement is

\[
 \frac12\left(1+
 \frac{1+t_i t_j+|t_i-t_j|}{\sqrt{(1+t_i^2)(1+t_j^2)}}\right),
\]

and is one if the two angle intervals overlap.

Five final rows retain

\[
\begin{aligned}
 y_D-y_G&\le-\delta,\\
 d&\le1-h_C^-+M,\\
 d&\le2-h_C^- -K,\\
 a x_D+b x_G&\le T+aM+b h_G^+,\\
 a x_D+b x_G&\le T+a-aK+b h_G^+.
\end{aligned}
\]

Inapplicable signed rows are the harmless identity `0<=0`. The original
physical D/G premise remains present behind the inherited cap and inset
rows even if a leaf closes before explicitly selecting that pair's axis.

## 5. Exact finite arithmetic and the two terminal rules

Every angle split retains both closed halves. Every separator split
retains every owner/sign not excluded by the complete physical lemmas.
An empty-interval terminal names one necessary interval and reconstructs
its exact strict endpoint contradiction.

Otherwise the terminal supplies nonnegative integer weights divided by
`2^40` for necessary rows `A_j X<=b_j`. Set
`r_0=sum lambda_j A_j`, `b_0=sum lambda_j b_j`. The verifier requires

\[
                       -b_0-\rho\sum_{k=1}^6|(r_0)_k|>0.        \tag{16}
\]

Since all six original coordinates have magnitude at most rho, (16)
contradicts the weighted inequality. Every residual center coefficient
is paid explicitly; no approximate cancellation is treated as exact.

All radicals are reconstructed with integer square-root bounds on the
`2^-48` grid. The replayer `weak_outer_hand_C_slant_verify.py` imports
only exact Fraction support/radical routines from
`weak_outer_hand_right_lower_verify.py`. It does not call that module's
separate four-original verifier and imports no numerical producer or
optimizer. Both exact-source hashes are bound in the replay report.

## 6. Finite coverage and independent acceptance

The complete forest has eight roots, 189,342 nodes, 92,691 closed angle
splits, 606 signed-owner separator splits, and 96,045 terminal proofs.
Of the terminals, 95,593 are nonnegative rational combinations and 452
are explicit empty necessary intervals. The maximum depth is 32 and
the unresolved frontier is empty.

Write `-` for `[-1,0]` and `+` for `[0,1]`. The exact root counts are:

| Root | C,D,G intervals | Nodes | Terminals |
|---|---|---:|---:|
| 0 | `---` | 8,815 | 4,664 |
| 1 | `--+` | 8,855 | 4,618 |
| 2 | `-+-` | 5,323 | 2,816 |
| 3 | `-++` | 13,635 | 6,948 |
| 4 | `+--` | 5,435 | 2,944 |
| 5 | `+-+` | 6,429 | 3,381 |
| 6 | `++-` | 23,239 | 11,756 |
| 7 | `+++` | 117,611 | 58,918 |
| **Total** | **All eight closed roots** | **189,342** | **96,045** |

Every exact terminal reserve is greater than

\[
                           \frac{132961}{10^{12}}>0.
\]

The complete exact minimum, including its full rational numerator and
denominator, is recorded in
`computer_assisted/weak_outer_hand_C_slant_exact_replay.json`.
The independent fresh replay is
`computer_assisted/weak_outer_C_slant_global_independent_replay.json`.
It reconstructed every root and child, checked all terminal arithmetic,
and confirmed the same zero frontier and minimum reserve. Its full
physical/source review is
`GLOBAL_OUTER_LINK_EXTRACTION_C_SLANT_INDEPENDENT_REVIEW.md`.

The 2,281,531-byte certificate
`computer_assisted/weak_outer_hand_C_slant_certificate.json.gz` has
SHA-256

`a18dd495524d1d92aefb3139bb5804851a19f50184570bab15d7fb1503dea238`.

The frozen replayer SHA-256 is
`fafbd5c58250832f56cca1bc3d3c143bf822bb440cbb644b2a725085787d5988`.
The inherited exact-helper SHA-256 is
`c3c66a1fcfca7d2e0acd8d9b5a32340f8e8d2253e5e802ff1be34f5cbd0e109f`.
Both hashes matched before the independent run and were unchanged after
it. The helper dependency is explicit; no numerical producer or optimizer
is imported into either exact arithmetic path.

All six deliberately damaged certificates were rejected: a missing
orientation root, a missing closed angle child, a missing owned-separator
child, a false whole-root combination, a negative multiplier, and a
false empty-interval terminal. Their source and complete rejection report
are `computer_assisted/weak_outer_hand_C_slant_controls.py` and
`computer_assisted/weak_outer_hand_C_slant_rejection_controls.json`.

The purely geometric scalar constants in Sections 1--2 also have a
separate exact Fraction replay,
`computer_assisted/weak_outer_hand_C_slant_geometry_replay.json`.
The source/file manifest binds these artifacts and both exact source
dependencies. The floating discovery outcome alone is not a premise.

## 7. Logical scope

The dependencies are the inherited center/inset/cap theorems, the
completed original G-order table, the independent signed cap, and the
strict weak-cone normal-sign theorem. All precede the slant conclusion.
The slant then gives the fixed-unit-disk region and the right-lower
exclusion in Section 1. No right-lower exclusion is assumed in any
table row.

The theorem does not prove that an unselected original must occupy that
forbidden region. The central-upper and left-side placements remain in
the full original-nine domain. This result alone closes neither a fixed
mask nor a positional root, and it does not change the fixed-mask ledger.
