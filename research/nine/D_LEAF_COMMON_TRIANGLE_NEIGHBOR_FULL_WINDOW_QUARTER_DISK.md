# A D root's common triangle neighbor avoids the quarter disk on the full window

**Status: new complete uniform hand proof, submitted for independent
review.** The conclusion and true-degree scope strengthen
`D_LEAF_COMMON_TRIANGLE_NEIGHBOR_AVOIDS_QUARTER_DISK.md` by removing its
separate radius-two prerequisite. The accepted source at SHA256
`2330462d457e8f6eaedae3f8d6c8d535379742a213e033c438827f86b4d31288`
is unchanged. No whole original fine or coarse family is closed here.

## 1. Whole original statement

Keep all nine original interior-disjoint unit squares, the unchanged
circle, and the compatible original selected certificate, with

\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

Let `L` be a genuine D leaf at `H`. The other positive neighbors of
`H` are exactly one actual unit `K` and the actual physical-boundary
units `A_1,...,A_m`, where `m>=1`. Suppose each `A_i` physically
touches `K`; these page--K contacts may carry zero stress. All
displayed units are distinct, and `K` and every page retain arbitrary
other degrees, loads, pair forces, circle masks and individual zero
weights. Every original root normal and application mean is retained.

**Theorem.** The actual closed unit `K` is disjoint from the closed
disk of radius `1/4` about the original circle origin.

The actual root degree is `m+2`. No force equation at `K` or at any
page is imposed by this proof, and no original root force is removed.
The theorem is valid directly on all of (1), with no appeal to a
radius-two lower bound, a measure certificate or a smaller packing.

## 2. A support-span estimate with arbitrary original means

Let `P` minimize `n=(-c,t)` on an actual unit square `W`, where
`c,t>0` and `c^2+t^2=1`. Then

\[
                         \min_W y\ge P_y-c.
\tag{2}
\]

At a minimum-support vertex, write the two orthonormal inward axes
as `u,v`, with `n.u,n.v>=0`. Any inward axis with negative y
component must also have negative x component. Write it `(-p,-q)`
with `p,q>0`. Its support condition `cp>=tq` and unit norm imply
`q<=c`. Two downward axes would both be strictly southwest and
could not be orthogonal. The complete downward span is therefore
at most `c`. This also covers a vertex endpoint of an owned side.

At a minimum-support side, retain `P` at its actual position on
the tangent interval. The inward normal has positive y component,
and the length-one tangent interval has vertical span `c`. This
gives (2) for every side mean. Reflecting vertically yields the
companion fact: if `Q` minimizes `(-u,-v)`, `u,v>0`, `u^2+v^2=1`,
then

\[
                          \max_W y\le Q_y+u.
\tag{3}
\]

Neither statement requires `W` to own the original support normal.

## 3. Full-window root margins and the complete normal cover

The existing genuine D-leaf chart, with the actual radial leaf east,
is

\[
 r=R-\sqrt2,\quad s=1-r,\quad
 H=[-s,r]\times[-b,a],\quad a,b>0,\quad a+b=1,
\]

\[
              p_{HL}=(r,0),\qquad n_{HL}=\mathrm{East}.
\tag{4}
\]

The actual root contains the origin in its open interior and is
physically circle-clear. The full-window physical kernel
`D_LEAF_SHALLOW_SIDE_BOUNDARY_FULL_WINDOW_EXCLUSION.md` proves

\[
 r>11/20,\qquad s>1/3,\qquad r^2-s^2>1/10>1/16
\tag{5}
\]

throughout (1), without any radius-two input.

Suppose an actual point `z` of `K` has `|z|<=1/4`. If both
`a,b>1/4`, all four root margins exceed one quarter and the whole
closed quarter disk lies in the open root. The point `z` would then
force open overlap of `K` with `H`. Reflect the entire actual
configuration vertically if necessary. The complete remaining
domain is

\[
                        0<a\le1/4,\qquad b\ge3/4.
\tag{6}
\]

Let `n` be the original `H`-to-`K` normal. The actual support
inequality gives

\[
                             h_H(n)\le n\cdot z\le1/4.
\tag{7}
\]

If `n_y<=0`, the exact root support is at least
`min(r,s,b)(|n_x|+|n_y|)>1/4`, contradicting (5)--(7). Thus
`n_y>0`. Apply the full-window force-free shallow-D theorem to
each actual triple `H,L,A_i`, using that page's unchanged normal
`m_i` and application. It gives

\[
                             (m_i)_y\le0\quad\text{for every }i.
\tag{8}
\]

Each triple `H,K,A_i` is a physical triangle. If `n` is North,
the complete owned-axis triangle theorem makes `(m_i)_y>=0`.
All pages are then horizontal, and the positive `HK` force makes
the complete root y-force positive, impossible.

If `n` is strict Northeast, the same owned-axis theorem excludes
West and South pages, while the physical opposite-vertex triangle
fact excludes strict Southwest pages. Together with (8), only
East and strict Southeast pages remain. Every root x-force is then
strictly positive, including the actual East leaf, impossible.

The surviving root support is consequently exactly

\[
 n=(-c,t),\quad c,t>0,\quad c^2+t^2=1,
 \qquad P=p_{HK}=(-s,a).
\tag{9}
\]

The same complete triangle cover leaves each page West or strict
Southwest: East and South fail the owned-axis dot-product bound;
strict Southeast is at the opposite root vertex; upward directions
were already excluded in (8). No normal was reselected.

A West page keeps its actual point `(-s,y_i)`, `-b<=y_i<=a`.
Every point of a physical boundary unit has norm at least `r`,
so (5)--(6) imply

\[
                 s^2+y_i^2\ge r^2,\qquad y_i<-1/4.
\tag{10}
\]

Its original origin moment is exactly `y_i<0`. A Southwest page
has its original normal and point

\[
 m_i=(-u_i,-v_i),\quad u_i,v_i>0,\quad u_i^2+v_i^2=1,
 \qquad Q_i=(-s,-b).
\tag{11}
\]

This includes all original axis and variable-mean alternatives
before obtaining the strict-vertex features in (9),(11).

## 4. All original root forces give an actual page with a short span

Let the actual positive leaf, common-neighbor and page magnitudes be
`alpha,gamma,beta_i`. Write `W,S` for the West and Southwest index
sets. The complete root force and origin-torque equations are

\[
 \alpha\mathrm{East}+\gamma n+\sum_i\beta_i m_i=0,
\]

\[
 \gamma(-st+ac)+\sum_{i\in S}\beta_i(sv_i-bu_i)
                  +\sum_{i\in W}\beta_i y_i=0.
\tag{12}
\]

The real leaf has zero origin moment. Every other term is present.
The y-force and then cancellation of the `s` terms give

\[
 \sum_{i\in S}\beta_i v_i=\gamma t>0,
 \qquad
 b\sum_{i\in S}\beta_i u_i
   =\gamma ac+\sum_{i\in W}\beta_i y_i\le\gamma ac.
\tag{13}
\]

The Southwest set is therefore nonempty. Taking the weighted average
with the actual strictly positive weights `beta_i v_i` produces an
existing index `j in S` with

\[
                  \frac{u_j}{v_j}\le\frac{ac}{bt},
                  \qquad u_j\le\frac{4ac}{3t}.
\tag{14}
\]

This chooses an existing page, not a different normal or stress.
The actual West-page moments have strengthened, rather than been
deleted from, (13).

The hypothetical point and (7),(9) also give

\[
 sc+at\le1/4,\quad 0<c<3/4,\quad
                       at<1/4-c/3.
\tag{15}
\]

Combining (14)--(15),

\[
 c+u_j<c+\frac{c(3-4c)}{9(1-c^2)}<1.
\tag{16}
\]

For the last inequality the positive-denominator deficit has numerator

\[
                  F(c)=9-12c-5c^2+9c^3.
\]

On all of `[0,3/4]`,

\[
 F'(c)=27c^2-10c-12
 \le(41/4)c-12\le-69/16<0,
 \qquad F(3/4)=63/64>0.
\]

This is a direct continuous-domain polynomial estimate. It covers
the original upper radius endpoint and a closed quarter-disk tangent
point with strict rational reserves.

## 5. The two actual physical squares have a strict gap

Apply (2) to `K` at its unchanged support `(P,n)` and (3) to the
actual page `A_j` at `(Q_j,m_j)`. They imply

\[
                  \min_K y\ge a-c,
                  \qquad\max_{A_j}y\le-b+u_j=a-1+u_j.
\]

Their strict difference is `1-c-u_j>0` by (16). Thus the two actual
closed squares are separated by a positive vertical gap, contradicting
their required physical contact. This proves the theorem directly on
the entire window (1), including `R=79/40` and the shallow endpoint
`a=1/4`.

## 6. Literal original callers and exact inputs

The same complete genuine D families retain these necessary conclusions:

| Original family | Root `H` | Common neighbor `K` | Complete page list |
| --- | --- | --- | --- |
| House roof AC and ABC | `T` | `D` | `A` |
| Fan leaf at endpoint 1, loads 234 | `1` | fan hub | `2` |
| Fan leaf at inner vertex 2, loads 134 | `2` | fan hub | `1,3` |

The root degrees are three, three and four respectively. In the last
row both original page forces remain; the fan hub retains its fourth
force in every row. The theorem does not make any completion square
physically boundary, assume a central location for a different clear
unit, or close one of these whole families.

The direct operative inputs are:

| Source | Exact SHA256 and operative scope |
| --- | --- |
| `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` | `faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676`; full original genuine D chart and physical root clearance |
| `D_LEAF_SHALLOW_SIDE_BOUNDARY_FULL_WINDOW_EXCLUSION.md` | `ca7c3f4b32e45fc0c118bd766f438fce3019b0b44220604e33bc842a504ac670`; entire full-window force-free boundary-page theorem and exact margins |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207`; degree-free physical owned-axis fact |
| `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` | `20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf`; only Section 2's physical opposite-vertex fact, with no loaded-tip equation |

The support estimates, complete root cover, arbitrary-degree weighted
average, torque cancellation and polynomial inequality are proved above.
The earlier quarter-disk source is a predecessor, not an operative
radius-two input. No theorem or analytic certificate used only to prove
`R>2` is a premise of this full-window proof. No original degree, physical
unit, force, normal, shared mean, mask, ledger, Lean source, build, CI or
remote object was changed.
