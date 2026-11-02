# A right-side unit cannot lie above a raised aligned proxy

November 2, 2026. Complete physical statement and 112-row exact cover,
with an independent integer dyadic replay. No Lean or CI.

Put \(Q=1105/256\), \(l=29/60\), \(u=13/12\),
\(\rho=91/60\).

## 1. Complete statement

Let C be an aligned closed square of any positive halfwidth g, centered
at \((X_0,Y_0)\), whose right edge and top satisfy

\[
                        X_0+g\ge7/10,
                 \qquad Y_0+g\ge869/1000.
\tag{1}
\]

Let R be an original physical unit square contained in the closed Q-disk,
with center \((s,z)\) satisfying

\[
                       l\le s\le u,
                 \qquad s\ge X_0,\quad z\ge Y_0.
\tag{2}
\]

Then C and R cannot have disjoint open interiors. The theorem includes
contact limits in (1)--(2), every original R orientation, both chiralities,
and every physical separator owner. In a caller C may be the contained
aligned square of another original unit.

## 2. Eliminate the arbitrary proxy

Write the absolute components of the one original R frame as

\[
 a=(1+t^2)^{-1/2},\quad b=ta,\quad
 h=(a+b)/2,\quad k=(a-b)/2,\quad 0\le t\le1.
\]

The two chiralities give the original corner upper bounds

\[
 U_+=\min\{\sqrt{Q-(s+k)^2}-h,
                  \sqrt{Q-(s+h)^2}+k\},
\]

\[
 U_-=\min\{\sqrt{Q-(s-k)^2}-h,
                  \sqrt{Q-(s+h)^2}-k\}.
\]

Thus every physical R satisfies

\[
                      z\le U:=\min(\rho,\max(U_+,U_-)).
\tag{3}
\]

These are actual corners in each original frame. Taking the maximum covers
both chiralities rather than imposing a favorable frame. The upper bound
also holds for arbitrary real z; the corner square inequalities always
bound the relevant signed vertical coordinate above by its positive root.

Let D=s-X0 and V=z-Y0, both nonnegative by (2). By (1) and (3),

\[
                  D-g\le d:=s-7/10,
             \qquad V-g\le v:=U-869/1000.
\tag{4}
\]

If C and R are disjoint, their separating-axis theorem requires at least
one of

\[
              d-h,\qquad v-h,\qquad
              ad+bv-1/2,\qquad bd+av-1/2
\tag{5}
\]

to be nonnegative. The first two alternatives are the coordinate axes
owned by C. For an R-owned axis, replacing its signed components by their
absolute values only increases its center projection because D,V>=0;
subtracting C's support then gives one of the last two alternatives.
This includes both component orders and every sign for the original frame.

## 3. The complete exact table

The root rectangle is \((s,t)\in[l,u]\times[0,1]\).
`right_unit_above_proxy_cover.json` is a complete midpoint binary cover of
that root, with 223 nodes and 112 leaves, maximum depth 10. At every leaf,
all four interval upper bounds in (5) are strictly negative. Every split
has both closed children, including midpoint faces, and every node is used
exactly once. There are no omitted or unresolved boxes.

The producer uses exact Fraction intervals with outward 64-bit square-root
bounds. The independent standalone `verify_right_unit_above_proxy.py`
implements outward 64-bit integer dyadic intervals, reconstructs every
box, and recomputes (3)--(5). It imports neither the producer nor its
Fraction interval evaluator. It explicitly loops over both chiralities
before taking the common upper bound.

The replay `right_unit_above_proxy_dyadic_replay.json` reports PASS on all
112 leaves, with least exact positive reserve
\(45534280734693/576460752303423488\). The certificate SHA256 is
`44b526b05af588c2268ff15d73874bb36484c23a0afe3a8c50450a86c2d84e81`.
The exhaustive strict exclusions in (5) contradict physical disjointness,
proving the theorem.

This is a standalone physical proxy cap. A caller must establish the two
edge bounds and the actual horizontal and vertical center orders in
(1)--(2); the table does not supply those hypotheses.
