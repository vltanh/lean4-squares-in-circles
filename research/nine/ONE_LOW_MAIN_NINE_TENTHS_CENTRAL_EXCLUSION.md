# A central outsider below an inner main forces its height above minus nine tenths

November 2, 2026. Complete physical hand reduction and a printed 25-row
exact interval table, discovered with Fraction arithmetic and replayed
with an independent directed-integer implementation. No Lean or CI.

Retain four original unit squares in the closed disk of squared radius
\(Q=1105/256\), forming an actual horizontal four-chain whose consecutive
center comparisons also lie in the horizontal cone. Retain all original
physical nonoverlap and independently oriented frames. Set

\[
                       l=29/60,\quad g_0=15/31.
\]

**Theorem.** If an original central outsider G, with \(|x_G|\le l\),
has center below an inner main M_i, then \(y_i>-9/10\). No height
assumption on the other inner main is needed. Horizontal and vertical
reflections give the corresponding statements for either inner main
and either vertical direction.

## 1. A complete two-variable physical reduction

Reflect horizontally if needed to use the left inner main M1. Suppose
for contradiction \(y_1\le-9/10\) and \(y_G<y_1\). Reflect
vertically, writing \((X,Y)\) for G and \((x_1,Z)\) for M1. Then
\(Y>Z\ge9/10\).

The local one-main argument in Section 2 of
`ACTUAL_FOUR_MIXED_FULL_SIDES_LOWER_CENTRAL_EXCLUSION.md` applies because
\(Z>3/5\). It gives

\[
                           1/3<X\le l.            \tag{1}
\]

That local implication uses only this main, G, the actual-four inset
bounds and the original circle; it does not assume the other main's
height or the presence of a side outsider.

Let \(g_1=1/(4h_1)>g_0\) be the main's aligned inset halfwidth.
The correlated actual-four main edge gives
\(x_1+g_1>-1/60\). Thus its horizontal gap D from G satisfies

\[
                  D-g_1<X+1/60\le1/2.            \tag{2}
\]

The contained radius-one-half disk of G must avoid the inset. Formula
(2) forces its positive vertical center gap \(V=Y-Z\) to exceed
\(g_1\). Therefore

\[
                  Y>9/10+g_0>X>0.                \tag{3}
\]

For G's one original frame put

\[
 t\in[0,1],\quad a=1/\sqrt{1+t^2},\quad b=ta,
 \quad h=(a+b)/2,\quad k=(a-b)/2.
\]

Both physical chiralities imply the common corner inequalities

\[
 Q\ge\max\{(X+h)^2+(Y+k)^2,(X-k)^2+(Y+h)^2\}.
\]

For one chirality these are original corners. For the other its corner
\((X+k,Y+h)\) has squared norm exceeding the second displayed
quantity by \(4Xk\), and the first by \(2(h-k)(Y-X)\).
Both differences are nonnegative by (3). Consequently every original
G obeys

\[
 Y\le U(X,t):=\min\{\sqrt{Q-(X+h)^2}-k,
                  \sqrt{Q-(X-k)^2}-h,91/60\}.      \tag{4}
\]

Put

\[
                    d=X+1/60,\qquad
                    v=U(X,t)-9/10-g_0.            \tag{5}
\]

The actual adjusted gaps satisfy \(D-g_1<d\) and \(V-g_1<v\).
Neither coordinate axis separates G from the main inset: horizontally
\(d\le1/2\le h\), and vertically

\[
 v\le91/60-9/10-15/31<1/2\le h.
\]

Any remaining physical side-axis separator is owned by G and would
require one of

\[
 a(D-g_1)+b(V-g_1)\ge1/2,
 \qquad b(D-g_1)+a(V-g_1)\ge1/2.                  \tag{6}
\]

Taking positive absolute components includes every sign and both
chiralities. If \(v\le0\), both expressions in (6) are strictly
less than one half already, using (2) and \(a\le1,b<1\).
Otherwise it suffices to prove

\[
             \max\{ad+bv,bd+av\}-1/2<0.          \tag{7}
\]

This leaves exactly the closed rectangle
\((X,t)\in[1/3,29/60]\times[0,1]\), with no orientation endpoint,
owner or chirality omitted.

## 2. Printed complete hand table

For a slope interval, a and k decrease while b and h increase. Enclose
their values by the two endpoint evaluations, using outward square-root
enclosures. Apply ordinary interval addition, multiplication, squaring
and minimum to (4)--(7). The following entries are rational upper bounds
rounded upward to multiples of \(10^{-6}\).

The `v` row bounds (5); all other rows bound the left side of (7).
The last column is the upper bound multiplied by \(10^6\).

| X interval | t interval | Rule | \(10^6\) times upper bound |
| --- | --- | --- | ---: |
| \([1/3,49/120]\) | \([0,1/2]\) | axes | -15611 |
| \([1/3,49/120]\) | \([1/2,1]\) | axes | -105722 |
| \([49/120,107/240]\) | \([0,1/4]\) | axes | -8192 |
| \([49/120,107/240]\) | \([1/4,1/2]\) | axes | -12442 |
| \([107/240,223/480]\) | \([0,1/8]\) | axes | -14803 |
| \([107/240,223/480]\) | \([1/8,1/4]\) | axes | -5190 |
| \([223/480,91/192]\) | \([0,1/8]\) | axes | -6632 |
| \([91/192,29/60]\) | \([0,1/16]\) | v | -16548 |
| \([91/192,29/60]\) | \([1/16,1/8]\) | axes | -873 |
| \([223/480,91/192]\) | \([1/8,3/16]\) | axes | -8507 |
| \([223/480,91/192]\) | \([3/16,1/4]\) | axes | -6588 |
| \([91/192,29/60]\) | \([1/8,3/16]\) | axes | -188 |
| \([91/192,919/1920]\) | \([3/16,1/4]\) | axes | -3317 |
| \([919/1920,29/60]\) | \([3/16,7/32]\) | axes | -4279 |
| \([919/1920,29/60]\) | \([7/32,1/4]\) | axes | -4074 |
| \([107/240,223/480]\) | \([1/4,3/8]\) | axes | -3004 |
| \([107/240,223/480]\) | \([3/8,1/2]\) | axes | -29561 |
| \([223/480,91/192]\) | \([1/4,5/16]\) | axes | -3638 |
| \([223/480,91/192]\) | \([5/16,3/8]\) | axes | -9636 |
| \([91/192,919/1920]\) | \([1/4,5/16]\) | axes | -783 |
| \([919/1920,29/60]\) | \([1/4,9/32]\) | axes | -3568 |
| \([919/1920,29/60]\) | \([9/32,5/16]\) | axes | -2739 |
| \([91/192,29/60]\) | \([5/16,3/8]\) | axes | -912 |
| \([223/480,29/60]\) | \([3/8,1/2]\) | axes | -12663 |
| \([49/120,29/60]\) | \([1/2,1]\) | axes | -42408 |

The corresponding 49-node binary midpoint tree proves full coverage of
the root rectangle, including all shared boundaries. Every row excludes
all remaining side-axis alternatives. This contradicts the original
physical nonoverlap of G and the main inset, proving the theorem.

## 3. Exact arithmetic record

`certify_one_low_main_nine_tenths.py` constructs the table with independent
Fraction arithmetic and outward 80-bit radical enclosures. The separate
`verify_one_low_main_nine_tenths.py` uses the directed-integer 64-bit
kernel, reconstructs the entire root cover, and verifies every printed
rational bound above. The certificate is
`one_low_main_nine_tenths_cover.json`, and the complete replay report is
`one_low_main_nine_tenths_replay.json`.

The report records 49 nodes, 25 leaves (one v leaf and 24 axes leaves),
maximum depth 10, and largest exact axes upper bound

\[
                  -3469629010161685/18446744073709551616<0.
\]

The certificate SHA-256 is
`6df3b4ee545678519f33e15af3cfd9103f35e22eeec7e5ee9620f72fb23ebb8f`.
The finite computation is an arithmetic audit of the printed table and
physical reduction, not a human or proof-kernel certification.
