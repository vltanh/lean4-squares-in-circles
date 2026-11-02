# Weak middle edge: central clearance, routing, and the lower-extra count

## 1. A twelve-row physical clearance lemma

**Lemma.** Let M,S be disjoint physical unit squares, with arbitrary
independent frames, and let `1/2<=h_M<=13/20`. Then

    |x_S-x_M|<=61/60-h_M  ==>  |y_S-y_M|>9/10.       (1)

This is a two-square statement; the main-chain caller enters only in
Section 2. Put `h=h_M`, `k=sqrt(1/2-h^2)`, `a=h+k`, `b=h-k`,
`d=61/60-h`, and `y=9/10`. The square M has side-frame components a,b.
The radius-1/2 disk centered at S must avoid the interior of M.

If (1) were false, its center would lie in the rectangle
`[-d,d] x [-y,y]` about M. Distance to a closed convex set is convex, so
it suffices to bound the distance to M at the rectangle's four corners.
Central symmetry reduces these to `(d,y)` for the two frame chiralities.
In M's side coordinates their unsigned coordinates are

    (a*d+b*y, a*y-b*d),
    (a*d-b*y, b*d+a*y).

All four displayed coordinates are nonnegative on the stated h-range;
the table verifier checks positive lower bounds on the two differences
in every row. For a point `(u,v)` in side coordinates, its squared
distance to M is

    max(u-1/2,0)^2+max(v-1/2,0)^2.                  (2)

For a row `[l,u]`, choose rational bounds `klo<=k<=khi` by squaring.
The functions a and b respectively decrease and increase with h.
Consequently, with

    aup=l+khi, blo=max(0,l-khi), bup=u-klo,
    dlo=61/60-u, dup=61/60-l,

upper bounds for the two coordinate pairs are

    (aup*dup+bup*y, aup*y-blo*dlo),
    (aup*dup-blo*y, bup*dup+aup*y).

Substitute these nonnegative upper bounds into (2). The following table
rounds each resulting bound upward to a multiple of `1/1000000`.
Every k-bound is independently checked by the squared inequalities.

| h interval | k lower | k upper | squared-distance upper |
|---|---:|---:|---:|
| [1/2,41/80] | 487179/1000000 | 1/2 | 34183/200000 |
| [41/80,21/40] | 236841/500000 | 24359/50000 | 181123/1000000 |
| [21/40,43/80] | 459449/1000000 | 473683/1000000 | 38227/200000 |
| [43/80,11/20] | 444409/1000000 | 9189/20000 | 200571/1000000 |
| [11/20,9/16] | 214239/500000 | 44441/100000 | 104659/500000 |
| [9/16,23/40] | 411551/1000000 | 428479/1000000 | 217263/1000000 |
| [23/40,47/80] | 393501/1000000 | 12861/31250 | 112139/500000 |
| [47/80,3/5] | 74833/200000 | 196751/500000 | 23023/100000 |
| [3/5,49/80] | 88333/250000 | 187083/500000 | 23497/100000 |
| [49/80,5/8] | 165359/500000 | 353333/1000000 | 238329/1000000 |
| [5/8,51/80] | 30593/100000 | 330719/1000000 | 15007/62500 |
| [51/80,13/20] | 69597/250000 | 305931/1000000 | 240091/1000000 |

The maximum is `15007/62500`, which is below `1/4` by `309/31250`.
Thus the entire rectangle lies at distance strictly less than `1/2`
from M. A radius-1/2 disk centered there would overlap M's interior,
contradicting physical disjointness. This proves (1), including all
boundary h and horizontal-gap values and both frame chiralities.

The exact arithmetic check is
`verify_weak_middle_central_clearance_table.py`; its complete rational
report is `weak_middle_central_clearance_table.json`. It uses only
`Fraction` arithmetic and integer square-root bounds. The twelve rows
above constitute the finite hand table; no subdivision discovery tree,
external solver, Lean, Lake, or CI is required.

## 2. An original outer-cone bound puts both main heights above -6/5

Keep the original `010/01` caller and its endpoint reserve. For either
inner main M, with `h=h_M`, `g=1/(4h)`, `eta=h+g-1`, the original outer
cone and inner-center bands imply

    y_M > g-199/120+(32/9)*eta.

Indeed the matched endpoint has height at least
`-1/8+(32/9)*eta`, horizontal coordinate of absolute value below
`rho=91/60`, and the inner main is horizontally at least `g-1/60`
inward from the central axis. This is the same reflected calculation
on both sides. The larger contribution from the other main is harmless
and can be dropped.

The arithmetic-geometric mean inequality gives

    g+(32/9)*eta
      = (32/9)*h+41/(36*h)-32/9
      >= 4*sqrt(82)/9-32/9 > 11/24.

For the last strict comparison, multiply by72 and use

    32*sqrt(82)>289,
    32^2*82-289^2=447>0.

Therefore

    y_B,y_C > 11/24-199/120 = -6/5.                (3)

No actual middle comparison is used.

## 3. Every central extra is above both mains or below both

Under the low-floor hypothesis, the complete exact theorem in
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md` gives

    y_B,y_C < -3/10.                               (4)

Combining (3)--(4), their height spread is strictly less than `9/10`.

Let F be any original extra whose center satisfies `|x_F|<29/60`.
If `x_F>=0`, use M=C; if `x_F<=0`, use M=B. At zero either choice works.
The original main-center bands show

    |x_F-x_M| <= max(61/60-h_M,1/2-g_M)
                =61/60-h_M.

The equality holds because `h_M-g_M<69/260<31/60`.
Lemma (1) thus gives `|y_F-y_M|>9/10`. Since the other main differs in
height by less than `9/10`, F cannot lie between the main heights:

    either y_F>max(y_B,y_C),
    or     y_F<min(y_B,y_C).                       (5)

This is an exhaustive routing statement for every original central
extra, independent of its orientation. It uses no near-aligned bound on
the inner main frames.

## 4. At most one original central extra can be lower

If F takes the lower alternative in (5), its clearance from its assigned
main and (4) give

    y_F < -3/10-9/10 = -6/5.

Every unit square has `h_F<=1/sqrt(2)<3/4`. Hence its whole upper edge
satisfies

    y_F+h_F < -6/5+3/4 = -9/20.                    (6)

Two such lower central extras would both lie in `|x|<29/60` and wholly
below `-9/20`. The reflected closed-Q theorem
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md` excludes that pair, including
the equality radius. Thus at most one original central extra is lower.

Once the separate side-extra exclusions place both original extras in
the central strip, (5)--(6) therefore guarantee an original extra U
above both main centers. This deduction does not yet prove that U is
above P or that its whole floor exceeds `1/10`; those remain the next
explicit geometric obligations.
