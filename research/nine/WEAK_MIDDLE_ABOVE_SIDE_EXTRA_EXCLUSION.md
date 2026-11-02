# Weak middle edge: low floor excludes above-main extras on both sides

## Theorem and original caller

Work in the complete closed-Q physical `010/01` caller,
`Q=1105/256`, with original main chain `A,B,C,D`, original selected
short chain `L,P,R`, and the two remaining original unit squares.
The actual comparisons are `A--B`, `C--D`, and `L--P`; retain both weak
cone comparisons and every physical nonoverlap constraint. Use the
upward routing in `WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md`.

**Theorem.** If `y_P-h_P<=1/10`, then every additional square S in either
closed side strip is below its assigned inner main:

    x_S<=-29/60  ==>  y_S<y_B,
    x_S>= 29/60  ==>  y_S<y_C.                       (T)

This is a complete exclusion of both above-main side branches. The below-main and central-extra consequences are separate and are
combined in `A2_010_01_WHOLE_DOMAIN_ASSEMBLY.md`. The sharper main-height statement from
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md` is **not** a dependency.
The proof below keeps the actual main width up to `13/20` and the extra's
entire independent orientation.

## 1. Every side extra has center height below 7/20

The standalone closed-disk theorem
`TWO_SQUARE_SIDE_STRIP_CENTER_CAP_HAND_PROOF.md` applies to any two
physical units in a side strip, without a main-chain hypothesis. The
selected shoulder has height greater than `25/32`, so a second side
square S must have `y_S<9/16`. The center-strip width is `3/5`; their
center distance is at least one. Thus S is at least `4/5` below that
shoulder. The shoulder's original center bounds give height less than
`131/100`, hence `y_S<51/100`.

Suppose `y_S>=7/20`. The matched endpoint inset contains the vertical
interval `[-c,c]`, where `c=221/600`, and has halfwidth above `15/32`.
If `y_S<=c`, disk-to-inset distance gives `|x_S|<263/480`. If `y_S>c`,
its vertical excess from the inset is less than `17/120`; the same
distance inequality gives `|x_S|<91/160`. Therefore S lies horizontally
between `29/60` and `91/160`, while its shoulder has absolute x-coordinate
`X in (23/30,13/12)`.

The squared S/shoulder center distance is strictly less than

    f(X)=(X-29/60)^2+(sqrt((91/60)^2-X^2)-7/20)^2.

This function is convex on the indicated interval. The endpoint checks
already given in `WHOLE_MASK_SHOULDER_AND_NORMAL_REDUCTIONS.md` are

    f(23/30)<1-371/9000000,
    f(13/12)<369/400<1.

This contradicts center distance at least one. Thus, on both sides,

    y_S<7/20.                                      (1)

Only the hypothetical lower bound `y_S>=7/20` was used for the inset
argument. In particular the old actual-four inner-main height bound was
not used here.

## 2. Bootstrap the above-main extra into the narrow endpoint strip

Assume S is above its assigned inner main M, and set

    h=h_M, g=1/(4h), eta=h+g-1,
    rho=91/60, B0=263/480.

The outer-link theorem gives `1/2<=h<13/20`, `g>5/13` and the two
reflected inner-center bands. The twelve-row physical clearance lemma
in `WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md` applies to M,S, so their
vertical gap exceeds `3/4`. The outer main cone gives

    y_M > -1987/1560,
    y_S > -817/1560.                               (2)

Together (1)--(2) place S at vertical distance less than

    817/1560-c = 101/650 < 4/25

from the matched endpoint inset. The contained radius-1/2 disk therefore
has horizontal distance greater than

    sqrt(1/4-(4/25)^2) > 47/100

from that inset. The last squared reserve is `7/2000`. As the endpoint
inset halfwidth is greater than `15/32`, this first squeeze yields

    |x_S| < rho-15/32-47/100 = 1387/2400.

The original inner-center band now gives

    |x_S-x_M| < max(1387/2400-(5/13-1/60),1/30)
                =6551/31200 <21/100.

Consequently their vertical gap exceeds
`sqrt(1-(21/100)^2)>97/100`, and

    y_S > -1987/1560+97/100
          =-2369/7800 > -c.

The last reserve is `c-2369/7800=21/325`. Equation (1) also gives
`y_S<7/20<c`. S is therefore inside the endpoint inset's vertical
projection, so the full horizontal disk-to-inset squeeze applies:

    29/60 <= |x_S| < B0.                            (3)

This bootstrap used no near-alignment hypothesis on M.

## 3. P is above S on either side

The same cap-and-center-disk argument as in the low-floor main-height
proof shows `Y=y_R>y=y_P`. The original `P--R` cone and the shoulder
height bound imply

    y >= Y-(X-x) > 3/4-X+x > x-1/3,
    -23/405 <= x=x_P <=23/60.                       (4)

If `y<=y_S`, then (1) bounds their vertical gap above by `41/60-x`.
Their horizontal gap is bounded above by `B0+x` on the left and `B0-x`
on the right. The corresponding squared upper bounds are convex
quadratics in x. All four endpoint reserves are positive:

| Side | x | 1 minus the squared-distance upper bound |
|---|---:|---:|
| Left | `-23/405` | `35441911/167961600` |
| Left | `23/60` | `219/5120` |
| Right | `-23/405` | `14536567/167961600` |
| Right | `23/60` | `203423/230400` |

Thus center distance would be below one, which is impossible. Therefore

    y_M<y_S<y_P.                                   (5)

## 4. Keep the main's endpoint reserve and both physical pairs

The endpoint budget is

    |y_A|+|y_D|+(37/50)(h_A+h_D-1)+(32/9)V <=1/8,
    V=eta_B+eta_C >=eta.

On the right, the outer cone and center bands give
`y_M>=y_D-(x_D-x_M)`, with
`y_D>=-1/8+(32/9)eta`, `x_D<rho`, and `x_M>g-1/60`.
The left is the reflected calculation. Hence, on both sides,

    y_M > g-199/120+(32/9)eta.                      (6)

Equation (3) and the main bands give

    |x_S-x_M| <=d1:=271/480-g <9/50,
    |x_P-x_S| <=d2:=B0+|x| <=149/160<1.             (7)

The harmless use of `|x|` covers both sides in one root.

For two physical units with folded parameters `(a_i,b_i,h_i,k_i)`,
define their smaller-chirality support by

    sigma=max(1+|h_1-h_2|,
              1/2+max(k_1*a_2+h_1*b_2,
                      h_1*a_2-k_1*b_2)).

The first term is a redundant valid support bound, retained to sharpen
interval evaluation. Section 2 of
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md` proves the formula for
both independent chiralities. For any positive vertical center gap and
horizontal gap at most `d<1`, put

    Gamma(d;1,2)=max(sqrt(sigma^2-d^2),
       min((sigma-a_1*d)/b_1,(sigma-b_1*d)/a_1,
           (sigma-a_2*d)/b_2,(sigma-b_2*d)/a_2)).    (8)

Omit zero denominators. Physical center distance supplies the square
root. A genuine physical separator has positive vertical component:
a nonpositive one could contribute at most `d<1<=sigma`. The four true
physical owner axes therefore give the four quotient bounds in (8).
Each numerator is at least `1-d`, and hence greater than `1/20` for
both distances in (7). This also handles the aligned boundary without
division by zero.

Combining (5)--(8), while keeping the original S frame, proves

    y_P >= ylo:=g-199/120+(32/9)eta
                 +Gamma(d1;M,S)+Gamma(d2;S,P).      (9)

This bound is the new necessary input for the completed table.

## 5. Complete six-variable interval root

Keep `tP,tR,x,X,h` and every cap/corner/physical-PR inequality from
Sections 1--5 of
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md`. Add the independent
folded orientation `tS` of the original extra. The complete closed root
is

    tP,tR,tS in [0,1],
    x in [-23/405,23/60], X in [23/30,13/12],
    h in [1/2,13/20].                              (10)

The orientation definitions are
`a(t)=1/sqrt(1+t^2)`, `b=t*a`, `h=(a+b)/2`, `k=(a-b)/2`.
For the actual main, use
`kM=sqrt(1/2-h^2)`, `aM=h+kM`, `bM=h-kM`, `g=1/(4h)`.
Replace only the previous main-height lower bound by (9).

The thirteen necessary expressions are unchanged; in particular they
retain `eta<=V`, the correlated endpoint lower bound A, both physical
R corner orders, the original P/R weak cone and all original P/R
physical owner possibilities. No unselected original square is dropped
from the geometric caller; S is one of the original two extras.

The table's complete leaf counts are:

| Rule | Leaves |
|---:|---:|
| 0 | 7,265 |
| 1 | 31 |
| 2 | 51 |
| 3 | 4,238 |
| 4 | 0 |
| 5 | 5,473 |
| 6 | 14,553 |
| 7 | 0 |
| 8 | 8,632 |
| 9 | 66 |
| 10 | 0 |
| 11 | 0 |
| 12 | 120,927 |
| **Total** | **161,236** |

The independent replay reconstructs all 322,471 nodes, root (10), exact
midpoint coverage, and the displayed necessary expressions using
directed integer interval arithmetic and integer square roots at
scale `2^80`. The maximum tree depth is 30. Floating discovery chooses
only split/leaf tags; its numerical arithmetic is not trusted.

The selected tree, verifier and replay report are
`weak_middle_above_side_physical_candidate.json`,
`verify_weak_middle_above_side_physical_certificate.py`, and
`weak_middle_above_side_physical_exact_replay_report.json`.
The earlier five-variable width-only elimination was too weak and is
not part of this proof. The sharper folded-angle elimination is a valid
auxiliary lemma but is also not used by this six-variable certificate.

Every above-main side extra would satisfy (10) and all table inequalities.
A complete exact replay excluding that root therefore proves (T). The below-main side and central-extra branches are treated in the full
assembly.

## 6. Fresh exact replay record

The independent replay passed every leaf. Its least strictly positive
reserve is

    91020787871806855/1208925819614629174706176

which exceeds `7/100000000`. The accepted tree's SHA-256 is

    9f539289f73dcdca07aca75ec083e9dc96f0bd2db27d1d51e2f3781a22b63c40

The separate executable control
`check_weak_middle_above_side_physical_controls.py` rejects an incomplete
tree, an invalid split axis, a false root leaf and a noninteger tag.
Its report is `weak_middle_above_side_physical_negative_controls.json`.
The exact table is therefore a complete finite exclusion of root (10),
and proves both assertions in (T), including all boundary orientations.

## Independent review record

The root proof agent independently audited the geometry, including the
two-stage endpoint-inset bootstrap, the two signs in the P-above-S
quadratic, the original endpoint reserve, both chiralities and all
physical owners. No gap was found. Its fresh complete exact replay also
passed with the same tree hash and exact least reserve. This record
makes no separate fixed-ledger mask claim.
