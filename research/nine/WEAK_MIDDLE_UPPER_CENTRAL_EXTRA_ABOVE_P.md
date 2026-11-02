# Weak middle edge: every upper central extra lies above P

## Complete statement

Retain the original closed-Q physical `010/01` caller and upward routing,
with `Q=1105/256`, actual outer main links and actual `L--P`, both weak
cone comparisons, independent physical frames, and all original squares.
Suppose `y_P-h_P<=1/10`. If an original extra U satisfies

    |x_U|<29/60,       y_U>max(y_B,y_C),

then

    y_U>y_P.                                        (T)

This is a complete consequence over the stated moving domain. It makes
no fixed-ledger mask closure claim. The input that some original extra
is upper central is separate; see
`WEAK_MIDDLE_CENTRAL_ROUTING_AND_LOWER_COUNT.md`. The next required
consequence is that this U has whole floor above `1/10`.

## 1. Choose an original main without restricting the extra's sign

Write `z=|x_U|`. If `x_U>=0`, choose M=C; if `x_U<=0`, choose M=B.
At zero either choice is valid. Put

    h=h_M, g=1/(4h), eta=h+g-1,
    p=h_P, r=h_R, x=x_P, X=x_R.

The original outer cone and endpoint reserve give, as proved in the
above-side manuscript,

    y_M > Ymin:=g-199/120+(32/9)*eta.                (1)

After reflection to the chosen half-plane, its center lies in

    g-1/60 < |x_M| < 61/60-h.

Consequently the actual horizontal gaps obey

    |x_U-x_M| <=d1:=max(z-g+1/60,61/60-h-z),
    |x_P-x_U| <=d2:=|x|+z.                         (2)

Both bounds cover the original point without assigning a new center to
M or U. On physical points `d1>=0`, and the complete domain gives
`d1<=31/60`, `d2<=13/15<1`. The harmless use of `|x|` permits both signs
of x_U in one table. Root points violating the already necessary
`eta<=1/30` need not describe a realizable inner-center interval; they
remain in the interval root as extra obligations.

## 2. Suppose U is at or below P

Equal heights are impossible because their horizontal gap is below
`13/15<1`, contradicting the radius-1/2 center disks. Hence a hypothetical
counterexample to (T) would have

    y_M<y_U<y_P.

Use the physical clearance function `Gamma` from Section 4 of
`WEAK_MIDDLE_ABOVE_SIDE_EXTRA_EXCLUSION.md`. It is the maximum of the
true support-based center-distance clearance and the minimum of all
four genuine physical side-axis clearances, with the smaller-chirality
support retained. All independent physical owners, signs, and frames
are covered. Since both distances in (2) are below one, its four
numerators are positive; the exact table weakens their lower bound to
`1/20`.

The two original physical pairs M/U and U/P therefore imply

    y_P >= ylo:=Ymin+Gamma(d1;M,U)+Gamma(d2;U,P).    (3)

This retains the original U orientation and uses U only after deriving
its original pair constraints. No coordinate separator or center-cone
condition is presumed for either of these new pairs.

## 3. Complete seven-dimensional table

Use the slope orientation parameter `t in [0,1]` with

    a=1/sqrt(1+t^2), b=t*a, h=(a+b)/2, k=(a-b)/2.

For M, retain h directly and set
`kM=sqrt(1/2-h^2)`, `aM=h+kM`, `bM=h-kM`.
The complete closed root is

    tP,tR,tU in [0,1],
    x in [-23/405,23/60], X in [23/30,13/12],
    h in [1/2,13/20], z in [0,29/60].               (4)

Keep exactly the thirteen necessary cap, corner, cone, low-floor and
physical-P/R expressions of Section 5 of
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md`, using (3) for ylo.
In particular `eta<=V=eta_B+eta_C` retains the common endpoint span, and
both actual R corner orders and all P/R physical owners remain live.
The finite complete tree has these leaf counts:

| Rule | Leaves |
|---:|---:|
| 0 | 12,801 |
| 1 | 20 |
| 2 | 129 |
| 3 | 1,427 |
| 4 | 0 |
| 5 | 25,812 |
| 6 | 16,900 |
| 7 | 0 |
| 8 | 3,066 |
| 9 | 147 |
| 10 | 0 |
| 11 | 0 |
| 12 | 95,093 |
| **Total** | **155,395** |

The independent directed-integer replay at scale `2^80` checked every
leaf, the exact rational root, every midpoint split, and complete
binary coverage. It passed all 310,789 nodes, maximum depth32, with
least positive reserve

    490502150380008487/1208925819614629174706176

which exceeds `4/10000000`. The accepted tree's SHA-256 is

    ca931848e2f5e76e7fff74a0233dd344fbccde2d11f0611f22de76907482a92a

Files:

- `weak_middle_central_below_p_candidate.json` — complete finite tree;
- `verify_weak_middle_central_below_p_certificate.py` — independent exact
  reconstruction; no floating arithmetic or discovery import;
- `weak_middle_central_below_p_exact_replay_report.json` — fresh complete
  replay record.

The floating producer only selected split and leaf tags. Exact products,
divisions, and integer square-root enclosures determine every final
reserve. No Lean, Lake, or CI was run.

Any original central U above both mains but at or below P would lie in
(4) and satisfy all table expressions. The complete exact exclusion is
a contradiction, proving (T).
