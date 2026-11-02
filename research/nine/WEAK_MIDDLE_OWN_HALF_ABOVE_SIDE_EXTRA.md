# No upper side extra can lie on the selected middle unit's own half

November 2, 2026. Complete physical pen-and-paper reduction and an
independently replayed exact finite arithmetic table. All 46,886 strict
leaves have passed a separate reconstruction. No Lean, Lake, or CI.
This local consequence does not itself assert whole-mask closure.

The later accepted component checkpoint at `3dd2` supplies the short
alternative in Section 8 below. It proves the same local theorem from
the already accepted 22,028-leaf low-side floor input. The independently
verified 46,886-leaf proof in Sections 1--7 remains a complete alternative.

## 1. Caller and precise target

Keep the nine original physical unit squares in the closed disk
`Q=1105/256`, with the original `010/11` marked comparisons. The outer
main links are actual, the middle main link and both selected short
links are weak horizontal-cone comparisons. Use the complete routing
from `WEAK_MIDDLE_TWO_WEAK_SHORT_ROUTING_AND_HIGH_FLOOR.md` to orient the
original selected middle P above both original inner mains B,C. Assume

    yP-hP <= 1/10.

The theorem is that an original extra S in the same horizontal half as P
cannot be in the closed side strip above its assigned inner main. By
horizontal reflection it suffices to consider

    0 <= xP < m=1129/3000,
    l=29/60 <= xS < u=13/12,
    yS > yC.

This note retains the complete inner range `1/2<=hC<13/20`. It does not
assume the main-height conclusion of any new finite table. The selected
right shoulder R remains an original distinct unit throughout.

## 2. The extra S has a sharp horizontal bound

The selected cone P--R and physical center disks imply

    xR-xP >= 1/sqrt(2) > 707/1000=:alpha,

so `xR>alpha`. The complete routing gives `yR>-9/20`; if `yR<3/5`,
the endpoint inset argument in the routing note would give
`xR<121/200<alpha`. Thus `yR>=3/5`.

The closed-Q theorem `TWO_SQUARE_SIDE_STRIP_CENTER_CAP_HAND_PROOF.md`
excludes two original units in `[l,u]` with both centers at height at
least `9/16`. It is a two-square theorem independent of any main-chain
bits. Applying it to R,S gives `yS<9/16`.

The original 3/4 clearance lemma also applies to C,S. Indeed

    |xS-xC| < max(u-gC+1/60,61/60-hC-l)
             < 7/5-hC,

because `hC-gC<69/260<3/10`. Since `yC>-6/5`, we have

    -9/20 < yS < 9/16,             |yS| < 9/16.

The original right endpoint inset has left edge less than
`A=503/480` and vertical inset margin greater than `221/600`.
Its vertical distance from the center of S is therefore less than

    e=9/16-221/600=233/1200.

The half-unit center disk of S avoids that inset. Its horizontal
distance is at least `sqrt(1/4-e^2)`, giving

    xS < A-sqrt(1/4-e^2) < 147/250.                 (1)

The last comparison is rational after squaring positive quantities:

    1/4-(233/1200)^2-(503/480-147/250)^2
       =111739/144000000 > 0.

## 3. The vertical order is C<S<P

The hypothesis gives C<S. We prove S<P using only center disks and
the already derived bounds, without choosing a new cone edge.

The horizontal order is `P<S<R`, because
`xP<m<l<=xS<147/250<alpha<xR`. Equal heights of P and S are impossible:
their horizontal gap is less than `147/250<1`, whereas their center
distance is at least one. Suppose instead `yP<yS`. Then also
`yS<9/16<3/5<=yR`, so the vertical order would be P<S<R.

Both horizontal gaps are less than `3/5`:

    xS-xP < 147/250 < 3/5,
    xR-xS < u-l = 3/5.

Their sum is `xR-xP<u`; hence at least one is less than `13/24`.
The corresponding vertical gap exceeds `21/25`, since

    1-(13/24)^2-(21/25)^2=359/360000>0.

The other vertical gap exceeds `4/5`, by the unit center distance and
the strict horizontal bound `3/5`. Consequently

    yR-yP > 21/25+4/5=41/25.                       (2)

On the other hand `xR>707/1000` and `|cR|<91/60` imply
`yR<671/500`, because

    (707/1000)^2+(671/500)^2-(91/60)^2
       =4817/9000000>0.

The unconditional central routing note proves own-half clearance
`yP-yC>909/1000`; together with `yC>-6/5`, this gives
`yP>-291/1000`. Therefore

    yR-yP < 671/500+291/1000=1633/1000<41/25,

contradicting (2). This establishes the original vertical order

    yC < yS < yP.                                  (3)

## 4. Complete signed physical clearance

For a folded slope `t in [0,1]`, write

    a=1/sqrt(1+t^2), b=t*a,
    f=(a,s*b),              s in {-1,+1}.

For the main retain its halfwidth h and put

    k=sqrt(1/2-h^2), aM=h+k, bM=h-k,
    fM=(aM,sM*bM).

The sum of two original square supports on any of their four genuine
side axes is exactly

    sigma(f,g)=(1+|f dot g|+|det(f,g)|)/2 >= 1.

For a lower square with center abscissa x and an upper one at x+d,
the upward versions of the axes of a frame `(a,s*b)` are

    (s*a,b), (-s*b,a).

Any actual separating normal with nonpositive vertical component has
projection at most `|d|`. All horizontal gaps used below are at most
`147/250<1`, so such a normal cannot reach support sigma. Thus one of
the four displayed upward owned axes separates the original pair.

For ease of exact arithmetic define the weakened clearance

    C(d;f,g) = min over the four upward owned axes (nx,ny) of
               (sigma(f,g)-nx*d)/max(ny,1/20).      (4)

Every numerator is positive, at least `1-147/250=103/250`. Increasing
a positive denominator only lowers the necessary clearance. At a zero
vertical component, the horizontal direction is not a possible actual
separator; adding its finite clipped term to the minimum can only
weaken the bound. Hence the original vertical gap is at least (4),
including all aligned and equal-angle faces.

For fixed frames (4) is a minimum of affine functions of d, and is
therefore concave. No circular center-distance lower bound is combined
with (4) in the concavity argument.

## 5. Eliminate all three horizontal coordinates at box vertices

Put `delta=331/20000`, `g=1/(4h)`, `eta=h+g-1`. The correlated outer
actual-edge bounds in the unconditional routing note give

    g-delta < xC < 1+delta-h.

The original outer cone and endpoint reserve give

    yC > Ymin(h):=g-199/120+(32/9)*eta.              (5)

Together (1), (3)--(5), and the bad selected floor imply

    hP+1/10 > Ymin(h)+C(xS-xC;fM,fS)
                          +C(xP-xS;fS,fP).        (6)

For fixed frames the sum of clearances in (6) is jointly concave in
the three horizontal coordinates `(xC,xP,xS)`: each summand is a
minimum of affine functions of those coordinates. Every point of a
closed rectangular box is a convex combination of its eight vertices.
Concavity therefore bounds the sum below by its minimum at a vertex.

Use the closed box

    xC in [g-delta,1+delta-h],
    xP in [0,1129/3000],
    xS in [29/60,147/250].                         (7)

At an original physical point the main interval is nonempty; indeed
the unconditional routing note supplies `eta<2delta`. The scalar table
may harmlessly evaluate the same endpoint formulas at additional h
values where that interval is inverted, since those points are not
needed by the physical caller.

Write T for the minimum, over the eight vertices of (7), of the sum
of the two clearances. It is enough to prove the following uniform
scalar inequality on three continuous variables and eight sign choices:

    hP+1/10-Ymin(h)-T < 0,
    h in [1/2,13/20], tP,tS in [0,1],
    (sM,sP,sS) in {-1,+1}^3.                      (8)

No shoulder angle, extra height, original main abscissa, or hidden
contact assumption remains. The selected R was used only in the
complete physical deductions of Sections 2--3.

## 6. Complete finite arithmetic table

The certificate `ownhalf_above_side_cover.json` is a forest of eight
closed rational boxes, one for each sign triple in (8). Every internal
node divides one coordinate interval at its exact rational midpoint.
Both children retain that midpoint, so the closed union covers every
boundary. Every leaf proves the strict negativity of (8) on its entire
box, using the minimum over all eight coordinate vertices in (7).

All operations are rational interval addition, subtraction,
multiplication, division by a positive interval, minimum, maximum,
absolute value, and outward square-root bounds. For a nonnegative
rational radicand r, a lower dyadic square-root endpoint is obtained
from the integer square root of `floor(2^180*r)`; the upper endpoint
is increased by one unit of `2^-90` when needed. Squaring the two
rational endpoints checks that they bracket the root. Thus the finite
table is an explicitly specified finite collection of rational
inequalities, rather than an appeal to a numerical optimizer.

The main lower function is evaluated without losing its common h:

    Ymin(h)=32h/9+41/(36h)-32/9-199/120.

It decreases up to `h^2=41/128` and increases afterward. Its exact
interval minimum is therefore the appropriate endpoint value, or
`4sqrt(82)/9-32/9-199/120` if that critical point lies in the interval.
The main a-component decreases with h and its b-component increases;
the slope-frame components use their analogous endpoint monotonicity.

The complete signed-family leaf counts are:

| Signs (main,P,S) | Strict leaves |
|---|---:|
| (-,-,-) | 8,577 |
| (-,-,+) | 1,964 |
| (-,+,-) | 5,399 |
| (-,+,+) | 16,528 |
| (+,-,-) | 652 |
| (+,-,+) | 915 |
| (+,+,-) | 813 |
| (+,+,+) | 12,038 |
| **Total** | **46,886** |

There are 93,764 nodes, maximum depth21, and no unresolved box. The
certificate SHA-256 is

    3a631f728e166fce940b2c69d7435c0ca9e191e9b8e5eab927268e12db56a6f3.

The independent standalone `verify_ownhalf_above_side.py` imports no
producer code or arithmetic. It reconstructs the rational roots, every
split, all eight signed frames and all eight horizontal vertices.
Every leaf passed its Fraction interval calculation with 90-bit outward
radicals. Its largest scalar upper bound is strictly below `-1/100000`;
the full exact rational is retained in
`ownhalf_above_side_cover_independent_replay.json`. The checker SHA-256
is

    a0541942633d3991a1c8fceff3db59f678c696feefc2208fc610d015b04d63b8.

All eighteen damaged or false proof objects were separately rejected;
the record is `ownhalf_above_side_rejection_controls.json`. The
original physical reduction and coordinate-vertex argument also passed
the independent review in
`OWNHALF_ABOVE_SIDE_INDEPENDENT_PHYSICAL_REVIEW.md`.

## 7. Physical conclusion and remaining scope

Any hypothetical original S in the stated own-half upper side strip
would satisfy (1)--(7), and hence (6), for a point of one of the eight
complete roots. The strict table (8) contradicts (6). Therefore such
an original S does not exist. Horizontal reflection covers the left
half; at `xP=0` either choice is valid, so both side strips are excluded
for an original upper side extra.

The theorem uses no new upper bound on either main height. It does not
exclude an extra below its assigned main, or an extra on P's opposite
horizontal half. Those are separate original-caller obligations in the
full 010/11 assembly. Floating discovery of the simplified scalar had
suggested the finite target, but no floating value is a premise of the
accepted exclusion.

## 8. Short proof using the later accepted wide-main low-side input

The accepted `WIDE_MAIN_LOW_SIDE_FORCES_CENTRAL_FLOOR_HAND_TABLE.md`
has the following original-square scope: with only the outer main links
actual, an original right-side unit S satisfying `yC<yS<3/5` forces
every further original upper central F in `0<=xF<=29/60` to have whole
floor greater than1/10. It retains the entire main range up to13/20,
both main and outsider frames, and the original S/endpoint rectangle.
Its complete exact table has22,028 strict leaves and an accepted replay.

For the present caller reflect so xP>=0. Section2 already proves that
the original selected R is a high right-side unit. If a distinct
original extra S were right-side and above C, the original two-square
side-center cap would give `yS<9/16<3/5`. The accepted low-side theorem
therefore applies with its F equal to the original P: P is central,
nonnegative in x, and above both mains. It yields `yP-hP>1/10`,
contradicting the selected bad floor.

This is a complete independent caller proof using the later accepted
input; it needs neither a new main-height theorem nor the finite table
of Section6. Horizontal reflection treats the other half, and at xP=0
the argument applies to each side separately. An assembly may cite this
short route while retaining Sections1--7 as the preserved alternative.
