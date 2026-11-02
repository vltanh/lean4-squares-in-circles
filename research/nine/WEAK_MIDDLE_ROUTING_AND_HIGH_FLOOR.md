# Uniform routing and the complete high-floor branch of 010/01

This note proves uniform routing and the complete high-floor branch of
the unchanged full `010/01` predicate. The complementary low-floor
analysis is assembled separately in `A2_010_01_WHOLE_DOMAIN_ASSEMBLY.md`.
No Lean, Lake or CI is used. The exact twelve-row discovery check is
followed here by its complete rational table proof.

Use the original labels A,B,C,D for the completed four-chain whose outer
links are actual, and L,P,R for the disjoint cone triple with L--P actual
and P--R weak. All original squares and pair constraints remain present.
Put Q=1105/256, rho=91/60, and write h for a square's coordinate
halfwidth, g=1/(4h), k=sqrt(1/2-h^2), eta=h+g-1.

## 1. A physical clearance lemma for wider inner frames

**Lemma.** Let B and S be physical unit squares with disjoint open
interiors. If `1/2 <= h_B <= 13/20` and

    |x_S-x_B| <= 7/5-h_B,

then `|y_S-y_B| > 3/4`.

The radius-1/2 open disk centered at S belongs to S's interior. Thus
its center must have distance at least 1/2 from B. We prove that the
entire rectangle

    |x-x_B| <= 7/5-h_B,  |y-y_B| <= 3/4

has distance strictly less than 1/2 from B. By coordinate reflections
it is enough to consider the positive quadrant and both chiralities
of B. Put `d=7/5-h`, `a=h+k`, `b=h-k`. At the far corner `(d,3/4)`,
the physical frame coordinates are one of

    (a*d+b*3/4, -b*d+a*3/4),
    (a*d-b*3/4,  b*d+a*3/4).

All four coordinates are positive: throughout this domain a>9/10,
b<2/5, and 3/4<=d<=9/10. If those coordinates are u,v, the squared
distance to B is exactly

    max(u-1/2,0)^2 + max(v-1/2,0)^2.                 (1)

The table below proves (1) <1/4 for both chiralities. Its h intervals
cover [1/2,13/20] with shared boundary endpoints. On each row [l,r],
the printed rational k bounds satisfy

    k_low^2 <= 1/2-r^2,  k_high^2 >= 1/2-l^2.

The functions a=h+k and b=h-k respectively decrease and increase.
Therefore set

    a_upper=l+k_high,
    b_lower=max(0,l-k_high), b_upper=r-k_low,
    d_lower=7/5-r, d_upper=7/5-l.

Valid upper bounds for the four positive frame coordinates are

    U1=a_upper*d_upper+(3/4)*b_upper,
    V1=(3/4)*a_upper-b_lower*d_lower,
    U2=a_upper*d_upper-(3/4)*b_lower,
    V2=b_upper*d_upper+(3/4)*a_upper.

Substitution into (1), taking the larger chirality, is at most the
printed last column. Every check is rational multiplication, addition,
squaring and ordering; no unevaluated real-number computation remains.

| h interval | k lower | k upper | Squared-distance upper |
|---|---:|---:|---:|
| [1/2,41/80] | 487179/1000000 | 1/2 | 119027/500000 |
| [41/80,21/40] | 236841/500000 | 24359/50000 | 233029/1000000 |
| [21/40,43/80] | 459449/1000000 | 473683/1000000 | 228881/1000000 |
| [43/80,11/20] | 444409/1000000 | 9189/20000 | 28209/125000 |
| [11/20,9/16] | 214239/500000 | 44441/100000 | 111737/500000 |
| [9/16,23/40] | 411551/1000000 | 428479/1000000 | 111193/500000 |
| [23/40,47/80] | 393501/1000000 | 12861/31250 | 111263/500000 |
| [47/80,3/5] | 74833/200000 | 196751/500000 | 28007/125000 |
| [3/5,49/80] | 88333/250000 | 187083/500000 | 113593/500000 |
| [49/80,5/8] | 165359/500000 | 353333/1000000 | 14513/62500 |
| [5/8,51/80] | 30593/100000 | 330719/1000000 | 239473/1000000 |
| [51/80,13/20] | 69597/250000 | 305931/1000000 | 248079/1000000 |

The largest bound is `248079/1000000`, leaving reserve
`1921/1000000` below 1/4. The other three vertices of the positive
rectangle have norm less than one and therefore belong to B plus the
open radius-1/2 disk, because B itself contains the closed radius-1/2
disk. This Minkowski sum is convex. Hence all rectangle points have
distance less than 1/2 from B. The hypothetical center of S cannot lie
there, proving the lemma. The two coordinate reflections and two
chiralities cover all signs and frames.

`verify_weak_middle_clearance_table.py` exactly checks the entire table;
its output is `weak_middle_clearance_table.json`.

## 2. Bounds inherited from actual outer links

`OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md` supplies, with
V=eta_B+eta_C,

    V<1/30, h_B,h_C<13/20, g_B,g_C>5/13,
    h_B-61/60 < x_B < 1/60-g_B-eta_C,
    g_C+eta_B-1/60 < x_C < 61/60-h_C,
    |y_A|+|y_D|<=1/8,
    x_D-x_A-h_A-h_D >= 2+V.

In particular `-31/60<x_B<0<x_C<31/60`. The original middle cone
edge gives `|y_C-y_B|<31/30`. Every outsider has `|x|<13/12`.
The selected actual/weak short-chain comparisons therefore give,
exactly as in the current `000/01` attempt,

    -13/12<x_L<-23/30, 23/30<x_R<13/12,
    -1/12<x_P<23/60.

The endpoint frame and inset estimates used below also survive:

    h_A,h_D<8/15, g_A,g_D>15/32,
    g_E-|y_E|>221/600  for E=A,D.

No actual middle edge has been assumed.

## 3. The complete selected triple has common upward routing

For P and B,

    0<x_P-x_B<7/5-h_B.

For P and C, the absolute horizontal gap is at most the larger of
`11/10-h_C` and `2/5-g_C-eta_B`; each is less than `7/5-h_C`.
The lemma gives height differences greater than 3/4 from both mains.
Since their height difference is less than 31/30<3/2, P cannot lie
between them. Reflect vertically so P is above both.

The horizontal gap from L to B is positive and less than
`11/10-g_B-eta_C`. This is less than `7/5-h_B`, because

    h_B-g_B < 13/20-5/13 = 69/260 < 3/10.

The same estimate holds for R and C. Thus L and R have height
clearance greater than 3/4 from their corresponding mains. If L were
below B, then `y_P-y_L>3/2`, whereas its original cone comparison
requires

    y_P-y_L <= x_P-x_L < 22/15 <3/2.

This is impossible. If R were below C, the same sum of clearances
would give `y_P-y_R>3/2`, whereas its cone comparison gives an upper
bound `x_R-x_P<7/6`. Hence L is above B and R is above C.

The outer main cone edges imply

    y_B,y_C > -1/8-(23/15-5/13) = -1987/1560.

Consequently `y_L,y_R > -817/1560 > -3/4`. Physical clearance from
their matched outer endpoints, whose horizontal gaps are less than
3/4, is greater than 7/8. An endpoint-below ordering would put the
shoulder below `1/8-7/8=-3/4`, a contradiction. Both shoulders are
therefore above their original outer endpoints.

The sharper endpoint-inset computation from
`WHOLE_MASK_SHOULDER_AND_NORMAL_REDUCTIONS.md` now applies and yields

    25/32<y_L,y_R<21/16.                            (2)

The upper bound follows also from `|c|<rho` and `|x|>23/30`.
These are the complete shoulder bands needed by the joint cap. This
proof does not assert that L is above C or that R is above B; neither
assertion is needed here.

## 4. Complete high-floor exclusion for 010/01

If `y_P-h_P >=1/10`, the original five physical squares A,L,P,R,D
satisfy every hypothesis of
`UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md`: the endpoints have
their inherited bands, (2) supplies both shoulder bands,
`|x_P|<29/60`, and P has the required whole floor. That theorem gives

    46*(x_D-x_A-h_A-h_D)+27/2 <= 211/2.

But the original middle edge is weak, so V=eta_B+eta_C>0. Its actual
outer links and cone/inset middle link give adjusted long span at least
`2+V>2`. The left side is strictly greater than 211/2. This contradiction
excludes the whole high-floor branch even at closed Q. Reversal supplies
the corresponding branch of `010/10`.

## 5. Why the full inner-frame range is retained

The full assembly treats `y_P-h_P<1/10` using both original extras.
The exact rational control in
`weak_middle_wide_inner_exact_control.json` shows that the selected
seven-square low-floor subsystem can have

    h_B-31/60 =239/72060>0.

Every pair of those seven squares is strictly physically separated, and
all corners lie below Q. Therefore the old actual-four bounds
`h_B,h_C<31/60`, the associated nearly aligned inner-frame estimates and
the dynamic insets from `2(h_B+h_C)` cannot simply be imported. The separate low-floor analysis therefore retains the whole wider
inner-frame range and the two remaining original physical units.
`verify_weak_middle_wide_inner_control.py` independently reconstructs
all 21 physical pairs, all 28 corners, and the five marked comparisons
of this rational control; its report is
`weak_middle_wide_inner_control_replay.json`.
