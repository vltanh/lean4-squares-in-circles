# Weak middle edge: a complete low-floor main-height table

## Statement and scope

Let the original physical unit squares be the main chain `A,B,C,D`, the
selected short chain `L,P,R`, and the two other original squares. Assume
all corners lie in the closed disk with squared radius

    Q = 1105/256.

The two outer main comparisons `A--B` and `C--D` and the comparison `L--P`
are actual horizontal projection separations. The original middle main
comparison `B--C` and short comparison `P--R` are the weak horizontal-cone
comparisons of mask `010/01`. All physical squares have disjoint
interiors, with independent frames. Keep the original cone comparisons;
no proxy separator replaces them.

Use the upward routing proved in `WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md`.
If the whole floor of P is at most `1/10`, then

    y_B < -3/10,             y_C < -3/10.              (T)

The complete finite table below proves (T). Its original root includes
all `h_B,h_C` allowed by the outer-link theorem, up to `13/20`; in
particular it does **not** import the false weak-middle restriction
`h_B,h_C<31/60`.

This result proves this complete low-floor consequence.
It does not close `010/01` or `010/10`: the two remaining original squares
are handled in the separate side/central consequences assembled in
`A2_010_01_WHOLE_DOMAIN_ASSEMBLY.md`. Horizontal reversal
transfers (T) to `010/10`.

The earlier attempts at the sharper threshold `-7/20` and at `-1/3`
remain incomplete discovery trees and are not dependencies of this proof.
No Lean, Lake, or CI was run.

## 1. Original-caller facts

Write `h_S` for a physical square's common horizontal/vertical
halfwidth, `g_S=1/(4h_S)`, and `eta_S=h_S+g_S-1`. Put

    V=eta_B+eta_C,   p=h_P,   r=h_R,
    x=x_P, X=x_R, y=y_P, Y=y_R, D=X-x,
    C0=451/810, J=29927/30000.

The outer-link theorem in
`OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md` gives

    1/2 <= h_B,h_C < 13/20,      0 <= V < 1/30,
    h_B-61/60 < x_B < 1/60-g_B-eta_C,
    g_C+eta_B-1/60 < x_C < 61/60-h_C,
    x_D-x_A-h_A-h_D >= 2+V,
    g_E-|y_E| > 4421/12000+(32/9)V  (E=A,D).

The uniform routing proof gives P above both B,C and

    25/32 < y_L,y_R < 21/16,
    -1/12 < x_P < 23/60,    23/30 < X < 13/12.

All subsequent uses of these facts weaken strict inequalities to closed
ones, so the final contradiction also covers the disk boundary `q=Q`.

Define adjusted endpoint contributions

    A0=-x_A-h_A,              A3=x_D-h_D.

Then `A0+A3>=2+V`, while each is less than `61/60`; consequently each is
larger than `59/60+V`. The original endpoint/shoulder weighted caps,
with `a=46`, `b=27/2`, `T0=211/4`, are

    a*A0+b*(-x_L-h_L) <= T0,
    a*A3+b*(X-r) <= T0.

Since `L--P` is actual, `-x_L-h_L>=p-x`. Combining these inequalities
retains the useful surplus V:

    x-p+C0-(92/27)V >= 0,
    r+C0-X-(92/27)V >= 0,
    V <= (27/92)W,       W=1+r-p-D,
    A3 >= max(59/60+V,157/184+(27/92)(p-x)+V).       (1)

The bound `x>=p-C0>=-23/405` supplies the complete x-root below.

## 2. Folded orientations, and both chiralities

For each of P,R use an independent parameter `t in [0,1]` and put

    a(t)=1/sqrt(1+t^2),      b(t)=t*a(t),
    h(t)=(a(t)+b(t))/2,      k(t)=(a(t)-b(t))/2.

These are the absolute components of a physical side frame; its
chirality is not fixed. The circle bounds below explicitly take the
maximum over the two physical corner orders.

For unsigned folded angles alpha,beta, the smaller possible
side-axis support of two physical unit squares is

    s(alpha,beta)=(1+cos(alpha-beta)+|sin(alpha-beta)|)/2.

To check the chirality claim, assume `alpha>=beta`. On the two signed
possibilities the relative angles are `alpha-beta` and `alpha+beta`.
Folding modulo `pi/2` preserves `|cos|+|sin|`, and

    (cos(alpha+beta)+sin(alpha+beta))
      -(cos(alpha-beta)+sin(alpha-beta))
       =2*sin(beta)*(cos(alpha)-sin(alpha)) >= 0.

Thus the difference angle gives a valid lower support for either
independent chirality. Moreover

    s(alpha,beta) >= 1+|h(alpha)-h(beta)|.            (2)

For example, for a fixed angular difference the largest halfwidth
difference occurs when the smaller folded angle is zero, where (2) is
an equality. These are support bounds for the original physical squares.

## 3. R lies above P, and its original corners bound its height

The inherited proof of `Y>y` does not use an actual middle main edge.
Indeed, if `y>=Y`, then `Y>3/4` and `y<=p+1/10` imply `p>13/20`.
Equation (1) gives `x>9/100`, hence `D<149/150`. Also

    0 <= y-Y < 1/sqrt(2)+1/10-3/4 < 3/50.

The center-distance square is then less than
`(149/150)^2+(3/50)^2=22282/22500<1`, contradicting the disjoint radius
`1/2` center disks. Therefore

    E=Y-y > 0,              E <= D.                 (3)

The second inequality is the original `P--R` cone comparison. Write
`aP,bP,p,kP` and `aR,bR,r,kR` for the folded parameters. The original
R corners give

    Uplus = min(sqrt(Q-(X+kR)^2)-r,
                kR+sqrt(Q-(X+r)^2)),
    Uminus= min(sqrt(Q-(X+r)^2)-kR,
                sqrt(Q-(X-kR)^2)-r),
    Y <= U=max(Uplus,Uminus).                       (4)

For any lower bound `A<=A3`, the retained original endpoint inset and
outward endpoint corner also give

    cA=max(4421/12000+(32/9)*eta,
           1-sqrt(Q-(A+J)^2)),
    Y >= cA+RR,
    RR=min(r,(1/2+(X-503/480)*bR)/aR,
             (1/2+(X-503/480)*aR)/bR).             (5)

Here `eta<=V` can be any valid lower contribution. At `bR=0`, omit the
last alternative. This is the same physical endpoint-inset calculation
as in the recovered complete `000/01` proof, with the stronger V
reserve retained. Both numerators are positive on the whole root.

## 4. Retain the actual width of the potentially high main

Suppose either original main M in `{B,C}` has `y_M>=-3/10`. Set

    h=h_M, k=sqrt(1/2-h^2), aM=h+k, bM=h-k,
    g=1/(4h), eta=h+g-1.

These variables belong to that one original physical main, and
`eta<=V`. Use the complete closed five-dimensional root

    tP,tR in [0,1],
    x in [-23/405,23/60],
    X in [23/30,13/12],
    h in [1/2,13/20].                              (6)

The inner coordinate bands imply, whether M is B or C,

    |x-x_M| <= d=61/60-h+|x| <= 9/10,
    g-|x-x_M| >= -|x|-1/60=:delta.                  (7)

In particular `g+1/2-|x-x_M|>=1/10`. The actual inset-to-P separator
therefore has positive vertical component. As P is above M, its
vertical clearance is at least

    g+RP,
    RP=min(p,(1/2+delta*bP)/aP,
             (1/2+delta*aP)/bP).                   (8)

Omit the last term when `bP=0`. Its numerator is positive because
`delta>=-2/5`.

The original M and P have the following physical support lower bound,
written in a form that is well suited to intervals:

    sMP=max(1+|h-p|,
            1/2+max(k*aP+h*bP,h*aP-k*bP)).          (9)

The second term is exactly the smaller chirality support of Section 2.
Physical center distance is at least this support, and (7) consequently
gives vertical clearance at least

    sqrt(sMP^2-d^2).                               (10)

Retaining all four genuine physical owner axes gives another bound:

    F=min((sMP-aM*d)/bM, (sMP-bM*d)/aM,
          (sMP-aP*d)/bP, (sMP-bP*d)/aP).            (11)

Terms with zero denominator are omitted. Each numerator is at least
`1/10`, since `sMP>=1`, `d<=9/10`, and all frame components are at most
one. An original separating axis has support at least `sMP`; replacing
its horizontal component by d yields its corresponding term in (11).
Taking the minimum covers every physical owner, sign and chirality.

Thus, for the original P center,

    y >= ylo=max(g+RP,sqrt(sMP^2-d^2),F)-3/10.       (12)

This is a consequence of the supposed high main, rather than a
replacement of that main by an independent proxy. Together with the
low-floor hypothesis it requires `ylo<=p+1/10`.

## 5. The finite necessary-inequality table

Set

    A=max(59/60,157/184+(27/92)(p-x))+eta,
    rad=Q-(A+J)^2,
    Z=min(U-ylo,D),
    sPR=max(1+|p-r|,
            1/2+max(kP*aR+p*bR,p*aR-kP*bR)).

Equation (1) shows `A<=A3<61/60`; equations (3)--(5) and (12) show
`0<E<=Z`. For P/R physical nonoverlap, their four physical owner axes
are dominated, using `D>=E>=0` and `aP>=bP,aR>=bR`, by

    max(aP*D+bP*E,aR*D+bR*E).

It must be at least `sPR`. Their physical center distance is also at
least `sPR`. These facts give all rows of the following table. The
right column records the leaf count in the completed certificate.

| Code | Necessary expression which must be nonnegative | Leaves |
|---:|---|---:|
| 0 | `x-p+C0-(92/27)*eta` | 4,084 |
| 1 | `r+C0-X-(92/27)*eta` | 24 |
| 2 | `W` | 50 |
| 3 | `2*D^2-(1+abs(p-r))^2` | 199 |
| 4 | `61/60-A` | 0 |
| 5 | `p+1/10-ylo` | 3,440 |
| 6 | `U-cA-RR` | 14,936 |
| 7 | `U-ylo` | 0 |
| 8 | `max(aP*D+bP*Z,aR*D+bR*Z)-sPR` | 8,874 |
| 9 | `(27/92)*W-eta` | 110 |
| 10 | `1/30-eta` | 0 |
| 11 | `rad` | 0 |
| 12 | `D^2+max(Z,0)^2-sPR^2` | 20,100 |
| **Total** | **Complete root (6)** | **51,817** |

In row 12 the harmless `max(Z,0)` only increases the squared bound
outside the already necessary region `Z>=0`.

## 6. Complete arithmetic replay and corruption controls

The canonical finite tree is
`weak_middle_mainheight_three_tenths_candidate.json`. Its status is
`DISCOVERY_COMPLETE_AWAITING_EXACT_REPLAY`; the independent replay report
subsequently certifies it. The discovery producer was
`make_weak_middle_mainheight_three_tenths.py`; floating arithmetic in
that producer is not part of the validity argument.

`verify_weak_middle_mainheight_three_tenths.py` reconstructs root (6)
with exact rational endpoints, every midpoint split, and every
inequality above. It uses directed integer intervals at scale `2^80`.
Products and divisions round outward by integer floor/ceiling; square
roots round outward using `isqrt`, with the two squared enclosure
checks. The verifier imports no producer, numerical optimizer or
external solver. At every leaf it proves an upper bound on one
necessary expression is strictly negative. Preorder coverage requires
exactly `2*leaves-1` nodes, no missing branches and no trailing nodes.

The fresh complete replay passed:

    nodes:       103633
    leaves:       51817
    max depth:       33
    scale:         2^80
    least exact positive reserve:
      57690775136268411/604462909807314587353088

The reserve is greater than `9/100000000`. The tree's SHA-256 is

    00016971cd1f58a35dfd16221d8f7baec40d983668fdea33bb6691b2be7c24f7

The exact report is
`weak_middle_mainheight_three_tenths_exact_replay_report.json`.
Four independent corruptions were also rejected: an incomplete tree,
an invalid split axis, a false root leaf, and a noninteger node tag.
The executable control and its report are
`check_weak_middle_mainheight_three_tenths_controls.py` and
`weak_middle_mainheight_three_tenths_negative_controls.json`.

Every possible offending original main M lies in root (6), while no
point of that root satisfies all its necessary inequalities. Hence
neither main can have height at least `-3/10`, proving (T). No statement
about complete side-extra or central-extra coverage follows without
additional geometric work on those original squares.

## Independent review record

The root proof agent independently audited the original-caller geometry,
endpoint/eta algebra, both chiralities, every physical owner, and the
interval expressions, and found no gap. A fresh root-side complete replay
also passed with the same accepted tree hash and exact least reserve.
This independent review does not change the fixed mask ledger.
