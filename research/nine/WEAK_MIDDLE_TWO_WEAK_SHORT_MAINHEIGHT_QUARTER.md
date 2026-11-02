# The low selected floor forces both weak-middle mains below −1/4

November 2, 2026. Complete computer-assisted hand/table proof. A separate
directed-integer checker has replayed every leaf of the complete finite
cover, and the original-square reduction has passed an independent
physical audit. No Lean, Lake, or CI.

## 1. Full original caller and theorem

Keep the nine original physical units A,B,C,D,L,P,R,F,G of the fixed
010/11 predicate. All their independent frames, corners and physical
pair constraints remain. The main outer comparisons are actual, the main
middle and both selected short comparisons are weak, and all five marked
center comparisons are horizontal cone comparisons. Set Q=1105/256.

The unconditional routing in
`WEAK_MIDDLE_TWO_WEAK_SHORT_ROUTING_AND_HIGH_FLOOR.md` reflects vertically
so P is above both B,C, L above B and R above C, with

    yL,yR > −9/20,
    |xP| < 23/60,   xL < −19/60,   xR > 19/60,
    |xS| < 13/12 for every outsider S.

Assume P's whole floor is at most 1/10. The complete conclusion is

    yB < −1/4,               yC < −1/4.                 (T)

For contradiction choose one offending original main M with yM≥−1/4.
Reflect horizontally, reversing both original chain labels together, so
x=xP≥0. Let zL=−xL and zR=xR. The original right cone comparison and
the physical half-unit center disks give zR−x≥1/√2>7/10.

The outer-link theorem, with h=hM, g=1/(4h), eta=h+g−1, gives

    1/2≤h<13/20,  eta≤V=etaB+etaC<1/30,
    hB−61/60<xB<1/60−gB−etaC,
    gC+etaB−1/60<xC<61/60−hC.

No actual middle edge and no old 31/60 inner-width bound is used. Each
possible offending original lies in one of the sixteen closed roots

    tP,tL,tR ∈ [0,1],  x ∈ [0,23/60],
    zR ∈ [7/10,13/12],  h ∈ [1/2,13/20],
    zL ∈ [19/60,3/5] or [3/5,13/12],
    (sP,sL,sR) ∈ {−1,+1}³.                            (1)

The same P parameter and chirality are retained in both original links.
The two extra originals F,G are not needed to prove (T), but no extra
positions or chain comparisons are imposed on them.

## 2. Frames and signed corner bounds

For each S=P,L,R put

    aS=1/√(1+tS²), bS=tS aS,
    hS=(aS+bS)/2, kS=(aS−bS)/2.

Its physical side axes are (aS,sS bS), (−sS bS,aS). The eight sign
triples in (1) include every independent original frame modulo quarter
turns. Write p=hP, l=hL and r=hR. For a center with nonnegative horizontal
coordinate X define

    U+(X,H,K)=min(√(Q−(X+K)²)−H, √(Q−(X+H)²)+K),
    U−(X,H,K)=min(√(Q−(X+H)²)−K, √(Q−(X−K)²)−H).

The actual signed corners give

    yP≤P+=min(p+1/10, UsP(x,p,kP)),
    yL≤L+=U−sL(zL,l,kL),    yR≤R+=Usr(zR,r,kR).     (2)

For a positive center height the other two corners are dominated by the
two displayed corners. The bounds remain valid for a nonpositive height
because their right sides are positive throughout (1).

## 3. The offending original main gives P's lower height

Set k=√(1/2−h²), aM=h+k, bM=h−k. The original main bands imply

    |x−xM|≤d=61/60−h+x≤9/10,
    g−|x−xM|≥delta=eta−x−1/60.                       (3)

For a left M, the latter follows from xM+g>eta−1/60. For a right M,
the two orders x≤xM and x≥xM give respectively a stronger positive-x
bound or g+xM−x>2g−1/60−x≥eta−1/60−x.

The original inset-to-P comparison has positive vertical separator
component: P is above M and g+1/2−|x−xM|≥1/10. It gives vertical
clearance at least g+RP, where

    RP=min(p, (1/2+delta bP)/aP,
              (1/2+delta aP)/max(bP,1/40)).          (4)

The floor 1/40 removes a zero denominator without changing the minimum.
Every numerator is at least 1/10; when bP<1/40 the last ratio is at least
4 while the first alternative is less than one.

The smaller possible physical support over the two main chiralities is

    sMP=max(1+|h−p|,
            1/2+max(k aP+h bP, h aP−k bP)).          (5)

This is the already proved unsigned two-frame support bound, applied to
the original M/P pair. Every one of its four genuine physical separating
axes has support at least sMP. Thus its center distance is at least sMP,
and its vertical clearance is also at least

    F=min((sMP−aM d)/max(bM,1/40),
          (sMP−bM d)/aM,
          (sMP−aP d)/max(bP,1/40),
          (sMP−bP d)/aP).                          (6)

All numerators are at least 1/10. A denominator floor, when active,
produces a ratio at least 4; an unchanged vertical facet is less than 2,
since sMP≤(1+√2)/2 and aP≥1/√2. Hence these floors again leave the
physical minimum unchanged, including both aligned faces.

Combining (3)–(6) with yM≥−1/4 gives

    yP≥P−=max(g+RP, √max(0,sMP²−d²), F)−1/4.        (7)

This lower bound is a consequence of one retained original main. Its
frame is not replaced by a freely chosen inset or a separate support
parameter.

## 4. Endpoint resources retain both original shoulder tilts

Put a=46, b=27/2 and T=211/4. The two accepted unrestricted physical
pair tolls give, for S=L,R,

    tauS=max(2 bS, 6 bS−b(1−aS)).                  (8)

Let A0=−xA−hA and A3=xD−hD. The actual outer links and middle cone
give A0+A3≥2+V, each Ai<61/60, and therefore Ai>59/60+V. The two
original endpoint/shoulder pairs satisfy

    a A0+b(zL−l)+tauL≤T,
    a A3+b(zR−r)+tauR≤T.

Consequently the following quantities are lower bounds on those same
original endpoint contributions:

    AL=max(59/60,157/184+(27/92)(zR−r)+tauR/46)+eta,
    AR=max(59/60,157/184+(27/92)(zL−l)+tauL/46)+eta. (9)

Necessary additional nonnegative quantities are

    61/60−AL,   61/60−AR,
    1+l+r−zL−zR−(tauL+tauR)/b−(92/27)eta,
    l+451/810−zL−(92/27)eta−tauL/b,
    r+451/810−zR−(92/27)eta−tauR/b.                (10)

The tau values in both the individual and summed inequalities are those
of the same original L,R frames, never independent replacement losses.

## 5. A raised original endpoint inset bounds the shoulders from below

Write J=29927/30000. For the matched endpoint and either lower bound
Astar in (9), its original inset contains

    [503/480,937/480] × [−c,c]

in the horizontally reflected right-hand coordinates, where

    c=max(4421/12000+(32/9)eta,
          1−√(Q−(min(Astar,61/60)+J)²)).           (11)

The first bound is the accepted outer-link endpoint reserve. For the
second use the endpoint's outward corner, hE+kE≥J and hE+gE≥1.
The min in (11) equals Astar on the necessary domain (10), and merely
extends the scalar formula to all roots with positive radicands.

Suppose a shoulder has horizontal absolute coordinate z≥3/5. Its
center height exceeds −9/20. A horizontal or downward separator from
this rectangle to its half-unit center disk would require norm at least
1/2, but

    (503/480−3/5)²+(9/20−221/600)² < 1/4.

Thus its height is above the rectangle and a separating axis between the
rectangle and its original physical square has positive vertical
component. The rectangle's vertical axis gives Y≥c+H. Of the two
upward physical axes, the one directed away from the endpoint has the
only possible improvement: the other is dominated by the vertical axis,
since 937/480−z≥139/160>K.

With local chirality s (the global chirality on the right and its negative
on the left), put q=503/480−z. The exhaustive lower bound is

    Y≥c+H−loss,
    loss=max(0,t(K+q))                         if s=+1,
    loss=max(0,(q−K)/max(t,t0))                if s=−1. (12)

For L in the raised root use t0=1/16; for R use t0=1/4, since zR≥7/10.
These positive denominators do not omit a zero-angle complement:

    k(1/16)>503/480−3/5,
    k(1/4)>503/480−7/10.

The inequalities follow by positive squaring. Below t0 the numerator in
(12) is negative, so its positive part is exactly zero.

Use (12) for R throughout the roots, with Astar=AR. Use it for L in
the raised zL root with Astar=AL; in the other closed zL root retain the
valid weaker lower bound L−=−9/20. This defines L−,R− on all sixteen
roots. The boundary zL=3/5 is included in both roots.

## 6. Every original L/P and P/R physical separator is retained

For an ordered pair i,j with positive horizontal gap D and necessary
vertical gap interval [e−,e+], intersect that interval with the original
cone:

    E−=max(e−,−D),        E+=min(e+,D).

For L→P use D=zL+x, e−=P−−L+, e+=P+−L−. For P→R use
D=zR−x, e−=R−−P+, e+=R+−P−. Its exact original-frame support is

    sigma=(1+|ai aj+si sj bi bj|
             +|sj ai bj−si bi aj|)/2.

Let N be the four actual unsigned owner axes
(ai,si bi),(−si bi,ai),(aj,sj bj),(−sj bj,aj). Each pair requires

    E+−E−≥0,
    D−7/10≥0,
    hi+hj−D≥0,
    D−1/(4hi)−1/(4hj)≥0,
    max[n in N, e in {E−,E+}] |nx D+ny e|−sigma≥0,
    D²+max((E−)²,(E+)²)−sigma²≥0.                 (13)

These include both signs of every owner axis, both possible vertical
orders, the exact weak-bit widths and the original inset cone span.
Taking endpoint maxima only enlarges the projection over the true
vertical interval. No separator family or independent chirality is
dropped.

## 7. Exact finite arithmetic obligation

The 21 necessary scalars are, in order: P+−P−; L+−L−; R+−R−;
1/30−eta; the five entries (10); the six entries (13) for L/P; and the
six entries (13) for P/R. A leaf proves an outward upper bound on one
of these scalars is strictly negative.

The discovery producer uses midpoint splits, with preorder codes 0–6
for a split coordinate and −code−1 for a selected scalar leaf. The
sixteen roots (1) are fixed in lexicographic sign order, with the low
left root before its raised counterpart. All shared faces are retained.

The independent checker reconstructs these exact rational roots, every
midpoint and every physical scalar with directed integer arithmetic. It
accepts every leaf strictly and requires no missing or trailing node.
The completed root counts are:

| (sP,sL,sR) | zL in [19/60,3/5] | zL in [3/5,13/12] |
|---|---:|---:|
| (−,−,−) | 51,589 | 641,977 |
| (−,−,+) | 14,418 | 341,042 |
| (−,+,−) | 38,429 | 332,278 |
| (−,+,+) | 11,360 | 148,956 |
| (+,−,−) | 18,464 | 301,198 |
| (+,−,+) | 53,054 | 4,845,849 |
| (+,+,−) | 24,651 | 220,330 |
| (+,+,+) | 118,192 | 2,526,853 |
| **Total** | **330,157** | **9,358,483** |

Thus the forest has 9,688,640 strict leaves, 19,377,264 nodes, maximum
depth 44, and no frontier. The node count is exactly twice the leaf
count minus the sixteen roots. Its least replayed positive reserve is

    3012203 / 2^48 > 0.

The certificate is `computer_assisted/two_shoulder_mainheight_cover.json.gz`,
a deterministic lossless gzip file with SHA-256

    96a56f82b46083b380ad17d85d343cfa20ae56cfbea26e6de6b429de369e5897.

Its decompressed JSON SHA-256 is

    749759fed4eada8d9fa646d2a1bae6c394cd3c2d4723c33b6951b53fecadcf16.

The standalone checker is `verify_two_shoulder_mainheight_exact.cpp`,
with its standard-library Python byte-binding wrapper of the same stem.
It imports no producer. All interval endpoints are signed integers over
2^48; products and quotients use signed 128-bit intermediates with
outward floor/ceiling. Integer square roots check their two squared
enclosure inequalities. Exact rational root coordinates are subdivided
by integer dyadic indices. The checker also reconstructs all four
original signed corners and the relative-frame support identities.

The complete raw arithmetic replay passed. A separate gzip roundtrip
proved byte-for-byte identity with that replayed JSON; no arithmetic
assertion depends on compression. The reports preserve both identities.
Eighteen malformed or false proof controls were rejected separately.
The independent physical audit is
`MAINHEIGHT_QUARTER_INDEPENDENT_PHYSICAL_REVIEW.md`; the root arithmetic
and coverage audit is `MAINHEIGHT_QUARTER_ROOT_ARITHMETIC_REVIEW.md`.

Every offending original main would supply a point of one of (1), with
all 21 scalars nonnegative. The complete exact forest excludes every
such point. Hence both original main heights are strictly below −1/4,
proving (T), including all closed-Q boundary configurations.

This theorem and the independent central-routing hand lemma imply that
at most one central outsider is below both mains in this low-floor
domain. They do not yet place the two extras in the central strip or
close the whole fixed 010/11 mask. No fixed-ledger count changes here.
