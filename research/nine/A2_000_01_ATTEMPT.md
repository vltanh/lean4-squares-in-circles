# Fixed target 000/01: uniform routing, exact deficit, and a seven-square obstruction

Continuation from `3b68416cfa087d56d737d5af0548ba106117fcc6`.

**Target status: OPEN / BLOCKED. New full-mask closures: zero.** This is an attempt record under the fixed-domain contract, not another roadmap or a collection of new mandatory subgates. The selected nine-square predicate has not been proved empty. The statements below have hand derivations; no independent human, second-agent, or kernel review is claimed for this continuation.

The target retains nine physical unit squares, all 36 corner conditions and all 36 physical nonoverlap conditions. In its witness frame, denote the actual center-cone four-chain by M0,M1,M2,M3 and the disjoint short chain by L,P,R. The L--P link is actual; P--R is weak but obeys the center-cone comparison. The other two squares are F,G. They are never assumed coordinate-separated from the selected seven or from each other.

Put Q=1105/256. Write h_S for either coordinate projection halfwidth, g_S=1/(4h_S), eta_S=h_S+g_S-1>=0, and delta_S=h_S-g_S>=0. The centered aligned square of halfwidth g_S is contained in the physical square. Every cone edge therefore has its positive designated coordinate gap at least the sum of the two g's.

## 1. A uniform routing consequence for the entire fixed target

The following does not add a hypothesis to 000/01. It is a consequence of its existing cone and actual links, together with the already proved unrestricted actual-four bounds.

The inputs from the actual-four sources are

    rho=91/60,  |c_S|<rho,
    -91/60<x_0<-89/60,   -31/60<x_1<-29/60,
     29/60<x_2<31/60,     89/60<x_3<91/60,
    h_1,h_2<31/60,       |y_0|+|y_3|<=1/8,
    |x_S|<13/12 for every outsider S.

The center bands and halfwidth bounds also follow directly by summing actual gaps and using |c|<rho. The endpoint budget and outsider strip are supplied by `UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`.

### 1.1 The short chain is forced into left, central, right positions

Its two gaps give

    x_R-x_L >= h_L+h_P+g_P+g_R
              =h_L+1+eta_P+g_R > 37/20,

because h_L>=1/2 and g_R>=1/(2sqrt(2))>7/20. Hence

    x_L < 13/12-37/20 = -23/30 < -3/4,
    x_R > -13/12+37/20 = 23/30 > 3/4.

Separately,

    x_P > -13/12+h_L+h_P >= -1/12,
    x_P < 13/12-g_P-g_R <= 13/12-1/sqrt(2) < 23/60.

Thus P lies strictly between the two internal main centers. These bounds do not assume that any cross-pair has a coordinate separator.

### 1.2 Physical clearances put P on one common side of both inner mains

For a physical unit disjoint from an aligned proxy of halfwidth g, with horizontal center gap D and vertical center gap V, its contained radius-1/2 disk gives

    max(D-g,0)^2 + max(V-g,0)^2 >= 1/4.

For g>15/31 and D<3/5 this implies V>29/30. The exact positive-root check is

    1/4-(18/155)^2-(29/30-15/31)^2 = 2960/864900 > 0.

For g>12/25 and D<9/10 it implies

    V > (12+sqrt(46))/25 > 3/4,

using sqrt(46)>27/4. In both applications D-g<1/2, so the vertical excess must be positive before taking the square root.

The center bands in Section 1.1 give

    0<x_P-x_1<9/10,      0<x_2-x_P<3/5.

Since g_1,g_2>15/31>12/25,

    |y_P-y_1|>3/4,       |y_P-y_2|>29/30.                 (1)

The main middle edge is a cone edge as well as an actual edge. Consequently

    |y_2-y_1| <= x_2-x_1 < 31/30.

If P were between the two main center heights, the left side would exceed 3/4+29/30=103/60, a contradiction. Therefore P is above both or below both. Reflect the vertical coordinate so that P is above both.

### 1.3 Both short-chain ends are above the corresponding inner main

The side bands give |x_L-x_1|<3/5 and |x_R-x_2|<3/5. The same physical clearance proves

    |y_L-y_1|>29/30,     |y_R-y_2|>29/30.

If L were below M1, then (1) would imply y_P-y_L>103/60. But its cone comparison with P gives

    y_P-y_L <= x_P-x_L < 23/60+13/12=88/60,

a contradiction. Thus L is above M1. If R were below M2, then y_P-y_R>58/30, whereas its cone comparison gives

    y_P-y_R <= x_R-x_P < 13/12+1/12=7/6.

This is also impossible. Thus R is above M2.

The existing one-sided physical main-height theorem, `UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`, Section 6, now applies: a side outsider above its corresponding inner main forces that main's center height below 7/20. Therefore

    y_1<7/20,           y_2<7/20.                         (2)

No lower bound -7/20 has been established here. In particular (2) is NOT the bounded-inner-height hypothesis |y_1|,|y_2|<7/20.

For completeness, L and R are also above both outer mains. The two outer main cone comparisons and the endpoint budget give y_1,y_2>-139/120. Hence y_L,y_R>-23/120. Their horizontal gaps from the matched outer mains are positive and below 23/30, so the two contained disks give a vertical gap greater than sqrt(371)/30>3/5. The possibility of an end lying below its matched outer main would give its height below 1/8-3/5=-19/40, contradicting the preceding lower bound. Both ends therefore have

    y_L,y_R > -1/8+3/5 = 19/40 > 7/20.

Together with (2), this puts L and R above both inner mains too. This is a statement about centers; it does not assert full vertical projection separation from any main.

### 1.4 The exact available whole-floor bound

P is between the inner main centers in x and above both in y. The physical adjacent-proxy barrier in `ADJACENT_PROXY_BARRIER_HAND_PROOF.md`, Section 6, therefore applies without an additional coordinate-cover assumption:

    y_P-h_P > min(y_1,y_2)+869/1860.                       (3)

The proof uses g_1,g_2>15/31 and the central proxy gap less than 1/30. This is useful whole-square information, not merely a center estimate. However it gives the needed transfer floor only after controlling the lower main heights. The upper bounds (2) do not supply that control.

**Uniform conclusion.** After one common vertical reflection, the selected short-chain squares are all above both inner main centers, both inner main centers are below 7/20, and (3) holds. All separator owners, all orientations, and both additional units F,G remain in the problem. This consequence resolves the selected chain's vertical sign ambiguity but does not close its full nine-square domain.

## 2. The weighted-cap attempt leaves an exact orientation deficit

Use the already proved physical two-square cap with

    a=46,  b=27/2,  T=211/4,    2T=2a+b.

Define nonnegative span reserves

    W = x_3-x_0-h_0-h_3-2,
    s = x_P-x_L-h_L-h_P,
    t = x_R-x_P-g_P-g_R.

W is nonnegative by the actual four-chain; s is nonnegative by L<_xP; t is nonnegative by the inset consequence of the P-to-R cone edge. These definitions retain the actual pose rather than replacing the weak edge by an actual edge.

The adjusted short span is exactly

    x_R-x_L-h_L-h_R = 1+eta_P-delta_R+s+t.                (4)

Define the actual two-square cap slacks

    K_L = T-a(-x_0-h_0)-b(-x_L-h_L),
    K_R = T-a( x_3-h_3)-b( x_R-h_R).

Both are nonnegative at q<=Q and strictly positive at q<Q, by Theorem 1 of `PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`. Adding the two cap expressions and using (4) gives the exact identity

    b*delta_R = a*W + b*(eta_P+s+t) + K_L+K_R.            (5)

This is not a contradiction. The rightmost square's orientation deficit delta_R can pay for positive cap slacks. At strict radius the necessary inequality is

    delta_R > (92/27)*W + eta_P+s+t.                     (6)

In particular the rightmost short-chain unit cannot be aligned in a strict counterexample. That necessary orientation condition is not a whole-mask exclusion and earns no closure credit.

A proof that the additional physical squares force the opposite weak inequality in (6) would close this cap argument. A different correctly derived sharp terminal would also suffice. Neither implication has been established for every nine-square pose. The next section proves that the seven-square premises alone cannot possibly supply it, even with s=t=W=eta_P=0.

## 3. Exact subcritical seven-square negative control for this same mask

Set q0=273/64. Then

    Q-q0 = 13/256 > 0.

Give M0,M1,M2,M3,L,P the coordinate-aligned unit frame and the centers

| Square | Center |
|---|---|
| M0 | (-3/2,0) |
| M1 | (-1/2,-1) |
| M2 | (1/2,-1) |
| M3 | (3/2,0) |
| L | (-11/12,1) |
| P | (1/12,25/112) |

Give R center

    c_R=(79/84,121/112)

and side axes

    u_R=(4/5,3/5),     v_R=(-3/5,4/5).

They are orthonormal. Its coordinate halfwidth is h_R=7/10 and its aligned inset halfwidth is g_R=5/14.

### 3.1 Every one of the 21 physical pairs is separated

For an aligned unit and R, the sum of support halfwidths in either coordinate direction is 1/2+7/10=6/5. In either axis owned by R the support sum is also 1/2+7/10=6/5. For two aligned units a coordinate center gap of at least one suffices.

| Pair family | Number of pairs | Separating comparison |
|---|---:|---|
| Two main squares | 6 | Horizontal center gap at least 1 |
| L with M0 or M3 | 2 | Vertical center gap 1 |
| L with M1 or M2 | 2 | Vertical center gap 2 |
| P with M0 or M3 | 2 | Horizontal gaps 19/12 and 17/12 |
| P with M1 or M2 | 2 | Vertical center gap 137/112 > 1 |
| R with M0 or M1 | 2 | Horizontal gaps 205/84 and 121/84, both > 6/5 |
| R with M2 | 1 | Vertical center gap 233/112 > 6/5 |
| R with M3 | 1 | v_R dot (c_R-c_M3)=6/5 |
| L with P | 1 | Horizontal center gap 1 |
| L with R | 1 | Horizontal center gap 13/7 > 6/5 |
| P with R | 1 | u_R dot (c_R-c_P)=6/5 |

The two oblique equalities are direct rational calculations:

    c_R-c_M3=(-47/84,121/112),
    (-3/5,4/5) dot (c_R-c_M3)=47/140+121/140=6/5;

    c_R-c_P=(6/7,6/7),
    (4/5,3/5) dot (c_R-c_P)=6/5.

Equality is permitted: the squares have disjoint open interiors. The table covers all 21 distinct pairs, not just the selected chain links.

There are exactly two coordinate-exceptional pairs among these seven: P,R and M3,R. For P,R both coordinate gaps are 6/7<6/5. For M3,R the absolute gaps are 47/84<6/5 and 121/112<6/5. Every other pair has the coordinate comparison printed in the table. Thus one weak selected link does not even guarantee a one-exception cover of the selected seven, let alone of all nine.

### 3.2 The selected links have exactly the target pattern

The three main consecutive center differences are

    (1,-1),   (1,0),   (1,1).

They are actual horizontal comparisons and all satisfy the center-cone inequalities, including both diagonal ties.

For the short chain,

    c_P-c_L=(1,-87/112),      c_R-c_P=(6/7,6/7).

The first is an actual x-comparison and a cone comparison. The second is a cone comparison with tied absolute coordinate gaps, but is weak because

    6/7 < h_P+h_R = 6/5.

This is precisely the selected seven-square portion of 000/01, not the different weak-four/actual-three pattern from the older eight-square obstruction.

### 3.3 Whole-square containment below Q

For an aligned unit centered at (x,y), its largest squared corner norm is (|x|+1/2)^2+(|y|+1/2)^2. Thus

| Square or pair | Largest squared corner norm or a proved upper bound |
|---|---|
| M0,M3 | 17/4 < 273/64 |
| M1,M2 | 13/4 < 273/64 |
| L | 613/144 < 273/64 |
| P | Less than (3/5)^2+(3/4)^2=369/400 < 1 |

The L comparison has exact margin

    273/64-613/144=5/576>0.

For R, its center projections onto its side axes are

    c_R dot u_R=2353/1680>0,      c_R dot v_R=3/10>0.

Consequently the farthest corner is c_R+(u_R+v_R)/2, namely

    (437/420,997/560).

Its positive coordinates obey

    437/420 < 25/24,      997/560 < 57/32,

since 10488<10500 and 31904<31920 respectively. Its squared norm is therefore less than

    (25/24)^2+(57/32)^2
      =39241/9216
      <39312/9216
      =273/64.

The final rational margin is 71/9216. All other corners are no farther by the positive side-projection calculation. Convexity of the disk turns the four-corner checks into containment of every point of every square. The construction is therefore a genuine subcritical physical packing, not a relaxed center assignment.

### 3.4 The cap deficit is actually realized with tight span lower bounds

For this construction,

    W=0,   s=0,   t=0,   eta_P=0,   delta_R=12/35.

The inset lower bound on the weak edge is exact:

    g_P+g_R=1/2+5/14=6/7=x_R-x_P.

The two cap slacks are exactly

    K_L=9/8,      K_R=981/280,
    K_L+K_R=162/35 = (27/2)*(12/35).

Thus (5) is realized with positive cap slacks and with all four span reserves zero. Sharpening an allegedly loose inset step cannot eliminate this example: the inset step is already tight.

This construction does NOT supply F or G. It disproves only the seven-square shortcut. At least one additional square, or another consequence genuinely requiring additional physical squares, must enter any successful extension of this argument. It does not prove that both additional squares are individually indispensable. No eight-square or nine-square counterexample is asserted.

## 4. The exact outstanding obligation remains the same

The full target is still D_000/01^lt, with the two extra physical units F,G and their original containment/nonoverlap constraints. The established same-side routing does not bound both inner main heights below, does not choose valid endpoint separator owners, and does not show that F,G exclude the deficit (6).

The missing implication is not relabeled as a list of new gates. It remains: prove the complete nine-square predicate impossible, either by using the two additional units to close the quantitative deficit or by deriving an already proved terminal with every premise satisfied. The existing one-exception theorem is not an unconditional caller, as the explicit two-exception seven-unit example demonstrates.

The broader eight-square shortcut was explored but not proved or disproved. Failure to find an eight-square example is not evidence of impossibility and is not an accepted lemma. The earlier eight-square construction in `END_EXCEPTION_EIGHT_SQUARE_OBSTRUCTION.md` concerns a different selected-chain mask and cannot be transferred without a valid new witness.

## 5. Method, review boundary, and accounting

Permitted numerical work was limited to direction checks: an eight-start seven-unit optimization batch, a four-start eight-unit batch, a twelve-start eight-unit batch, and a sampled frame search on the repository's existing eight-unit negative control. The frame search tested 721 angles. These were exploratory searches, not exhaustive physical certificates or proof verification. No failed search is used as an exclusion. The seven-unit direction was replaced by the entirely explicit rational construction and the hand pair/corner checks above.

No Lean, Lake, CI, proof enumeration, symbolic verification script, or numerical certificate was run to establish a theorem. The scalar and coordinate calculations in this note were derived and checked by hand. No second-agent or human review of this new source is claimed.

The 32-mask frontier remains unchanged: two inherited complete strict-radius proofs and 30 OPEN masks. No root exclusion, strict root discharge, new mandatory gate, or global equality claim is made. The active target and its reversal partner are still 000/01 and 000/10. This file is a blocked attempt report, not a closure checkpoint.
