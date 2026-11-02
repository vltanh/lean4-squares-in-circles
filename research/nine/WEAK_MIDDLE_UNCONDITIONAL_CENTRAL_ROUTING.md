# Every weak-middle central outsider has an unambiguous vertical side

November 2, 2026. Complete hand consequences of accepted weak-middle
geometry, with a rational strengthening of its existing 12-row clearance
table. No new exclusion tree, Lean, Lake, or CI.

## 1. Domain and correlated inward inset edges

Retain four original physical units A,B,C,D in the closed Q-disk,
Q=1105/256, with actual outer links and the original middle horizontal
cone comparison. The middle link may be actual or weak. Every outsider
below is an original independently oriented physical unit disjoint from
both original inner mains. Put

    l=29/60, delta=331/20000,
    h_i=coordinate halfwidth, g_i=1/(4h_i),
    eta_i=h_i+g_i-1, V=eta_B+eta_C.

The accepted outer-link reserve theorem gives h_i<13/20, g_i>5/13,
the original inner bands, and |y_C-y_B|<31/30. The universal center
radius is rhoStar=sqrt(Q-1/4)-1/2<3/2+delta, because

    (2+delta)^2-(Q-1/4)=27061/400000000>0.

The actual left outer edge, h_A>=1/2, and x_A>-rhoStar give

    x_B+g_B>eta_B-delta.

The right outer edge similarly gives

    x_C-g_C<delta-eta_C.                           (1)

The middle cone/inset comparison also gives x_C-x_B>=g_B+g_C. Hence
the actual horizontal gap between these two inner inset edges satisfies

    0<=x_C-g_C-(x_B+g_B)<2delta-V.                (2)

In particular V<2delta. These statements keep the two varying g_i and
do not replace them by the old actual-four lower bound 15/31.

## 2. Every central center clears both insets vertically

Let F be any original unit with |x_F|<=l. The horizontal distance from
its center to either inset's horizontal interval is strictly less than
1/2. For the right inset,
if x_F<=x_C, (1) gives

    x_C-x_F-g_C<delta-eta_C+l<=delta+l
                  =1/2-7/60000<1/2.

If x_F>=x_C, the inherited lower band
x_C>g_C+eta_B-1/60 gives

    x_F-x_C-g_C<l+1/60-2g_C-eta_B<0.

Taking the positive part supplies the actual horizontal distance in
both alternatives. The left argument is reflected. Since the open
half-unit disk centered at F avoids the original inset's interior,
F cannot be vertically inside that inset. Therefore

    |y_F-y_B|>g_B>5/13,
    |y_F-y_C|>g_C>5/13.                            (3)

This includes central boundary and zero-coordinate cases.

## 3. Own-half physical clearance and unconditional routing

The accepted 12-row lemma in
`WEAK_MIDDLE_CENTRAL_ROUTING_AND_LOWER_COUNT.md`, Section 1, states

    |x_F-x_M|<=61/60-h_M ==> |y_F-y_M|>9/10,       (4)

for every physical main frame 1/2<=h_M<=13/20. Its proof is a
two-original-square statement, independent of any main-height premise.

Assign M=C when x_F>=0 and M=B when x_F<=0; either choice works at
zero. The actual horizontal center gap has the bound

    |x_F-x_M|<=max(61/60-h_M,1/2-g_M)
                =61/60-h_M.

The equality follows from h_M-g_M<69/260<31/60. Thus (4) applies
to F and its own-half main. If F lay between the two main heights,
its own-half clearance and its other inset clearance in (3) would give

    |y_C-y_B|>9/10+5/13=167/130>31/30,

contradicting the original middle cone comparison. Equality with either
main is already excluded by (3). Consequently every original central F
satisfies exactly one of

    y_F>max(y_B,y_C),
    y_F<min(y_B,y_C).                             (5)

No low-floor hypothesis, selected short actual edge, or upper bound on
the main heights is needed for this complete routing conclusion.

## 4. The old clearance table already gives 909/1000

The maximum squared distance in the complete 12-row table proving (4)
is 15007/62500. Its proof bounds the distance from every point of the
rectangle |dx|<=61/60-h, |dy|<=9/10 to the original main by the
square root of that number. The exact rational reserve is

    (491/1000)^2-15007/62500=969/1000000>0.

Thus that distance is strictly less than 491/1000. Distance to a fixed
closed set is 1-Lipschitz: the triangle inequality proves that moving
the point by length at most e increases its distance by at most e.
Every point with the same horizontal bound and |dy|<=909/1000 lies
within 9/1000 of the old rectangle. Its distance to the main is
therefore strictly less than

    491/1000+9/1000=1/2.

The original half-unit disk argument proves the strictly stronger bound

    |x_F-x_M|<=61/60-h_M ==> |y_F-y_M|>909/1000.   (6)

This is a hand collar of the already proved rational table. There is
no numerical sample or new tree-coverage assertion in this step.

## 5. A useful conditional lower-central count

Suppose, additionally, both inner main heights are at most -1/4.
Every lower central original in (5), using its own-half main and (6),
has

    y_F<-1/4-909/1000.

Since h_F<=1/sqrt(2)<709/1000, its whole upper edge satisfies

    y_F+h_F<-1/4-909/1000+709/1000=-9/20.          (7)

The radical comparison is exact since (709/1000)^2>1/2. Two such
original central units are excluded by the reflected closed-Q theorem
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`. Hence at most one
central outsider can be below both mains under this additional
main-height premise.

The main-height premise in this section has not been proved here for
the 010/11 low-floor domain. Sections 1-4 are unconditional for the
stated outer-actual/main-cone domain; only the count in Section 5
requires the displayed extra height assumption. This distinction is
retained in any subsequent whole-domain assembly.
