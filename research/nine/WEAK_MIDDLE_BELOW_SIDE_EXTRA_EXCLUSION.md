# Weak middle edge: transfer of the lower-side height envelope

## Statement and complete caller

Retain the original closed-Q physical `010/01` caller, its upward routing,
actual outer main links and actual `L--P`, both original weak cone
comparisons, all physical pairs, and independent frames. Assume
`y_P-h_P<=1/10`. The complete consequence is that no original
extra in either closed side strip lies below its assigned inner main.
Together with `WEAK_MIDDLE_ABOVE_SIDE_EXTRA_EXCLUSION.md`, this puts both
original extras in the open central strip. This note does not itself
change any fixed-ledger mask count.

The physical lower-side pair theorem is supplied by the separately
checked envelope table in `side_height_envelope_bump_plus_1_400_candidate.json`
and its independent `verify_side_height_envelope.py` replay. For the
assigned original main M, it gives

    y_M > f(h),
    f(h)=-(2/3)h+max(0,min((h-1/2)/6,(27/50-h)/3))+1/400,
    1/2<=h=h_M<=13/20.                             (1)

Its complete three-dimensional root retains the side extra's physical
frame, original corners, and every genuine M/extra owner-axis and inset
clearance. The exact complete pair table has3,387 leaves. The envelope
is a derived consequence of an original lower-side extra, rather than a
freely chosen main-height hypothesis.

## 1. Transfer (1) into the original P/R cap system

Keep exactly the notation and complete five-dimensional root of
`WEAK_MIDDLE_LOW_FLOOR_MAINHEIGHT_THREE_TENTHS.md`:

    tP,tR in [0,1], x in [-23/405,23/60],
    X in [23/30,13/12], h in [1/2,13/20].            (2)

Let `KMP` be the maximum of the original inset, support-based center
distance, and four genuine side-axis clearances from that note's
Section4. The original P lies above both mains. Hence (1) gives

    y_P >= ylo:=f(h)+KMP.                            (3)

Every other cap/corner/cone/physical-P/R expression in that note's
thirteen-row table remains necessary. No old actual-middle width bound
is imported. The target f includes its whole h-range and both pieces of
the bump, with their equality faces.

The additional row below is a positive weighted sum of two of those
necessary inequalities. It makes the finite table much less dependent
on independently enclosing the two center coordinates.

## 2. A positive weighted combination retaining a physical P/R owner

Put `lambda=9/10`, `kappa=27/92`, and `a0=503/480`.
Write `a_i,b_i` for either P's or R's absolute folded frame components.
The original cone gives `D=X-x>=E=Y-y>0`, so some original physical owner
must satisfy

    a_i*(X-x)+b_i*(Y-y)-sigma_PR >=0.               (4)

The original endpoint inset also gives

    Y-cA-RR >=0.                                   (5)

Here `sigma_PR` is the smaller-chirality physical support, and cA,RR
are exactly the original endpoint bounds from the thirteen-row table.
Adding lambda times (5) to (4) shows that, for at least one i,

    a_i*X-a_i*x+(b_i+lambda)*Y-b_i*y
       -sigma_PR-lambda*cA-lambda*RR >=0.           (6)

No signed-normal owner or endpoint is changed by this step.

## 3. Exact scalar maximization used in the new interval row

For rational `alpha`, positive rational `beta`, and `0<=l<=u`, define

    H(alpha,beta;[l,u])
      =max_{z in [l,u], z^2<=Q}
          (alpha*z+beta*sqrt(Q-z^2)).               (7)

This maximum has an elementary exact enclosure. For `alpha<=0` it is
at l. For `alpha>0`, its unconstrained maximizer is
`sqrt(Q)*alpha/sqrt(alpha^2+beta^2)`. Comparing that point with l or u
requires only squaring positive quantities:

    Q*alpha^2 compared with (alpha^2+beta^2)*l^2
    or with (alpha^2+beta^2)*u^2.

If it is to the left or right, evaluate the corresponding endpoint;
otherwise the answer is `sqrt(Q*(alpha^2+beta^2))`. An upper interval
endpoint beyond `sqrt(Q)` simply removes the right-endpoint case.
Thus (7) needs rational arithmetic and directed integer square roots,
with no numerical maximizer.

For a current exact interval box, write a subscript `lo` or `hi` for a
rigorous enclosure endpoint. Define

    C=J+157/184+kappa*p_lo+eta_lo,
    J=29927/30000, eta=h+1/(4h)-1.

The original endpoint has adjusted coordinate at least
`157/184+kappa*(p-x)+eta`, so its inset top satisfies

    cA >= 1-sqrt(Q-(C-kappa*x)^2).                  (8)

At every physical point the radical is real and its argument has
nonnegative horizontal coordinate. For either rational endpoint
`a in {a_i,lo,a_i,hi}`, equations (7)--(8) give

    -a*x-lambda*cA
      <= H(a/kappa,lambda;[C-kappa*x_hi,C-kappa*x_lo])
          -(a/kappa)*C-lambda.                     (9)

Taking the maximum over those two a-values bounds the actual
`-a_i*x-lambda*cA`, since this expression is affine in a_i for fixed x.
Call that interval upper bound `Gx_i`.

## 4. Eliminate the original R-center coordinate in the same row

Its inset reach has the three exact alternatives

    RR=min(r, 1/(2aR)+tR*(X-a0),
                 (1/2+(X-a0)*aR)/bR).

The last alternative is omitted at `bR=0`. On an interval box, RR is at
least the minimum of the following affine lower bounds:

    r_lo,
    1/(2aR_hi)+tR_lo*(X-a0),
    1/(2aR_hi)+tR_hi*(X-a0),
    L2 := lower(1/2+(X-a0)*aR)/bR_hi.               (10)

Omit L2 when `bR_hi=0`. Positivity of its numerator is already proved
on root (2). The two middle alternatives cover the uncertain tR for
either sign of `X-a0`. Thus (10) keeps the complete minimum reach; it
does not choose a favorable physical owner.

For one R chirality, the two valid corner upper bounds have the form

    Y<=sqrt(Q-(X+c)^2)-o,
    (c,o)=(kR_lo,r_lo) or (r_lo,-kR_hi).

For the other chirality, the corresponding pairs are

    (c,o)=(r_lo,kR_lo) or (-kR_hi,r_lo).             (11)

All `X+c` are positive on the root. Replacing a physical horizontal
corner offset by its lower bound and the vertical offset by its lower
bound increases the displayed height cap.

For a lower-reach alternative `q+t*(X-a0)` from (10), put

    alpha=a_i,hi-lambda*t, beta=b_i,hi+lambda.

Since `X>0` and `Y>0`, the corresponding part of (6) is at most

    H(alpha,beta;[X_lo+c,X_hi+c])
       -alpha*c-beta*o-lambda*q+lambda*t*a0.        (12)

For each fixed reach alternative and chirality, take the minimum of
the two corner bounds (12). Then take the maximum over both
chiralities and all reach alternatives. Call this upper bound `GX_i`.
The minimum/maximum order covers every original physical possibility;
maximizing each individual corner cap only enlarges the result.

Finally, (3), (9), and (12) bound (6) above by

    Bi=GX_i+Gx_i-lower(b_i*ylo)-lower(sigma_PR).     (13)

Every physical witness must have `max(BP,BR)>=0`. The new leaf rule13
proves its exact upper enclosure strictly negative. This argument uses
the original physical P/R owner and endpoint inset throughout.

## 5. Complete discovery and separate exact acceptance

The selected finite tree is `weak_middle_below_side_fast_balanced_candidate.json`.
A C++ floating producer selected its split and leaf tags; that producer
is untrusted discovery only. It produced a complete closed cover with
736,249 nodes,368,125 leaves, maximum depth43, and no frontier.
Its SHA-256 is

    db6894140b37c3ffb69a45b2f2fe68e8c928c5b00b562e7601a777dfa5fb45a5

The independent checker is
`verify_weak_middle_below_side_weighted_transfer_certificate.py`. It
reconstructs root (2), all exact midpoint splits, all original thirteen
rows and the new weighted row13. It uses directed integer arithmetic at
scale `2^80`, plus exact Fraction comparisons for the scalar maxima
(7). No discovery code or floating arithmetic is imported.

The complete leaf counts are:

| Rule | Leaves |
|---:|---:|
| 0 | 24,838 |
| 1 | 47 |
| 2 | 58 |
| 3 | 757 |
| 4 | 0 |
| 5 | 24,594 |
| 6 | 59,854 |
| 7 | 0 |
| 8 | 91,488 |
| 9 | 279 |
| 10 | 0 |
| 11 | 0 |
| 12 | 66,466 |
| 13 | 99,744 |
| **Total** | **368,125** |

**Accepted complete replay.** Every node and every leaf passed the
independent exact reconstruction. The least positive exclusion reserve is

    2193945960125041/151115727451828646838272

which exceeds `1/100000000`. The complete report is
`weak_middle_below_side_fast_balanced_exact_replay_report.json`.

Every original lower-side extra would supply a point of (2) satisfying
(1), (3), and all necessary expressions. The complete exact exclusion
contradicts that consequence. Thus no original extra can lie below its
assigned main in either closed side strip. Together with the complete
above-side theorem, both original extras lie in the open central strip.

## Independent geometry and checker audit

The root proof agent independently reviewed the complete original-caller
reduction and the weighted exact checker, finding no gap. The review
checked the positive lambda combination, sign-sensitive maximization of
`-a_i*x`, exact circular-arc cases including negative alpha and empty
physical intervals, all four lower-reach alternatives, both R
chiralities, the minimum/maximum order, and the possibly negative ylo
inside the interval product with b_i. The original thirteen rows remain
valid with the certified function f(h).

Five deliberately invalid trees were rejected by
`check_weak_middle_below_side_weighted_controls.py`: an incomplete tree,
an invalid split axis, a false original-row root leaf, a noninteger tag,
and a false weighted-row root leaf. The complete control record is
`weak_middle_below_side_weighted_negative_controls.json`.

These independent reviews and corruption controls are separate from
the completed exact replay. This consequence has no pending arithmetic
or geometric dependency.
