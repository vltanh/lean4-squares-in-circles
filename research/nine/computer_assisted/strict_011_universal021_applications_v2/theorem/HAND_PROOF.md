# Universal actual-AB two-link terminal

This gives a shared terminal for all remaining A, B and C originals of
`001/00`. It has no endpoint-angle sign, shoulder-height or D/G corridor
hypothesis. It is a conditional theorem, not a complete original closure.

## Statement

Let A,B,X,D,E,F,G be seven distinct original physical unit squares, with
independent original frames, disjoint open interiors and all corners in
a circle centered at zero of squared radius q. Put Q=1105/256. Suppose

    x_B-x_A >= h_A+h_B,
    x_F-x_E >= h_E+h_F,    x_G-x_F >= h_F+h_G,
    x_B <= x_X <= x_D,
    W=|y_X-y_B|+|y_D-y_X| <= 21/100.

Here h=(alpha+|beta|)/2, alpha=cos(theta), beta=sin(theta), and canonical
angles range through [-pi/4,pi/4]. Then q>=Q. Equality forces A,B,X,D
to align and x_D-x_A=3.

For the original-nine `001/00` caller, X can be either original H or I.
Keep the other two originals physical. Its actual BC link, original CD
center cone and strictly weak CD comparison exclude the equality case
as well. The statement imposes no new condition on the omitted originals.

## Universal endpoint caps

The accepted original-pair cap, applied to A,E and after a pi rotation
to D,G, gives

    46[-x_A-h_A]+(27/2)[-x_E-h_E]+46 T(A) <= 211/4,
    46[x_D-h_D]+(27/2)[x_G-h_G]+46 T(D) <= 211/4,

where

    T(S)=max{(2/23)|beta_S|,
             (5/23)|beta_S|-(1-alpha_S)} >= 0.

Both caps are strict if q<Q. They require the physical pairs and their
original corners, with no separator-direction or frame-sign guard.
The actual EFG chain gives x_G-x_E-h_E-h_G>=2h_F>=1. Summation yields

    x_D-x_A-h_A-h_D+T(A)+T(D) <= 2,                 (1)

strictly if q<Q. The source is `UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md`;
its existing complete physical proof and certificate are reused unchanged.

## Two genuine physical links

Number the reversed non-actual subrow D,X,B as 0,1,2. For j=0,1 choose
the genuine separating-axis owner o_j in {j,j+1}. Define

    R_ij=(1+cos(theta_i-theta_j)+|sin(theta_i-theta_j)|)/2.

Each owned separating axis has support sum R_ij. If d is the nonnegative
horizontal gap of a link and v its vertical gap, the open half-unit
incircles imply d^2+v^2>=1. Since |v|<=21/100 and
2*(21/100)^2=441/5000<1, d>|v| and d>0. A backwards horizontal normal
cannot separate, since its projection is at most |v|<1. Both forward
axes satisfy projection<=alpha_owner*d+|beta_owner|*|v|; for the steep
axis this uses alpha_owner>=|beta_owner| and d>|v|. Consequently

    d >= R_ij/alpha_owner-|tan(theta_owner)|*|v|.   (2)

Every owner, axis and sign is retained. The actual AB link contributes
h_A+h_B directly, with no charge for its vertical height difference.

## Complete scalar certificate

Set

    C=R_01/alpha_o0+R_12/alpha_o1+h_2-h_0+T(0)-2.

The delivered table proves, for every distinct k in {o_0,o_1},

    C >= (211/1000)|tan(theta_k)|,                 (3)

strictly unless all three angles vanish. Reflection of all three angles
leaves C unchanged, so take theta_0>=0; both signs of theta_1,theta_2
are included. This reflection is a scalar symmetry and imposes no
physical orientation restriction on the caller.

Write x_i=tan(|theta_i|/2). The physical range lies in the rational box
[0,5/12]^3, because sqrt(2)-1<5/12. Multiply the difference in (3) by
736000 product_i(1-x_i^4)>0. There are two valid lower expressions,
according to either branch of T(0). On a leaf, branch 0 uses
(5/23)|beta_0|-(1-alpha_0), and branch 1 uses (2/23)|beta_0|.
No extra angle restriction is inferred from the chosen lower branch:
both are at most T(0) everywhere. In each case the result is
P_0+|P_1|+|P_2|, with degree at most four in each variable.

Each leaf supplies a positive integer denominator N and integers
w_1,w_2 in [-N,N]. Thus

    N(P_0+|P_1|+|P_2|) >= N P_0+w_1 P_1+w_2 P_2.

All 125 degree-(4,4,4) Bernstein coefficients are strictly positive,
except the exactly zero origin coefficient on a leaf containing the
origin. The other 124 coefficients there are positive. This proves
(3), including strictness at all nonzero closed boundary points.

All four sign patterns, four physical owner patterns, and every selected
owner occur in the complete binary partitions: 28 domains, 351 leaves,
43,875 exact rational coefficient checks, and no frontier. LP proposals
only choose the rational weights; the producer then checks integer
coefficients. The independent checker reconstructs the physical dot and
determinant polynomials with Fraction arithmetic, reconstructs every
closed partition, verifies each chosen toll branch and each weight bound,
and checks all coefficients. It imports no optimizer or discovery code.

## Conclusion and original strict-bit equality face

Put M=max(|tan(theta_o0)|,|tan(theta_o1)|). From actual AB and (2),

    x_D-x_A-h_A-h_D+T(D)+T(A)
       >= 2+C-MW+T(A)
       >= 2+M/1000+T(A) >= 2.

This contradicts strict (1) below Q. At Q, strictness in (3) forces
D,X,B to align. Then T(A)=0 forces A to align, since T(A)>=2|beta_A|/23.
Each aligned remaining pair has vertical gap less than one and therefore
separates horizontally. Equation (1) forces x_D-x_A=3.

For unchanged `001/00`, actual AB and BC, followed by the original CD
cone and inset separation, give

    3 >= h_A+2h_B+h_C+g_C+g_D
       =1+2h_B+h_C+g_C >=3,
    g_C=1/(4h_C),
    h_C+g_C-1=(2h_C-1)^2/(4h_C)>=0.

Equality forces C aligned and x_D-x_C=1=h_C+h_D, contradicting the
strict weak CD bit. No numerical strict margin is assumed at Q.

## Complete application cover

If the same original proves x_X<x_D, the remaining possibilities are
covered by these five closed domains:

1. x_X<=x_B;
2. y_D-y_B>=21/100;
3. y_B-y_D>=21/100;
4. 2y_X-y_B-y_D>=21/100;
5. y_B+y_D-2y_X>=21/100.

Without the proved right order, also retain x_X>=x_D. These are closed,
overlapping alternatives and preserve every equality face. They follow
from the four signed-sum expression for W. Either original extra can be
used; all omitted originals and their physical constraints remain active.
Every complementary domain still requires a complete exclusion before
counting its original closed.

## Replay

    python -B -S check_universal_two_link.py cover fresh_replay.json

The delivered exact report records the complete fresh run. No Lean,
Lake or CI was run. The fixed count remains 222/231 cells and 8/32 masks
closed; this theorem alone adds no closure credit.
