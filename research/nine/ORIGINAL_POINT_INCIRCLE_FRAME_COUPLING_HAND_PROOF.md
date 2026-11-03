# Original square points against another original's incircle

November 3, 2026. A complete physical implication and exact affine row
family, valid for any two independently oriented original unit squares.
There is no separating-axis choice, new case split, or disk-radius
assumption. This theorem alone changes no cell or mask status.

## 1. The point-distance inequality retains the original frame

Let original squares i and j have disjoint open interiors. Write

    u_i=(alpha_i,beta_i), v_i=(-beta_i,alpha_i),
    alpha_i^2+beta_i^2=1, d=c_j-c_i=(x,y).

For any fixed real s,t in [-1,1], the point

    p=c_i+(s u_i+t v_i)/2

belongs to the same closed original square i. The open radius-1/2 disk
about c_j belongs to the open interior of original square j. Therefore

    ||p-c_j|| >= 1/2.                                (1)

For completeness, a point of the closed first square cannot belong to
the open second square: an open neighborhood about such a point would
contain points in the interior of the first square. This would contradict
the disjoint-interior premise. Thus (1) holds for side and corner points
as well as interior points. Physical contact remains allowed.

Expanding (1), using the original orthonormal frame, gives

    x^2+y^2-alpha_i(sx+ty)-beta_i(sy-tx)
                      +(s^2+t^2-1)/4 >= 0.           (2)

The assertion is simultaneous for every s,t in the closed parameter
square. A finite rational selection gives necessary rows; it is not
claimed equivalent to complete physical nonoverlap. Both originals may
be used as the owner. For owner j, replacing d by -d and then replacing
(s,t) by (-s,-t) yields the same displayed form with j's actual frame.
The finite parameter table is centrally symmetric, so all those rows
are valid without an owner or sign assumption.

This row family uses more than unit center separation: it retains the
location of a point of one square relative to the other original's
incircle. The first original's alpha and beta are the same variables
that occur in its corner containment, inset, and other pair constraints.

## 2. Exact affine rows on previously proved whole-parent intervals

Suppose the unchanged whole caller has already proved

    x in [l_x,u_x], y in [l_y,u_y],
    alpha_i in [a_L,a_U], beta_i in [b_L,b_U].

Put P=sx+ty and T=sy-tx. Evaluating these two linear forms at the four
corners of the difference rectangle gives rigorous rational intervals
[P_L,P_U] and [T_L,T_U]. No independence of the actual coordinates or
frame is assumed; using a containing rectangle only weakens the rows.

Choose either matching pair (a_0,P_0)=(a_L,P_L) or (a_U,P_U), and
independently either (b_0,T_0)=(b_L,T_L) or (b_U,T_U). Products of
nonnegative interval distances give

    alpha_i P >= a_0 P+P_0 alpha_i-a_0 P_0,
    beta_i T  >= b_0 T+T_0 beta_i-b_0 T_0.            (3)

For an upper-endpoint choice both factors in the residual are
nonpositive, and their product is still nonnegative. Consequently (3)
holds for signed intervals, degenerate intervals, and both beta signs.

The square secants give

    x^2+y^2 <= (l_x+u_x)x+(l_y+u_y)y-l_x u_x-l_y u_y.

Combining this upper bound with (2)-(3) yields the exact necessary row

    (a_0 s-b_0 t-l_x-u_x)x
      +(a_0 t+b_0 s-l_y-u_y)y
      +P_0 alpha_i+T_0 beta_i
      <= (s^2+t^2-1)/4-l_x u_x-l_y u_y
                             +a_0 P_0+b_0 T_0.      (4)

There are four plane combinations per owner and parameter point.
Substitute x=x_j-x_i and y=y_j-y_i to obtain coefficients on the same
original center variables. No new physical point becomes a square,
chain witness, or independent frame variable.

An exact check of every sign is the following slack identity. The
right side minus left side of (4) equals the physical left side of
(2), plus

    (x-l_x)(u_x-x)+(y-l_y)(u_y-y)
      +(alpha_i-a_0)(P-P_0)+(beta_i-b_0)(T-T_0).      (5)

Every added term is nonnegative on the proved intervals. Equations
(2) and (5) therefore give a direct hand proof of each printed row.

## 3. Finite rational table and valid induction

The initial discovery table uses the sixteen boundary points of

    {-1,-1/2,0,1/2,1}^2

for which max(|s|,|t|)=1. For each of the 36 original pairs it retains
both owners and all four plane combinations: 4,608 exact rational rows.
Other rational points of [-1,1]^2 are independently permitted by (2).
They are auxiliary proof parameters, not geometric case divisions.

Every row must be constructed from intervals proved before its deduction
round. The original interval bounds may come from the fixed ancestor
path or from an earlier exact nonnegative row sum. All deductions of a
round use the old state; improved bounds are installed only afterwards.
This is a finite implication induction, with no self-supporting bounds.

A numerical solver may propose multipliers. Only an exact weighted
sum, with coefficient residuals paid by proved variable bounds, can
establish a new interval or a contradiction. The complete original
parent must reach a contradiction before it can be counted as closed.
All nine original squares, their 36 physical pairs, 36 corners, marked
cone comparisons, and exact mask bits remain in that caller.

No Lean, Lake, CI, human verification, or proof-kernel verification is
claimed by this hand argument or its computational discovery use.
