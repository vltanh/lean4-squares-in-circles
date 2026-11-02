# An actual-four-chain sharp terminal with unrestricted inner heights

Continuation from PR #11, commit `5fd0452a965220b7f895ee7a3273a5590613a3d2`.

**Scope.** This is a proved conditional seven-square terminal. It removes all
height and tilt guards on the two inner squares of an actual four-chain.
It does not prove that the complete moving `000/01` domain enters this
terminal. No complete mask, original positional root, or global equality
classification is closed by this note. No Lean, Lake, CI, or independent
human/kernel review is claimed.

The derivation below is a pen-and-paper proof. The separate standard-library
checker `verify_free_inner_terminal.py` reconstructs its two polynomial
identities and its rational comparisons. Numerical searches motivated the
argument but are not premises of it.

## 1. The complete physical statement

Put

    Q = 1105/256,       rho = 91/60,
    Phi(b) = 11/24 + (51023/10800)b + (47/16)b^2 + (47/12)b^3.

Let seven independently oriented unit squares M0,M1,M2,M3,L,C,R have
pairwise disjoint open interiors and lie in the disk centered at zero with
squared radius q. In one common orthonormal coordinate frame suppose:

* M0,M1,M2,M3 form an actual horizontal projection-disjoint chain.
* x_M0 is in [-91/60,-89/60], x_M3 is in [89/60,91/60], and
  |y_M0|,|y_M3| <= 1/8.
* x_L is in [-13/12,-23/30], x_R is in [23/30,13/12], and
  y_L,y_R >= 19/40.
* |x_C| <= 2/5 and y_C >= f.
* Each of M0,M3,L,C,R has a representation by side axes
  (a_i,t_i),(-t_i,a_i), with a_i >= 0, a_i^2+t_i^2=1 and |t_i| <= b.
* 0 < b <= 1/18, 3/5 <= f <= 4/5, and f > Phi(b).

Then **q >= Q**. All displayed position bounds are closed; physical touching
is allowed. There are no bounds on the heights or orientations of M1,M2
other than their physical containment and actual-chain constraints.
There is no prescribed separating-axis owner, no common frame assumption
for the seven squares, and no actual L--C or C--R projection separation
assumption. Further physical squares can be present without new restrictions.

Three useful exact parameter choices are

| b | f |
|---:|---:|
| 1/64 | 3/5 |
| 1/32 | 2/3 |
| 1/18 | 3/4 |

For an active `000/01` witness, the endpoint and L,R position bounds above
are already consequences recorded in `../A2_000_01_ATTEMPT.md`.
Its selected P also satisfies |x_P|<2/5. Nevertheless its required height
and the five tilt bounds are NOT automatic. C may instead be either of
the other two outsiders if all the same guards are established for it.

## 2. Universal center and small-tilt estimates

It suffices to consider q <= Q. A unit square with center c has largest
squared corner norm

    |c|^2 + 1/2 + |c.u| + |c.v| >= |c|^2 + |c| + 1/2.

At |c|=rho the last expression exceeds Q by 31/57600, and it is increasing
for nonnegative |c|. Thus every center has |c|<rho.

Set beta0=7/250 and tau0=501/1000. For |t|<=b<=1/18,

    a >= 1-b^2,
    1-a = t^2/(1+a) <= tau0 t^2 <= beta0 |t|.

Indeed 1+a >= 2-b^2, and at b=1/18 the two positive reserves are

    beta0 - b/(2-b^2) = 29/161750,
    tau0 - 1/(2-b^2) = 147/647000.

The relevant fractions increase with b. This proves the estimates on the
entire interval, not only at the endpoint.

For two of the five small-tilt squares put d=|t_i-t_j|. Then

    |a_i-a_j| = |t_i+t_j|d/(a_i+a_j) <= 2bd,
    |a_i t_j-t_i a_j| >= (1-3b^2)d,
    a_i a_j+t_i t_j
      = 1-((a_i-a_j)^2+d^2)/2 >= 1-b(1+4b^2)d > 0.

Consequently their sum of support halfwidths along an axis owned by either
square is at least

    1+c d,          c = (1-b-3b^2-4b^3)/2.                 (1)

Here the exact support sum is (1+dot+|det|)/2. The dot product is positive
by the displayed estimate. All choices of physical owner are retained.

## 3. Force the required axis directions, not their owners

A left endpoint-to-shoulder displacement has horizontal component between
2/5 and 3/4 and positive vertical component at least 7/20. The corresponding
right pair is its horizontal reflection. The absolute vertical displacement
is at most rho+1/8. Thus a nearly horizontal side-axis projection has magnitude
at most

    3/4 + b(rho+1/8) < 1,

whereas the positive nearly vertical axis projection has lower bound

    (1-b^2)(7/20) - 3b/4 > 0.

Since any two unit squares require separating projection at least one,
the separating-axis theorem leaves a nearly vertical axis of one of the
actual squares. In particular their upward center gap is at least 1-3b/4.
Both shoulders therefore satisfy

    y_L,y_R >= 7/8-3b/4 >= 5/6 > 4/5 >= f.                (2)

All three selected upper squares have heights in [f,rho]. Their consecutive
horizontal center gaps lie in [11/30,89/60]. A nearly vertical axis has
projection magnitude at most

    b(89/60) + rho-f < 1,

and the forward nearly horizontal projection is at least

    (1-b^2)(11/30)-b(rho-f) > 0.

Consequently each of L--C and C--R is separated by a forward nearly horizontal
axis owned by one of its actual endpoints. These statements require physical
nonoverlap only; they do not assume horizontal projection separation.

The following are uniform lower bounds for the strict reserves just used,
evaluated at the worst endpoints b=1/18, f=3/5:

| Comparison | Positive reserve |
|---|---:|
| 1 minus upper horizontal-chain wrong-axis projection | 1/1080 |
| Horizontal-chain correct-axis positive projection | 1529/4860 |
| 1 minus endpoint-pair wrong-axis projection | 343/2160 |
| Endpoint-pair correct-axis positive projection | 1991/6480 |
| c-(rho-f)/2 | 13/1458 |
| Shoulder lower height minus 4/5 | 1/30 |

Monotonicity in b and f gives each entire parameter range. In particular
c-(rho-f)/2 is positive throughout it.

## 4. Reflect vertically and retain the true owners in the products

For the algebra reflect all seven physical squares and the coordinate frame
vertically, so L,C,R are below the mains. Reparameterize their second axes if
necessary; the same small-tilt bounds hold. From now on all symbols refer to
these reflected coordinates. Use base centers

    M0*=(-3/2,1/16),  M3*=(3/2,1/16),
    L*=(-1,-15/16),   R*=(1,-15/16).

For these four anchors write c_i=c_i*+(dx_i,z_i). Their deviations need not be
small. For C write z_C=y_C+15/16, and put

    m=15/16-(rho+f)/2,       h=(rho-f)/2,
    V_B=|t_C-t_L|+|t_R-t_C|,
    V_C=|t_0-t_L|+|t_3-t_R|.

Every triple z-coordinate lies in [m-h,m+h]. From (1) and the horizontal
axis result, each forward pair satisfies

    Delta x >= 1+c|Delta t|-t_owner Delta z.

For the left owner, for example,

    -t_i(z_j-z_i)=t_i z_i-t_j z_j+m(t_j-t_i)
                   +(z_j-m)(t_j-t_i).

For the right owner the last z_j is replaced by z_i. In either case the last
term is at least -h|t_j-t_i|. Summing the two edges gives

    x_R-x_L-2 >= (c-h)V_B+t_L z_L-t_R z_R+m(t_R-t_L).       (3)

For the actual four-chain let h_i be its coordinate projection halfwidth.
Because h_1,h_2>=1/2 and h_i-1/2 >= (243/500)|t_i| for the two anchors,

    x_3-x_0-3 >= (h_0-1/2)+(h_3-1/2)
                         +2(h_1-1/2)+2(h_2-1/2)
                 >= (243/500)(|t_0|+|t_3|).               (4)

This is the step that eliminates any need for bounds on the inner heights
or inner tilts. It uses actual-chain separation, not the cone relaxation.

Let ell be the tilt of the owner of the left upward vertical separator,
so ell is t_0 or t_L. Let r be its right counterpart, t_3 or t_R. Applying
(1) to these two pairs and retaining the owners gives

    (y_0-y_L-1)+(y_3-y_R-1)
      >= (c-1/4)V_C -(t_0+t_L)/4+(t_3+t_R)/4
           +ell(dx_0-dx_L)+r(dx_3-dx_R).                  (5)

To check the only estimate in this formula, the constant horizontal base
displacements are -1/2 and +1/2. Use ell<=max(t_0,t_L) and
r>=min(t_3,t_R) there, and expand max and min. The SAME actual owners
remain in the displacement products. Thus all four ownership choices are
covered consistently.

## 5. The exact physical four-corner identity

Set

    w=23/64, v=9/64, k=207/512,
    W_M=4w=23/16, W_B=3v=27/64, A=851/2048.

Choose one actual corner of each anchor, with these signs and weights:

| Anchor | u sign s_i | v sign e_i | weight w_i |
|---|---:|---:|---:|
| M0 | -1 | +1 | w |
| M3 | +1 | +1 | w |
| L | -1 | -1 | v |
| R | +1 | -1 | v |

Let L_i=s_i x_i+e_i y_i and J_i=-e_i x_i+s_i y_i. Its squared corner
norm is |c_i|^2+1/2+a_i L_i+t_i J_i. The weights sum to one. Expanding their
weighted sum about the four stated base centers and using containment gives

    q-Q >= W_M(x_3-x_0-3)+W_B(x_R-x_L-2)
       +k[(y_0-y_L-1)+(y_3-y_R-1)]
       +sum_i w_i |d_i|^2
       +sum_i w_i[(a_i-1)L_i+t_i J_i].                    (6)

There is no assumption that the selected corner is the farthest one. Each
is an actual contained corner. Before imposing the four unit-frame equations,
the expansion's residual is exactly sum_i (w_i/2)(a_i^2+t_i^2-1).

Insert (3)--(5). Group all terms linear in the four anchor deviations into
L'_i.d_i. Direct collection gives:

| Anchor | x coefficient of L'_i | y coefficient |
|---|---|---|
| M0 | w(1-a_0-t_0)+k ell | w(a_0-1-t_0) |
| M3 | w(a_3-1-t_3)+k r | w(a_3-1+t_3) |
| L | v(1-a_L+t_L)-k ell | v(1-a_L+2t_L) |
| R | v(a_R-1+t_R)-k r | v(1-a_R-2t_R) |

The remaining base tilt terms are

    A(t_0-t_3)+B(t_R-t_L),       B=225/2048+W_B m.          (7)

The base values of L_i are 25/16 for M0,M3 and 31/16 for L,R. Equations
(6) and this displacement grouping are the two identities independently
expanded by the arithmetic checker.

## 6. Absorb all anchor deviations by positive squares

For each positive w_i, completing a square gives

    w_i |d_i|^2+L'_i.d_i >= -|L'_i|^2/(4w_i).              (8)

Put P=w(1+beta0)+k and H=v(1+beta0)+k. Use
|ell|<=|t_0|+|t_L|, |r|<=|t_3|+|t_R| and
(u+v)^2<=2u^2+2v^2. The total negative quadratic cost from (8) and the base
terms (a_i-1)L_i is at most

    C_M(t_0^2+t_3^2)+C_B(t_L^2+t_R^2),

where

    C_M=[2P^2+w^2(1+beta0)^2]/(4w)+k^2/(2v)+(25/16)w tau0
       =229167423/128000000 < 9/5,

    C_B=[2H^2+v^2(2+beta0)^2]/(4v)+k^2/(2w)+(31/16)v tau0
       =202189959/128000000 < 79/50.

The respective positive reserves are 1232577/128000000 and
50041/128000000. To make the allocation explicit: the two main x coefficients
are bounded in absolute value by P|t_main|+k|t_shoulder|, their y coefficients
by w(1+beta0)|t_main|; the shoulder coefficients are bounded by
H|t_shoulder|+k|t_main| and v(2+beta0)|t_shoulder|. Apply (8) and sum.
No bound on any anchor displacement was used.

## 7. Replace an orientation case table by three inequalities

Define

    alpha=(243/500)W_M-(9/5)b,
    beta=W_B(c-h),       gamma=k(c-1/4).

Use t_i^2<=b|t_i|, and write x=t_0, y=t_3, l=t_L, r=t_R. The preceding
bounds give

    q-Q >= W_B(c-h)[V_B-|r-l|]+F(x,y,l,r),                 (9)

where

    F=alpha(|x|+|y|)+beta|r-l|
       +gamma(|x-l|+|y-r|)+A(x-y)+B(r-l)
       -(79/50)b(|l|+|r|).

The first term of (9) is nonnegative by the triangle inequality and Section 3.
Both gamma and B are positive on the stated parameter domain; in particular
B decreases with f and B(4/5)>0. Set

    p=alpha-A-gamma,
    q0=gamma-(79/50)b,
    r0=q0+beta-B.

The elementary inequalities |x-l|>=|l|-|x|, |y-r|>=|r|-|y| imply

    F >= p(|x|+|y|)+q0(|l|+|r|)+(beta-B)|r-l|
      >= p(|x|+|y|)+min(q0,r0)(|l|+|r|).                 (10)

For the last step, if beta-B>=0 discard that term; otherwise use
|r-l|<=|r|+|l|. This covers ALL real signs and relative magnitudes of the four
tilts. It is not a sample or an assumption of equal tilts.

Finally, on 0<b<=1/18,

    p >= (243/500)W_M-1/10-A-k/4 = 10499/128000 > 0,
    q0 >= q0(1/18) = 461/8294400 > 0,
    r0 = (27/64)[f-Phi(b)] > 0.                           (11)

The second expression decreases with b because c does. The third identity
follows by substitution; it is exactly the stated threshold Phi. Thus (9)--(11)
prove q>=Q on the entire stated domain.

For convenient hand checks, the three explicit parameter rows have reserves:

| b, f | p | q0 | r0 |
|---|---:|---:|---:|
| 1/64, 3/5 | 1318757539/8388608000 | 122602873/1677721600 | 47504353/1677721600 |
| 1/32, 2/3 | 139153883/1048576000 | 9387937/209715200 | 5105737/209715200 |
| 1/18, 3/4 | 3950801/41472000 | 461/8294400 | 68111/8294400 |

Every numerator and denominator is positive. The checker additionally tests
all 30 nonzero signed indicator layers for each row (90 checks total), but
(10) is the complete analytic replacement for such a table.

## 8. Equality in this terminal

If q=Q, positivity in (10)--(11) forces t_0=t_3=t_L=t_R=0. Equation (9),
with c-h>0, then forces t_C=0. All five guarded units are aligned.

Return to (6), rather than discarding its completed squares. The orientation
terms now vanish. Both endpoint pairs are actually vertically separated,
the triple is actually horizontally separated, and the main chain is actual
by hypothesis. Each span/vertical excess in (6) is nonnegative. Therefore all
four anchor deviations vanish and every listed excess is zero. The main
span equality forces h_1=h_2=1/2 and all three main x-gaps equal one.
The short span equality forces both triple x-gaps equal one.

In the ORIGINAL upper-triple coordinates the four anchors are consequently

    M0=(-3/2,-1/16), M3=(3/2,-1/16),
    L=(-1,15/16), R=(1,15/16).

The inner main heights and C's height retain their original physical
containment and nonoverlap constraints; they are not asserted fixed.
This supplies an actual physical four-plus-three chain terminal at equality.
It does not classify the two additional physical units in a nine-square
packing and is not an unrestricted equality theorem.

## 9. Exact replay and the still-missing full-domain caller

Run, with Python's standard library only:

    python verify_free_inner_terminal.py

The checker imports no search/generator module. It expands the selected
physical corners, verifies the explicit unit-equation residual and the
owner-preserving displacement grouping, checks the rational bounds, and
rejects two deliberate algebraic corruptions. Its report is
`free_inner_terminal_verification.json`. The universal geometric reasoning
and the elementary reduction (10) are given above, not delegated to a solver.

A complete `000/01` proof would still have to show that every strict
counterexample satisfies this terminal's guards for some physical C, or
exclude the entire complementary domain by another complete argument.
The tests performed in this continuation do not establish that coverage.
The unrestricted model and its strengthened version both returned UNKNOWN
under their recorded solver time budgets. The pose-graph/linear-programming
work is floating-point exploration with an unresolved frontier, not an exact
UNSAT certificate. None of it changes the historical 5,838/7,915 root ledger
or the 2/32 full-mask ledger.
