# A joint five-square cap with shoulders on the full upper side bands

This manuscript proves the support reduction and hand parts of a wider
five-square cap. Four complete exact interval covers supply its outer
envelopes. The final independent replay status is recorded in Section 7.
An application to a nine-square gate must still produce the three distinct
upper squares with the stated whole-floor condition.

Put

    Q=1105/256, r=sqrt(Q), a=46, b=27/2,
    K=207/16, T=211/4, rho=sqrt(Q-1/4)-1/2<91/60.

For an original physical square V, write `H_V(q)` for its centered support
halfwidth in direction q, and `h_V=H_V(e_x)=H_V(e_y)`.

## 1. The cap statement

Let E_L,L,U,R,E_R be five distinct interior-disjoint physical unit squares
in the centered disk of radius `R0<=r`. Assume

    E_R: 89/60<=x<=91/60, |y|<=1/8,
    E_L: -91/60<=x<=-89/60, |y|<=1/8,

and both endpoint frames, reduced modulo a quarter turn, have slopes in
`[-7/100,7/100]`. It suffices to assume `h_E<=8/15`: the function
`(1+t)/(2sqrt(1+t^2))` increases for `0<=t<=1`, and at `t=7/100` its
square exceeds `(8/15)^2`, since

    11449*225-10049*256=3481>0.

The three upper squares satisfy

    -13/12<=x_L<=0<=x_R<=13/12,
    y_L,y_R>=3/5,
    |x_U|<=29/60,  y_U-h_U>=1/10.

No orientation of L,U,R, no endpoint separator owner, and no prescribed
central normal is assumed. Define

    D=x_E_R-x_E_L-h_E_L-h_E_R.

Then

    46D+27/2 <= 211/2,  equivalently D<=2.        (1)

If `R0<r`, the inequality is strict. Therefore an actual four-chain with
`D>=2` cannot coexist with these three original upper squares in a
strictly smaller disk. The reflected lower-side statement follows by
vertical reflection.

## 2. Every central normal is included

The five-row hand theorem `UPPER_COLUMN_SEPARATION_HAND_TABLE.md` proves
that any two original squares of center height at least `3/5` have
horizontal center distance strictly greater than `29/60`.

Here `y_U>=h_U+1/10>=3/5`. If `x_R<=x_U`, then both x coordinates belong
to `[0,29/60]`, contradicting that theorem. Likewise `x_L<x_U`. The
same theorem and the universal center bound give

    |y_R-y_U|, |y_L-y_U| < 91/60-3/5=11/12<1.

For a genuine directed separating unit normal from U to R, a nonpositive
horizontal component would give scalar product with the displacement less
than one. The two supports have sum at least one, because both unit squares
contain centered half-unit disks. Hence its horizontal component is positive.
The left argument is reflected. Dividing by the absolute horizontal
component gives the complete directed normal forms

    m_R=(1,z_R), m_L=(-1,z_L), z_R,z_L in R.       (2)

This includes all physical owners and touching boundaries. The vertical
and oppositely directed normal cases have been excluded, not omitted.

## 3. Every endpoint normal is included in two compact charts

It suffices to work on the right. Let `d=c_S-c_E=(-X,Y)` for E=E_R,S=R.
The physical center boxes give

    2/5<=X<=91/60,  19/40<=Y<=197/120.

Choose a genuine separating unit normal n from E toward S, owned by E
or S. Its scalar product with d is at least one. A southeast normal has
nonpositive scalar product, so is impossible.

A northeast normal with `n_x>=n_y>=0` is also impossible. Using the
universal center bound and `n_x>=1/sqrt(2)>7/10`,

    n.d < 91/60-(89/60)n_x+(1/8)n_y
        <=91/60-(163/120)n_x
        <679/1200<1.

A southwest normal with `|n_y|>=|n_x|` is impossible because

    n.d <=(X-Y)|n_x| <=(25/24)|n_x|
        <=(25/24)/sqrt(2)<25/32<1.

Every remaining unit direction, after positive rescaling, belongs to one
of the following closed charts:

    up:   n=(-w,1),  -1<=w<=1;
    left: n=(-1,w),  -1<=w<=1.                    (3)

If S owns n, its actual frame is fixed by n: a representative side axis is
`(1,w)` in the up chart and `(1,-w)` in the left chart. If E owns n, its
small-frame premise additionally forces `|w|<=7/100`, in either chart.
The four resulting owner/chart families exhaust all genuine endpoint
separators. In particular near-horizontal endpoint owners are retained.

## 4. The outer envelopes and their exact physical formulas

Define the continuous piecewise linear function

    ell(z)=(29/2)z                         for z>=0,
    ell(-t)=max(-16t,-(29/2)t-3/2)         for t>=0.

Equivalently,

    ell(z)=(29/2)z+(3/2)min(0,max(-1,z)).

For any original endpoint separator n in Section 3 and central vector
`m=(1,z)`, the proved envelope supplies a nonnegative rational multiplier
k, depending on its parameter cell, such that

    Phi=(a e_x-kn).c_E+(bm+kn).c_S
             -a h_E-kH_E(n)-bH_S(m)-kH_S(n)
        <=T+ell(z).                              (4)

The right-hand original shoulder has its complete center box

    B_S=[0,13/12] x [3/5,91/60].

All bounds below are uniform over that box. The actual frame of whichever
square owns n is fixed. The other square retains its independent physical
frame; the endpoint free-frame interval is the complete small interval in
Section 1, and a free shoulder has every possible orientation.

Here are the exact scalar formulas evaluated by the finite rows. For a
fixed side axis u, define

    H_u(q)=(|q.u|+|det(q,u)|)/(2|u|).

For a list of vectors, `M_I(q_1,...,q_j)` denotes the minimum of the sum
of these supports over the appropriate compact frame set I. Its complete
candidate list consists of the frame interval endpoints and the frames
aligning a nonzero q_i with a side, whenever admitted. Between alignment
changes the positive sum has negative second derivative, so it has no
interior minimum. A zero vector contributes zero.

The exact unboxed center support for a known frame is

    C_Q(q;u)=rho A,                           if A^2>=(4Q-1)B^2,
             r sqrt(A^2+B^2)-(A+B)/2,         otherwise,

where A and B are respectively the larger and smaller absolute projections
of q onto the two unit side axes. In frame coordinates the farthest corner
requires `(X+1/2)^2+(Y+1/2)^2<=Q`; the two branches are respectively the
axis-boundary maximizer and the circular maximizer.

For a center box `[x_l,x_h] x [y_l,y_h]` and four nonnegative rational
face multipliers `lambda_l,lambda_r,lambda_b,lambda_t`, write

    q'=q+(lambda_l-lambda_r,lambda_b-lambda_t),
    J=-x_l lambda_l+x_h lambda_r-y_l lambda_b+y_h lambda_t.

The known-frame contribution with support penalties q_i is bounded by

    C_Q(q';u)+J-sum_i H_u(q_i).                    (5)

For a free frame, each of the following is a valid bound:

    r|q'|-M_I(q',q_1,...,q_j)+J,
    rho|q'|-M_I(q_1,...,q_j)+J,
    H_box(q)-M_I(q_1,...,q_j).                    (6)

Their minimum is also a valid bound. Formula (6) is merely the original
containment or center-radius inequality with nonnegative center-box
constraints added; no actual frame, center or physical square is replaced.

For E use `q=a e_x-kn` and penalties `a e_x,kn`; for S use `q=bm+kn`
and penalties `bm,kn`. The S-owner rows apply (6) to E with zero box-face
multipliers and (5) to S. The E-owner rows apply (5) to E and (6) to S.
Every printed integer multiplier is divided by 4096 and is nonnegative.

## 5. The local hand rectangle and the unbounded tails

In the up chart with `|w|,|z|<=1/80`, choose `k=K`. The unboxed,
orientation-free inequality in `LOCAL_QUADRATIC_JOINT_CAP.md` applies to
both owner cases and gives

    Phi <=T-(K/2)|w|+(3K/2)z-K(z-w)_+
                  +(20+23*1_{w<0})w^2+19z^2.

The exact comparison with `T-16|z|` for negative z and with
`T+(29/2)z` for positive z is the hand calculation in Section 1 of
`LINEAR_OUTER_SCALAR_ENVELOPES.md`. It is strict away from `(w,z)=(0,0)`.
These estimates use no old shoulder-position restriction: the underlying
bound is unboxed and valid for every physical frame.

For the unbounded central tails take `k=0`, independently of n and its
owner. Subadditivity of square support gives

    H_S((1,+t)),H_S((1,-t)) >=t h_S-h_S.

Use `x_E-h_E<61/60`, `x_S<=13/12`, `h_S<17/24`, and hence

    a(x_E-h_E)+b(x_S+h_S) <17029/240.

For `z=t>=24`, the universal center bound gives `y_S-h_S<61/60`, so
the reserve in (4) is greater than or equal to

    (31/40)t-4369/240 >=19/48>0.

For `z=-t`, `t>=57`, the actual height floor and `h_S>=1/2` give
`y_S+h_S>=11/10`. The reserve over the active negative-tail target is
greater than or equal to

    (7/20)t-4729/240 >=59/240>0.

Thus only the compact central range `-57<=z<=24` remains for finite rows.

## 6. Complete joint cancellation

Apply (4) to the right endpoint and its reflected left counterpart.
The two actual central separating inequalities in (2), and the
nonnegative endpoint multipliers, give

    aD+bC <= Phi_L+Phi_R,
    C=H_U(m_L)+H_U(m_R)+(z_L+z_R)y_U.

The original whole-floor condition is exactly the hypothesis of
`PIECEWISE_CENTRAL_TRANSFER_UNBOUNDED.md`. It proves, for every pair of
real central slopes,

    C>=1+(ell(z_L)+ell(z_R))/b,                    (7)

strictly unless both slopes vanish. Combining (4) and (7) cancels both
slope costs and gives `aD+b<=2T`, which is (1).

If `R0<r`, every finite row or tail bound is already strict. In the only
remaining hand equality case `w=z=0`, the original endpoint disk-support
coefficient is nonzero, so replacing R0 by r makes the local bound strict
as well. Hence (1) is strict in a strictly smaller disk.

At equality `D=2` in the closed Q-disk, (7) forces `z_L=z_R=0` and
`2h_U=1`; U is aligned. The two horizontal central separators give

    B=x_R-x_L-h_L-h_R>=2h_U=1.

Adding the global physical two-square caps gives `46D+(27/2)B<=2T`.
At `D=2`, this forces `B=1` and equality in both individual pair caps.
The global physical two-square cap, Theorem 1 of
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`,
then forces both endpoint/shoulder pairs to attain its equality. The
positive shoulder heights select

    c_E_L=(-3/2,-1/16), c_E_R=(3/2,-1/16),
    c_L=(-1,15/16),     c_R=(1,15/16),

with all four squares aligned. The horizontal central separators force
`x_U=0`. In particular L,U,R themselves form an actual horizontal cone
three-chain, since `3/5<=y_U<91/60` gives `|y_U-15/16|<1`.
This is a necessary equality description of the five-square cap, not an
assertion excluding every closed-Q packing.

## 7. Complete covers and independent replay

Each owner/chart family has one exact rational root:

    S-owned: [-1,1] x [-57,24],
    E-owned: [-7/100,7/100] x [-57,24].

The four complete trees are `wider_outer_E_up_cover.json`,
`wider_outer_E_left_cover.json`, `wider_outer_S_up_cover.json`, and
`wider_outer_S_left_cover.json`. Every internal node is an exact midpoint
bisection retaining both closed children. Local leaves in the up chart
must lie in the full hand rectangle of Section 5; every other leaf
contains a rational multiplier row and a strict interval upper bound.

`certify_wider_outer.py` proposes rows and certifies them with outward
96-bit dyadic intervals. `verify_wider_outer.py` imports no producer or
floating proposal code. It separately reconstructs all four roots, the
two physical owner formulas, target branches, original center boxes,
nonnegative multiplier conditions, every split and every terminal.
Its arithmetic engine is the separately audited 64-bit integer dyadic
implementation `verify_joint_five_dyadic.py`.

Both evaluators use the minimum of the direct interval upper bound and
the centered mean-value upper bound. At support, minimum, maximum and
circle-branch changes, derivative intervals include all branches that
can be active. All square-root denominators are positive. Integration
along a segment therefore justifies the centered bound through branch
changes. No floating optimizer success flag is a proof premise.

| Owner | Chart | Nodes | Strict interval leaves | Local hand leaves |
|---|---|---:|---:|---:|
| E | up | 491 | 243 | 3 |
| E | left | 303 | 152 | 0 |
| S | up | 2469 | 1231 | 4 |
| S | left | 3653 | 1827 | 0 |

The four covers contain 3453 strict interval leaves and seven hand leaves.
All four complete independent replays have passed. Their largest replayed
residual upper bounds, in table order, are

    -1014195892802533/2305843009213693952,
    -1491685992409079591/18446744073709551616,
    -158810711441393/2305843009213693952,
    -87820983618864619/18446744073709551616.

All four numbers are strictly negative. The certificate SHA-256 values,
in the same order, are

    d9a08f01f76922cd8b86f680aaf0d21cbf5f5dde81a5f5432565de8ea7fcc8fe
    0bc3b4b76d972de0cfb025c02ac0e2cfab9311a4610b58093ddec0bf8a2307db
    5666c8f13e63f5abbefc5ba7beb638710ab59871244b0dfadae0b839188b7082
    29c18466f47ce0d614a5b8f5510f0d3e8ab572d6d419831f16adf1533c2aa461

A second agent independently replayed all four covers through the separate
exact-Fraction arithmetic kernel, with all four replays passing. That
agent also independently reviewed the physical face-multiplier formulas,
both normal-chart complements, the two unbounded tails, every central
piecewise case and Bernstein coefficient, and the complete joint cap
assembly including the equality comparison `B>=2h_U>=1`.

The scope remains explicit: this cap removes the old shoulder bound
`|x_S|>=23/30`, the old high shoulder floor `y_S>=25/32`, the old upper
shoulder bound `y_S<=21/16`, every endpoint normal-owner restriction and
every central slope bound. A full gate application still has to supply
the three original upper squares with `y_L,y_R>=3/5` and the original
central whole floor `y_U-h_U>=1/10`.
