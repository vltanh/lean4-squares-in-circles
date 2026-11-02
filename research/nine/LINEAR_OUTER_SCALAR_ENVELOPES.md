# Complete shoulder-owned linear outer support envelopes

This note proves both scalar target inequalities by a local hand
argument and two complete, independently replayed finite certificates.
The negative table has 1,700 leaves; the positive table has 490. There
are no unclosed parameter cells. This theorem treats the case in which
the shoulder owns the endpoint-to-shoulder separating normal.

Let E and S be original physical unit squares in the centered Q-disk.
Their centers satisfy

    E: [89/60,91/60] x [-1/8,1/8],
    S: [23/30,13/12] x [25/32,21/16].

The endpoint's frame, reduced modulo a quarter turn, belongs to
`[-atan(7/100),atan(7/100)]`. The shoulder owns the vector `n=(-w,1)`,
so its physical frame has side direction `(1,w)`. Write

    Q=1105/256, r=sqrt(Q), a=46, b=27/2,
    K=207/16, T=211/4, epsilon=1/80.

For a physical square V, let H_V denote its centered support halfwidth
and let `h_V=H_V(e_x)=H_V(e_y)`. Put `m=(1,z)`. The expression retained
from the two original squares is

    Phi(E,S;w,z,k)
      =(a e_x-kn) dot c_E+(bm+kn) dot c_S
         -a h_E-kH_E(n)-bH_S(m)-kH_S(n).

For a shoulder-owned endpoint normal, the scalar domain is
`w in [-2/3,6]`, `t in [0,6]`. A separate nonnegative rational multiplier
k may be chosen for each parameter box. The target inequalities are

    Phi(E,S;w,-t,k_-) <= T-16t,                  (1)
    Phi(E,S;w, t,k_+) <= T+(29/2)t.             (2)

The endpoint side keeps its original small free-frame interval, and
the shoulder frame is the actual one fixed by its normal. All five
center domains later used in the joint proof remain free; these are
support maxima over their complete original domains.

## 1. Local hand proof

On `|w|,t<=epsilon`, choose k=K. The independently audited scalar
estimate in `LOCAL_QUADRATIC_JOINT_CAP.md` gives

    Phi<=T-(K/2)|w|+(3K/2)z-K(z-w)_+
                +(20+23*1_{w<0})w^2+19z^2.      (3)

For z=-t, subtract the right side of (1), bound the quadratic terms
by `43epsilon|w|+19epsilon t`, and drop the nonpositive positive-part
term. The remaining upper bound is

    -(949/160)|w|-(507/160)t.

For z=t and w>=0, put

    alpha=29/2-K-39epsilon=43/40>0.

Subtracting the right side of (2), the lower deficit is at least

    alpha*t+(K/2+20epsilon)(t-w),  if w<=t,
    alpha*t+(K/2-20epsilon)(w-t),  if w>=t.

All coefficients are positive. For w<0 the lower deficit is at least

    (3K/2-43epsilon)|w|+(29/2-K/2-19epsilon)t,

whose coefficients are also positive. Thus both local claims hold,
strictly away from w=t=0. This is a hand calculation independent of
the finite exclusion program.

## 2. Exact two-component support formulas

For a frame with unit side vectors u,v, one has

    H_theta(q)=(|q dot u|+|q dot v|)/2.

Let `M_I(q_1,...,q_j)` be the minimum of the sum of these supports over
the endpoint frame interval I. Its finite candidate list consists of
the interval endpoints and the frames aligning one of the nonzero
q_i with a side, when that frame belongs to I. Between successive
candidate angles the sum is a positive `A cos(theta)+B sin(theta)`;
its second derivative is negative, so an interior minimum is impossible.
Zero vectors are omitted, and limiting cases follow by continuity.

Write `v_E=(a+kw,-k)`. The endpoint contribution to Phi is bounded by
the minimum of these three valid quantities:

    r|v_E|-M_I(v_E,a e_x,kn),
    rho|v_E|-M_I(a e_x,kn),
    H_endpoint_box(v_E)-M_I(a e_x,kn),

where `rho=sqrt(Q-1/4)-1/2`. The first is the ordinary disk-support
inequality, the second uses the universal center-radius bound, and the
third uses the original center rectangle. Taking their minimum cannot
exclude an admitted endpoint.

For the shoulder, write `v_S=(b-kw,k+bz)` and retain its known frame
`u=(1,w)/sqrt(1+w^2)`, `v=(-w,1)/sqrt(1+w^2)`.
The exact support maximum of its unboxed circle center region is

    C_Q(q;theta)=rho*A,
      if A^2>=(4Q-1)B^2;
    C_Q(q;theta)=r sqrt(A^2+B^2)-(A+B)/2,
      otherwise,

where `A=max(|q dot u|,|q dot v|)` and B is the smaller projection.
To prove this formula, reflect the two frame coordinates to their
nonnegative quadrant. The farthest square vertex then imposes
`(X+1/2)^2+(Y+1/2)^2<=Q`. The maximizer of AX+BY is either the circle
point in direction (A,B) or the boundary Y=0. Its nonnegative-Y
condition is precisely the displayed branch test.

For a rectangle `[x_l,x_h] x [y_l,y_h]` and four nonnegative face
multipliers `(lambda_l,lambda_r,lambda_b,lambda_t)`, put

    q'=(q_x+lambda_l-lambda_r, q_y+lambda_b-lambda_t).

The boxed support is at most

    C_Q(q';theta)-x_l lambda_l+x_h lambda_r
                     -y_l lambda_b+y_h lambda_t.

Subtract `bH_theta(m)+kH_theta(n)` from this bound for q=v_S. This is
the shoulder contribution used in each row. All center-box multipliers
are nonnegative rationals, so every choice is a valid upper bound;
numerical optimization supplies no assumption about the actual center.

## 3. Exact complementary tables

For each target the three exact roots are

    [-2/3,-1/80] x [0,6],
    [1/80,6] x [0,6],
    [-1/80,1/80] x [1/80,6].

They and the hand rectangle cover the entire closed parameter domain.
Every interval row supplies a nonnegative rational k and nonnegative
shoulder box-face multipliers, all with denominator 4096. Section 2's
two-component formulas bound the complete original physical domain.

`certify_outer_scalar_family.py` proposes the rows and proves strict
negative interval residuals. `verify_outer_scalar_family.py` separately
reconstructs the two physical components, the target expressions, every
root, and every exact midpoint split. It imports no producer code and
uses the independently audited directed-integer arithmetic engine.

The complete certificates and replay reports are in `computer_assisted`.
Every numeric row passed the independent exact checker:

| Target | Nodes | Interval leaves | Maximum depth | Largest replayed residual upper |
|---|---:|---:|---:|---:|
| Negative, coefficient 16 | 3,397 | 1,700 | 17 | `-6934341744629233/18446744073709551616` |
| Positive, coefficient 29/2 | 977 | 490 | 24 | `-8221223209480849/18446744073709551616` |

The certificate hashes, in the same order, are

    10d5ed1ef26b97ecaf86d0149a4840040804d2e31dc5a147b05047629e0852ed
    36d29da96f39618b2a74a8fe1c2f7a30e97acc2bfc713e1f41c72999ebc2db66

The files are `outer_R_linear_negative_cover.json` and
`outer_R_linear_positive_cover.json`; the corresponding complete
records add the suffix `_verification_report.json`.

The checker uses 64-bit fractional directed-integer intervals with
integer-square-root radical bounds. It reconstructs the full root
partition and every midpoint split. Direct interval bounds and centered
mean-value bounds are both valid; at an absolute-value, min, max, or
circle-support branch change, derivative intervals include every
potentially active branch. The finite tree and its strict row bounds
prove the inequalities, independently of the floating proposal process.

Thus (1)--(2) hold on the whole closed parameter domain. Each is strict
away from w=t=0, by its finite row or Section 1. At w=t=0 and any
strictly smaller containing radius, the original nonzero endpoint
disk-support coefficient makes the local bound strict as well.

## 4. Joint use

Together with the independently proved endpoint-owned scalar claims,
these bounds remove
the endpoint slope variables from the joint cap. Let p be the sum of
positive central slopes, n the sum of negative magnitudes, and S=p-n.
The outer contribution is at most `2T+(29/2)p-16n`.
The original central square remains present once, with its actual
height and both support costs.

The separate central transfer theorem in
`CENTRAL_LINEAR_TRANSFER_HAND_TABLE.md` pays the remaining original
central support terms. The full five-square assembly is in
`UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md`; it applies these
scalar bounds with nonnegative multipliers on genuine separating
slacks and keeps the original central square only once.
