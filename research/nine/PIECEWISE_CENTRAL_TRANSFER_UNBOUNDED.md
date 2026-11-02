# An unbounded central transfer with a milder negative tail

This note proves a new central-square support inequality. It is a component
for a possible wider five-square cap; it is not a closure of `000/11`.
The outer envelopes and the full physical caller remain separate obligations.

Put

    Q = 1105/256, r = sqrt(Q), b = 27/2,
    ell(z) = (29/2)z                         if z >= 0,
    ell(-t) = max(-16t, -(29/2)t - 3/2)      if t >= 0.

Thus the negative branches switch at `t=1`. Let L,U,R be original
interior-disjoint unit squares in the centered Q-disk. Assume the original
central square has whole floor `y_U-h_U >= 1/10`, and there are genuine
directed central separators

    m_L=(-1,z_L), m_R=(1,z_R),  z_L,z_R in R.

Then, with all supports and the height belonging to this one original U,

    C = H_U(m_L)+H_U(m_R)+(z_L+z_R)y_U
      >= 1 + (ell(z_L)+ell(z_R))/b.                 (1)

The inequality is strict whenever either slope is nonzero. The two zero
slopes give `C=2h_U>=1`.

## 1. Inherited exact facts

The exact central triangle of `CENTRAL_LINEAR_TRANSFER_HAND_TABLE.md`
has vertical candidate `1+max(p,n)` and the two sloping-edge candidates
given in its Section 2. Put

    p=(z_L)_+ +(z_R)_+, n=(-z_L)_+ +(-z_R)_+,
    S=p-n, s=|S|.

If M is the least sum of two orthogonal projection widths of that triangle,
then every actual central frame satisfies

    s h_U+H_U(m_L)+H_U(m_R) >= M.

We use its proved facts

    M >= 1+s                 when z_L z_R <= 0,
    y_U+h_U <= r < 133/64,
    |c_U| <= rho < 91/60,
    H_U(q) >= |q|/2.

The unbounded extension in `CENTRAL_TRANSFER_UNBOUNDED_SLOPES.md` proves

    C >= 1+(29/27)p-(32/27)n                       (2)

strictly away from the origin. Its positive-quadrant compact part is the
existing independently replayed central table; its new positive tail is
the elementary bound

    M >= sqrt(s^2+2s),  s>=2,

for a triangle whose two slope parameters have the same sign. That bound
also applies to the negative quadrant after reflection.

If no negative slope has magnitude greater than one, (1) is exactly (2).
Only cases with a negative magnitude at least one need new work. Values
equal to one may be assigned to either neighboring case.

For negative sums, the preceding facts give the useful bounds

    C >= M-rs,
    C >= (|z_L|+|z_R|)/2-(91/60)s.                (3)

The first bound retains `h_U+y_U`, not merely `y_U`.

## 2. Opposite signs

Write the slopes as `-t,p`, where `t>=1` and `p>=0`. The target in (1) is

    8/9+(29/27)(p-t).

If `S=p-t>=0`, the actual whole floor and `M>=1+S` give

    C >= 1+(11/10)S.

The reserve is `1/9+(7/270)S>0`.

If `S=-s<0` and `s<=16`, (3) and the mixed-sign triangle bound give

    C >= 1-(69/64)s.

Its reserve over the target is at least

    1/9-(7/1728)s >= 5/108 > 0.

If instead `s>=16`, then `t=p+s`, and the second bound in (3) gives

    C >= p-(61/60)s.

The reserve is at least

    p+(31/540)s-8/9 >= 4/135 > 0.

This proves all opposite-sign cases, with no upper slope bound.

## 3. Both negative magnitudes at least one

Write the slopes as `-t,-u`, with `t,u>=1`, and `s=t+u>=2`. The target is

    7/9-(29/27)s.

For `s>=16`, the second bound in (3) has reserve

    (31/540)s-7/9 >= 19/135 > 0.

For `2<=s<=16`, put

    kappa=133/64-29/27=1735/1728.

It suffices to prove

    sqrt(s^2+2s) > 7/9+kappa s.

Both sides are positive. Their squared difference is a concave quadratic
in s, since `kappa>1`. Its values at the two endpoints are

    s=2:   178319/746496 > 0,
    s=16:  50471/11664 > 0.

A concave function on an interval lies above the segment joining its
endpoint values, so the squared difference is strictly positive throughout.

## 4. One negative magnitude large and one small

It remains to consider slopes `-t,-u`, with `t>=1`, `0<=u<=1`, and
`s=t+u`. The target is

    (8-u)/9-(29/27)s.

For `s>=16`, (3) again gives the positive reserve

    (31/540)s-8/9+u/9 >= 4/135.

Assume henceforth `s<=16`. It is enough to prove that every triangle
candidate is strictly larger than

    kappa s+(8-u)/9.                              (4)

The vertical candidate `1+s` has reserve

    (1+u)/9-(7/1728)s >= 5/108 > 0.

For a nonnegative parameter z, the sloping candidate is

    L(s,z)=max(d_z+s/d_z, s(z+1)/d_z),
    d_z=sqrt(1+z^2).

### 4.1. The region tu<=1

Both candidates use their first branch. Since `t>=u`,

    L(s,t)-L(s,u)=(d_t-d_u)(1-s/(d_t d_u))>=0,

because `(d_t d_u)^2-s^2=(tu-1)^2>=0`. It therefore suffices to bound
`L(s,u)=d_u+s/d_u`.

Its reserve over (4) is strictly decreasing in t, because its t coefficient
is `1/d_u-kappa<0`. We may overcover the actual region by `t<=16` and
`t<=1/u` (when `u>0`).

If `0<=u<=1/16`, use `d_u>=1` and
`1/d_u>=1-u^2/2`. Since `s<=16+1/16=257/16`, the reserve is at least

    1/9-(7/1728+1/512)(257/16)
      =3245/221184 > 0.                           (5)

If `1/16<=u<=1`, the minimum for fixed u occurs at `t=1/u`. Section 4.3
proves its strict reserve there.

### 4.2. The region tu>=1

Both candidates use their second branch. Define
`f(z)=(z+1)/sqrt(1+z^2)`. The identity `f(z)=f(1/z)`, its increase on
`[0,1]`, and `1/t<=u<=1` show `f(u)>=f(t)`. It therefore suffices to bound
`L(s,t)=s f(t)`.

For fixed t, its reserve over (4) has u coefficient

    f(t)-kappa+1/9 >= 1-kappa+1/9 =185/1728>0.

Thus the minimum occurs at `u=1/t`. Since `1<=t<=16`, this boundary has
`1/16<=u<=1`, and Section 4.3 applies. The vertical candidate remains
separate; no assertion is made that a sloping candidate always minimizes M.

### 4.3. The reciprocal boundary and its three exact rows

On `t=1/u`, the required inequality is

    (1+u)sqrt(1+u^2)
      > kappa(1+u^2)+u(8-u)/9,  1/16<=u<=1.       (6)

Both sides are positive. After squaring and multiplying by 2985984,
their difference is the quartic

    P(u)=-24241+642048u-1741538u^2
                    +1231872u^3+605135u^4.

The following table gives positive Bernstein coefficients for
`P(u)/2985984` on three closed intervals. In a row, each of the five
displayed integers is divided by the common positive denominator.

| Closed u interval | Common denominator | Five Bernstein numerators |
|---|---:|---|
| `[1/16,1/4]` | 195689447424 | 615651791, 1965435452, 2740609520, 3090554816, 3213668096 |
| `[1/4,1/2]` | 2293235712 | 37660173, 39583818, 36781796, 34765128, 40860240 |
| `[1/2,1]` | 143327232 | 2553765, 3315654, 6105488, 14586480, 34237248 |

To check a row directly, substitute `u=a+(b-a)v` in `P/2985984`, write
the ordinary coefficients as `q_0,...,q_4`, and compute

    beta_i=sum_{j=0}^i q_j binom(i,j)/binom(4,j).

The result is
`sum_{i=0}^4 beta_i binom(4,i)v^i(1-v)^(4-i)`.
These five nonnegative basis functions sum to one on `[0,1]`. All row
coefficients are strictly positive, proving (6), including both endpoints
and both overlap boundaries. These are fifteen displayed exact rational
numbers, not a sampled assertion.

## 5. Scope

The preceding cases exhaust every real pair of slopes. They prove (1),
strictly away from `(0,0)`, while preserving the one original physical
central square and both genuine separators. No endpoint owner assumption
occurs in this central theorem. The separate outer problem is to prove,
with a nonnegative multiplier on each original endpoint separator,

    Phi_i <= T+ell(z_i),  T=211/4.

If those wider outer envelopes and a complete physical caller are proved,
(1) provides their exact cancellation in the joint five-square expansion.
Neither of those additional obligations is claimed here.
