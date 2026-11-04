# Positive-D replacement row with total variation at most 3/5

November 4, 2026 (UTC). This is a complete conditional geometric theorem and
an exact guard implementation. It strengthens the accepted total-variation
limit from **1/2 to 3/5**, while retaining every original frame and physical
separator owner. The unchanged original-nine caller and strict CD predicate
remain required. The root independently reviewed the full physical, continuous
scalar and equality argument and reran the exact arithmetic.

[Source-bound packet and review](computer_assisted/positive_d_row_terminal_v2/MANIFEST.json) ·
[Original six-domain implementation](A2_00100_POSITIVE_D_GLOBAL_ANGLE_COMPLEMENT.md) ·
[Coverage contract](A2_COVERAGE_AND_CLOSURE_CONTRACT.md)

This theorem alone closes **zero original cells and zero masks**. At this
checkpoint the fixed register remains **216 CLOSED / 15 OPEN**, and the mask
ledger remains **8 CLOSED / 24 OPEN**. Every complementary domain still needs
a complete proof before a parent can be credited. Existing 1/2 certificates
and their source files remain unchanged.

This strengthens the accepted positive-D two-link theorem from total variation
at most 1/2 to total variation at most 3/5. It uses the same original physical
pairs and the same signed D/G cap. The proof is conditional on the complete
original-nine 001/00 caller and earns no original-cell or mask closure alone.
The six complementary domains for each chosen extra still require a complete
proof. No Lean, Lake or CI is used.

## Statement

Let B,X,D be three distinct retained original unit squares with pairwise
disjoint interiors and horizontal center order `x_B<x_X<x_D`. Their frames
are independent. D has nonnegative canonical signed angle, so
`alpha_D>=beta_D>=0`. Write

`v1=y_X-y_B`, `v2=y_D-y_X`, `U=3/5`,

and assume `|v1|+|v2|<=U`. With the accepted signed-cap toll

`sigma_D=alpha_D-1+(23/32)beta_D`,

the following holds:

`x_D-x_B+h_B-h_D+sigma_D >= 2`.

Equality forces B,X,D all aligned and the two horizontal gaps both equal
to one. The conclusion permits every B and X chirality, every physical
separating-axis owner, every contact, and the two closed horizontal-order
faces. Those faces are impossible under the variation hypothesis by the
original unit center-distance bound.

## 1. The same physical owned-support reduction

Use the complete physical pair estimate from Section 1 of
`WEAK_OUTER_NUMERIC_NEAR_HORIZONTAL_REPLACEMENT_ROW_HAND_TERMINAL.md`.
If a physical pair has positive horizontal gap d, vertical gap v and
`d>=|v|`, then one actual owned axis supplies

`d >= 1+|h_i-h_j|+sqrt(1+s^2)-1-|v|s`,

where `0<=s<=1` is that original owner's absolute folded tangent. The
accepted estimate includes steep axes by square quarter-turn invariance
and the comparison `beta*d+alpha*|v|<=alpha*d+beta*|v|`.

Here each `|v_i|<=3/5`. The two original open radius-one-half incircles
are disjoint, so

`d_i >= sqrt(1-v_i^2) >= 4/5 > 3/5 >= |v_i|`.

The strict comparison uses `4/5>3/5`. Thus both physical pair estimates
apply without imposing any additional angle bound or choosing an owner.

Set

`r(s)=sqrt(1+s^2)`, `h(s)=(1+s)/(2r(s))`,

`q_U(s)=r(s)-1-U*s`, `k=23/32`,

and `t=beta_D/alpha_D`. Then `0<=t<=1` and

`sigma(t)=(1+k*t-r(t))/r(t)`.

Let s be the larger of the two actual owner slopes. Their total vertical
loss is at most `U*s`; their total `r-1` contribution is at least `r(s)-1`.
The same original width variation as in the accepted theorem satisfies

`V=|h_B-h_X|+|h_X-h_D|+h_B-h_D >= 2(max(h_B,h_X,h_D)-h_D)`.

Since an actual owner is one of B,X,D and h is increasing on [0,1],
`V>=2(h(s)-h(t))_+`. Therefore the surplus of the claimed row bound over
two is at least

`q_U(s)+2(h(s)-h(t))_+ + sigma(t)`.

## 2. Minimize over the actual owner slope

The function `q_U` decreases until

`s0=U/sqrt(1-U^2)=3/4`

and increases thereafter. Here `0<s0<1`. The derivative of `q_U+2h` is

`(1+s^3)/(1+s^2)^(3/2)-U >= 1/sqrt(2)-3/5 > 0`.

The first inequality follows by squaring nonnegative quantities and using
`2(1+s^3)^2-(1+s^2)^3 = (1-s)^2*(s^4+2s^3+2s+1)>=0`.
The last follows from `9/25<1/2`. Splitting at s=t
therefore gives the exact lower bound

`q_U(s)+2(h(s)-h(t))_+ >= q_U(min(t,s0))`.

Indeed, for s<=t the second term vanishes and the minimum of q_U is at
`min(t,s0)`. For s>=t, the strict monotonicity of q_U+2h puts the minimum
at s=t, which is no smaller than the preceding bound.

## 3. Exact scalar payment on the complete interval

First suppose `0<=t<=s0=3/4`, and write r=r(t). The unchanged
algebraic identity is

`r*(q_U(t)+sigma(t)) = (r-1)^2 + t*(23/32-3r/5)`.

For `0<t<=3/5`, we have `r<=sqrt(34)/5<7/6`. The latter comparison
has exact squared reserve `49/36-34/25=1/900>0`. Consequently

`23/(32r)-3/5 > 69/112-3/5 = 9/560 > 0`.

Both terms in the scalar identity divided by r are nonnegative, and
the second is strictly positive. At t=0 they both vanish.

For `3/5<=t<=3/4`, we instead use

`sqrt(34)/5<=r<=5/4`, `sqrt(34)/5>29/25`.

The last strict comparison has exact squared reserve `9/625`. Therefore

`(r-1)^2 > 16/625`,

`t*(23/32-3r/5) >= -t/32 >= -3/128`.

Their sum is strictly greater than

`16/625-3/128 = 173/80000 > 0`.

Thus the scalar payment is positive for every `0<t<=s0`. At t=0,
strict increase of q_U+2h makes the earlier two-variable expression
positive for every s>0.

Next suppose `s0<=t<=1`. Here

`q_U(s0)=-1/5`, `sigma'(t)=(23/32-t)/(1+t^2)^(3/2)`.

Because `23/32<3/4=s0`, sigma decreases on this whole interval. Its
minimum is at t=1, where the total payment is

`55/(32sqrt(2))-6/5`.

Use `sqrt(2)<10/7`, whose exact squared reserve is `2/49`. This gives

`55/(32sqrt(2))-6/5 > 77/64-6/5 = 1/320 > 0`.

The two ranges cover every t in [0,1], including the overlap at 3/5
and the joining point s0=3/4. The full two-variable expression can
vanish only when s=t=0.

## 4. Equality and the unchanged strict caller

Equality forces D and both selected separator owners aligned. The
remaining original width variation V must then vanish. Since h_D=1/2,
this forces B and X aligned as well. Their two vertical gaps have
magnitude at most 3/5<1; aligned physical nonoverlap therefore gives
both horizontal gaps at least one. Equality in their sum makes each
exactly one.

Now retain the unchanged strict original-nine 001/00 predicate, its
normalized CD transverse gap `y_D-y_C>=2/3`, and nonnegative D tilt.
The previously proved G order and horizontal bounds force an upward
actual D/G separating axis, as required by the accepted signed cap.
The actual AB and EFG links, the row just proved, the ordinary A/E cap,
and the signed D/G cap force equality throughout, exactly as in Section
4 of `WEAK_OUTER_NUMERIC_POSITIVE_D_TOTAL_VARIATION_ROW_HAND_TERMINAL.md`.
They yield aligned B,X,D and

`D=(3/2,-1/16)`, `G=(1,15/16)`, `x_B=-1/2`, `x_X=1/2`.

Because U<1, the variation bound gives `y_X<y_G`. The aligned X/G
horizontal gap is one half, so physical nonoverlap forces `y_X<=y_D`.
Because U<2/3, the same bound gives

`y_X>=y_D-3/5>y_D-2/3>=y_C`.

The original actual BC link gives `x_C>=h_C>=1/2`. The original C/D
cone and transverse gap give `x_C<=5/6`. Put `p=x_C-1/2`, so
`0<=p<=1/3`. The retained C/X center-distance condition and the original
C/D cone then imply

`1 <= |c_C-c_X|^2 <= p^2+(1-p)^2`.

For `0<p<=1/3` the right side is strictly below one. Hence p=0 and
h_C=1/2. The C/D horizontal gap is now exactly
`1=h_C+h_D`, contradicting the retained strictly weak CD bit. This
excludes the guard region even at closed Q=1105/256, and in particular
for every q<Q.

If either horizontal order is equality, its corresponding vertical gap
has magnitude at most U<1, contradicting the unit center-distance bound.
Thus the weak order `x_B<=x_X<=x_D` is sufficient for the closed guard.
Both X=H and X=I are permitted independently. Every application must
retain the same original labels, exact frames, corners, physical pairs,
actual marked links and strict CD comparison; no numerical separation
margin is needed on the equality face.

## 5. Finite complementary cover

For either fixed X=H or X=I, the complement is covered by exactly six
closed domains: `x_X<=x_B`, `x_D<=x_X`, and, for each independent pair
of signs s,t, the domain

`s(y_X-y_B)+t(y_D-y_X) >= 3/5`.

The maximum of those four signed forms is exactly the total variation.
Every shared equality face is retained. A full original or fixed-center
parent closes only after all six domains are excluded or attached to
complete, source-bound subcovers. The exact arithmetic companion checks
the constants above; it does not replace this continuous physical proof
or certify any particular caller's interval bounds.

## Exact replay

From `research/nine/computer_assisted/positive_d_row_terminal_v2`, run:

```sh
python -B -S check_positive_d_3_5.py
python -B -S review_positive_d_row_guard_v2.py
```

These replay the 23 exact scalar identities/constants and 529 guard checks.
The continuous physical proof above is an essential part of the theorem.
The helper requires independently proved bounds for the same immutable
original caller; it does not certify ancestry or whole-parent coverage.
