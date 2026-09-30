# Analytic removal of the cardinal-W missing-south case

This note gives the mathematical argument behind
`Analytic/CardinalSouthTail/{Scalar,Support,Geometry}.lean`, and the sharper
shared-center estimate in `Analytic/CoupledWingBudgetSharp.lean`.
These are new source proof bodies; Lean compilation and kernel acceptance have
not been performed. The unrestricted OWN-W mixed cases and the south upper
tail are not claimed solved.

## 1. The four actual inequalities

Use the unchanged normalized frame, with central center `(cx,cy)`, west tilt
`w`, south tilt `s`, and diagonal angle `d`. Write `v=-w`, `q=d+v`, `r=d-s`,
and

    H(x) = 1/2 + (|cos x| + |sin x|)/2.

Let `(aW,bW)`, `(aD,bD)`, `(aS,bS)` be the signed local center coordinates of
the three exterior squares. Their far-corner constraints are

    (a+1/2)^2 + (|b|+1/2)^2 <= Q0,
    Q0 = 142559/50000,
    R0 = sqrt(Q0),
    rho0 = sqrt(Q0-1/4)-1/2,
    c0 = rho0-1.

The central box gives `0<=cx,cy<=c0`. W is cardinal. The earlier
`MixedCardinalSouth` argument already rules out a missing south wing when
`s<=12/25`. Above that value S must be OWN, since a cardinal S has `|s|<2/5`.
Thus the only case needed here is

    -2/5 <= v <= 2/5,
    12/25 <= s <= 2/3,
    1/2 <= d <= pi/4 < 11/14.

In a missing-south configuration the W/D edge has the candidate W source,
while D/S has the D source. Together with the actual central separators they
give exactly

    CW: H(v) <= aW cos v + bW sin v + cx,
    CS: H(s) <= aS - cx sin s + cy cos s,
    WD: H(q) <= aD sin q + bD cos q - bW,
    DS: H(r) <= aS cos r + bS sin r - bD.

Multiply these inequalities by **4, 10, 3, 3**, respectively. No candidate
S-sourced D/S inequality is substituted for the last line.

## 2. Four support estimates

For any contained local center `(a,b)` the far-corner disk and Cauchy--Schwarz
give

    U a + V b <= R0 sqrt(U^2+V^2) - (|U|+|V|)/2.

The same disk also gives the global radial estimate already proved in
`OwnWingProfileSharpening`:

    a + (31/100)(|b|+b^2) <= rho0.

### West

The W force in local coordinates is `(4 cos v, 4 sin v-3)`. Its squared
length is `25-24 sin v`. For every `-1<=z<=1`,

    sqrt(25-24z) <= 5-(12/5)z,

because the right side is positive and the difference of squares is
`(144/25)z^2`. Therefore W contributes at most

    UW = R0(5-(12/5)sin v) - (4 cos v+3-4 sin v)/2.

### Diagonal

The D force is `(3 sin q, 3 cos q-3)`. Since `0<=q<=6/5`, its length is
`6 sin(q/2)`. Its contribution is at most

    UD = 6 R0 sin(q/2) - (3 sin q+3-3 cos q)/2.

### South

The S force is `(10+3 cos r, 3 sin r)`. Here `cos r>=0`, so its radial
coefficient is at least 10 and its transverse coefficient has absolute value
at most 3. Since `(31/100)*10>3`, the radial estimate implies directly

    (10+3 cos r)aS + 3 sin r bS <= rho0(10+3 cos r) = US.

This proves the axial support without presupposing a support branch.

### Central square

The total central contribution is

    (4-10 sin s)cx + 10 cos s cy.

On the present interval, `sin s>=2/5` and `cos s>=0`. Thus it is at most

    UC = 10 c0 cos s.

The negative x-force must be retained until CW and CS have been added. Bounding
their central contributions independently would lose this estimate.

## 3. A positive scalar defect

Let

    T = 4H(v)+10H(s)+3H(q)+3H(r).

The four separators and their supports require `T-UW-UD-US-UC<=0`.
Use `|sin r|>=sin r` and the signs of the other widths. The resulting lower
bound is

    13-10rho0-5R0 + (15-10rho0)cos s + 5 sin s + 4 cos v
    + 2(|sin v|-sin v) + (12/5)R0 sin v
    + 3 sin(d+v) - 6R0 sin((d+v)/2)
    + (3/2-3rho0)cos(d-s) + (3/2)sin(d-s).

Use the rational bounds

    5/3 <= R0 <= 1689/1000,    rho0 <= 1113/1000.

The sign of `sin v` matters. Define `B=4` for `v>=0`, and `B=67/1250` for
`v<=0`. In either case

    B sin v <= 2(|sin v|-sin v)+(12/5)R0 sin v.

All the other weakened products have nonnegative cosine or half-sine factors.
Consequently the defect is at least

    F(v,s,d) = -263/40 + (387/100)cos s + 5 sin s
               + 4 cos v + B sin v
               + 3 sin(d+v) - (5067/500)sin((d+v)/2)
               - (1839/1000)cos(d-s) + (3/2)sin(d-s).

We now prove `F>0` on the entire domain.

### Diagonal monotonicity

Put `C=cos((d+v)/2)`, so `0<=C<=1`. The chord part of the d derivative is

    3 cos(d+v)-(5067/1000)C
      = 6C^2-(5067/1000)C-3
      <= -2067/1000.

Indeed, subtracting its value at `C=1` factors as

    (C-1)(6(C+1)-5067/1000) <= 0.

Also `-1/6<=r<=107/350`, whence `sin r<=107/350` and `cos r<=1`. Therefore

    F_d <= -2067/1000+(1839/1000)(107/350)+3/2
         = -1677/350000 < 0.

It suffices to prove positivity at `d=11/14`.

### South concavity

For fixed v and d, the s-dependent part is `A cos s + E sin s`, where

    A = 387/100-(1839/1000)cos d+(3/2)sin d,
    E = 5-(1839/1000)sin d-(3/2)cos d.

Both coefficients are positive (the elementary bounds `|sin d|,|cos d|<=1`
already suffice). Since s is in the first quadrant, this function is concave.
Its minimum occurs at `s=12/25` or `s=2/3`.

### West concavity

On each side of the genuine sign wall `v=0`, B is constant and

    F_vv = -4 cos v-B sin v-3 sin(d+v)
           +(5067/2000)sin((d+v)/2).

Throughout either interval, `cos v>=23/25`, `B sin v>=-67/3125`, and
`sin(d+v)>=0`. Hence

    F_vv <= -4(23/25)+67/3125+5067/2000
          = -56253/50000 < 0.

The remaining west endpoints are `-2/5`, `0`, `2/5`.

### Six rational endpoint inequalities

Use the Taylor bounds

    cos x >= 1-x^2/2+x^4/24-x^6/720,
    cos x <= 1-x^2/2+x^4/24                  (x>=0),
    sin x >= x-x^3/6+x^5/120-x^7/5040       (x>=0),
    sin x <= x-x^3/6+x^5/120               (x>=0),

and oddness for negative sine arguments. Substitute lower bounds into positive
terms of F and upper bounds into negative terms. At `d=11/14`, the resulting
rational polynomials exceed the following values:

| v | s | strict lower bound |
|---|---|---|
| -2/5 | 12/25 | 7/10 |
| -2/5 | 2/3 | 3/4 |
| 0 | 12/25 | 1/10 |
| 0 | 2/3 | 3/20 |
| 2/5 | 12/25 | 11/50 |
| 2/5 | 2/3 | 27/100 |

These are exactly the endpoints left by the preceding monotonicity and
concavity arguments, not a sampled cover of the domain. All are positive,
contradicting the required nonpositive defect.

Combining this large-tail argument with the earlier `s<=12/25` result proves:

> A normalized packing with cardinal W cannot have a missing south wing,
> regardless of the S central bit.

## 4. A sharper budget for two OWN wings

There is a separate improvement that does not assume either candidate D edge.
For OWN W and OWN S, the shared-center inequalities give

    aW+aS >= 1+(387/1000)(cos v+cos s)+(61/100)(sin v+sin s).

Suppose `v+s>=24/25`. Since both angles are at most `2/3`, both lie in
`[22/75,2/3]`. The function

    G(x) = 1/2+(387/1000)cos x+(61/100)sin x
           -(941/1000+(9/25)x)

is concave there, with strictly negative second derivative. The same Taylor
bounds show `G(22/75)>1/5000` and `G(2/3)>1/5000`. Thus

    aW+aS > 2(941/1000)+(9/25)(24/25)
           = 5569/2500,

whereas each radial coordinate is less than `1113/1000`. The contradictory
bounds differ by `1/625`. Therefore

    s-w = s+v < 24/25.

In a missing-west configuration the already proved D-sourced west gap gives
`d-w>1`. Combining the two inequalities yields the new strict reserve

    d-s > 1/25

when both wings are OWN. This uses only the original normalized frame.

## 5. What remains

The three independent obligations in `ReductionInterface.lean` remain:
exclude MissingWestWing, exclude MissingSouthWing, and prove the canonical
OWN-S upper bound `s<=11/25`. Their domains are now smaller:

- A missing south wing must have W OWN; the cardinal-W / large-S exception is gone.
- A missing west wing still has `d>3/5`. If W is cardinal then S is OWN;
  if both are OWN, additionally `s-w<24/25` and `d-s>1/25`.

The old finite classification has not yet been removed from the public
lower-bound and uniqueness endpoints. The completely analytic replacement is
the active work target, not merely a packaging requirement.
