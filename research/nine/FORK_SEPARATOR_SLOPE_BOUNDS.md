# Finite slope bounds for the active 000/01 fork

This is a hand deduction within the full moving `000/01` domain, after the
existing common vertical reflection. It proves no whole-mask exclusion.
No floating optimization enters the argument.

Write `E=M3` for the right outer main square, `R` for the right short-chain
endpoint, and `P` for the short-chain middle square. Use the established
whole-domain bounds

    89/60 < x_E < 91/60,        |y_E| <= 1/8,
    23/30 < x_R < 13/12,       |c_R| < 91/60,
    -1/12 < x_P,              |c_P| < 91/60,
    y_R > 25/32.

The last bound is the stronger right-shoulder routing estimate established
in the current continuation. The weaker published `y_R>31/60` does not
suffice for the finite negative-PR-slope bound below.

Every physical unit square contains its concentric radius-1/2 disk.
Consequently any nonzero separating vector `v` for two such squares obeys

    v dot (c_B-c_A) >= H_A(v)+H_B(v) >= |v|.             (1)

## 1. The E-to-R normal satisfies -2/3 < w < 6

Take any E-to-R separating normal `n=(-w,1)`, after normalizing its
positive vertical component. Put `D=x_E-x_R` and `V=y_R-y_E`. The bounds
above give

    2/5 < D < 3/4.

Moreover `y_R<21/16`: indeed

    (21/16)^2+(23/30)^2-(91/60)^2 = 13/1280 > 0.

Thus `V<23/16`. Equation (1) implies

    sqrt(1+w^2) <= w D + V.                            (2)

If `w=-u` with `u>=2/3`, the right side of (2) is less than
`23/16-2u/5`. But the unit vector `(4/5,3/5)` gives

    sqrt(1+u^2) >= (4+3u)/5,
    (4+3u)/5 - (23/16-2u/5)
      = u-51/80 >= 7/240 > 0.

This is a contradiction. If `w>=6`, the right side of (2) is less than
`3w/4+23/16`, whereas the unit vector `(7/25,24/25)` gives

    sqrt(1+w^2) >= (7+24w)/25,
    (7+24w)/25 - (3w/4+23/16)
      = 21w/100-463/400 >= 41/400 > 0.

This is again a contradiction. Hence every such normal has

    -2/3 < w < 6.

## 2. Every negative P-to-R slope satisfies -4 < z < 0

Take a P-to-R separating normal `m=(1,z)` with `z<0`, normalizing its
positive horizontal component (whose positivity is proved separately from
the weak cone condition). Put `t=-z>0`. The established center bands give

    x_R-x_P < 13/12+1/12 = 7/6,
    y_P-y_R < 91/60-25/32 = 353/480.

Equation (1) consequently yields

    sqrt(1+t^2) < 7/6 + (353/480)t.                    (3)

If `t>=4`, the same unit vector `(7/25,24/25)` gives

    sqrt(1+t^2) >= (7+24t)/25,
    (7+24t)/25 - (7/6+(353/480)t)
      = (539t-2128)/2400 >= 7/600 > 0,

contradicting (3). Thus `-4<z<0`. This conclusion does not select the owner
of either separating normal and does not add an orientation assumption.

## 3. Use in an exact certificate

The entire negative-slope fork is confined to the finite open rectangle

    (w,z) in (-2/3,6) x (-4,0).

An exact table over its closed rectangle is therefore a sound stronger
target. The point `(0,0)` is a sharp limit and needs an analytic local
bound or a certificate preserving its zero, rather than a uniform positive
numerical margin. Owner relations and all physical hypotheses still have
to be retained in the fork inequality.
