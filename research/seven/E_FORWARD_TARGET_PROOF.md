# E1–E3 — forward-negative target support without Bernstein certificates

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Targets in `SquaresInCircles/Seven/ForwardNegativeTarget.lean`:
`axial_target_support` and `sideTarget_negative_pos`.
This note provides replacements for both complete statements. It eliminates
all three Bernstein applications in that file, not merely their coefficient
lists. Production files are unchanged; formal integration is separate.

Write `c=cos z`, `s=sin z`, `X=A+1/2`, `Y=v+1/2`, and `R^2=13/4`.
Admissibility implies `X^2+Y^2<=R^2`. The following uses only that disk,
the existing label constraints, elementary trigonometry, and calculus.

## 1. Axial targets: the statement and the actual support switch

For an axial-labelled target, the tie-line constraint is

```text
9X+11Y <= 2 pi+17.
```

We must prove, for `0<=z<=pi/2`,

```text
T(z) = 1+2 pi/15-4z/5+c-Xc-Y(1-s) > 0.
```

Use two support estimates meeting at `z=pi/6`. This is not a fitted
breakpoint: it is exactly where the nonnegative dual multiplier

```text
lambda(z)=(3/40)(1-2 sin z)
```

becomes zero. Below it we use the axial tie line together with the disk;
above it the disk alone suffices. This replaces the old split at `1/3`.

## 2. Small axial turns: derive the residual support cone

Suppose `0<=z<=pi/6`, so `lambda>=0`. Subtract `lambda*(9,11)` from the
force `(c,1-s)` and put

```text
U = c-9 lambda = c-27/40+(27/20)s,
V = 1-s-11 lambda = 7/40+(13/20)s.
```

The scalar `3/40` is a convenient nonoptimal dual weight. Its role is to keep
the residual force in a narrow cone, which we now prove rather than assume:

```text
U>0,                    U/2 <= V <= 3U/5.
```

First `c>=sqrt(3)/2>5/6` gives `U>=19/120>0`. Next

```text
V-U/2 = (41-40c-2s)/80 >= 0
```

because `c<=1` and `s<=1/2`. Finally

```text
3U/5-V = (30c+8s-29)/50 > 0.
```

The function `30 cos z+8 sin z` is concave on `[0,pi/6]`; its endpoint
values are `30` and `15 sqrt(3)+4`, both greater than 29, using
`sqrt(3)>5/3`. This proves the cone on the entire interval.

## 3. A linear bound for the disk support on this cone

For `U>0` and `r=V/U` in `[1/2,3/5]`, consider

```text
(13/8+4r/5)^2-(13/4)(1+r^2)
  = -39/64+(13/5)r-(261/100)r^2.
```

It is a concave quadratic. At its two endpoints its values are respectively
`61/1600` and `441/40000`, both positive. Hence

```text
R sqrt(U^2+V^2) <= (13/8)U+(4/5)V.
```

Equivalently, the squared difference is the following explicitly nonnegative
sum; this is also convenient for an algebraic Lean proof:

```text
((13/8)U+(4/5)V)^2-(13/4)(U^2+V^2)
 = (261/100)(V-U/2)(3U/5-V)
   +(271/1000)U(3U/5-V)+(441/40000)U^2.
```

Thus the choice of the two rational support coefficients is fully checked by
the cone geometry. It is not a table of sampled directions.

Cauchy–Schwarz on the target disk and the axial tie line now give

```text
Xc+Y(1-s) <= lambda*(2 pi+17)+(13/8)U+(4/5)V.
```

After substitution, the required defect T is bounded below by

```text
M(z) = 1091/1600-pi/60 -(5/8)cos z
       +(3 pi/10-131/800)sin z -(4/5)z.
```

This is the quantity to understand instead of the old degree-14 discriminant.

## 4. A single tangent parabola proves the small-turn defect positive

Put `b=3 pi/10-131/800>0`. Elementary bounds `157/50<pi<22/7` give

```text
M(0) = 91/1600-pi/60 > 151/33600 > 1/250,
M'(0)=b-4/5 > -87/4000 > -1/40.
```

On `0<=z<=pi/6`, `cos z>5/6` and `sin z<=1/2`, so

```text
M''(z)=(5/8)cos z-b sin z > 4411/33600 > 1/8.
```

Integrating the curvature bound twice from zero yields

```text
M(z) >= 1/250-z/40+z^2/16
      = (z-1/5)^2/16+3/2000 > 0.
```

This replaces the entire degree-14 positivity block with a narrow support
cone and one completed square. All constants have identified roles: a dual
weight, a cone support bound, or a lower curvature/value/slope reserve.

## 5. Large axial turns: half-angle support is concave

For `pi/6<=z<=pi/2`, discard the tie line. Put

```text
h(z)=cos(z/2)-sin(z/2) >= 0.
```

The squared length of `(c,1-s)` is `2h(z)^2`, so Cauchy–Schwarz and
`sqrt(13/2)<51/20` give

```text
T(z) >= G(z)
 = 1+2 pi/15-4z/5+cos z-(51/20)h(z).
```

There is no reason to approximate G by a degree-7 polynomial. Its second
derivative factors:

```text
G''(z) = h(z)*(51/80-cos(z/2)-sin(z/2)) <= 0,
```

because `cos(z/2)+sin(z/2)>=1`. Thus G is concave. At the endpoints,

```text
G(pi/6) = 1+sqrt(3)/2-51 sqrt(2)/40 > 1/84,
G(pi/2) = 1-4 pi/15 > 17/105.
```

For the first comparison it suffices that `sqrt(3)>5/3` and
`sqrt(2)<10/7`; for the second use `pi<22/7`. Concavity proves positivity
throughout the interval. Together with section 4 this proves the original
`axial_target_support` on its full domain, with no Bernstein call.

## 6. Side targets: the statement and transition tangent

Now assume the target is side-labelled, and `0<z<1`. The statement
`sideTarget_negative_pos` asks that

```text
T = c-2/15-4z/5 +(3/5-c)X+(s-4/15)Y > 0.
```

Let `(a0,u0)` be the existing circle/tie-line transition state, and write
`X0=a0+1/2`, `Y0=u0+1/2`. Existing geometric facts give

```text
A<=a0,       v>=u0,       a0>11/10,       u0>29/100,
a0-A >= (12/25)(v-u0).
```

The last inequality is the circle's tangent inequality at `(X0,Y0)`:
`X0(A-a0)+Y0(v-u0)<=0`, with `Y0/X0>=12/25`.
It is `side_transition_trade` in the production proof.

Define the force along that tangent by

```text
K(z)=(12/25)(cos z-3/5)+sin z-4/15.
```

We split by the actual coefficient signs `cos z-3/5` and K, not by an
arbitrary angle such as `1/6`. K describes exactly when moving from the
transition state along the available tangent direction improves the support.

## 7. Side regime with cos z < 3/5

Since `0<z<1`, we have `cos z>1/2`, `sin z>4/5`, `X>=1` and `Y>79/100`.
Both force coefficients in T are positive. Therefore

```text
T > 3/5-2/15-4/5+(8/15)(79/100) = 11/125 > 0.
```

This is a direct support sign argument; there is no polynomial.

## 8. Side regime with cos z >= 3/5 and K(z) >= 0

Let T0 denote T at the transition state. The tangent inequality gives

```text
T-T0 = (c-3/5)(a0-A)+(s-4/15)(v-u0)
     >= K(z)(v-u0) >= 0.
```

At that state, write `r0=remainder(a0,u0)>=0`. Then

```text
T0 = 2r0/15 +(a0-1/2)(1-c)+(u0+1/2)s-4z/5
   >= (3/5)(1-c)+(79/100)s-4z/5.
```

The elementary Taylor bounds `1-c>=z^2/2-z^4/24` and
`s>=z-z^3/6`, together with `0<z<1`, imply

```text
T0 >= -z/100+(3/10)z^2-(2/15)z^3-z^4/40
    >= z*(-1/100+(17/120)z).
```

Meanwhile `c<=1` and `s<=z` imply `K(z)<=z-28/375`.
So `K(z)>=0` forces `z>=28/375`, and hence

```text
T0 >= (13/22500)z > 0.
```

The lower angle bound has been derived from the tangent-force sign. It is not
an input or an experimental threshold.

## 9. Remaining side regime: K(z) < 0

On `[0,1]`,

```text
K'(z)=cos z-(12/25)sin z >= 1/2-12/25 = 1/50 > 0.
```

Also Taylor bounds at the single rational point `1/12` give

```text
K(1/12) >= 8947/1296000 > 0.
```

Therefore `K(z)<0` implies `z<1/12`. This is a consequence of the geometric
regime, not another subdivision of it.

Set

```text
L=c-2/15-4z/5,
p=3/5-c,                   q=s-4/15.
```

Here `L>=1147/1440>0`. Using `c^2+s^2=1`, the squared support margin is

```text
Delta = L^2-(13/4)(p^2+q^2)
      = c^2+(109/30-8z/5)c+(26/15)s
          +(2/15+4z/5)^2-2093/450.
```

All coefficients to be bounded are positive on `0<=z<=1/12`. Substitute
only `c^2>=1-z^2`, `c>=1-z^2/2`, and `s>=z-z^3/6`:

```text
Delta >= z*(26/75-(653/300)z+(23/45)z^2)
       >= (119/720)z > 0.
```

Cauchy–Schwarz gives `pX+qY>-L`, so T is positive. This proves the last side
regime with a cubic inequality and visible positive margin, replacing the old
degree-6 Bernstein block and the angle split at `1/6`.

## 10. Equality and integration

The two replaced statements remain strictly positive on exactly their original
domains. `axial_target_support` includes z=0; `sideTarget_negative_pos` does
not. Do not extend the latter to zero, where the actual side contact can have
zero support.

Leave the nonnegative-turn bounds, `forward_negative_target_lower`,
`negative_target_axial_pos`, and the contact extraction in
`fixed_gap_forward_negative_target` unchanged. They consume only the same
statements proved above.

Suggested new local helpers for the integrator:

```lean
-- All names below are proposed, not existing declarations.
lemma residual_cone {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    0 < U z ∧ U z/2 ≤ V z ∧ V z ≤ (3/5)*U z := ...
lemma cone_disk_support {X Y U V : ℝ}
    (hdisk : X^2+Y^2 ≤ 13/4) (hU : 0 < U)
    (hlo : U/2 ≤ V) (hhi : V ≤ (3/5)*U) :
    U*X+V*Y ≤ (13/8)*U+(4/5)*V := ...
lemma axial_small_margin {z : ℝ} (hz : 0 ≤ z ∧ z ≤ Real.pi/6) :
    3/2000 ≤ M z := ...
```

Use `Seven.trig_concave_gt` for the cone bound, `Seven.curvature_tangent`
for M, and the same concavity/endpoint principle for G. The polynomial identity
in section 3 is a `ring` calculation; its signs need only `mul_nonneg`.
For the side proof, use `side_state_transition_bounds`,
`side_transition_trade`, `remainder_nonneg`, sine/cosine Taylor bounds, and
`Seven.monoOn_of_hasDeriv_nonneg` for K. No import of a replacement target's
old positivity proof should be used to establish the replacement.

## Validation

The residual-force identities, cone squared difference, tangent-parabola
reserves, endpoint margins, and side discriminant identity were independently
checked by exact algebra/rational arithmetic. The mathematics above is
self-contained in those displayed identities and standard calculus; no
computational PASS result is a premise. Lean implementation, compilation and
kernel validation remain a maintainer integration task.
