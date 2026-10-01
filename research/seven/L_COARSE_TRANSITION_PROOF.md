# L — coarse transition geometry without five-decimal radical enclosures

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
Targets: the tight `J_bounds`, `transition_bounds`, `rd_bounds`, and
`diagonal_angle_bounds` dependency cluster. This note supplies the bounds
actually needed after J/K/M/N; it does not assert the old tight bounds from
weaker hypotheses. Production integration is separate.

Use `157/50 < pi < 377/120 < 22/7`. A short arctangent-integral derivation
of these bounds is given in `P_ELEMENTARY_PI_BOUNDS.md`.

## 1. Characterize the transition as a circle/line intersection

Write `X0=a0+1/2`, `Y0=u0+1/2`, `M=2pi+17`. The defining geometry is

```math
X_0^2+Y_0^2=\frac{13}{4},\qquad 9X_0+11Y_0=M.
```

The production formula chooses the lower-Y intersection:

```math
J^2=202\cdot\frac{13}{4}-M^2,\quad
X_0=\frac{9M+11J}{202},\quad Y_0=\frac{11M-9J}{202}.
```

No precise value of J is needed. The coarse inequalities `23<M<24` give
`8<J<12`. Hence `0<Y0<1`, `X0>0`. For example,
`11M-9J>11*23-9*12>0`, while
`11M-9J<11*24-9*8<202`.
The two circle/line identities follow directly from the formulas and J squared.

On `0<=y<=1`, put

```math
h(y)=9\sqrt{13/4-y^2}+11y.
```

Then `h'(y)=11-9y/sqrt(13/4-y^2)>=5>0`, because the radical is at least
3/2. Thus the transition coordinate Y0 can be located by *two line/circle
comparisons*, not by a decimal approximation to J.

## 2. A lower transition bound

At `y=79/100`,

```math
\left(\frac{1459}{900}\right)^2
 -\left(\frac{13}{4}-(\frac{79}{100})^2\right)
 =\frac{851}{405000}>0.
```

The number 1459/900 is exactly
`(2*(157/50)+17-11*(79/100))/9`. Therefore
`h(79/100)<2*(157/50)+17<M=h(Y0)`, so

```math
u_0>\frac{29}{100}.
```

This is one explicit squared comparison at a coarse proposed bound.

## 3. Choose the upper bound from the required diagonal-angle window

Let `r=rd=sqrt(13/8)-1/2`. Two small squared comparisons give

```math
\frac{55}{71}<r<\frac{31}{40},
```

because

```math
\frac{13}{8}-(\frac{55}{71}+\frac12)^2=\frac{11}{40328}>0,
\qquad(\frac{31}{40}+\frac12)^2-\frac{13}{8}=\frac1{1600}>0.
```

The diagonal angle used by the inward-opposite proof is

```math
\psi=t_d+s_0-\pi/6=\frac7{12}-\frac5{12}r+\frac54u_0.
```

To keep its existing whole-domain upper bound `psi<5/8`, it suffices that
`u0<(1+10r)/30`. Using the proved lower bound `r>55/71` suggests the
**derived comparison point**

```math
u_* =\frac{1+10(55/71)}{30}=\frac{207}{710},
\qquad y_*=u_*+\frac12=\frac{281}{355}.
```

This endpoint is chosen to preserve a geometric domain condition, not to
approximate u0 to a requested number of decimal places.

Since `M<1397/60`, the required upper comparison follows from

```math
81\left(\frac{13}{4}-(\frac{281}{355})^2\right)
 -\left(\frac{1397}{60}-11\frac{281}{355}\right)^2
 >\frac1{40}>0.
```

The terms to be square-rooted are positive, so `h(y*)>1397/60>M`.
Monotonicity gives

```math
\frac{29}{100}<u_0<\frac{207}{710}<\frac7{24}.
```

Consequently `psi<5/8`. Also, using the opposite coarse bounds,
`psi>299/480>3/5`. This replaces the five-decimal interval around 0.6247
by exactly the useful domain statement

```math
\frac35<\psi<\frac58.
```

## 4. Recover all ordinary coarse bounds

From `79/100<Y0<19/24` and the circle identity,

```math
\frac{11}{10}<a_0<\frac98,
\qquad \frac9{25}<s_0=\frac54u_0<\frac25.
```

For the radial bounds, compare X0 squared with `(8/5)^2` and `(13/8)^2`;
all coordinates are positive. In fact the same argument gives
`a0>67/60`, a useful but still coarse bound in J.

The diagonal label satisfies

```math
t_d=\pi/6+7/12-(5/12)r>627/800>18/25.
```

Also `td<pi/4`: this is equivalent to `7-5r<pi`, and already follows from
`r>17/22` (a consequence of `55/71<r`) and `pi>157/50`.
The exact circle/label identities and `Z(td)=(13/12)(r+1/2)` remain unchanged.

For the side tangent used by replacement E, coarse bounds already suffice:

```math
Y_0-\frac{12}{25}X_0
 >\frac{79}{100}-\frac{12}{25}\frac{13}{8}=\frac1{100}>0.
```

Therefore the old `side_transition_trade` does not need `transition_bounds`.

## 5. Source-level dependency handoff

A search of the baseline references identifies these uses. Do not conflate
`side_state_transition_bounds` (a geometric theorem about arbitrary states)
with the tight numerical lemma named `transition_bounds`.

| Use of tight data | Replacement |
| --- | --- |
| `LabelBoundary.J_sq` and the selected intersection branch | Coarse 23<M<24 and 8<J<12, then the exact identities. |
| `LabelBoundary.transition_coarse` | Sections 1–4. |
| `D_range`, radicand positivity, circle parametrization | Exact identities plus the new coarse bounds. |
| `td_bounds`, positive diagonal coordinate, circle/line displacement domains | 55/71<rd<31/40 and section 4. |
| `BoundaryProfiles.test_point` | Delete its use; replacement J anchors at the geometric diagonal junction. |
| `BoundaryProfiles.diagonal_value_pos` | Replacement J compares its angle with the transition endpoint; no evaluation of the diagonal angle is needed. |
| `BoundaryProfiles.diagonal_angle_bounds` | Replace the tight statement with 3/5<diagonalAngle<5/8, updating callers rather than claiming the old interval. |
| `ForwardNegativeTarget.side_transition_trade` | The displayed tangent ratio reserve 1/100. |
| `InwardOppositeMinima.opposite_upper_circular` | The proved upper bound diagonalAngle<5/8 and u0<3/10. |
| `InwardOppositeMinima.diagonal_junction_pos` | Positive diagonalAngle and replacement J's positive diagonalValue. |
| `InwardOppositeMinima.circular_source_line_reduction` caller | Its 19/100 turn lower bound follows already from 2s0-pi/6>19/100. |
| Capped/diagonal branches in `ForwardBothNegative`, `InwardOpposite`, and `InwardOppositeMinima` | rd<31/40 and pi/5<rd suffice. |
| `TargetBoundaryMonotonicity` radial domain | u0<3/10, rd>3/4, and the exact circle equation. |

The old five-decimal constants can remain in historical source, but no such
statement is a premise of the proposed human-proof route. Deleting or altering
production declarations is explicitly left to the integrator.

## 6. Integration order and validation

Prove the circle/line identities and select 0<Y0<1 first; establish monotonicity
of h next; then use the endpoint comparisons. This avoids circularly invoking
`transition_coarse` to prove its own replacement. The radius comparison for rd
is independent of the transition.

Suggested helpers are `transition_coarse_geometric`,
`diagonal_angle_coarse`, and a replacement proof of `side_transition_trade`.
The exact squared comparisons are finite rational arithmetic at explicitly
derived endpoints. They are not an interval grid or an external oracle.
Lean implementation, compilation and elaborated dependency validation have
not been performed here.
