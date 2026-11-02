# Independent physical review of the upper-side/central position lemma

November 2, 2026. Review by the computational certificate agent of
`UPPER_SIDE_GOOD_CENTRAL_POSITION_HAND_TABLE.md` and the corrected producer
and verifier in `pr11_current/research/nine/computer_assisted`.

**Conclusion:** the corrected physical reduction is complete. No missing
chirality, separator owner, zero-angle boundary, position boundary, or
height-order assumption was found. This review concerns the analytic
reduction and its match to the two scalar evaluators; the root agent's
fresh independent arithmetic replay and damaged-certificate controls are
separate checks.

## Checked geometric coverage

The fixed left-endpoint rectangle has halfwidths `217/480,221/600`,
center `(-3/2,0)`, and the stated horizontal interval. It is a contained
subset of every permitted original endpoint inset. No endpoint is
silently replaced by a larger object.

If the central position fails the target, write `xL=-z,xP=-v`. The
original centered half-unit disks and the retained center-cone comparison
give `dx>=1/sqrt(2)>7/10`. Together with `v>=1/10`, this justifies the
whole overcover `z>=4/5`. The remaining endpoint and central position
bounds in the root follow directly from their original strips.

For `D=3/2-z`, the adjusted endpoint horizontal gap is in
`[-17/480,119/480]`. Since its maximum is below `1/2`, a horizontal
coordinate axis cannot separate. Downward owned axes fail as well, using
the nonnegative height premise `yL>=0`. Their adjusted scalar projection
is strictly below `1/2`. A minor wording detail in the first manuscript
version was reported to the root agent: if `D-gx<0`, the uniform bound
should be `max(0,D-gx)`, rather than `D-gx` itself. The exclusion and all
code formulas are unaffected.

The two signs of the original L frame give the exact upward thresholds

```text
negative sign: gy+1/(2a)-t(D-gx), gy+1/(2b)+(D+gx)/t;
positive sign: gy+1/(2a)+t(D+gx), gy+1/(2b)-(D-gx)/t.
```

The terms involving `D+gx` are dominated by the coordinate top facet,
because `D+gx>=139/160>k`. The corrected simplified losses therefore
keep precisely the correct original chirality. The first slope chart
`0<=t<=1/4` has `k>=3/(2sqrt(17))>|D-gx|`; its positive-sign loss is
zero and its negative-sign loss is the shallow expression. The other
chart has denominator at least `1/4`. Both aligned and shared chart
boundaries are covered.

Every surviving threshold is at least `1489/2400>31/50`. This validates
the stronger height bound used by the scalar root from the weaker
physical premise `yL>=0`. In the steep case, the required inequality is
immediate from `sqrt(1+t^2)>=1`, `0<t<=1`, and `D-gx<1/2`.

## Checked original pair and circle formulas

At a negative horizontal center, the two signed circle upper bounds are
the actual relevant original corners for that same sign. The sign is
retained across the circle, endpoint, and central-pair constraints.

The possible vertical displacement is exactly overcovered by
`max(P0-L1,-dx)<=dy<=min(P1-L0,dx)`. Since `dx<=59/60<1`, a normal with
nonpositive horizontal component cannot separate: its projection is at
most `abs(dy)<=dx<1`, below the common support sum. The two
positive-horizontal representatives of each original frame are therefore
exhaustive. The producer and checker choose the correct endpoint of the
dy interval for the sign of each normal's vertical component.

The support sum in the four owned unit normals is
`(1+abs(cos(relative angle))+abs(sin(relative angle)))/2`, reconstructed
with the original signed components. The additional horizontal-gap
constraint `dx>=gL+gP` follows from the two original aligned insets and
the cone comparison: a smaller gap in both coordinates would make their
interiors meet.

## Evaluator comparison

The corrected producer evaluates the simplified loss. The independent
checker reconstructs the unsimplified physical facet thresholds, including
the `D+gx` terms, before taking minima. Their pointwise expressions agree.
The different interval widths can require additional leaves, which the
root agent's final refinement and fresh replay explicitly handled.

The eight roots cover all four actual sign pairs and both slope charts.
Every scalar necessary condition in the manuscript appears in both
evaluators. The reviewed certificate's scope is exactly the original
cone-neighbor position statement; no stronger claim that all high-center
pairs automatically satisfy the cone comparison is being used.
