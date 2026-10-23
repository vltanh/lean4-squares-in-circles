# Whole-domain core/core pair replacement

## Active change

`Arithmetic/CorePairGeometry.lean` implements the complete core/core
argument from `../CORE_CORE_WHOLE_PAIR_HAND_PROOF.md`, with the same
marker used by both incident four-type pair inequalities. The actual
cycle dispatcher in `Arithmetic/FourTypePairs.lean` now invokes that
geometric theorem for core/core pairs before using any finite problem.

The four recursive decisions `coreSide_coreSide_certificates`,
`coreSide_coreCorner_certificates`, `coreCorner_coreSide_certificates`,
and `coreCorner_coreCorner_certificates` have been deleted. Together
they represented 32 source-axis/sign chart problems; reflected reversal
previously supplied the target axes. The new argument applies directly
to all signs and all actual axes, including ties. The public
`four_type_pair_bound` statement is unchanged. The other 21 analytic
chart pairs remain backed by their existing finite problems.

This is an uncompiled Lean source replacement. No claim about successful
elaboration, kernel checking, or compilation cost is made.

## The geometry

Write

\[
K=\frac{7506931}{1000000},\qquad
g=\frac{269343}{250000},\qquad
\psi(a,b)=\arctan(b/a)-K(7/12-a)-gb.
\]

The positive core boundary is the union of the closed side
`a=7/12, 0≤b≤1/2` and the closed corner

\[
b\ge\tfrac12,\quad b\le a,\quad
(a-\tfrac12)^2+(b-\tfrac12)^2=\tfrac1{144}.
\]

### 1. Bound one marker on the entire core

On the side, put `x=12b/7`. The derivative of arctangent decreases on the
nonnegative axis, so its tangent at `3/4` is a global upper bound:

\[
\arctan x\le\arctan(3/4)+\frac{16}{25}(x-3/4).
\]

Together with `arctan(3/4)<161/250`, this gives `ψ<7/40` for
`0≤x≤6/7`. The elementary lower bound `arctan x≥x-x³/3` gives `ψ≥0`.

On the corner put `d=b-1/2` and `e=a-1/2`. The circle equation and
`0≤d≤e` give

\[
a>\frac{67}{120}>\frac59,\qquad
6d^2\le\frac7{12}-a\le\frac d2.
\]

The lower radial-loss bound is the identity

\[
\frac1{12}-e-6d^2=6(e-\tfrac1{12})^2.
\]

For the upper bound, use

\[
(e+d/2)^2-(e^2+d^2)=d(e-d)+d^2/4\ge0.
\]

The arctangent tangent at `6/7` now bounds the entire corner without
differentiating a square root:

\[
\arctan(b/a)-\arctan(6/7)
\le\frac{49}{85}(b/a-6/7)\le\frac95d.
\]

Thus

\[
\psi<\frac7{40}+(\tfrac95-g)d-6Kd^2
<\frac7{40}+\frac1{300}<\frac9{50}.
\]

The displayed quadratic bound follows by completing one square and
using `K≥7`. For the opposite bound, `d≤e` and `a>67/120` imply
`K(7/12-a)+gb<977/1200`, while `b/a≥6/7` and
`arctan(6/7)>2/3`. Hence `ψ>-59/400>-9/50`.

Both arctangent endpoint bounds use the existing exact alternating-series
lemmas at two fixed rational arguments. They are constant checks, not
subdivisions of the state or angle domain. The odd extension preserves
`|ψ|<9/50` for both signed representatives.

### 2. Bound the center gap using the inscribed disks

On both core charts, `a²+b²<16/25`. On the corner this follows from
`e+d<3/25`, which is an immediate consequence of
`(e-d)²≥0` and `e²+d²=1/144`.

Every unit square contains the open radius-`1/2` disk about its center.
Disjoint interiors therefore force center distance at least one. For
center radii `0<r,s<4/5`, the cosine law and the elementary chord bound

\[
r^2+s^2-\frac7{16}rs\le1
\]

force `cos δ≤7/32`. The chord bound follows from `r²≤(4/5)r`,
`s²≤(4/5)s`, and the explicit nonnegative remainder

\[
1-\tfrac45(r+s)+\tfrac7{16}rs
=\tfrac9{20}(\tfrac45-r+\tfrac45-s)
+\tfrac7{16}(\tfrac45-r)(\tfrac45-s).
\]

The sixth-degree cosine lower bound gives
`cos(4/3)≥7709/32805>7/32`. Monotonicity on the positive interval
then yields `δ>4/3`. No separating-axis case is inspected.

### 3. Finish the same pair cost

Cauchy gives the uniform charge bound
`h(φ)=(|cos φ|+|sin φ|-1)/2<21/100`. Consequently

\[
\delta-\frac9{50}h(\phi)+\psi_j-\psi_i
>\frac43-\frac9{50}\frac{21}{100}-\frac9{25}
=\frac{14033}{15000}>\frac{23}{25}.
\]

The reserve over the exact core/core table entry `23/25` is
`233/15000`. The vertex marker is the original marker throughout;
neither its sign nor its value depends on which incident pair is used.

## Source checks performed

The two rational arctangent endpoint enclosures, the marker and pair
reserves, and the three displayed circle/chord identities were checked
with exact integer and rational arithmetic in Python. Source review
confirmed deletion of the four recursive declarations and the unchanged
actual-cycle theorem interface. `git diff --check` passed. Lean, lake,
and CI were not run.
