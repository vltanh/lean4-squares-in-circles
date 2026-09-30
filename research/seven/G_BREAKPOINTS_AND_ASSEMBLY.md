# G/H — breakpoint audit and preservation of the global proof

Baseline: `1dbbd4f106e9860752e9c0c612864196167df103`.
This note records which numerical cuts disappear, which have a mathematical
reason to remain, and why the replacement lemmas preserve the seven-square
proof. All proposed changes are research handoffs, not production edits.

## 1. Inventory and decisions

| Location | Original cut | Decision / mathematical explanation |
| --- | --- | --- |
| `ForwardNegativeTarget.axial_target_support` | z=1/3 | Removed by note E. Use z=pi/6, the zero of the nonnegative axial dual multiplier. |
| `ForwardNegativeTarget.sideTarget_negative_pos` | z=1/6 | Removed by note E. Split by the sign of the actual tangent-force coefficient K(z). |
| `InwardSideTarget.targetH_zero_gt_one` | side label s=2/3, also s=pi/6 | Both can be removed by the single monotone profile proved in section 2 below. |
| `OppositeForward.opposite_side_axial_pos` | z=1/3 | May be replaced by the crossing of its two available affine clearance bounds; see section 3. |
| `EasySectors.fixed_gap_forward_positive` | source label t=5/16 | May be replaced by t=3/10, the exact zero of the coarse support reserve; see section 4. |
| `ForwardBothNegative.fixed_gap_forward_both_negative_side` | source label t=2/5 | Retain as an explicitly justified overlap cut: the short marker estimate has reserve 1/1050 there; see section 5. |
| `AllGaps` | marker gap g=1 | Retain: the marker arcs contain three common points with explicit angular slack, followed by a continuous leftmost-minimum argument. |
| Label-boundary modules | s0, td, switchLabel, cap boundaries | Retain. These are intersections of the disk, tie line, diagonal, or the sign change of a support coefficient. |
| Source/sign splits | sine/cosine zeros, transverse signs, four axes | Retain. These are the actual absolute-value and separating-axis cases. |

The new proof C uses a single cut at z=1. Its exact purpose is recorded there:
a nonnegative Taylor-error factor on `[0,1]`, followed by a derivative bounded
below by 3/100 on `[1,pi/2]`. This is not a fine partition.

## 2. Remove the inward side-target label split

Target: the private `targetH_zero_gt_one` lemma in
`Seven/InwardSideTarget.lean`. Let s be the target's side label and
`d=pi/3-s`. Existing label bounds give

```text
pi/12 <= d < 7/10,
A >= tieA(s) = (2 pi+7)/9-(44/45)s,
v <= 1/2+(6/5)(s-pi/6).
```

Both sine and cosine of d are positive. Therefore

```text
H=(A+1/2)cos d+(1/2-v)sin d >= J(d),

J(d)=(alpha+(44/45)d)cos d+((6/5)d-pi/5)sin d,
alpha=23/18-14 pi/135.
```

The coefficients follow by substituting `s=pi/3-d`; no support branch is
assumed. Differentiate without expanding the trigonometric functions:

```text
J'(d)=(44/45+(6/5)d-pi/5)cos d
       +(6/5-alpha-(44/45)d)sin d.
```

Throughout the interval,

```text
44/45+(6/5)d-pi/5 >= 44/45-pi/10 > 3/5,
6/5-alpha-(44/45)d > -1/2,
cos d > 3/4,                 0 < sin d < 7/10.
```

For the second inequality use `alpha<1` and `d<7/10`; for the cosine
bound use `cos d>=1-d^2/2`. It follows that

```text
J'(d) > (3/5)(3/4)-(1/2)(7/10)=1/10.
```

Thus J is increasing on the whole domain. At its left endpoint,

```text
J(pi/12)=(23/18-pi/45)cos(pi/12)-(pi/10)sin(pi/12)
        > (6/5)(24/25)-4/45
         = 1196/1125 > 1.
```

The last estimate uses `pi<22/7`: it implies
`23/18-pi/45>6/5`, `pi/12<4/15`, `cos(pi/12)>24/25`, and
`pi/10<1/3`. Hence `H>1` as required, without the three old label regimes.

Integration: retain `target_angle`, `targetH_support`, and the source-label
concavity argument. Replace only `targetH_zero_gt_one` by this profile bound.
A `HasDerivAt` proof and `Seven.monoOn_of_hasDeriv_nonneg` suffice.

## 3. Replace the remaining mixed opposite-forward cut by a clearance crossing

This is separate from the Bernstein site D. In the negative-turn branch of
`opposite_side_axial_pos`, the existing geometry provides, for `0<=z<7/10`,

```text
1-u-v >= L1(z)=1/170+4z/5,
1-u-v >= L2(z)=1/2-pi/5+6z/5.
```

Their crossing is

```text
z_star=pi/2-5/4+1/68,
1/3 < z_star < 40/119.
```

The bounds follow from `157/50<pi<22/7`. Unlike a chosen mesh boundary,
z_star records exactly when the stronger of two geometric clearances changes.

Below z_star, use L1 and the elementary bounds
`sqrt(3)-1<11/15`, `sin z<=z`, `1-cos z<=z^2/2`. The support is at least

```text
q(z)=1/170+z/15-z^2/4.
```

This quadratic is concave on `[0,40/119]` and its endpoint values are

```text
q(0)=1/170,
q(40/119)=19/424830>0.
```

Above z_star, use L2. The lower bound is the existing far profile

```text
B(z)=1/2-pi/5+6z/5-(sqrt(3)-1)sin z-(1/2)(1-cos z).
```

The derivative-vector estimate from note D gives `B'(z)>3/10` on the whole
real line. One endpoint comparison suffices because `z>=z_star>1/3`:

```text
B(1/3) > 11353/3061800 > 0.
```

For this fraction use `pi<22/7`, `sqrt(3)-1<11/15`,
`sin(1/3)<=1/3-(1/3)^3/6+(1/3)^5/120`, and
`1-cos(1/3)<=1/18`. Thus the point 1/3 remains at most a single rational
comparison point, not the unexplained boundary between support methods.
The existing `side_axial_far_profile` can also be reused unchanged.

## 4. Explain or sharpen the forward-positive cutoff 5/16

In `fixed_gap_forward_positive`, the coarse estimate is

```text
support_target > -37/50,
u >= 4t/5.
```

Thus the full support is greater than

```text
1/2+4t/5-37/50 = 4t/5-6/25.
```

This is nonnegative precisely when `t>=3/10`. Strictness of the target bound
handles t=3/10 as well. The old 5/16 leaves an extra 1/100 reserve, but is not
necessary. It can be replaced by 3/10, the zero of the displayed bound.

For `t<3/10`, the existing complementary argument still applies: its lower
angular endpoint requirement `pi/6-t>21/100` is now stronger, not weaker.
The natural split at `z=pi/4` inside that argument remains because the ordering
of sine and cosine reverses there. No new proof machinery is required.

## 5. Why the remaining 2/5 source-label cut is acceptable

The short marker estimate in `forward_negative_negative_small` gives

```text
support >= 1/2-u-sin(pi/3-t-1/2).
```

For a side source, `1/2-u>=pi/5-6t/5`. For t<=2/5 the sine argument is
nonnegative, so `sin x<=x` gives

```text
support >= 1/2-2 pi/15-t/5
        >= 21/50-2 pi/15 > 1/1050 > 0.
```

The larger-label proof uses exact circular/straight boundary support and its
proved monotonicity/concavity lemmas on t>=2/5. The number 2/5 is a
convenient common endpoint for these analytic estimates, not a geometric
singularity. Its mathematical role and positive reserve are now explicit.
No continuous interval is being accepted by testing a collection of cells.

## 6. Other domain constants versus case splits

The following should not be conflated with numerical subdivisions:

- `[0,3/4]` in A is a whole radicand-comparison domain; its proof is uniform.
- `[8/5,7/4]` in B is a radial-coordinate enclosure proved from the circle.
- `[0,5/8]` in F is the whole two-circular-boundary turn range supplied by
  `opposite_upper_circular`, using `diagonal_angle_bounds`. It is not an
  enumeration of smaller ranges. The replacement proves its polynomial
  decreasing even on `[0,1]`, but positivity is only asserted up to 5/8.
- The `19/100` lower bound for the circular-source/straight-target reduction
  is derived from the label transition in its caller, not an independent
  assumption added to the packing.
- `s0` is the circle/tie intersection; `td` is the diagonal junction;
  `switchLabel` is the zero of `cos d-(4/9)sin d`. These are structural.
- The four finite separating directions and two signs must remain exhaustive.

## 7. Preserve the assembly and equality proof

The replacement dependency map is

```text
A -> marker-arc curvature -> marker_arc_support
B -> circular-boundary target monotonicity
C -> inward axial-turn support
D -> opposite-forward axial scalar
E1/E2 -> axial_target_support
E3 -> sideTarget_negative_pos
F -> radialPolynomial_pos -> radialE_pos -> inward_circular_pos
```

These feed the existing strict sector statements. `FixedGap.fixed_gap_active`
still splits by four separating axes, transverse signs, and active labels.
Capped labels still reduce to the three actual vertices of their convex
triangle; that is geometric convexity, not an angle cover.

For gaps below pi/3, `AllGaps` still uses the marker-arc contradiction for
g<=1 and the leftmost-minimum argument on the remaining continuous interval.
The marker half-width 801/1600 permits the three angles with offsets
`0,+1/3200,-1/3200` when g<=1. Their inclusion is proved as an inequality,
not sampled. The larger-gap argument uses compactness and derivatives.

At equality, no positivity lemma is weakened. E3 and F still require z>0,
leaving the original z=0 contact branches intact; C is zero only at z=0;
A, B, D, and the axial E statement remain strict on their closed domains.
Thus the three contact types, the regular hexagon of six exterior markers,
and the column-packing reconstruction retain the same logical inputs.
The original `Packing`, `Congruent`, radius and column family are unchanged.

## 8. Validation and integration boundary

All algebraic constants and the new derivative/profile identities above were
cross-checked exactly. This is a mathematical and source-level dependency
review, not an elaborated dependency audit. No production Lean file or proof
entry point was changed. The integrator must implement the proposed local
replacements, compile them, and rerun the existing theorem/axiom checks.
