# Independent review of the wide-main low-side inputs

November 2, 2026. Reviewer: `root_certificates`, a separate collaborating
agent. This is an independent analytic/code review and fresh exact
execution, not human review or a proof-kernel verification. No Lean or CI.

**Result: PASS.** I found no gap in either complete physical statement,
the finite scalar reductions, their acceptance evaluators, or their
full-root coverage. Both fresh exact executions passed, and all eight
damaged controls were rejected.

## 1. Reviewed statements and exact scope

The reviewed source manuscripts are:

- `agent_whole_mask/weak_middle_low_side/WIDE_MAIN_UPPER_CENTRAL_HEIGHT_HAND_TABLE.md`;
- `agent_whole_mask/weak_middle_low_side/WIDE_MAIN_LOW_SIDE_FORCES_CENTRAL_FLOOR_HAND_TABLE.md`.

Both retain the original cone-four mains A,B,C,D in the closed
`Q=1105/256` disk, with actual outer projection links A--B and C--D.
The middle link may be actual or weak. All original frames remain
independent and every original square is physically interior-disjoint.

The first theorem uses just one further central original F, above both
inner mains, and proves `yF > -7/40`. The second retains a right-side
original S above C with `yS < 3/5`, and a right-half central original F
above both mains, and proves `yF-hF > 1/10`. Neither statement assumes
a selected outsider cone chain or an outsider occupancy count. The
horizontal and vertical reflections stated by the author are legitimate
common reflections of the complete original configuration.

This review accepts these two reusable inputs. It does not assert a
new full-mask or original-root closure.

## 2. Upper-central height: physical and algebraic audit

I read the supporting physical reduction in Sections 2--4 of
`root_wide_pair/WEAK_MIDDLE_UPPER_CENTRAL_PAIR_REPLACEMENT_HAND_PROOF.md`
and Sections 1--2 of
`agent_low_floor/weak_middle_11/WEAK_MIDDLE_BOTH_WEAK_COMMON_REDUCTIONS.md`.
The height bound is established before the former manuscript uses a
second central square. Its use for a single F is therefore sound.

The own-half clearance and `yB,yC > -6/5` give `yF > -3/10` using
only the original main cones and actual outer links. The two individual
endpoint-diagonal resources, the summed endpoint resource, and both
possible height orders of the physical B/C pair give exactly the five
terms in Y. In the middle-pair term, the higher main is paired with F;
taking the minimum of the two resulting lower bounds retains both
height orders.

The original-pair support lower bound

\[
\sigma=\frac{1+ac+bd+|ad-bc|}{2}\ge1
\]

is valid for both original chirality relations. The four unsigned owned
axes and the exact zero-vertical-component convention give a necessary
lower bound K for vertical clearance. No actual frame is replaced by a
free inset in this step.

On the admitted central/main position bands the gap D is at most one.
Each finite owner numerator is then nonnegative. The expressions
`K(|x-z|)`, with either `+z` or `-z`, are concave in the main position:
they are minima of concave affine-minus-absolute-value functions.
The minimum therefore occurs at an interval endpoint. The zero-owner
value that can occur at D=1 is explicitly included there; its lower
endpoint value does not invalidate the endpoint minimum. No concavity
for D>1 is used.

Horizontal reflection exchanges B,C, so the full root with
`0 <= xF <= 29/60` retains both halves. Boundary `|xF|=29/60` is also
covered: the own-half clearance uses the nonstrict gap bound and the
above-both-mains hypothesis is supplied directly.

## 3. Low side: main-position elimination and vertical order

The initial side/main horizontal gap is less than `93/130 < 4/5`.
Their original radius-one-half disks, the specified upper order, and
`yC > -6/5` yield `-3/5 < yS < 3/5`.

The fixed endpoint rectangle is genuinely contained in the original D:
its horizontal halfwidth is

\[
15/32-1/60=217/480,
\]

and its vertical halfheight is the accepted original endpoint reserve.
Applying the original S disk to this rectangle gives `xS < 49/80`.
The separate upper-central-height theorem then supplies `yF > -7/40`.
If F were below S, their center gaps would have squared sum below one.
Thus `yF > yS` follows before any low-floor hypothesis is used. The
dependency is one-way; there is no circular use of the floor theorem
to prove its own required vertical order.

For an owned folded frame `(a,b)`, `a >= b > 0`, the difference between
its shallow and steep clearances is exactly

\[
\frac{(a-b)[\sigma-(a+b)D]}{ab}.
\]

It is nonnegative for `D < 1/sqrt(2)`, because `sigma >= 1` and
`a+b <= sqrt(2)`. A shallow axis with b=0 is impossible in this range.
Consequently the complete K equals the minimum of the two steep-owner
clearances, with slopes between -1 and zero. This minimum is
nonincreasing and 1-Lipschitz. It follows that

\[
z+K(C,S,|x_S-z|)
\]

is nondecreasing in z. This argument includes the crossing at `z=xS`
and both possible horizontal orders.

For every z between `gC-1/60` and the actual xC, the forward gap is less
than `763/3120 < 1/4` and the reverse gap is less than `1/30`.
Thus the steep-owner reduction holds on the entire interval used to
remove xC. The original C/S frames are retained in the resulting K.
Replacing V by etaC and dropping the other main's nonnegative
contribution weakens both cone bounds in the necessary direction.
This proves the lower S-height resource L without a hidden assumption
on the second main's frame or height.

The assumed bad F floor, the established order `yF > yS`, and
`0 <= xS-xF <= xS` give precisely the upper resource H. Both original
S/F frames are retained. If `L > H`, the original configuration is
already impossible.

## 4. Endpoint SAT and interval evaluator audit

When `L <= H`, every feasible original yS belongs to that containing
interval. Hence `max(|L|,|H|)-c` is a valid upper bound W for its
adjusted vertical displacement from the contained endpoint rectangle.
The adjusted horizontal displacement is `E=503/480-xS > 0`.

The two rectangle-owned coordinate expressions and the two original
S-owned expressions in the manuscript bound every actual rectangle/S
separator. The folded S coefficients are nonnegative, and each signed
projection is bounded above by the corresponding absolute-coordinate
expression. Subtracting the rectangle supports gives `aS E+bS W`
or `bS E+aS W` even when W is negative. The source keeps that sign;
it neither replaces W by zero nor swaps in an independently chosen
S orientation. Thus a negative maximum T excludes the original pair.

I compared both acceptance evaluators with all displayed formulas.
Shape component monotonicities, signed interval products, support sums,
upward gap bounds, downward clearance values, and the directions of
every height rounding are correct. A box with inconsistent containing
height bounds is already infeasible; evaluating the endpoint rule there
does not create an accepted physical point.

The helpers are only the acceptance module
`root_wide_pair/verify_wide_central_pair.py` and its previously reviewed
integer interval kernel `verify_joint_five_dyadic.py`. No numerical
producer or discovery verdict is imported.

## 5. Fresh exact execution and full coverage

The adjacent driver `replay_wide_low_side_inputs.py` executes the frozen
acceptance formulas with 80 fractional bits, raising the accepted
integer kernel's precision only in this fresh process. This is a fresh
exact execution of the acceptance formulas, not a claim of an
independently reimplemented formula program.

| Gate | Complete nodes | Strict leaves | Maximum depth | Leaf counts |
|---|---:|---:|---:|---|
| Upper central height | 5,377 | 2,689 | 23 | 18 V exclusions; 2,671 height bounds |
| Low side central floor | 44,055 | 22,028 | 26 | 0 eta exclusions; 20,325 height conflicts; 1,703 endpoint exclusions |

Both literal rational roots, the entire preorder binary trees, split
axis ranges, leaf rules, counts, and maximum depths were checked. There
is no unresolved frontier. All equality faces and zero slopes are
included. The respective least exact reserves were

\[
\frac{200532146437509771547}{27200830941329156430888960}>0,
\qquad
\frac{26899511682574979363}{27200830941329156430888960}>0.
\]

For each input, changing the root, introducing an illegal split axis,
removing a child, and replacing the whole tree by a false terminal were
all rejected. The full output, source/certificate/helper/kernel hashes,
and timings are in `wide_low_side_inputs_independent_replays.json`.

The reviewed certificate hashes are:

- Height: `007aa80cc2a5f57c18e20d9ee0fd1c9676fbb0fd34c64cff7b28bb74dcdea968`.
- Floor: `a92bed3c0804b76bcd92679da11826ce2ab1ad0fe57ee1dabb5b7088f222a2d3`.

The reviewed acceptance evaluator hashes are:

- Height: `0090523bf3027b674b51089e137f15ba6ee46ee40d9bd59e3d81010ec05b974c`.
- Floor: `cea3a6f8abf3f70f599d7159333e2fbb41c4b2f9352bcf90c9a511fae90b997b`.

I also freshly checked the hand arithmetic with exact Fractions. In
particular the narrow-side squared reserve is `38839/5760000`, the
vertical-order disk reserve is `31/1280`, the narrow main gap is
`763/3120 < 1/4`, the weak endpoint-height reserve is `1/12000`, and
the main-height radical comparison has integer reserve 447. The
displayed rectangle width, left edge, and initial `93/130` gap identity
also agree exactly.

**Accepted scope:** both stated original-square implications are
mathematically supported by the physical reductions and complete exact
covers. Their use in a full fixed-mask proof still requires that proof's
caller to supply the stated original units, orders, and location bounds.
