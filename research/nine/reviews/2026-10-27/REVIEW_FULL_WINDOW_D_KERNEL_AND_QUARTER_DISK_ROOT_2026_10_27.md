# Root acceptance of the full-window D-root kernel and quarter-disk theorem

Date: October 27, 2026 (America/Chicago).

**Decision: ACCEPT both complete new physical implications.**

| Source | SHA-256 |
| --- | --- |
| D_LEAF_SHALLOW_SIDE_BOUNDARY_FULL_WINDOW_EXCLUSION.md | ca7c3f4b32e45fc0c118bd766f438fce3019b0b44220604e33bc842a504ac670 |
| D_LEAF_COMMON_TRIANGLE_NEIGHBOR_FULL_WINDOW_QUARTER_DISK.md | c39605b955d98f7fbe8499cf0a06dc4cc780a7dada4ee83c05ffc627f6d866bc |

Both sources were read completely. This review is independent of their
author. Their separate six_body review is retained. The earlier
R>2-dependent shallow and quarter-disk sources remain unchanged; these
are separately proved stronger statements, not silent changes to their
old hypotheses or source hashes.

## 1. The physical shallow-side proof covers the full window

The actual D chart and `79/40<=R<=sqrt(1105)/16` give
`11/20<r<2/3`, `1/3<s<9/20` and `r²-s²>1/10` directly.
No independent packing theorem is needed for these inequalities.
A physical boundary contact must have norm at least r; this removes
the upper-left root vertex and yields `q>s`, `r+q>1`,
`q>sqrt(6)/5` and `|P|<3/4` for every remaining upper contact.

I reconstructed the full feature cover. At an upward support vertex,
the actual leaf barrier excludes `Delta>=1/2`: the first intersection
occurs at `t=(a+r-q)/Delta<5/8`, at a height strictly inside the
actual leaf edge. For `Delta<1/2` the farthest-corner norm increases
strictly with Delta and remains below `553/144<(79/40)²`.
The adjacent corners are already below R. Thus no physical circle
corner exists in this entire vertex family.

For a North support side, disjointness from the actual leaf forces
`x+1<=r+a`, with the original mean anywhere on that side. All four
corners then have squared norm below `41/16`, again strictly below
the original lower radius. No side endpoint was discarded.

For a strict Northeast normal owned by a neighbor side, the full
parameter `0<=rho<=1` is retained first. The actual leaf edge gives
`rho<=a/(c+d)`. The inward normal segment gives the stronger necessary
condition `d>1/4`, since every `d<=1/4` crosses the open leaf before
parameter 1/2 and below height 3/8. The complete far-corner calculation
is then

    a² + 2(r+a)c + 2(a-r)d - 2 sqrt(2) r
      < a² + (5/2)a + (3/2-2 sqrt(2))r
      < -11/400.

The signs of both substitutions are correct: `a-r<0`, `c<1`, and
the final coefficient of r is negative. Convexity of squared norm
bounds every original positive-side parameter, and the negative-side
corner has the independent norm bound below 15/8. Near-face corners
are shorter than their corresponding far-face corners. This excludes
the whole owned-side family, including both endpoints.

Finally, for a support vertex at the root's northeast corner, the
original normal lies between its two actual inward axes. A nonpositive
lower-axis angle crosses the real leaf at height strictly between zero
and its upper vertex; a positive lower-axis angle is exactly the
already excluded upward-vertex form. Together with North and Northwest,
these cases exhaust every `n_y>0` without a normal reselection.

The strict rational reserves remain valid at `R=79/40`, the upper
radius endpoint, and `a=1/4`. This proves the force-free shallow-side
theorem on the entire original radius window. Arbitrary neighbor degree
and zero circle multipliers are permitted because the argument uses
physical boundary contact only.

## 2. The arbitrary-degree quarter-disk proof no longer needs R>2

I checked the complete second source against the original quarter-disk
argument already accepted in `REVIEW_NEW_UNIFORM_GEOMETRY_ROOT_2026_10_27.md`.
Its support-span proof, full triangle cover, West mean signs, complete
root force and torque, actual weighted-page selection and cubic
estimate are restated and unchanged mathematically. The stronger
full-window margins supply every inequality formerly obtained from
R>2. In particular `r²-s²>1/10>1/16` gives the strict negative West
moments at the shallow endpoint as well.

All root forces remain in

    gamma t = sum_S beta_i v_i,
    b sum_S beta_i u_i = gamma a c + sum_W beta_i y_i.

The second sum on the right is nonpositive. Selecting an existing
Southwest page by its actual weighted average gives the same
`c+u_j<1`, with cubic endpoint reserve `63/64` and derivative upper
bound `-69/16`. The resulting positive vertical gap contradicts that
page's actual contact with the common neighbor. No force at a true
degree-four root is dropped, and the common neighbor's equation is
never replaced by a smaller-degree equation.

Thus the full-window conclusion has no measure-theorem, eight-square
or radius-two prerequisite. Its direct earlier inputs are the genuine
D chart and the physical owned-axis/opposite-vertex triangle facts;
the latter uses no loaded-tip force equation. The listed original
house-roof and fan caller maps retain all original physical squares,
degrees, masks, contact means and page forces.

## 3. Exact scope of the accepted advance

These lemmas prove a genuine uniform necessary condition for several
remaining D-leaf families. They do not exclude those whole families:
the three arbitrary completion squares have not all been confined away
from the central disk or given a sufficient joint exterior capacity
bound. No original fine or coarse checkbox changes. The full sharp
theorem, all equality cases and the other inherited project audits
remain open. No Lean compilation, CI dispatch or merge was used.
