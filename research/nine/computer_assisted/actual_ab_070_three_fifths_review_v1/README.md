# Root review of the 7/10 theorem with selected-extra slope at most 3/5

This reviews the exact extension committed in
`0d321eb7f76117097900b5d3f11d4ec0a39f21fd`. The older half-slope review
remains a separate historical snapshot. This packet does not install a new
runtime or close an original or mask.

The conditional theorem retains actual AB, EF and FG, the order
`x_B <= x_extra <= x_D`, nonnegative D slope, `y_G >= y_D`, and the strict
D/G horizontal corridor. Its height-variation threshold is `7/10`, provided
the **selected extra original** has absolute slope at most `3/5`.

The independent scalar checker freshly replayed all 28 domains, 163 leaves
and 20,375 rational Bernstein coefficients, with no unresolved frontier.
The enclosing half-angle box is `[0,29/70] × [0,5/18] × [0,29/70]`
in the order D, extra, B. The scalar coefficient `701/1000` leaves margin
`1/1000` above the physical variation threshold. Every closed leaf face and
the all-zero equality point is retained.

Root controls separately compare 252 exact physical-frame expressions with
the independently reconstructed polynomials and reject ten damaged covers.
An exact countercase has D frame `(21/29,20/29)`, extra frame
`(21/29,-20/29)`, and B frame `(1,0)`, with owned separators `[0,2]`.
Bounding B's slope instead of the selected extra's would admit scalar
deficit `-100711/5602800`. The selected-extra guard is therefore essential.

The physical lifting is unchanged: unit-incircle separation and
`2(7/10)^2=49/50<1` retain every owned axis and sign; the endpoint cap and
actual AB then contradict a radius strictly below the target. The closed-Q
equality blocker additionally uses the original actual BC and strictly weak
CD in the `001/00` caller. It is not transferred to the strict `011/00`
application.

A complete angle cover can use `[-1,-3/5]`, `[-3/5,3/5]`, and `[3/5,1]`.
The outer intervals retain the unrestricted `16/25` theorem and every shared
endpoint. This review proves no complementary case empty.

`SOURCE_BINDING.json` pins 41 theorem and physical-prerequisite files.
`FRESH_SCALAR_REPLAY.json` records the observed-zero exact run;
`ROOT_CONTROLS.json` binds its separate executable control source. From a
complete checkout, the controls can be repeated with explicit paths:

```sh
python -B -S check_root_controls.py \
  /absolute/path/to/actual_AB_two_link_row_070_bounded_extra_v1 \
  /absolute/path/to/a-new-root-controls.json
```

The theorem folder's unchanged checker also replays its complete cover:

```sh
python -B -S check_conditional_three_angle.py cover /absolute/path/to/a-new-scalar-replay.json
```

No Lean, Lake or CI was run. The fixed original and mask counts are unchanged.
