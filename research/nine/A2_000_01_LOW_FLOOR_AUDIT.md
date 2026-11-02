# Independent recovery audit of the complete low-floor argument

Independent agent review on November 2, 2026, against the exact `000/01`
domain at PR head `add3c530e760ddf15cb936a72ee4761a1fcdbe73`. The recovered
source files were read without modification before publication. The fresh
exact replay reports are in `computer_assisted/`. No Lean, Lake or CI was used.

## Conclusion

The low-floor argument covers the entire complementary domain
`y_P-h_P <= 1/10` of the routed original `000/01` predicate. It produces
an original extra square U with `|x_U| < 29/60` and
`y_U-h_U > 1/10`. No extra orientation, separator-owner, coordinate-cover
or placement hypothesis is needed. Combined with the separately reviewed
unrestricted joint five-square cap, this supplies the missing complete
caller, including closed Q. The present audit does not independently
replay the joint-cap tables.

## Physical coverage checked

1. The original physical weighted endpoint caps and actual L--P edge
   imply `x_P > h_P-451/810`, `x_R < h_R+451/810` and
   `W=1+h_R-h_P-(x_R-x_P) >= 0`. Under the low floor, R lies above P;
   the original cone edge then gives `x_R-x_P >= y_R-y_P > 0`.
2. The same shared main span implies
   `h_M1+h_M2 <= 1+(27/184)W`. Therefore both original insets have
   halfwidth at least `max(15/31,1/(2+(27/46)W))`. This bound retains
   the actual original inner frames and does not replace them by
   independently chosen small squares.
3. The main/P inset argument includes the vertical separator and both
   physical P side axes. Its minimal vertical reach correctly keeps
   both chiralities, signs of horizontal offsets and the zero-slope
   boundaries. The first complete table rules out either inner-main
   height at least `-7/20`.
4. The complete right-side hand barrier and left-side hand/table barrier
   put every side extra below its corresponding inner main. The inherited
   one-sided main-height theorem would then put that main above `-7/20`,
   contradicting item 3. Thus both extras are in the open central strip.
5. Main vertical separation is less than `97/120`, whereas every central
   extra has distance greater than `59/60` in height from its assigned
   main. Each extra is above both mains or below both. Reflecting the
   adjacent-proxy barrier puts every lower central extra wholly below
   `-9/20`; the physical two-square central-strip cap permits at most
   one. Consequently some original extra is above both mains.
6. The second complete table retains that extra's original main clearance
   and all four P/extra side-axis possibilities. It rules out height at
   or below P. The bound on its unsigned angle covers `[0,1]`; both
   physical chiralities are retained through a valid common support
   lower bound.
7. The final 356-leaf theorem handles every original central extra U
   above P. If U's whole floor were at most `1/10`, the orientation-aware
   distance bound forces U to the left of P with horizontal gap greater
   than `3/5`. The original shoulder L bounds U's height by a maximum
   over two endpoints of a scalar interval. The derivative sign has only
   a negative-to-positive change, so this endpoint maximum is valid.
   The last table excludes every P/U owner and physical chirality.

The repeatedly used orientation-aware distance inequality
`|c_A-c_B| >= 1+|h_A-h_B|` was checked independently. A genuine side-axis
separator has support sum `(1+cos(gamma)+sin(gamma))/2`, and the reduced
relative angle is at least the difference of the unsigned frame angles.
The elementary increment formula for `(cos(alpha)+sin(alpha))/2` gives
the claimed lower bound. No disk-only or common-frame assumption enters.

## Exact replay

The four independently written Fraction/integer-square-root checkers
were read and compared with their manuscript inequalities. Their interval
operations enclose the stated real operations. The square-root enclosures
are rounded outward and verify both squared endpoints. Clipping a negative
lower enclosure to zero only enlarges the real physical domain. The
orientation functions have the stated monotonicity on the entire closed
parameter interval. Divisions with a zero sine component are handled by
omitting an impossible separator branch while retaining a valid minimum
reach bound.

The checkers reconstruct each prescribed rational root and every midpoint
split. The preorder traversal requires complete binary coverage, rejects
trailing nodes and invalid split indices, and accepts a leaf only with
strict positive rational reserve. The four trees have respectively:

| Component | Leaves | Nodes | Maximum depth | Uniform reserve |
|---|---:|---:|---:|---:|
| Left-side extra | 11,744 | 23,487 | 33 | `1/10000000` |
| Inner-main heights | 59,225 | 118,449 | 38 | `1/10000000000` |
| Central extra at or below P | 62,000 | 123,999 | 27 | `1/10000000000` |
| Upper extra with low floor | 356 | 711 | 16 | `1/100000` |

The exact replay covers **133,325 strict interval leaves**. Fresh negative
controls feed each checker an incomplete tree, invalid split and false
root leaf; all **12 corruptions are rejected**. Source and certificate
hashes and exact smallest reserves are recorded in
`computer_assisted/low_floor_independent_replay_report.json`.

## Scope and acyclicity

The physical two-square caps and elementary actual-four bounds precede
the shoulder and side barriers. Those precede the dynamic-main-inset
table, central-placement argument and upper-extra/P table. The final
whole-floor theorem uses these results and basic physical separation;
none uses the new joint five-square cap. The joint cap can therefore be
applied afterward without a cycle. The equality portion of the whole
assembly is a separate short argument from its strict central transfer
and the inherited two-square equality theorem.

This is independent agent review with exact computational replay, not
human review or kernel verification. Broader masks, the unrestricted
lower bound and the global equality classification do not follow without
their own complete callers.
