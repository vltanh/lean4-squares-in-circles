# Review of the full-window shallow-D kernel and common-neighbor consequence

Reviewer: six_body. Date: October 28, 2026.

**PASS unchanged on the entire original radius window.** I read both
complete new sources and reconstructed every new radius comparison,
physical feature alternative and original-force join. The frozen sources
are:

* `D_LEAF_SHALLOW_SIDE_BOUNDARY_FULL_WINDOW_EXCLUSION.md`, SHA256
  `ca7c3f4b32e45fc0c118bd766f438fce3019b0b44220604e33bc842a504ac670`.
* `D_LEAF_COMMON_TRIANGLE_NEIGHBOR_FULL_WINDOW_QUARTER_DISK.md`, SHA256
  `c39605b955d98f7fbe8499cf0a06dc4cc780a7dada4ee83c05ffc627f6d866bc`.

Authorship and independence are explicit: diamond authored the new
full-window shallow-D kernel and the new full-window supplement. This
reviewer authored the earlier radius-two-dependent common-neighbor
argument, which already has diamond's separate complete independent
review at its frozen SHA256 `2330462d457e8f6eaedae3f8d6c8d535379742a213e033c438827f86b4d31288`.
Thus this is an independent reconstruction of the new shallow-D proof
and of its new full-window transfer, together with a literal check of
the already separately reviewed common-neighbor argument. It is not
described as an independent discovery of that predecessor's mathematics.

## 1. The physical lower-radius margins are independent of any packing theorem

The new kernel assumes only the actual displayed H/L chart, an arbitrary
physical-boundary neighbor T, and `79/40<=R<=sqrt(1105)/16`. The
rational radical comparisons give

    11/20 < r < 2/3,
    1/3 < s < 9/20 < r,
    r^2-s^2 = 2r-1 > 1/10 > 1/16.

I recomputed the positive-square and rational reserves: `49/1600`,
`9/4096`, `2/9801` and `17/6336`. No radius-two theorem, n=8
theorem, force equation or circle multiplier enters these bounds.

Every actual point of T has norm at least r, regardless of whether its
physical circle corner carries positive weight. This excludes the
northwest root vertex. At any remaining upward support point `(q,a)`,
the stated lower bound `q>sqrt(6)/5`, the relation `r+q>1` and
the upper norm `|P|<3/4` all follow with the correct strictness.
The exact squared comparisons are `6/25` and `73/144<9/16`.

## 2. Every upward vertex and North side is covered

In the upward-vertex chart, each adjacent actual corner has norm less
than `7/4<R`; the possible farthest circle corner is exactly the
one named Z. The real side-to-leaf crossing excludes every
`Delta>=1/2`: both its crossing parameter and crossing height are
strictly below `5/8`, and the height lies strictly inside the leaf's
inner upper edge. After the crossing the actual side enters the open
leaf. Interior disjointness rules this out even though the offending
segment may be part of T's boundary.

The squared norm of Z is strictly increasing on the full interval
`[-1,1/2]`. This includes negative Delta without assuming its sign.
The upper norm estimate is strictly below `553/144`, whose reserve
against `(79/40)^2` is exactly `869/14400`. Thus the whole upward
vertex family is impossible on the complete original radius interval.

For a North minimum side, the physical leaf barrier forces
`x+1<=r+a`, including all actual contact means and either endpoint
of their overlap. The resulting corner bound `41/16` has exact
reserve `2141/1600` against the lower radius square. The vertex
and side cases exhaust every actual North support feature.

## 3. The new neighbor-owned northeast estimate is sound at every endpoint

For a northeast normal `n=(c,d)`, the original root contact is the
northeast vertex `(r,a)`. The retained neighbor side chart has its
full parameter `0<=rho<=1`. The actual negative tangent segment
gives `rho<=a/(c+d)<1/4`; no mean is reselected.

The new decisive estimate is `d>1/4`. If `d<=1/4`, then
`c>3/4`, `d/c<1/3` and `c-d>1/2`. The original length-one
segment in direction n meets the physical inner upper leaf edge at

    t=a/(c-d)<1/2,
    y=ac/(c-d)<3a/2<=3/8<1/sqrt(2).

The contact lies in the relative interior of that leaf edge, and a
subsequent nonempty part enters the open leaf. The weak endpoint
`d=1/4` is therefore excluded as well. This is a physical argument,
independent of any body equation.

The two near-face corners have strictly smaller squared norm than
their far-face counterparts because `P.n>0`. The negative-tangent
far corner has norm less than `15/8<79/40`. The positive-tangent
far corner lies between `P+n` and `P+n+k`. I independently expanded
the latter norm difference and checked every inequality direction:

    |P+n+k|^2-R^2
      = a^2+2(r+a)c+2(a-r)d-2sqrt(2)r
      < a^2+(5/2)a+(3/2-2sqrt(2))r
      < 11/16-(13/10)(11/20) = -11/400.

The strict sign uses `a-r<0`, so increasing d above one quarter
improves the bound. Convexity supplies the actual intermediate corner.
Both side endpoints and all interior means remain covered.

For the remaining neighbor-vertex case, the actual right-angle tangent
sector must lie outside H's open southwest quadrant. Its start angle
can be lifted into `[-pi/2,pi/2]`; the strict northeast normal excludes
the two endpoints. A nonpositive start angle gives an actual southeast
edge crossing the leaf, so the start angle is positive. This is
precisely the upward-vertex case already excluded. The argument covers
every original free-normal interval and axis-ray limit; it never invokes
a new generic normal selection.

These cases exhaust `n_y>0`. The full-window kernel therefore proves
the stated force-free conclusion `n_y<=0`, including both radius
endpoints and the shallow endpoint `a=1/4`.

## 4. The full-window common-neighbor transfer preserves the entire m+2 star

I checked the whole second source against its previously independently
reviewed predecessor. The old radius-two entry has been replaced by
the new full-window physical kernel and the explicit margins in
Section 1 above. No other step uses `R>2`.

The hypothetical actual K point in the closed quarter disk makes H
shallow; otherwise that closed disk is inside `int(H)` and the actual
units overlap. The unchanged HK support forces a positive vertical
normal component. The full physical triangle cover, applied separately
to every page, excludes North and Northeast through the complete root
force equation and leaves HK Northwest, with each page West or
Southwest. Every actual West mean has height below `-1/4` by the
full-window boundary-point radius and the strict root margin.

Both complete root equations are printed. The actual West moments are
retained with their negative signs; after the real y-force cancellation
they strengthen the bound on the weighted Southwest sum. The weights
`beta_i v_i` are strictly positive, so the weighted-average conclusion
chooses an existing original page. No new force, reduced root equation
or degree-three equation is imposed when there are multiple pages.

The hypothetical support gives `c<3/4` and `at<1/4-c/3`.
The complete polynomial estimate has positive denominator and deficit

    F(c)=9-12c-5c^2+9c^3,
    F'(c)<=-69/16<0 on [0,3/4],
    F(3/4)=63/64>0.

Thus `c+u_j<1`. The actual minimum-support span bounds, with every
side mean allowed, give a strict vertical gap between K and that
actual page, contradicting the required physical contact. Those span
bounds use no owner or concurrence assumption. This reconstructs the
entire arbitrary-degree theorem, not only its one-page special case.

## 5. Exact caller, dependency and bookkeeping boundary

The two new sources' operative pins match the current original radial
leaf, physical owned-axis triangle and physical opposite-vertex sources
exactly. Only the degree-free physical fact of the latter is used; no
end-triangle force equation is assigned to a higher-degree page or hub.

The literal house roof AC/ABC and fan endpoint/inner-root maps keep
their original genuine D alternative, every boundary page and the
actual root degrees three, three and four. K and each page retain
their full additional stars. Page--K contact need not carry stress.
Arbitrary completing physical squares remain. The conclusion is
quarter-disk avoidance by that one actual common neighbor, not a claim
that every possible completion unit stays outside the disk.

Both new results consequently have zero coarse and zero fine gate
delta. They remove the separate radius-two dependency of this local
route, but close none of the still-open whole house/fan families.
The original accepted radius-two-dependent predecessor remains intact.

No original graph, force, degree, mean, normal, mask, shared ledger,
Lean build, CI job or remote object was modified by this review.
