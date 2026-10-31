# Independent review: the common triangle neighbor of a genuine D root

**Verdict: PASS at the exact stated scope and with the declared radius-two
prerequisite retained.** This is an independent mathematical review of the
complete source, not an inference from a checker, an old review, or a count.
No original fine or coarse closure follows from this local conclusion alone.

## Exact source and inputs read

The source reviewed is
`D_LEAF_COMMON_TRIANGLE_NEIGHBOR_AVOIDS_QUARTER_DISK.md`, SHA256
`2330462d457e8f6eaedae3f8d6c8d535379742a213e033c438827f86b4d31288`.
I read and reconstructed all seven sections. Its actual lower-degree
predecessor was not substituted for its arbitrary-degree argument.

I separately read the physical input statements and the portions used:

| Source | SHA256 of the exact baseline bytes read |
| --- | --- |
| `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md` | `faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676` |
| `D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md` | `79ddc3bc94613ba34b30ea3b1e4176a14d644b08887020cbc38f9ef9d785d8a8` |
| `D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md` | `ab7f91fab2d8223466646640bd7fee0bf3678479e9b25b1cf28a583ebc11ad17` |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207` |
| `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` | `20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf` |
| `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` | `46220c8a3eb3f539c682bf6a6fa932edf003e37484e0f6004d321e7cb14d7957` |

The last input is retained as an accepted earlier same-nine prerequisite;
this review does not re-prove its analytic mass certificate. The new local
argument is on `R>2`. The two geometric triangle inputs are used only for
their degree-free physical facts, not for loaded-tip force equations.

## Complete reconstruction and scope checks

1. The genuine D leaf, under the existing compatible original certificate,
   gives the displayed aligned root with `a,b>0` and its actual radial
   application `(r,0)`. This root contains the origin in its open interior
   and is physically circle-clear, so its full force equation has exactly
   the leaf, common neighbor, and every listed page term. The root's true
   degree remains `m+2` throughout.

2. The arbitrary-support span lemma is valid both at a strict vertex and
   at an owned side with an arbitrary actual mean. For `n=(-c,t)`, an inward
   axis pointing down must point left, and its downward component is at
   most `c`; two orthogonal inward axes cannot both point southwest. A
   side's tangent span gives the same weak bound, including its endpoints.
   Vertical reflection gives the other inequality with coefficient `u`.

3. A hypothetical actual point of `K` in the closed quarter disk forces a
   shallow root side. If both vertical root margins were greater than
   one quarter, all four margins would be, and the entire closed quarter
   disk would lie in the open root. A closed full-dimensional square
   meeting another square's open interior then gives open overlap.

4. The original support inequality excludes every `n_y<=0` using the
   actual root margins. The complete force-free shallow-D input forces
   every page normal weakly down. The subsequent triangle cover is
   exhaustive: North at `HK` leaves only horizontal pages and contradicts
   the full vertical force; Northeast leaves only East/Southeast pages
   and contradicts the full horizontal force including the real East
   leaf. Northwest leaves precisely West or strict Southwest pages.
   These exclusions use owned-axis dot products and opposite root
   vertices, without asserting any ownership at `K` or a page.

5. A West page keeps its original variable height. Physical boundary
   clearance gives `s^2+y_i^2>=r^2`; the exact margin
   `r^2-s^2>1/16` and `a<=1/4` force `y_i<-1/4`. Its origin moment is
   therefore strictly negative. Southwest pages have the unchanged
   bottom-left application, as stated.

6. The full root y-force and torque identities are correct, including
   all West-page moments. Their elimination gives
   `b sum_S beta_i u_i <= gamma a c` and
   `sum_S beta_i v_i=gamma t>0`. The positive weighted average supplies
   an actual Southwest page with `u_j/v_j<=a c/(b t)`. This selection is
   of an existing index, not of a new normal, contact or certificate.

7. The hypothetical point gives `s c+a t<=1/4` and therefore
   `c<3/4` and `a t<1/4-c/3`. Combining this with the actual selected
   page yields the displayed strict bound on `c+u_j`. I independently
   expanded the positive-denominator deficit as
   `F(c)=9-12c-5c^2+9c^3`. On `[0,3/4]`,
   `F'(c)<=-69/16` and `F(3/4)=63/64`, so the claimed strict deficit
   is valid on the entire continuous interval.

8. The two support-span estimates then place all of `K` above `a-c`
   and all of the actual selected page below `a-1+u_j`. Their positive
   vertical gap contradicts that page's required physical contact with
   `K`. This covers zero page stress on the page--K contact, a tangent
   quarter-disk point, the shallow endpoint `a=1/4`, every arbitrary
   actual side mean and the original upper radius endpoint.

The three literal caller maps preserve their actual degrees, including
the two-page degree-four fan root. They are valid necessary conditions.
They do not alone eliminate any arbitrary completion square or complete
either the house or fan gate.

## Review boundaries

All nine physical units, true positive forces, original support normals,
application means, circle masks and individual zero weights remain.
The proof uses no equation at `K` or at a page and no proper-concurrence
claim. No fine/coarse ledger, source bytes, remote repository, Lean
file, build or CI was changed by this review.
