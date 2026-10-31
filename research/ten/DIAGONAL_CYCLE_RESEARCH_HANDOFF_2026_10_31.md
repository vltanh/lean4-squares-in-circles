# Diagonal-cycle research handoff, 2026-10-31

**Status:** handoff index and explicit unfinished research. LSLSLD is
still open; no whole-signature count changes follow from this work.

## Reviewed exact progress

* `ONE_DIAGONAL_TWO_SIDE_SAME_SIGN_NORMALIZATION.md`: both S directions
  in LSLSLD point to the same vertical side of the D strip, including
  arbitrary radial endpoint circle-load splits. At most one D endpoint
  is radial; that branch has R²<17/4. Root and independent full reviews
  passed.
* `ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md`: when both D endpoints
  have unique geometric circle vertices, the two contacts on C lie on
  one edge. Three disjoint C support rows retain all horizontal-side
  endpoint contacts and both full S-transmitter slide intervals. Root
  and independent full reviews passed.
* `ONE_DIAGONAL_VERTICAL_SOURCE_SIDE_EXCLUSION.md` and
  `check_diagonal_vertical_source_side.py`: the vertical-A/E_A source
  row and its reflection are excluded by a complete 16-interval rational
  table. Root and independent analytic reviews passed; the exact checker
  reproduces all 32 printed bounds, each positive.

* `ONE_DIAGONAL_VERTICAL_SOURCE_TORQUE_EXCLUSIONS.md`: further torque
  exclusions remove the other source rows with a vertical endpoint,
  except V_V with radial C. Root and independent full reviews of the
  assembled note passed. That final remaining row is now excluded by
  [RADIAL_VERTICAL_SOURCE_EXCLUSION.md](RADIAL_VERTICAL_SOURCE_EXCLUSION.md).

`RADIAL_VERTICAL_SOURCE_RESEARCH_HANDOFF.md` and
`explore_radial_vertical_source.py` preserve the unfinished work on that
remaining row. They preserve the earlier incomplete exploration. Its 30 unresolved cells
are now resolved by [RADIAL_VERTICAL_SOURCE_EXCLUSION.md](RADIAL_VERTICAL_SOURCE_EXCLUSION.md)
and [radial_vertical_source_exclusion.json](radial_vertical_source_exclusion.json).
All both-unique D endpoint survivors therefore have strict/strict S supports.

## Numerical work, without exhaustive or existence claims

`ONE_DIAGONAL_TWO_SIDE_NORMAL_FORM_EXPLORATION.md`, its Python script,
and its JSON output survey all 27 numerical equation rows in the
both-unique-D-endpoint family. The run found the known asymmetric
candidate and its reflection, plus a symmetric V_V/radial-C candidate
near R=1.99993764. This is not root isolation, an exhaustive root count,
or a certificate that the full six-body configurations can be realized.
The survey does not cover a radial D endpoint.

A prospective completion route is to use only A,B,C,D as four fixed
cores. If their common uncovered center domain can be covered by at most
five sets of diameter below one, the whole packing has at most nine
squares. This would automatically retain every S-transmitter slide.
No uniform finite capacity certificate has yet been constructed.

## Existing unreviewed local observation for the radial D-endpoint branch

**NOT PROMOTED.** The following is an unfinished normalization observation,
not a result used in a count or completion theorem.

The two S contacts on C should also be distinct when one D endpoint is
radial. If they coincided at P, the two outward path normals on C would
belong to one square normal cone, so their angle would be at most pi/2.
The two far contacts on A and B would then be at distance at most
sqrt(2). The D separating strip forces every A--B point distance to be
at least sqrt(2). Equality would therefore be necessary: the two S
directions would be perpendicular, and the far-contact segment would be
normal to the D strip. Each S direction would make an angle pi/4 with
that strip normal. At least one D endpoint is unique-circle, by the
reviewed same-sign normalization. Its strict torque inequality requires
its S vertical component to exceed the horizontal component, contradicting
the putative pi/4 direction. This observation still needs a full
independent audit of the equality and contact-support steps.

The main missing work remains a completion bound for every surviving
support/multiplicity case, including the radial D-endpoint branch.
