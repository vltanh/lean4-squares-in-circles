# Independent review of the four-center second moment

The `n8_lessons` agent independently reviewed
`boundary/FOUR_CENTER_SECOND_MOMENT.md`, SHA-256
`6d96a6a20c468c2504bae35217bb15f46c03a9c191a54dc6fb5d132a2d2ca467`.

**Conclusion: pass.** After translation to zero centroid, the stated
three-vector change of variables gives both the six signed pair differences
and the sum-of-squared-norm identity. The six unit-distance inequalities
bound each absolute Gram entry as claimed. The row bound
`(a+S-2)/2` is strictly below its positive diagonal when `S<2`, so the
explicit quadratic-form estimate makes the Gram matrix positive definite,
contradicting its planar rank. At `S=2` the same estimate applies unless
one diagonal vanishes; the remaining two norms must then equal one. This
gives precisely the unit-side rhombus with diagonals at least one.

For actual nonoverlapping unit squares, a center-distance-one pair forces
equality in both Cauchy--Schwarz for the selected separator and the minimum
support widths. Thus the squares share a frame, with displacement along
one of its axes. The four unit rhombus sides propagate that frame, and the
two distinct adjacent side directions must be orthogonal. This establishes
the two-by-two square equality case.

The note correctly retains the centroid term and distinguishes this necessary
moment inequality from a proof of the unrestricted four-core case. The stated
numerical linear-program experiment is a discovery limitation, not a proof
input. No Lean code or kernel verification is asserted.
