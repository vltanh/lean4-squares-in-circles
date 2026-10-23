# Independent mathematical review of sparse minimizer stresses

The `n8_lessons` research agent independently reviewed
`SPARSE_MINIMIZER_STRESS.md` and the auxiliary `CENTER_SHELL_BOUND.md`.
This is a source-level mathematical review, not compiled Lean verification.

**Conclusion: pass for the stated extraction and auxiliary exclusions.**
Neither source claims the sharp unrestricted eleven-square theorem.

The stress extraction correctly starts from an actual global minimizer and
chooses strict own-axis separation for pairs of disjoint closed squares. Thus
a positively weighted pair is a genuine physical contact. The common strict
first-order variation supplies the constraint qualification used in the
finite cone argument. The fixed-frame stationarity equations, normalization,
completed-square identity, and 23-term thinning count have the stated signs.

The separate variable-angle construction uses all four smooth nonowner
support-vertex inequalities. It handles parallel ties without differentiating
an absolute-value cusp. Simultaneous global rotation annihilates all gradients,
so their span has dimension at most 33; this justifies 33 positive atoms, not
23 atoms with angular stationarity. The warning that an active support vertex
need not be an actual point of physical overlap is necessary and present.

I checked the multiplier bound by dotting center stationarity with the
centers, and the compact-chart discussion keeps physical-contact witnesses
separate from zero-weight support indices. Normalizing a connected positive
component preserves every force and angular equation. The weighted loaded
corners sum to zero, proving the asserted unique minimum-enclosing-disk
property for that component's actual position. Repeated thinning and retaining
a component terminates because each disconnection lowers the retained vertex
count. Omitted squares remain physical completions throughout.

The auxiliary center-shell proof passes independently. The center bound
`sqrt(q-1/4)-1/2` follows from a farthest corner. Three points in the closed
radius-`11/20` disk contradict their squared-distance sum. On the radial
rectangle `[11/20,27/20]^2`, separate convexity reduces the angular distance
bound to its corners. The cubic comparison
`8(25/33)^3-6(25/33)+1=-2413/35937` has the correct sign and uses the
strictly increasing branch above `1/2`. The mixed and outer corner bounds
are strictly below one. Thus eleven centers force `q>1469/400`.

The two- and three-body stress exclusions are valid. A physical triangle
fits in the stated centroid disk of squared radius `49/18`. For a three-body
path, the comparison positions retain the two positively weighted frozen-frame
separators while fitting all three squares in squared radius
`9/4+sqrt(2)`. The endpoints may overlap: the dual comparison is an explicitly
identified relaxation using only weighted constraints, so no physical-packing
claim is required for those comparison positions. The exact inequality
`9/4+sqrt(2)<1469/400` closes this case. The final conclusion `4<=k<=11`
therefore holds for both extracted certificate types.

The unloaded-leaf obstruction and equal-force straight transmission rule
follow directly from center stationarity. These results restrict possible
positive stress supports; they do not classify or solve all such supports,
nor prove that all global minimizers have the candidate's contacts.

Reviewed SHA-256 snapshots are recorded below.

- `CENTER_SHELL_BOUND.md`:
  `da097a4d662d4f4335ab97025be597820f15c51cb1416e4c3b3fab164b0e2514`.
- `SPARSE_MINIMIZER_STRESS.md`:
  `f7d1f2fafd9e8829843c3aacb88191d9150b12275b09da3e93cd6fe152a2004b`.
