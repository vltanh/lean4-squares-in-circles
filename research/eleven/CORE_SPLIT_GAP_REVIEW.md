# Independent review of the core split-gap obstruction

The `n8_lessons` agent independently audited
`boundary/CORE_SPLIT_GAP_EXCLUSION.md` and ran its coarse occupancy enumerator.
This is mathematical source review and exact integer enumeration, not Lean
kernel verification.

**Conclusion: pass.** The own-frame circle topology has at most two
components. A split forces `3/4<a<17/20`, `b<1/2`, and gap half-angle below
`2/5`; both gap endpoints belong to the closed core square even in a tangent
case. I checked the proof that a ring arc has no internal point on its
square boundary. The only way such a point could be internal to the angular
arc is a side tangency; every near-side and far-side possibility is excluded
by the center bounds and the other coordinate interval. Thus a closed core
point cannot be crossed by a ring's open angular interval. The density of
square interiors justifies using a core boundary point as an obstruction.

If a ring arc entered the internal gap, its whole arc would fit there and
force `eta>7/20`, hence `b<1/20`. I independently checked the inscribed-disk
endpoint estimates `2459/12800` and `3469/14400` using the full ring-center
interval `[41/40,5/3]`; no stronger empty-shell theorem is needed. They put
the ring's center angle within `3/20` of the core axis. The resulting squared
center-distance bound is `3349/3600<1`, a contradiction. Every strict
inequality and threshold endpoint is retained.

Filling each core's internal gap therefore creates a proper closed angular
hull avoided by ring open arcs. The union of at most `k` such hulls has at
most `k` complementary gaps, with the stated separate convention if all
hulls are empty. Hull overlap is explicitly permitted; their widths are not
added. The enumerator's weak compositions, cyclic/reflection quotient, and
stars-and-bars counts give the reported 16 and 33 coarse rows. These are
necessary occupancy alternatives, not solved sharp terminal cases.

The source snapshots are recorded below.

- `boundary/CORE_SPLIT_GAP_EXCLUSION.md`: SHA-256
  `1ba35abdc6dbd88c5582bb7f0d17d4115dfb95013485a45580637041a665edf0`.
- `boundary/enumerate_core_gap_counts.py`: SHA-256
  `8e8881f90765dcef99214a48d566abc7c1b22e693de1cb00ba3b43faad7e9f0f`.
