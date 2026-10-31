# No entirely loaded component in the jointly selected physical stress

**Status:** reviewed hand theorem; root and independent full mathematical
reviews passed on 2026-10-30, including the joint certificate selection,
all local estimates, global boundary assembly, and imported premises.
This closes C04, the entirely loaded positive-component case.

**Theorem.** Suppose an unrestricted ten-unit-square packing has minimizing
radius `R<3/sqrt(2)`. Its normalized physical force-and-torque stress can
be selected so that it has no entirely loaded positive component.

The assertion concerns one jointly selected certificate. It does not say
that every possible physical stress has this property, and it does not
exclude components containing unloaded bodies. In particular, it is not
a complete unrestricted n=10 proof.

## 1. Make all normal choices before selecting the positive graph

The declared existing-theorem route in Section 1 of
[EXPANDED_TREE_INVENTORY.md](EXPANDED_TREE_INVENTORY.md) gives

```text
79/40<=R<3/sqrt(2),       6241/1600<=R^2<9/2.
```

Specifically, the pinned existing n=8 theorem gives `R^2>=qStar`, with
`qStar>7831/2000` and
`7831/2000-(79/40)^2=119/8000>0`, after deleting two squares. This is an
explicit import of that theorem and its exact interval bracket, rather
than a new independent hand proof of the lower window. The physical
stress source and force/torque conventions are the pinned research
dependencies recorded in
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md).

At the minimizing geometric packing, impose the following choices jointly:

* the coherent planar normal choice and finite generic exclusions in
  [PLANAR_SELECTED_PHYSICAL_STRESS.md](PLANAR_SELECTED_PHYSICAL_STRESS.md),
  including strictness, avoidance of incident diagonals and radial lines,
  and the loaded-VV concurrence-polynomial restrictions;
* the circle-adjacent VV open-interval restrictions in
  [SEVEN_RING_ALL_INNER_FACE_CAPACITY.md](SEVEN_RING_ALL_INNER_FACE_CAPACITY.md);
* the enlarged opposite-circle VV midpoint intervals in Section 2 of
  [LOADED_OUTER_CORNER_CLEARANCE.md](LOADED_OUTER_CORNER_CLEARANCE.md).

The last two restrictions involve disjoint geometric pair categories.
Their pairs have both endpoints geometrically circle-loaded and hence
cannot be the coupled opposite pairs at a four-square junction in this
radius window. Their normal parameters remain independent of the coherent
junction parameters. Each prescribed interval is nonempty and open;
the remaining finite nonzero-polynomial exclusions can be imposed on
their joint open parameter product. Thus the three choices are compatible
on a single set of normals, not merely on separately chosen stresses.

Construct the physical stress using those normals. Perform the planar
junction replacements and side-force aggregation from the planar
selection theorem, and only then classify the positive graph. Surviving
point-only VV directions remain unchanged. The local restrictions are
therefore derived from the final physical equilibrium equations and the
chosen geometric normals; no old positive graph is transferred through
reselection or replacement.

## 2. An entirely loaded component would give an impossible seven-ring

Suppose the selected graph has an entirely loaded positive component.
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md) makes it
a physical seven-ring enclosing the origin, with all three remaining
squares having centers of norm below one and lying on its bounded side.
The circle loads, support features, and contact points are the physical
ones, including possible radial-side loads and shared-side aggregate
contacts.

The reviewed ownership classification and incident-mixed exclusion leave
unique-circle rows U1,U4,U5,U6,U7,U8,U9,U10, with all radial cases retained.
The outer-corner clearance theorem applies to this jointly selected stress
and gives, for every U4/U5 body, the extra boundary-corner estimate

```text
|B|^2<33/20.
```

The global argument in
[SEVEN_RING_OUTER_CORE_ASSEMBLY.md](SEVEN_RING_OUTER_CORE_ASSEMBLY.md)
therefore applies. It inserts each extra corner into the core chain,
chooses geometric inner endpoints at SS overlaps without moving force
points, and proves that the resulting Jordan boundary encloses all three
inner squares. Its exact winding identity covers that enclosure by the
enlarged core hull and the contact triangles, including degenerate and
radial cases.

The old proper and VV triangles retain their reviewed bounds. Every new
outer proper triangle is controlled by
[OUTER_SIDE_SPIKE_CAP_BOUND.md](OUTER_SIDE_SPIKE_CAP_BOUND.md) and
[OUTER_SIDE_CAPACITY_MARGIN.md](OUTER_SIDE_CAPACITY_MARGIN.md).
Consequently every vertex of each inner square has squared norm strictly
below `83/50`; convexity puts all three entire squares in that disk.
This contradicts the exact minimum squared radius `425/256` from the
repository's pinned hand
[three-square theorem](https://github.com/vltanh/lean4-squares-in-circles/blob/4bea747b3efa13c869b956cb28435efaf21526fa/docs/proof/06-three.md),
since

```text
425/256-83/50=1/6400>0.
```

The selected stress has no entirely loaded positive component, as claimed.
This discharges C04. Components containing unloaded bodies remain separate
obligations. This is a hand research proof with the stated imports; no new
Lean theorem or local Lean build is claimed.
