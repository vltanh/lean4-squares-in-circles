# A two-side loaded bridge fixes its endpoint frames

**Status:** reviewed hand deductions; independent full mathematical reviews
passed on 2026-10-29. These are necessary restrictions on an SS bridge, not a proof
that its ten-square completion is impossible throughout the target window.

Use the selected physical positive stress of a strictly subcritical
ten-square packing. The
[loaded bridge reduction](BRANCHING_LOADED_BRIDGE_EXCLUSIONS.md) leaves
only a two-side path SS when both retained endpoints of a skeleton bridge
are loaded. The two internal squares have whole-graph degree two.

Rotate the common radial bridge line to the horizontal axis. Its loaded
endpoint contacts are `(-r,0)` and `(s,0)`, where

```text
r,s>0,       r+s=2,       R<3/sqrt(2)<17/8.
```

The left endpoint square lies in `x<=-r`, and the right endpoint square
lies in `x>=s`. All the statements below apply to either endpoint by
reflection.

**Theorem.** Both endpoint contacts belong to relative side interiors of
their loaded squares. All four squares in the SS chain have parallel
frames. Put `T=sqrt(R^2-1/4)`. Then

```text
3-T<=r,s<=T-1,       R^2>17/4.
```

The endpoint centers have transverse coordinates of absolute value less
than `3/8`. Neither endpoint can belong to a double-S or double-SS bundle
to any other retained vertex. This last restriction applies even if that
other retained vertex is unloaded.

## 1. A radial endpoint cannot use a vertex contact

Every unit square has horizontal width at least one. Containment of the
two endpoint squares consequently gives

```text
r,s<=R-1,       r,s>=3-R.                              (1)
```

Suppose the right contact `(s,0)` were a vertex of its endpoint square.
Because the square is supported in `x>=s`, its two incident unit edge
vectors can be written, after reflection, as

```text
(c,d), (d,-c),       c,d>=0,       c^2+d^2=1.
```

Its opposite vertex has squared norm

```text
(s+c+d)^2+(d-c)^2
 =s^2+2s(c+d)+2
 >=(s+1)^2+1.
```

This includes a contact at an endpoint of a vertical support side. Disk
containment would imply `s<=sqrt(R^2-1)-1`. But

```text
3-R>sqrt(R^2-1)-1,
```

because both sides of `4-R>sqrt(R^2-1)` are positive and their squared
difference is `17-8R>0`. This contradicts (1). A supported contact is
on the boundary, so its only remaining possibility is a relative side
interior. Its horizontal inward normal fixes a vertical side and an
axis-parallel frame. Reflection proves the same for the left endpoint.
The two S transmitters already have this frame.

## 2. The endpoint positions and the improved radius window

Write the right square as

```text
[s,s+1] x [y-1/2,y+1/2],       |y|<1/2.
```

It is loaded, so one of its outer vertices is on the circle and

```text
R^2=(s+1)^2+(|y|+1/2)^2.                              (2)
```

In particular `s<=T-1`; the same bound holds for r. Since `r+s=2`,
this proves `3-T<=r,s<=T-1`, as well as `T>=2` and `R^2>=17/4`.

At equality, both r and s equal one and (2) forces both transverse
endpoint coordinates to be zero. The internal side transmitters have
centers `(-1/2,t_1)` and `(1/2,t_2)`, with `|t_1|,|t_2|<=1/2`, because
their radial contact points have height zero. The four-square core is
exactly the one in
[STAGGERED_CHAIN_REDUCTION.md](STAGGERED_CHAIN_REDUCTION.md), whose
arbitrary-orientation capacity theorem excludes a completion to ten
squares. Thus a hypothetical SS bridge in the current ten-packing has
`R^2>17/4`.

Equation (2) also gives a useful uniform transverse estimate. Since
`s>=3-T` and `R^2=T^2+1/4`,

```text
(|y|+1/2)^2
 <=T^2+1/4-(4-T)^2
 =8T-63/4
 <3/4.
```

Here `T<sqrt(17)/2<33/16`, and the last exact radical comparison is
`17*64=1088<1089=33^2`. Finally `sqrt(3)/2<7/8`, since `48<49`, so

```text
|y|<3/8.                                             (3)
```

## 3. No endpoint can have a double transmission bundle

Suppose the right endpoint H also belongs to a double-S or double-SS
bundle. Section 3 of the reviewed
[skeleton reduction](BRANCHING_COMPONENT_SKELETON_DRAFT.md) proves that
both endpoint support faces of such a bundle are unit sides. Thus its
force direction is one of H's horizontal or vertical frame directions,
and its other endpoint J has the same axis-parallel frame. Its width W
is respectively one or two. The two endpoint center projections in
that force direction differ by `W+1>=2`.

If the direction from H to J is vertical, (3) gives

```text
|center(J)_y|>=2-|center(H)_y|>13/8>25/16.
```

This contradicts the universal strict center bound `|center(J)|<25/16`.
If the direction is horizontally outward, its center first coordinate
is at least `s+1/2+2>5/2`, again impossible.

The only remaining direction is horizontally inward. The first S body
in each of the two new paths and the first S body in the original bridge
all have the same open horizontal interval `(s-1,s)`. Their three unit
vertical intervals must have pairwise disjoint interiors. Each overlaps
H's unit vertical support interval in positive length:

* the original bridge contact has height zero in the relative interior
  of H's side;
* the other two positive overlaps follow from the selected-certificate
  strict-normal convention, exactly as in the bundle reduction. A
  singleton side/side overlap would be a point-only vertex/vertex contact
  carrying a side normal, which that convention excludes.

Three unit intervals with pairwise disjoint interiors cannot each overlap
one fixed unit interval in positive length. Indeed, in their increasing
order the third left endpoint is at least two beyond the first left
endpoint; points in the first and third positive overlaps would then be
more than one apart. This contradiction excludes the inward case too.

All directions have been exhausted. Neither loaded bridge endpoint may
have an incident double-S or double-SS bundle.

## 4. The inner side cannot support another loaded square

Use the right endpoint H with its reviewed coordinates above, and put
`h=|y|+1/2`. The estimates in Section 2 give

```text
h<7/8,       s>=3-T>15/16,
R^2=(s+1)^2+h^2.
```

Let a physical unit-square neighbor J be supported in `x<=s` and contain
a point `P=(s,z)` of H's inner side. Its application point may be a side
endpoint, but the supporting normal here must be horizontal; membership
of P alone does not impose the half-plane hypothesis. One has `|z|<=h`.

Reflect vertically and rotate by a quarter turn. J is then supported
above the line of a point `(|z|,-s)`. The one-sided supported-square
bound in Section 1 of
[LOADED_DOUBLE_SIDE_RESTRICTION.md](LOADED_DOUBLE_SIDE_RESTRICTION.md)
applies with `x=|z|>=0` and `H=s>1/2`. Every vertex v of J consequently
satisfies

```text
|v|^2<=s^2+(|z|+1)^2
     <=s^2+(h+1)^2
      =(s+1)^2+h^2-2(s-h)
      =R^2-2(s-h)
      <R^2-1/8<R^2.
```

Thus such a neighbor is geometrically circle-clear. Any direct contact
from this endpoint to another loaded body cannot use its inner-side
normal, including that side normal applied at a corner. Strict vertex
normals with tilted supporting lines remain outside this local claim.
The original adjacent S transmitter is unloaded and is consistent with
the restriction.

## 5. Exact finite-filter form and remaining scope

In the b=0 catalog, remove a digit-5 edge to test whether it is a graph
bridge. If it is, neither endpoint may be incident to digit 3 or digit 6.
The rejection has a finite witness: the bridge edge, one proper cut of
its deletion, and the incident forbidden bundle. This filter never
changes the raw stable catalog or asserts feasibility for a retained code.

The four endpoint frames and coordinate bounds do not extend the old
capacity-nine theorem automatically from `R^2=17/4` to larger radii.
In particular a loaded endpoint may have only one circle vertex when
`R^2>17/4`, leaving a geometric passage around its other outer corner.
No full barrier or completion-capacity claim is made here for that range.
