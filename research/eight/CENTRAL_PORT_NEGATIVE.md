# Negative result: central-cardinal separation is not pairwise forced

A tempting strengthening of the central-square reduction is false:

> every exterior square disjoint from the central square is separated from it
> on one of the central square's two axes.

This fails even far below the candidate ceiling and while respecting the
radius-`1/12` central core.

## Exact counterexample

Let the central square be axis-parallel with center

```text
C=(1/5,1/12).
```

Let the exterior square have orthonormal frame

```text
e=(4/5,3/5),   f=(-3/5,4/5)
```

and center

```text
P=(1,-269/300).
```

Thus its displacement from the central center is

```text
Delta=P-C=(4/5,-49/50).
```

For this relative orientation the separating-axis threshold is

```text
W=(1+|4/5|+|3/5|)/2=6/5.
```

Both CENTRAL projections are too small to separate:

```text
|Delta_x|=4/5<6/5,
|Delta_y|=49/50<6/5.
```

But the exterior square's `f` projection is

```text
f dot Delta
 =-(3/5)(4/5)+(4/5)(-49/50)
 =-158/125,
```

so

```text
|f dot Delta|=158/125>6/5.
```

Hence the two open squares are disjoint, with separation available only on an
axis of the exterior square.

## Containment and the central core

The central square is trivially far inside the candidate disk.

In the exterior frame the center coordinates are

```text
e dot P = 131/500,
f dot P = -494/375.
```

Therefore its farthest-corner squared distance is exactly

```text
(131/500+1/2)^2+(494/375+1/2)^2
 =349501/90000
 =3.883344... < 98/25.
```

This is also below the candidate squared radius
`q*=3.9155341375...`.

Its nearest closed-square distance from the origin is at least

```text
(494/375-1/2)^2=(613/750)^2 > 1/144,
```

so it avoids the closed radius-`1/12` core contained in the central square.

All claims above are exact rational arithmetic.

## Consequence

The desired `2,2,2,1` structure cannot be obtained by a pairwise theorem
saying every orbital square uses a central cardinal separator.

A viable global statement must be weaker. Possibilities include:

1. assign a *port* from marker position rather than from the actual separating
   axis, then use the central obstacle only after neighboring orbitals are
   coupled;
2. prove that in each marker quadrant at least one of a pair of orbitals uses a
   central separator;
3. use a weighted three-square inequality involving the central square and two
   consecutive orbital squares;
4. retain OWN separators but show a seven-cycle cannot contain too many of them.

This counterexample does not contradict the candidate's actual `2,2,2,1`
central-contact pattern. It only rules out forcing that pattern one
central/exterior pair at a time.
