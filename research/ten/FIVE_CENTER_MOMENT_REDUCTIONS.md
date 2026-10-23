# Reductions for the five-center moment problem

The following are hand proofs. They do not yet prove the remaining moment
inequality. Let five unit squares have pairwise disjoint interiors, with
centers `c_i` satisfying `|c_i| <= 1`. The proposed inequality is

```text
sum_i |c_i|^2 >= 4.
```

Its equality candidate is the plus: one center at zero and four centers at
the unit vectors of a common square frame.

## 1. A nonextreme center forces the plus

Every pair of centers is at distance at least one, since each square
contains the open disk of radius `1/2` about its center.

Suppose one center `c` belongs to the convex hull of the others. Choose
nonnegative weights with `sum lambda_i = 1` and `c = sum lambda_i c_i`.
Then

```text
1 <= sum_i lambda_i |c_i-c|^2
   = sum_i lambda_i |c_i|^2 - |c|^2
   <= 1 - |c|^2.
```

Thus `c=0`. Every other center has norm exactly one, because its distance
from this center is at least one and its norm is at most one.

Two disjoint unit squares whose centers are exactly one apart have parallel
frames, and the center displacement is a unit edge vector. Indeed, a
separating unit normal `n` satisfies

```text
1 = |d| >= n dot d >= h_1(n)+h_2(n) >= 1,
```

where `h_i(n)` is the half-width of the corresponding square in direction
`n`. Equality forces `d=n` and `h_1(n)=h_2(n)=1/2`. A unit square has
half-width `1/2` precisely in its edge directions. Applying this to the
square centered at zero and each of the other four squares gives the four
distinct cardinal centers in its frame.

Consequently every configuration other than the plus has all five centers
as vertices of a strictly convex pentagon. In particular, no three centers
are collinear, and no center is zero.

## 2. Independent outward radial translations preserve disjointness

Fix two of the squares. A separating line gives a unit normal `n`, oriented
from the first square to the second, such that

```text
n dot (c_j-c_i) >= H,
H = h_i(n)+h_j(n) >= 1.
```

Since both centers have norm at most one,

```text
n dot c_i <= n dot c_j - H <= 1-H <= 0,
n dot c_j >= n dot c_i + H >= H-1 >= 0.
```

For any factors `s_i,s_j >= 1`, it follows that

```text
n dot (s_j c_j-s_i c_i)
  >= n dot (c_j-c_i)
  >= H.
```

Thus translating each square so that its center becomes `s_i c_i`, while
keeping its frame fixed, preserves this separating line direction.
The argument holds simultaneously for every pair and every independent
choice of the factors.

Equivalently, the open radial sweeps

```text
S_i^circ + {t c_i : t >= 0}
```

are pairwise disjoint. If a point belonged to two sweeps, it would lie in
the interiors of two independently translated squares, contradicting the
preceding argument.

These two reductions isolate the unresolved case: a strict convex
pentagon of nonzero centers, with disjoint outward radial sweeps. A
weighted angular or neighboring-separation inequality proving the proposed
moment bound in that case is still needed.
