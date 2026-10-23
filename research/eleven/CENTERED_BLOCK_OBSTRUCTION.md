# A four-square block near the disk center cannot have seven completions

**Marker lemma.** Let `B=[-1,1]^2`. Any closed unit square with open interior
disjoint from the open interior of `B`, and contained in the disk centered at
zero of squared radius `V=4999/1000`, contains at least one of

\[
(3/2,0),\quad(0,3/2),\quad(-3/2,0),\quad(0,-3/2)
\]

in its **open** interior.

Consequently at most four pairwise interior-disjoint unit squares can complete
this centered `2` by `2` block at that radius. An eleven-square packing in
`q<=U=49013/10000` cannot contain an exact `2` by `2` block of four unit
squares whose block center is within `1/50` of the containing disk's center.
The block may have any common orientation.

This is a conditional exclusion within the unrestricted four-core case. It
does not say that arbitrary four core squares form a block.

## 1. The eight exhaustive marker-missing branches

The separating-axis theorem for the two convex squares `B` and `S` supplies
a signed axis of one of them on which their support intervals do not overlap
in their interiors. The dihedral symmetries of `B` preserve the four-marker
set. Quarter turns of `S`'s own frame preserve the square itself. These
symmetries reduce the chosen separator to one of two cases:

- **Own-axis separator:** the chosen outward normal is the unit square's
  first axis `u=(c,s)`, with `c>=s>=0`.
- **Block-axis separator:** the chosen outward normal is `ex`, and the unit
  square's frame can be chosen, after a possible reflection, with `c>=s>=0`.

In both cases put `v=(-s,c)` and express the square center as `a u+b v`.
Let `t=tan(theta/2)`, where `theta` is the angle of `u`. Then

\[
0\le t\le\sqrt2-1<5/12,\quad
c=\frac{1-t^2}{1+t^2},\quad s=\frac{2t}{1+t^2},\quad
t^2+2t\le1.
\]

Its largest corner norm squared is exactly

\[
a^2+b^2+|a|+|b|+1/2\le V.                   \tag{1}
\]

The farthest-corner center bound gives `sqrt(a^2+b^2)<7/4`, since
`(7/4)^2+7/4+1/2=85/16>V`. Thus `a,b` lie in the initial rational
interval `[-7/4,7/4]`.

The selected separator is respectively

\[
a-c-s-1/2\ge0,
\quad\hbox{or}\quad
ca-sb-1-(c+s)/2\ge0.                        \tag{2}
\]

The corresponding marker is `M=(3/2,0)`. Its displacement from the center
in the square's own axes has coordinate magnitudes
`|a-3c/2|` and `|b+3s/2|`. If the marker is not in the open square, one
of the following four weak alternatives holds:

\[
\sigma(a-3c/2)\ge1/2
\quad\hbox{or}\quad
\sigma(b+3s/2)\ge1/2,\qquad \sigma\in\{-1,1\}. \tag{3}
\]

There are exactly two separator choices times four marker-missing choices.
The exact finite certificate excludes every one. Individual squares may use
different symmetries and different marker labels; the marker set itself is
fixed in the block's frame.

## 2. Exact box certificate

`block_marker_certificate.py` generates `BLOCK_MARKER_COVER.json` using
only rational arithmetic. Every branch starts with the same closed box

\[
(a,b,t)\in[-7/4,7/4]^2\times[0,5/12].
\]

At a leaf it proves one of four contradictions to `(1)`--`(3)` and the
angle chart:

1. the lower `t` endpoint already gives `t^2+2t>1`;
2. the minimum of `a^2+|a|+b^2+|b|+1/2` on the box exceeds `V`;
3. the interval upper bound of the selected separator expression is negative;
4. the interval upper bound of the selected signed marker displacement is
   strictly less than `1/2`.

The frame intervals are obtained from monotonicity on `[0,5/12]`: `c(t)`
decreases and `s(t)` increases. Products use all four rational endpoint
products. Every internal node bisects one coordinate at its exact rational
midpoint; its two closed children cover the parent, including the midpoint.
Consequently the finite leaf cover proves the marker lemma without omitted
boundary cases.

The certificate has the following per-branch node and leaf counts:

| Separator | Marker axis | Sign | Nodes | Leaves |
| --- | ---: | ---: | ---: | ---: |
| Own | 0 | -1 | 65 | 33 |
| Own | 0 | +1 | 45 | 23 |
| Own | 1 | -1 | 165 | 83 |
| Own | 1 | +1 | 887 | 444 |
| Block | 0 | -1 | 133 | 67 |
| Block | 0 | +1 | 65 | 33 |
| Block | 1 | -1 | 425 | 213 |
| Block | 1 | +1 | 1097 | 549 |

The total is 2882 nodes and 1445 leaves, with maximum depth 43.
This is an exact rational certificate, not Lean kernel verification.

## 3. Four markers exclude seven completions

Four mutually touching, consistently aligned unit squares making an exact
`2` by `2` block have union `B`. If another square's open interior met the
open interior of `B`, that open intersection could not be contained in the
two internal grid lines, so it would meet the open interior of one of the
four constituent squares. Therefore every completion square is disjoint in
open interior from `B`, as required by the marker lemma.

Each completion square contains a marker in its open interior. Two distinct
completion squares cannot contain the same marker. There are only four
markers, so there are at most four completion squares. In particular seven
completions are impossible.

Now let an exact block in an eleven-square packing at squared radius at most
`U` have center `g` with `|g|<=1/50`. Translate the block center to zero and
rotate its axes to the coordinates above. Every square then lies in a disk
about zero of radius at most `sqrt(U)+1/50`. Since `sqrt(U)<9/4`,

\[
(\sqrt U+1/50)^2
<U+9/100+1/2500
=49917/10000<4999/1000.
\]

The marker lemma applies and excludes the seven remaining squares.

## 4. What this closes

The result excludes the exact centered block, a block-center displacement
up to `1/50`, and their rotations, under the eleven-square upper window.
It does not by itself exclude arbitrary deformations of the four squares.
Compactness also implies some open neighborhood of this compact family of
blocks is excluded among physical eleven-square packings, but this note
does not supply a numerical size for that additional neighborhood.

The unrestricted four-core case still includes displaced blocks farther
from the disk center, nonblock shapes, and independently rotated frames.
Those cases and the three-core/eight-ring case remain to be sharply solved.
