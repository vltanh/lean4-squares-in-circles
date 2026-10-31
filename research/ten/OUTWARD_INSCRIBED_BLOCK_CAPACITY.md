# An outward inscribed two-by-two block admits at most five more squares

**Status:** complete hand proof, checked in this session, including the
sharp boundary. No independent agent review or Lean verification is claimed.
This completes and extends the geometric lead in
[DIAGONAL_TRANSLATED_BLOCK_RESEARCH.md](DIAGONAL_TRANSLATED_BLOCK_RESEARCH.md).

Suppose four interior-disjoint unit squares tile

```text
K=[s-1,s+1] x [t-1,t+1],
0<=s,t<=1/2,
R^2=(1+s)^2+(1+t)^2.
```

All squares under consideration lie in the origin-centered disk of radius
R and have pairwise disjoint open interiors. Their orientations are
arbitrary.

**Theorem.** At most five further unit squares can be added, so the total
packing has at most nine squares. The circle is required to pass through
K's upper-right corner; arbitrary larger containing circles are not covered.

The theorem applies in particular to `s=t=a`, `0<a<1/2`, the four-square
junction in the on-ray row of
[LOADED_DEGREE_TWO_VV_SUPPORT_TABLE.md](LOADED_DEGREE_TWO_VV_SUPPORT_TABLE.md).
It also permits unequal s,t and requires no inner-center hypothesis.

## 1. Coordinate separation leaves only two strict caps

Neither the right nor the upper coordinate cap can contain a unit square.
Every unit square has projection width at least one, whereas

```text
R^2-(2+s)^2=(1+t)^2-3-2s<=9/4-3<0,
R^2-(2+t)^2=(1+s)^2-3-2t<=9/4-3<0.
```

Thus `R-(1+s)<1` and `R-(1+t)<1`. Any additional square separated by a
coordinate axis from K must instead be wholly in at least one of

```text
L: x<=s-1,       B: y<=t-1.                           (1)
```

Both caps lie beyond a line at distance at least 1/2 from the origin.

## 2. An oblique separator can be moved into actual corner contact

Let S be an additional square not coordinate-separated from K. The
rectangle separating-axis theorem supplies a noncoordinate side normal
n of S, pointing outward through a corner q of K, with

```text
n dot S>=n dot q=max_{x in K} n dot x.
```

Every coordinate of q has the sign of the corresponding component of n,
because `s,t<=1/2`. In particular `n dot q>0`. Translate S inward along
n until its inner side line passes through q, producing S'. This keeps
S' in the disk: if the shift is d>=0, each point p' of S' satisfies

```text
n dot p'>=n dot q>0,
|p'+d*n|^2=|p'|^2+2d*(n dot p')+d^2>=|p'|^2.
```

The corner q belongs to that inner unit side segment. To check this
coverage point, reflect coordinates about the relevant corner so that
the outward directions are positive and n=(c,e), c,e>0. A tangent is
v=(-e,c). The inner segment is `q+[u,u+1]*v`. If it did not contain q,
its tangent interval would be strictly positive or strictly negative.
In the first case all of S' is above q; in the second all of S' is to
the right of q. Outward translation preserves the respective coordinate
separation, contradicting the choice of S. Reflecting back proves the
assertion at every corner.

## 3. Three of the four oblique corners are impossible

At any corner reflect the coordinate axes so that

```text
q=(a,b),       n=(c,e),       a,b,c,e>0,
c^2+e^2=1.
```

The inner side of S' contains q. Its outer side has normal projection
`n dot q+1`. Of its two endpoints, at least one has tangent projection
of absolute value at least that of q: their tangent interval contains
q's tangent projection. Therefore some vertex has squared norm F with

```text
F >= (n dot q+1)^2+(v dot q)^2
  = a^2+b^2+2(ac+be)+1
  > a^2+b^2+2min(a,b)+1.                            (2)
```

The strict inequality follows from `c+e>1`. This is the same corner
estimate as in [GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md),
whose separator-to-contact coverage was checked directly above without
its inner-center premise.

For the upper-right corner, (2) is strictly greater than `R^2` immediately.
For the upper-left corner, the absolute coordinates are `a=1-s`,
`b=1+t`, so a<=b and

```text
F > (1-s)^2+(1+t)^2+2(1-s)+1,
F-R^2 > 3-6s>=0.                                    (3)
```

For the lower-right corner the corresponding difference is `3-6t>=0`.
Each contradicts disk containment, including s=1/2 or t=1/2 because
the vertex estimate is strict. Only the lower-left oblique corner remains.

## 4. At most one square lies outside both coordinate caps

At the lower-left corner q=(s-1,t-1), an oblique separator has both normal
components negative. Its outside half-plane avoids the open northeast
quadrant based at q. An additional square outside both caps (1) also has

```text
max x>s-1,       max y>t-1.
```

It is a straddler of that quadrant. The
[quadrant-straddler theorem](QUADRANT_STRADDLER_LEMMA.md) permits at most one
such square. Call this possible family H. No motion of one added square
relative to another was used in this counting: each original square
itself avoids the quadrant.

## 5. Count the caps, retaining the equality boundary

If `R^2<9/2`, the [sharp three-square cap theorem](THREE_SQUARE_CAP.md)
allows at most two squares in L and at most two in B. Indeed each lies
in a cap beginning at distance at least 1/2, and three squares in even
that larger cap require radius squared at least 9/2. With at most one
H square the total number of additions is at most `2+2+1=5`.

Under the present parameter bounds, `R^2=9/2` is possible only when
`s=t=1/2`. Then q=(-1/2,-1/2). If neither cap contains three squares,
the preceding count still applies. Otherwise the equality classification
of the same cap theorem forces the square

```text
Z=[-3/2,-1/2]^2
```

to belong to the packing, whether the three-square cap is L or B.
Relative to q, Z is the anchored southwest square `[-1,0]^2`. Section 3
of the quadrant-straddler theorem excludes every H square in its presence.
Each cap contains at most three squares. If both contain three, both
contain Z, so their union has at most `3+3-1=5` squares. If only one
contains three, their union has at most `3+2=5`. This proves the theorem
also on the sharp boundary.

## 6. Consequence and remaining scope

In a hypothetical subcritical ten-packing, the on-ray loaded-VV residual
cannot occur at a geometric four-square junction: its four right-angle
sectors force exactly the block `K=[a-1,a+1]^2` above. Its completion
capacity is nine.

This removes the four-square-junction portion of that residual for every
loaded count and every unloaded branch count. Three-square junctions and
the other irreducible branching structures remain open. No full master
family is closed by this local theorem alone, so the 336-entry denominator
and its closed count do not change.

