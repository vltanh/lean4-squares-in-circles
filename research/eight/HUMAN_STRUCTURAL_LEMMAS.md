# An analytical corner-capacity lemma for central separators

**Status.** The theorem below is a pen-and-paper result for arbitrary
interior-disjoint unit squares. It uses neither a numerical experiment nor an
interval certificate. It does not require disk containment. Its application
to an eight-square packing with a central square is stated separately from the
still-missing sharp structural reduction.

## 1. Central-axis separation and the four remaining corner types

Fix a unit square `C`. Choose coordinates in which its center is the origin
and its sides are horizontal and vertical. Let `S` be another unit square with
center `d=(d_x,d_y)` and side-frame angle `alpha`. Set

```text
H = (|cos(alpha)|+|sin(alpha)|)/2,
W = 1/2+H.
```

The two squares have a separating axis parallel to an axis of `C` exactly when

```text
|d_x| >= W    or    |d_y| >= W.                         (1)
```

Call `S` **corner-separated relative to C** if its open interior is disjoint
from that of `C`, but neither inequality (1) holds. This is the case sometimes
called an `OWN` separator in the existing notes. The definition concerns the
actual geometry of the pair; it does not arbitrarily select a separator when
a central-axis separator is also available.

The separating-axis theorem gives an outward unit normal `e` along an axis of
`S` such that

```text
e dot d >= 1/2+(|e_x|+|e_y|)/2.                         (2)
```

Both components of `e` are nonzero. Otherwise (2) is a central-axis separator,
contrary to the definition. Reflect the central coordinate axes according to
the signs of `e`, so that

```text
e=(c,s),   c>0, s>0, c^2+s^2=1.
```

The half-width of `S` on each central axis is now `(c+s)/2`, so its `W` is
`(1+c+s)/2`. The assumptions imply

```text
d_x < W,   d_y < W,   c d_x+s d_y >= W.
```

Consequently

```text
d_x > W(1-s)/c = (1+c-s)/2 > 0,
d_y > W(1-c)/s = (1+s-c)/2 > 0.                         (3)
```

For example, the first strict inequality follows by substituting `d_y<W`
into `c d_x >= W-s d_y`. The displayed identities follow from `c^2+s^2=1`.

Undoing the reflections, the signs of `d_x,d_y` are therefore exactly the
signs of the selected outward normal. This assigns `S` to one uniquely
determined corner of `C`: the corner in the quadrant of its center. The
assignment does not depend on a choice among possible separators. In fact,
among the four signed axes of a non-cardinal square there is only one in a
specified open quadrant, so the outward separating axis itself is unique.

This derivation also covers boundary contacts: inequality (2) may be an
equality, whereas the absence of (1) is necessarily strict.

## 2. The exact triangle of possible centers at one corner

Work at the northeast corner `v=(1/2,1/2)`, as permitted by the reflections
above. Write

```text
e_theta=(cos(theta),sin(theta)),
f_theta=(-sin(theta),cos(theta)),       0<theta<pi/2,
H_theta=(cos(theta)+sin(theta))/2.
```

If `P=d-v` is the center of a corner-separated square measured from `v`, the
conditions just proved become

```text
P_x < H_theta,
P_y < H_theta,
e_theta dot P >= 1/2.                                    (4)
```

The closure of the region (4) is the triangle `T_theta` with vertices

```text
A_theta=(e_theta-f_theta)/2,
B_theta=(e_theta+f_theta)/2,
D_theta=(H_theta,H_theta).                               (5)
```

Indeed, the line `e_theta dot P=1/2` meets the right and top lines respectively
at `A_theta` and `B_theta`; their other intersection is `D_theta`. Both
components of `e_theta` are positive, so these three inequalities bound just
that triangle. The actual region excludes its right and top sides, including
all three vertices, but may include interior points of its sloping side.

In particular, every such `P` satisfies

```text
1/2 <= e_theta dot P <= (1+sin(2 theta))/2,
|f_theta dot P| < 1/2.                                    (6)
```

The first bound is obtained at the sloping side and at `D_theta`. For the
second, the values of `f_theta dot P` at the three vertices (5) are

```text
-1/2,   1/2,   cos(2 theta)/2.
```

Since `0<theta<pi/2`, the third value lies strictly between the first two.
Equality at either extreme is possible only at the corresponding vertex
`A_theta` or `B_theta`, both excluded by the strict inequalities (4). This is
the strictness needed in the overlap argument below.

## 3. Theorem: one corner accommodates at most one corner-separated square

**Theorem.** Let `S` and `T` be two unit squares, each corner-separated
relative to the fixed unit square `C`. If they are assigned to the same
corner of `C`, their open interiors intersect.

### Proof

By reflecting the coordinates, take the common assigned corner to be the
northeast one. Write the two centers relative to that corner as

```text
P in T_theta,   Q in T_phi,       0<theta,phi<pi/2,
```

with the strict exclusions (4). Define

```text
delta=phi-theta,
K=(cos(delta)+|sin(delta)|)/2.
```

Here `-pi/2<delta<pi/2`, so `cos(delta)>0`. The sum of the half-widths of `S`
and `T` on either axis of `S` is exactly

```text
1/2+K.                                                     (7)
```

We will show that every possible separating projection on an axis of `S` is
strictly smaller than (7). Interchanging `S` and `T` will give the same result
for the axes of `T`.

**The transverse axis.** The values of `f_theta dot Q` at the three vertices
of `T_phi` are

```text
(sin(delta)-cos(delta))/2,
(sin(delta)+cos(delta))/2,
(cos(theta+phi)+sin(delta))/2.                              (8)
```

The absolute values of the first two are at most `K`. For the third, use

```text
|cos(theta+phi)| <= cos(theta-phi)=cos(delta).
```

This last inequality follows directly from
`|cos(theta)cos(phi)-sin(theta)sin(phi)|`
`<=cos(theta)cos(phi)+sin(theta)sin(phi)`, since all four factors are positive.
Thus (8), followed by convexity of the triangle, proves

```text
|f_theta dot Q| <= K.
```

Combining this with the strict transverse bound in (6) gives

```text
|f_theta dot (Q-P)| < 1/2+K.                               (9)
```

**The outward axis.** The values of `e_theta dot Q` at the same vertices are

```text
(cos(delta)-sin(delta))/2,
(cos(delta)+sin(delta))/2,
(cos(delta)+sin(theta+phi))/2.
```

The third vertex is coordinatewise at least the other two, and `e_theta` has
positive components. It therefore supplies the maximum. The minimum is one
of the first two. Consequently

```text
(cos(delta)-|sin(delta)|)/2
    <= e_theta dot Q
    <= (cos(delta)+sin(theta+phi))/2.                       (10)
```

From the upper bound in (10), the lower bound in (6), and
`sin(theta+phi)<=1`, we obtain

```text
e_theta dot (Q-P) <= cos(delta)/2 < 1/2+K.                 (11)
```

For the other sign, the upper bound in (6) and the lower bound in (10) give

```text
e_theta dot (P-Q)
    <= (1+sin(2 theta)-cos(delta)+|sin(delta)|)/2.
```

This is strictly below `1/2+K` because

```text
sin(2 theta) < 2 cos(delta).                              (12)
```

For completeness, `delta` lies between `-theta` and `pi/2-theta`, whence

```text
cos(delta) >= min(cos(theta),sin(theta))
           > cos(theta)sin(theta).
```

The last inequality is strict because both sine and cosine are strictly
between zero and one. Multiplication by two proves (12). Together with (11)
this excludes separation on the outward axis:

```text
|e_theta dot (Q-P)| < 1/2+K.                               (13)
```

Equations (9) and (13) exclude both axes of `S`. The argument is symmetric in
the squares, so applying it with `theta,P` and `phi,Q` interchanged excludes
both axes of `T`. The separating-axis theorem now implies that the open
interiors intersect, as claimed. The proof has kept strict projection
overlap throughout, so a possible shared boundary cannot evade it. `QED`

## 4. Consequence for seven squares surrounding a fixed square

**Corollary.** Among seven pairwise interior-disjoint unit squares, all
interior-disjoint from a fixed unit square `C`, at least three have a
separating axis parallel to an axis of `C`.

**Proof.** Every square lacking such a separator has the unique corner
assignment of section 1. By the theorem, no two can have the same assignment.
There are four corners, so at most four of the seven lack a central-axis
separator. `QED`

More generally, in a packing of `m+1` unit squares, at least `m-4` of the
other squares have a separator parallel to an axis of any chosen square.
This statement has no containment or central-position hypothesis.

For the eight-square problem, apply it to the central square whenever one is
available. It then supplies at least three genuine central-axis separators
without assuming that every exterior square has one. In a complete branch
argument, the squares lacking them must occupy distinct central corners.
The four remaining corner possibilities come from exact geometric types,
not a discretization of the angle space.

## 5. What this advances and what it leaves open

`CENTRAL_PORT_NEGATIVE.md` disproves a universal pairwise claim that every
exterior square must be centrally separated. The theorem here is a global
replacement: all exceptional squares together have capacity at most four,
with at most one exception at each corner. It is fully compatible with the
counterexample in that note.

This does not yet force the five-corner projected chain. In particular:

- it does not identify which three or more exterior squares have central-axis
  separators, or require them to use distinct central sides;
- it does not force their orientations to agree with the central square;
- it does not assert that the seven exterior squares all touch the circle;
- the existence and quantitative location of a central square at the
  candidate ceiling remain separate theorems, whose currently recorded
  proofs use certificates.

The next structural question can now retain at most one exceptional square
per corner and at least three central-axis-separated squares. A successful
completion must use disk support and separation among these outer squares
to force the five-corner inequalities, or derive a radius obstruction for
the remaining corner assignments. No such final implication is asserted
here, and no Lean proof is being attempted.
