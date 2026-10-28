# Consolidated two-row core exclusion over a wider displacement range

**Handoff status:** draft proof; the independent audit was incomplete when
work paused. Review the constant replacements and dependencies below before
using this extension as an established result.

Put `r=sqrt(1+1/sqrt(2))`. Suppose a packing in the origin-centered disk
of squared radius `9/2` contains four axis-parallel unit squares with
centers

```text
(-1/2,-t), (1/2,-t), (-b_L,1-t), (b_R,1-t),
0<t<3/2-2^(-1/4),
b_L+b_R>=1,
b_L^2+(1-t)^2<=1,  b_R^2+(1-t)^2<=1.
```

Then at most five additional unit squares fit, with arbitrary independent
orientations. Thus the entire packing has at most nine squares.

This is the latest two-row statement. The earlier
[symmetric theorem](SYMMETRIC_TWO_ROW_COMPLETION.md),
[asymmetric theorem with quarter-offset bounds](ASYMMETRIC_TWO_ROW_COMPLETION.md),
and [extreme-asymmetry extension](EXTREME_ASYMMETRIC_TWO_ROW.md) remain
useful shorter subcases and supply the detailed small-displacement proof.
This note gives the exact constant changes extending that proof, then a
short separate argument for the rest of the displayed interval.

The theorem requires the exact displayed core. It does not reduce an
arbitrary four-inner-center configuration to two rows. The upper offsets
may be unequal and their gap may exceed one. The lower pair must touch and
have horizontal midpoint zero, and the two row heights differ by one.

Write

```text
A=(sqrt(17)-1)/2<25/16,
h=1/2-t, z=3/2-t,
t_0=2^(-1/4)-1/2,
t_*=r/sqrt(2)-1/2=(sqrt(2+sqrt(2))-1)/2.
```

## 1. The small-displacement proof extends through t_*

The proof in
[EXTREME_ASYMMETRIC_TWO_ROW.md](EXTREME_ASYMMETRIC_TWO_ROW.md) extends
from `t<=5/12` to `t<=t_*` with the explicit replacements below. Its
noncrossing branch `t<=t_0` is unchanged.

First

```text
t_*<17/40,
b_i^2<=2t-t^2<1071/1600<81/121,
2/11<b_i<9/11,
z>43/40,
b_i+1/2>15/22>2/3.
```

For the first inequality it suffices to square
`r/sqrt(2)<37/40`; use `1/sqrt(2)<99/140` to bound
`r^2/2<239/280<1369/1600`. The lower bound on each b follows from
`b_L+b_R>=1` and the upper bound on the other.

The following table lists every bound in the crossing proof which changes.

| Use | Bound valid through t_* |
| --- | --- |
| Positive retained upper quadrant traces when both b values are at least 1/4 | `(3/4)^2+(43/40)^2=2749/1600>r^2` |
| Upper inner-edge exit angle exceeds 3pi/8 | `b_i-1/2<7/22<1/2` |
| A side gap containing two exterior arcs forces a small offset | `b_i<=t_0<41/120` |
| Middle opening when six arcs fit and both b values are at least 1/4 | `g=b_L+b_R-1<41/120+9/11-1=211/1320<4/25` |
| Upper-sector center's horizontal bound | `A^2(1-z^2/r^2)<772125/978944<81/100` |
| Center's possible height above the top row | `A-z<25/16-43/40=39/80<1/2` |
| Center-clearance square in the middle opening | `(2/25)^2+(39/80)^2=39049/160000<1/4` |
| Outer-corner endpoint with center x equal to the outer edge | Vertical distance `<3/2-43/40=17/40<1/2` |

Here `t_0<41/120` follows by comparing the fourth power of `101/120`
with `1/2`. The horizontal-bound fraction comes from
`(25/16)^2[1-(43/40)^2/(239/140)]`. The other outer-corner endpoint
estimate is unchanged: the coordinate differences are less than `7/30`
and `105/416`, because it uses only `z<H=(1+sqrt(2))/2<5/4`,
`r>13/10`, and an outer-edge coordinate greater than `2/3`.

For the extreme-asymmetry branch `b_R<1/4` (after reflection),

```text
g<1/4+9/11-1=3/44<4/25.
```

Thus the same upper-sector clearance bound applies. The three retained
arc gaps, the restriction on their center angles, and the contained
one-by-two rectangle argument are unchanged. In that argument the top
auxiliary vector has squared norm at most `2t<17/20<1`, while the bottom
auxiliary vector still has squared norm at most one. The top-corner
normal projection remains strictly greater than `17/16`, since

```text
z>43/40>17/16,
(b_R+1/2+z)/sqrt(2)
 >(2/3+43/40)/(3/2)=209/180>17/16.
```

The exclusion of a left-corner separator uses the unchanged lower center
height bound `y>-9/8` and now the bound `y-z<39/80<1/2` at the top.
Every remaining comparison and every cap-rigidity step is unchanged.
These replacements establish the full small-displacement theorem for
`0<t<=t_*`.

## 2. Every additional center is exterior in the remaining range

Now assume

```text
t_*<t<3/2-2^(-1/4)<2/3.
```

The final inequality follows from `2^(-1/4)>5/6`.
Put `B=sqrt(2t-t^2)`. Since `t<2/3`,

```text
b_i<=B<sqrt(8/9)<19/20,
b_i>=1-B>1/20.
```

Below height h, every point of the unit disk is at distance at most
`max(1/2-t,0)<1/2` from the lower rectangle
`[-1,1] x [-t-1/2,h]`.

Above h, the two upper horizontal intervals have middle opening
`b_L+b_R-1`, and their outer endpoints miss the interval `[-1,1]`
by at most `max(1/2-b_i,0)`. The distance from any horizontal coordinate
in `[-1,1]` to their union is consequently at most `B-1/2<9/20`.
The vertical distance above their common top z is at most
`max(1-z,0)=max(t-1/2,0)<1/6`. Hence the squared distance of such a
unit-disk point from the upper core squares is less than

```text
(9/20)^2+(1/6)^2=829/3600<1/4.
```

Every unit-disk point is therefore within distance strictly less than
`1/2` of the core. Each additional center has norm greater than one,
and at most A, so its square occupies one connected test-circle arc
of angle at least `pi/4`.

## 3. Three core arcs already leave room for at most five squares

At least one upper offset is at least `1/2`; reflect horizontally to
take `b_L>=1/2`. Retain only that upper-left square's second-quadrant
trace, and the two lower squares' fourth- and third-quadrant traces.

Put `gamma=acos(1/r)`, with `pi/8<gamma<pi/4`. The lower traces have
endpoints determined by gamma and

```text
delta=asin((t+1/2)/r)>pi/4,
```

because `t>t_*`. Their upper outside corners are inside the test circle,
since `|h|<1/6`; their lower outside corners are outside. The inner
corners are inside since `t+1/2<2-2^(-1/4)<r`. Thus these are exactly
the two arcs used in the preceding proofs.

The retained upper-left arc is

```text
[pi-beta,pi-alpha],        0<=alpha<=gamma<beta<pi/2.
```

Its outward corner is outside the test circle because
`b_L+1/2>=1` and `z>2^(-1/4)`. Its inward corner is inside. The lower
endpoint's outer vertical-edge bound is at most gamma, since its absolute
x-coordinate is at least one. Any positive lower horizontal-edge bound
is smaller than gamma, since `h<1/2<2^(-1/4)=r sin(gamma)`.
If h is nonpositive, clipping to the quadrant just supplies the bound zero.

For the upper endpoint, the top-edge angle is greater than gamma because
`z>2^(-1/4)`. The inner vertical-edge angle is also greater than gamma:
`b_L-1/2<1`, so
`acos((b_L-1/2)/r)>acos(1/r)=gamma`.
This proves the displayed endpoint inequalities and positivity of the arc.

The three complementary gaps now have angles

```text
alpha+gamma<=2gamma<pi/2,
pi-2delta<pi/2,
pi-beta+gamma<pi.
```

They accommodate at most one, one, and three disjoint connected exterior
arcs of angle at least `pi/4`, respectively. Thus at most five additional
squares fit. Together with Section 1, this proves the consolidated theorem.
