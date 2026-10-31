# Angular budgets for two transmission runs sharing a loaded endpoint

**Status:** independently reviewed exact hand proof, including the angular
order argument, all inequalities, and the finite-case IDs. This
note excludes eight further entries of the fixed mixed-cycle inventory.
It does not identify the order of an arbitrary mixed cycle with the radial
order of its loaded centers.

Work in `79/40<=R<=3/sqrt(2)`. Suppose a whole positive component is a simple
cycle with k loaded bodies, `k>=4`, and **exactly two nonempty unloaded
runs sharing a loaded endpoint V**. Denote a one-body side run by S, a
one-body diagonal run by D, and a two-body side run by SS. Then each of
the following cases is impossible:

| Two run types | Sufficient loaded count |
| --- | --- |
| SS and SS | `k>=4` |
| SS and S | `k>=6` |
| SS and D | `k>=5` |
| S and D, or D and D | `k>=7` |

## 1. The two endpoint pairs must be radial neighbors

The loaded-ray and contact lemmas in
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md), Sections
1 and 2, hold also for loaded subsets of mixed components. Every pair
of loaded rays has minor separation greater than `pi/5`, while touching
loaded pairs have separation less than `2pi/5`. Consequently every direct
loaded-loaded edge belongs to the abstract cycle H joining the k centers
in their radial angular order.

Deleting both unloaded runs leaves V isolated and a direct-contact path
P on the other `k-1` loaded bodies. Its `k-2` edges belong to H. The graph
`H-V` is itself a path with the same `k-1` vertices and `k-2` edges, so P
is exactly `H-V`. Its two endpoints are therefore adjacent to V in H.
These are the two transmission endpoint pairs.

Only this forced adjacency is used below. In particular no transmission
path has been assumed to follow a circular arc, and no Jordan embedding
of the original body-pair cycle is assumed.

## 2. Rational lower bounds for the angular gaps

Write

```text
M=25/16,
c=asin(8/25), v=asin(16/25),
a=asin(24/25), b=asin(328/425).                    (1)
```

Every loaded center has radius strictly between `5/4` and M.
First, **every** pair of loaded centers has minor angle greater than `2c`.
Otherwise its squared distance is at most

```text
r^2+s^2-2rs cos(2c),       cos(2c)=497/625.
```

This expression is convex in each radius. Its corner values on
`[5/4,M]^2` are `16/25`, `1149/1280`, and `1`. Since the actual radii lie
strictly inside that rectangle, its value is strictly below one, contrary
to the distance-at-least-one condition for square centers. Thus every
successive radial gap is greater than `2c`.

A nonempty transmission path of width W has loaded endpoint center
distance `d>=W+1`, as proved in
[THREE_LOADED_LONG_CYCLES.md](THREE_LOADED_LONG_CYCLES.md). In particular
d is at least two. If the minor center angle delta were at most `pi/3`,
then

```text
d^2 <= r^2+s^2-rs <= M^2 < 4,
```

where the middle bound follows by separate convexity on `[0,M]^2`.
This is impossible. For `delta>pi/3`, the squared-distance expression
is strictly increasing in each radius throughout `[5/4,M]^2`: its
partial derivative in r is

```text
2(r-s cos(delta)) > 2(5/4-M/2)>0,
```

and the other derivative is symmetric. Hence

```text
d^2 < 4M^2 sin^2(delta/2).                         (2)
```

It follows that the transmission endpoint half-angle exceeds v for S,
a for SS, and b for D. For the diagonal case, use

```text
1+sqrt(2)>41/17,
(41/17)/(2M)=328/425,
```

with `sqrt(2)>24/17` obtained by squaring. Thus the corresponding radial
gaps, whose lengths are at least their minor angles, exceed

```text
S: 2v,            D: 2b,            SS: 2a.         (3)
```

All remaining `k-2` radial gaps exceed `2c`. A necessary condition is
therefore that the sum of the two half-angle bounds and `(k-2)c` is
strictly below pi. We now contradict that condition in each row of the
theorem.

## 3. Two elementary budgets

The reference angles satisfy

```text
a>2pi/5,       v>pi/5,       c>pi/10.              (4)
```

For the first bound compare
`sin^2(2pi/5)=(5+sqrt(5))/8<29/32<(24/25)^2`.
For the second compare
`sin^2(pi/5)=(5-sqrt(5))/8<3/8<(16/25)^2`.
For the third use
`sin(pi/10)=(sqrt(5)-1)/4<5/16<8/25`.
The radical comparisons use only `2<sqrt(5)<9/4`.

For SS and SS with `k>=4`, the half-gap sum is greater than

```text
2a+2c > 4pi/5+pi/5=pi.
```

For SS and S with `k>=6`, it is greater than

```text
a+v+4c > 2pi/5+pi/5+2pi/5=pi.
```

Both contradict the angular budget from Section 2.

## 4. One side run and one diagonal run with seven loads

Exactly

```text
sin^2(v)+sin^2(b)
 = (16/25)^2+(328/425)^2
 = 181568/180625 > 1.                              (5)
```

Since v and b lie in `(0,pi/2)`, (5) implies `v+b>pi/2`: if their sum
were at most `pi/2`, then `sin(b)<=cos(v)` would give the reverse
inequality. Also `b>v`, so `2b>v+b>pi/2`.

For either S-D or D-D and `k>=7`, the two transmission half-angles plus
the other `k-2` half-gaps therefore exceed

```text
pi/2+5c > pi/2+pi/2=pi.
```

This excludes both cases.

## 5. A width-two run and a diagonal run with five loads

The remaining sharper inequality is

```text
a+b+3c > pi.                                      (6)
```

All three angles are explicit in (1), with

```text
cos(a)=7/25,
cos(b)=sqrt(73041)/425,
cos(c)=sqrt(561)/25.
```

Using `sqrt(73041)<271`,

```text
cos(a+b)
 = [7sqrt(73041)-7872]/10625
 < -239/425.                                       (7)
```

The triple-angle identity and `sqrt(561)<237/10` give

```text
cos(3c)=369sqrt(561)/15625
 < 87453/156250
 < 239/425.                                        (8)
```

The last difference is exactly `7049/2656250>0`; the two radical bounds
follow from `271^2-73041=400>0` and `(237/10)^2-561=69/100>0`.
Equations (7) and (8) show

```text
cos(a+b) < -cos(3c)=cos(pi-3c).
```

Here `a+b` lies in `(0,pi)`, and `c<pi/6` makes `pi-3c` lie in
`(pi/2,pi)`. Strict decrease of cosine on `[0,pi]` proves (6).
For SS-D with `k>=5`, its half-gap sum is at least this excluded sum.
This completes all four rows of the theorem.

## 6. Eight further finite cases

The theorem closes these previously unresolved entries. The fixed
[279-case inventory](cycle_cases.json) is unchanged; progress is recorded
in [cycle_progress.json](cycle_progress.json).

| Stable ID | Canonical word | Applied row |
| --- | --- | --- |
| `C20-M08-L04-B01-T01` | `LLLSSLSS` | SS-SS, four loads |
| `C20-M09-L05-B01-T01` | `LLLLSSLSS` | SS-SS, five loads |
| `C20-M10-L06-B01-T01` | `LLLLLSSLSS` | SS-SS, six loads |
| `C20-M09-L06-B01-T01` | `LLLLLSLSS` | SS-S, six loads |
| `C20-M09-L06-B01-T02` | `LLLLLDLSS` | SS-D, six loads |
| `C20-M08-L05-B01-T02` | `LLLLDLSS` | SS-D, five loads |
| `C20-M09-L07-B02-T02` | `LLLLLLSLD` | S-D, seven loads |
| `C20-M09-L07-B02-T03` | `LLLLLLDLD` | D-D, seven loads |

The theorem also reproves the two shared-endpoint cases already closed
in [SEVEN_LOADED_LONG_PATHS.md](SEVEN_LOADED_LONG_PATHS.md); those are not
counted a second time. Cases with two separated transmission runs, or
three or more nonempty runs, are not covered by this theorem.
