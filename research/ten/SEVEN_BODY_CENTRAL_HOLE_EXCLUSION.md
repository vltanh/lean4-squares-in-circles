# A seven-square core leaves no eighth-square position

**Status:** reviewed exact conditional hand proof with a rational finite-cover
certificate; root and two independent reviews passed on 2026-10-30. No whole-cycle case is closed.
The hypotheses describe a neighborhood of the numerical configuration in
[TWO_SIDE_ONE_DOUBLE_SIDE_COMPONENT_CANDIDATE.md](TWO_SIDE_ONE_DOUBLE_SIDE_COMPONENT_CANDIDATE.md).
They have not been established for all LSLSLSS realizations.

## 1. Statement

Suppose a packing in the centered disk of radius `R≤3/sqrt(2)` contains
seven distinct unit squares A, B, C, U, V, S, T satisfying the following
conditions. All decimal endpoints in this note are exact rationals.

```text
U=[−1,0]×[−1.5,−0.5],       V=[0,1]×[−1.5,−0.5].
```

The other centers belong to these closed boxes:

| Square | Center region |
| --- | --- |
| A | [−1.55,−1.54]×[−0.16,−0.15] |
| B | [1.54,1.55]×[−0.16,−0.15] |
| C | [−0.01,0.01]×[1.40,1.42] |
| S | [−0.75,−0.74]×[0.74,0.75] |
| T | [0.74,0.75]×[0.74,0.75] |

S and T are diamonds with sides at 45 degrees to the coordinate axes.
There is no orientation hypothesis on A, B, or C. Then **no eighth unit
square can be added**, regardless of its orientation.

The proof has two parts. A finite rational center cover confines any new
center to a small central rectangle. The lower SS row then restricts its
orientation, forcing it to contain a point already in S or T.

## 2. Exact localization of any new center

Every unit square in this disk has center norm strictly below `25/16`,
by the reviewed universal bound

```text
|center|≤sqrt(R²−1/4)−1/2≤(sqrt(17)−1)/2<25/16.
```

The last inequality follows from `sqrt(17)<33/8`. Distinct square centers
are at distance at least 1, since each square contains the open disk of
radius 1/2 about its center.

Let K_A,...,K_T be the seven center regions in Section 1, with U and V
singletons. Let m_i be the midpoint of K_i. Use the following rational
outer polygon P for the disk of radius 25/16:

```text
|x|,|y|≤25/16;
|x+y|,|x−y|≤125/56;
|2x±y|,|x±2y|≤85/24;
|3x±y|,|x±3y|≤475/96;
|4x±y|,|x±4y|≤155/24.
```

Each half-plane `n·x≤b` contains the disk because `b²≥(25/16)²|n|²`.
Partition P into the seven closed nearest-midpoint regions

```text
V_i = P ∩ {x : 2(m_j−m_i)·x≤|m_j|²−|m_i|² for every j}.
```

These cover P, including their ties. Intersect each V_i with each of
the four exterior half-planes

```text
east: x≥1/5,    west: x≤−1/5,
north: y≥1/10,  south: y≤−1/5.
```

The resulting 28 rational convex polygons cover the portion of P outside
the open rectangle

```text
H=(−1/5,1/5)×(−1/5,1/10).                            (2)
```

For each nonempty cell assigned to i, the table below gives

```text
max {|v−w|² : v is a cell vertex, w is a vertex of K_i}.
```

Every bound is at most `197/200<1`. Convexity in both arguments extends
this bound to every point of the cell and every allowed actual center
in K_i. Thus a center outside H would be less than distance 1 from an
existing center, which is impossible. Every possible new center is in H.

The complete certificate is [seven_body_central_hole_cover.json](seven_body_central_hole_cover.json).
[check_seven_body_central_hole_cover.py](check_seven_body_central_hole_cover.py)
recomputes every polygon intersection and table entry with `Fraction`
arithmetic. It uses the reviewed rational clipping function from
[check_six_body_center_cover.py](check_six_body_center_cover.py), checks
that the displayed boxes and all 28 region/exterior pairs match the
certificate, and verifies that every outer half-plane contains the
center disk. This check performs no optimization or floating-point work.

<!-- SEVEN_BODY_CENTRAL_HOLE_TABLE -->

| Region | Exterior | Maximum squared distance |
| --- | --- | --- |
| `A` | east | EMPTY |
| `A` | west | `329055259609/418091560000` |
| `A` | north | `770908637/1411200000` |
| `A` | south | `1216034581/1747240000` |
| `B` | east | `329055259609/418091560000` |
| `B` | west | EMPTY |
| `B` | north | `770908637/1411200000` |
| `B` | south | `1216034581/1747240000` |
| `C` | east | `18493828321/38753280000` |
| `C` | west | `18493828321/38753280000` |
| `C` | north | `408555277/707560000` |
| `C` | south | EMPTY |
| `U` | east | EMPTY |
| `U` | west | `4668815281/4872040000` |
| `U` | north | EMPTY |
| `U` | south | `89/100` |
| `V` | east | `4668815281/4872040000` |
| `V` | west | EMPTY |
| `V` | north | EMPTY |
| `V` | south | `89/100` |
| `S` | east | EMPTY |
| `S` | west | `4735229981/4872040000` |
| `S` | north | `197/200` |
| `S` | south | EMPTY |
| `T` | east | `4735229981/4872040000` |
| `T` | west | EMPTY |
| `T` | north | `197/200` |
| `T` | south | EMPTY |

## 3. The lower row restricts orientation

Suppose an eighth square K has center `(x,y)∈H`. Its horizontal and
vertical halfwidths are at most `1/sqrt(2)`. Since `1/sqrt(2)<4/5`,
every point of K has x-coordinate strictly between −1 and 1. Likewise
every point has y-coordinate greater than `−1/5−1/sqrt(2)>−3/2`.

If K had minimum height below −1/2, its interior would enter the interior
of U or V; the shared line x=0 cannot contain an open piece of K. Hence
its minimum height is at least −1/2.

Write its unsigned frame angle using `c≥s≥0`, `c²+s²=1`. Its vertical
halfwidth is `(c+s)/2`, so

```text
y≥(c+s−1)/2≥0,        c+s≤1+2y<6/5.                 (3)
```

The function `sqrt(1−s²)+s` increases for `0≤s≤1/sqrt(2)`.
At `s=1/4` it equals `(sqrt(15)+1)/4>6/5`, since
`15>(19/5)²`. Therefore

```text
0≤s<1/4,        c>sqrt(15)/4>19/20.                 (4)
```

## 4. A fixed point forces overlap

Reflect in the vertical axis if necessary so `x≥0`. Consider

```text
p=(2/5,9/20)=(0.4,0.45).
```

Set `d_x=p_x−x`, `d_y=p_y−y`. By (2)–(3),

```text
0<d_x≤2/5,
0<d_y≤19/20−(c+s)/2.
```

The absolute values of K's two own-frame coordinates of `p−(x,y)` are
bounded by `c d_x+s d_y` and `s d_x+c d_y`, regardless of chirality.
For the first bound, use `c≤1` and `2/5−s/2>0`:

```text
c d_x+s d_y
 ≤ c(2/5−s/2)+(19/20)s−s²/2
 ≤ 2/5+(9/20)s−s²/2
 < 77/160 < 1/2.
```

For the second, use `1−c≤s`, `c/2−9/20≤1/20`, and
`2/5−c/2<−3/40` from (4):

```text
s d_x+c d_y
 ≤ 9/20+(1−c)(c/2−9/20)+s(2/5−c/2)
 ≤ 9/20+s/20−3s/40
 ≤ 9/20 < 1/2.
```

Thus p is in the interior of K. But T is a 45-degree diamond centered
at `(u,v)∈[0.74,0.75]²`, so

```text
|p_x−u|+|p_y−v|=u+v−17/20≤13/20<1/sqrt(2).
```

Hence p is also in the interior of T, a contradiction. For x≤0 the
reflected point lies in both K and S. No eighth square exists.

## 5. Scope

The theorem uses a finite rational center localization and elementary
orientation inequalities. It applies to all seven-square cores satisfying
the stated boxes and shapes, not merely to rounded numerical coordinates.
The candidate's membership in these boxes is currently established
numerically; existence of that candidate is not a premise of this theorem.

The missing whole-case step is a finite classification of arbitrary
LSLSLSS realizations into completion-capacity families. In particular,
the SS transmitter slides and the two single-S slides are not fixed by
the positive stress. This note does not reduce all such slides or all
loaded endpoint orientations to its hypotheses.
