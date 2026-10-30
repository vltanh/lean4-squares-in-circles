# A loaded diagonal endpoint cannot send a second nonempty path outward

**Status:** reviewed exact shared geometric/stress restriction; root and
independent mathematical reviews passed on 2026-10-30. This is not a whole-signature exclusion or a completion bound.
It applies without fixing the number of loaded bodies in the component.

Use the selected physical certificate and assume
`79/40≤R≤3/sqrt(2)`. Let a degree-two loaded body A have a D transmission
path to another loaded body B, and a second nonempty unloaded transmission
path to a body C. The second path has width W≥1. C need only be contained
in the disk; it need not carry circle load for the main direction theorem.

The reviewed generic-normal theorem makes both contacts of the D body
relative side-interior contacts. Rotate so A is its left endpoint and B
its right endpoint. Their frames are parallel and may be written

```text
A=[−u,1−u]×[a,a+1],
B=[v−1,v]×[b,b+1],
u+v=2+sqrt(2),
P_D=(1−u,h) in A,       (v−1,h) in B,
a<h<a+1,                b<h<b+1.                    (1)
```

Let n be the outward unit direction of the other path at A, pointing
from A toward C.

**Theorem.** `n_x≥0`. Thus the other nonempty path cannot leave A toward
the outer side of the D strip. If A is radial-side loaded, then `n_x>0`.
The reflected statement holds for B: its other nonempty path has
nonpositive horizontal component.

## 1. Basic endpoint bounds and the normal-step observation

The two loaded endpoints have negative and positive horizontal centers,
respectively. Indeed a unit square has horizontal width at least one,
so the D separating strip gives each inward face an offset at least
`1+sqrt(2)−R>0` from the origin. Since their frames are parallel to the
strip, their outer horizontal coordinates are −u and v.

Containment and their unit vertical height give

```text
u,v≤sqrt(R²−1/4)≤sqrt(17)/2<33/16.
```

Using `sqrt(2)>7/5` and (1),

```text
u,v>17/5−33/16=107/80>4/3.                           (2)
```

Set `H_A=sqrt(R²−u²)` and `H_B=sqrt(R²−v²)`. Both are at least 1/2.
Since A and B are loaded, their vertical intervals are necessarily one
of

```text
[−H_i,1−H_i]       or       [H_i−1,H_i].             (3)
```

When `H_i=1/2` these coincide and give the radial-side case. Otherwise
the chosen interval has a unique lower or upper outer circle vertex.

If the other path starts at P with unit direction n, its far endpoint
contains `P+(W+1)n`: the path gives `P+Wn`, and the supported-square
unit-normal-step lemma supplies the further n. Since P is also in the
disk and `W+1≥2`, convexity of the disk implies

```text
|P+2n|≤R.                                          (4)
```

This observation is valid for every W≥1, not just a single S path.

## 2. Unique-circle A: an outward path would start at its outer corner

Reflect vertically if necessary so A has its unique lower circle vertex

```text
Z=(−u,−H_A),       A=[−u,1−u]×[−H_A,1−H_A],
H_A>1/2.
```

Write mu>0 for the D force magnitude, sigma>0 for the other path force,
and lambda>0 for A's circle coefficient. Using outgoing forces at A,
force balance is

```text
mu(1,0)+sigma n=lambda(u,H_A).                      (5)
```

Hence `n_y>0`. Suppose `n_x<0`, and write `n=(−p,q)` with p,q>0 and
`p²+q²=1`. The support point is necessarily the upper outer corner

```text
P=(−u,1−H_A).
```

Apply (4). Expansion using `R²=u²+H_A²` gives

```text
0≥|P+2n|²−R²
 =5−2H_A+4u p+4(1−H_A)q.                           (6)
```

If `H_A≤1`, the right side is positive. If `1<H_A≤3/2`, use q≤1
and the negative coefficient `1−H_A` to bound it below by
`9−6H_A+4u p>0`. Thus

```text
H_A>3/2,       u<3/2.                               (7)
```

The second bound follows from `u²=R²−H_A²<9/4`.
By (1) and `sqrt(2)>7/5`, now

```text
v>19/10,
H_B²<9/2−(19/10)²=89/100<(19/20)²,
H_B<19/20.                                          (8)
```

A's upper side has height `1−H_A<−1/2`. For B's open vertical interval
to contain the same D force height h, B cannot use the upper-loaded
interval `[H_B−1,H_B]`, whose lower endpoint is at least −1/2. Therefore
B must use the lower-loaded interval in (3). Strict side-interiority
in (1) gives

```text
h+H_A>H_A−H_B>11/20.                               (9)
```

## 3. Torque forces the opposite height bound

Torque about Z gives

```text
mu(h+H_A)=sigma p.
```

Together with (5), `mu−sigma p=lambda u` and `sigma q=lambda H_A`,
this yields the exact identity

```text
h+H_A=H_A p/(u q+H_A p).                            (10)
```

The horizontal coordinate of `P+2n` in (4) is `−u−2p`, so

```text
p≤(R−u)/2 < (17/8−4/3)/2=19/48.
```

Consequently

```text
q²>1−(19/48)²=1943/2304>(11/12)²,
q/p>44/19,
u/H_A>(4/3)/(17/8)=32/51.                           (11)
```

Substituting into (10),

```text
h+H_A
 =1/[1+(u/H_A)(q/p)]
 <1/[1+(32/51)(44/19)]
 =969/2377<11/20,                                   (12)
```

where the last rational comparison is `19380<26147`. This contradicts
(9). The outward direction `n_x<0` is impossible for unique-circle A.
Vertical reflection covers an upper circle vertex.

## 4. Radial-side A and the single-S corollary

If A is radial-side loaded, its vertical interval is `[−1/2,1/2]`.
Its outer corners `(−u,±1/2)` are both on the containing circle and
cannot be shared with another square. A direction with `n_x<0` and
`n_y≠0` would expose one of those forbidden circle corners. The remaining
outward direction `n=(−1,0)` violates (4), since its point would have
x-coordinate `−u−2`. A vertical normal likewise violates (4), placing
a point at height ±5/2. Therefore `n_x>0`.

When the other path is a **single S leading to a loaded C**, the remaining
horizontal possibility `n=(1,0)` is also impossible. The far S contact
is Q=`(2−u,k)`, `|k|≤1/2`. In this radial case

```text
19/10<u=sqrt(R²−1/4)<33/16,
|2−u|<1/10,
|Q|²<1/100+1/4< (21/40)².
```

Every point of C is within sqrt(2) of Q, so, using `sqrt(2)<57/40`,

```text
|point of C|<21/40+57/40=39/20<79/40≤R.
```

C would have no circle contact. Hence in a D/S loaded cycle endpoint,
a radial-side A must use a strict inner-corner S support with nonzero
vertical direction.

Combining this with Sections 2–3 gives a finite local support alphabet
for every degree-two loaded endpoint incident to a D and a single S:

* Unique circle vertex: the S direction points vertically away from
  that circle vertex and either uses the opposite inner corner strictly,
  or is normal to the opposite horizontal side.
* Two circle vertices: the S direction is strict at one inner corner.
  Either circle-load split is retained, including a zero coefficient
  at one of the two geometric circle vertices.

Boundary side normals are covered by the side-support alternative;
no point-only vertex/vertex normal has been altered. The endpoint C's
own support type and all S slide parameters remain unrestricted.

This restriction is available in every applicable D-containing cycle
signature and in larger positive graphs whenever the stated endpoint
degrees and loaded D neighbor are present. It does not bound the number
of additional squares and does not classify direct loaded-neighbor
edges, for which W=0 and observation (4) is unavailable.
