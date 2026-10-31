# A four-loaded five-cycle forces a diagonal transmitter

**Status:** independently reviewed hand proof (2026-10-29), with the
explicitly imported n=8 lower-radius dependency below.

Use the original physical positive stress certificate. Suppose a whole
positive component is the simple cycle

```text
U-A_1-A_2-A_3-A_4-U,
```

where precisely `A_1,...,A_4` are circle-loaded and U is unloaded. Work in

```text
R^2>5/2+sqrt(2),       R<=3/sqrt(2).                     (1)
```

**Theorem.** U must be a diagonal transmitter. A side transmitter is
impossible throughout (1).

This closes the side-transmitter subcase of the four-loaded five-cycle
left open in Section 5 of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). The diagonal
case remains open. This theorem does not classify other component graphs
or exclude completion to ten for the remaining diagonal case.

## 1. The radius dependency

Window (1) is the same slightly sharper window justified in Section 1 of
[RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md).
For a ten-square packing, the imported n=8 lower bound gives
`R^2>=qStar>7831/2000`, and

```text
7831/2000>5/2+sqrt(2),
2831^2-2*2000^2=14561>0.
```

The exact source is the n=8 main-branch theorem at commit
`cd9127ff04e089909cc460d817ea28c4b1eb9ea9`, pinned and explained in that
manuscript. Its coarse `qStar` bracket uses the repository's generated
exact interval data. This note is a hand deduction from the explicitly
imported lower bound, not an independent hand derivation of that bracket.
The older window `R>=79/40` follows, as recorded in the same source.

## 2. The loaded contact path follows cyclic center-ray order

The following local geometric bounds are proved in Sections 1--3 of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md):

* Every loaded center has norm in `(5/4,25/16)`.
* Distinct loaded center rays have minor angular separation greater than
  `pi/5`.
* Touching loaded center rays have minor angular separation less than
  `2pi/5`.

Although the main theorem of that manuscript assumes an all-loaded
component, these three local estimates require only that the particular
bodies are loaded. They therefore apply to the four loaded bodies here.

Only neighbors in their cyclic center-ray order can touch. For
nonneighbors, both circular arcs between their rays contain at least two
successive gaps greater than `pi/5`; their minor angle would exceed
`2pi/5`, contradicting the contact bound. The three loaded-loaded path
edges thus follow their cyclic order. Reverse the labeling direction if
needed and take lifts

```text
phi_1<phi_2<phi_3<phi_4<phi_1+2pi.
```

Every contact gap on this path is its pair's minor angle. If such a gap
were at least `pi`, the complementary arc would consist of the other
three gaps and have length greater than `3pi/5`, still larger than the
permitted contact angle. Therefore all three path gaps satisfy

```text
pi/5<phi_(i+1)-phi_i<2pi/5       (i=1,2,3).
```

In particular the lifted path span S and its complementary gap G obey

```text
S=phi_4-phi_1<6pi/5,
G=2pi-S>4pi/5.                                         (2)
```

This is a statement about the actual center-ray order. No assumption
about a physical ring enclosing the origin is used.

## 3. A side transmission would force the endpoint minor angle below 144 degrees

Assume for contradiction that U is a side transmitter. Its two contact
application points differ by a unit vector, by the degree-two transmission
formula in Section 2 of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). Each contact
belongs to its loaded endpoint square and is within `1/sqrt(2)` of that
square's center. Hence

```text
|c_4-c_1|<=1+sqrt(2).                                   (3)
```

The two loaded centers have norms `r,s>=R-1/sqrt(2)`. If kappa is their
minor angle, then

```text
|c_4-c_1|^2=(r-s)^2+4*r*s*sin(kappa/2)^2,
sin(kappa/2)<=(1+sqrt(2))/(2R-sqrt(2)).                   (4)
```

The radius window gives a particularly simple strict bound on this
ratio. Indeed

```text
38^2*(5/2+sqrt(2))-(20+39sqrt(2))^2
 =168-116sqrt(2)>0,
```

because `42^2>2*29^2`. All compared quantities are positive, so (1)
implies `38R>20+39sqrt(2)`, or equivalently

```text
(1+sqrt(2))/(2R-sqrt(2))<19/20.                         (5)
```

Also

```text
(19/20)^2<(5+sqrt(5))/8=sin(2pi/5)^2.
```

For this exact comparison it suffices that `sqrt(5)>111/50`, whose
square is `12500>12321`. Since `kappa/2` lies in `[0,pi/2]`, (4)--(5)
therefore give

```text
kappa<4pi/5.                                           (6)
```

But `kappa=min(S,G)`, and (2) says `G>4pi/5`. It follows that the whole
loaded path fits in the shorter interval:

```text
S=kappa<4pi/5.                                         (7)
```

## 4. All circle loads would lie in one open semicircle

Every circle vertex of a loaded square lies within

```text
beta=asin(1/(2R))
```

of its center ray, by Section 4 of
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). This estimate
also covers a square with two circle vertices and arbitrary positive
load weights on them.

We need only the elementary bound `beta<pi/10`. It follows from

```text
1/(2R)<=20/79<3/10<sin(pi/10)=(sqrt(5)-1)/4,
```

where the final comparison uses `sqrt(5)>11/5`.
All loaded circle directions consequently lie in the real angular
interval

```text
[phi_1-beta,phi_4+beta],
```

whose length, by (7), is strictly less than

```text
4pi/5+2*(pi/10)=pi.
```

A positive weighted sum of vectors in an interval of length less than pi
cannot vanish: its dot product with the interval's midpoint direction is
strictly positive. However, summing the force equations over the whole
positive component cancels every pair force and leaves the sum of the
circle loads equal to zero. U has no circle load, so the four displayed
loaded bodies supply every positive term. This contradiction excludes a
side transmitter.

U is unloaded of degree two, so the only remaining transmission type is
diagonal. This proves the theorem. Lean formalization and kernel
verification have not been performed.
