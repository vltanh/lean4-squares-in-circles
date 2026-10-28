# Positive force circulation around an all-loaded ring

This note is a conditional refinement of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md). It does not
exclude a nonuniform seven-square ring or prove that its hole has area less
than three.

Use the same radius window `79/40 <= R <= 3/sqrt(2)`, the original physical
pair forces, and the cyclic order of the loaded bodies. Write their centers
as `c_i`, their contact application points as `p_i`, and orient the unit
pair normal `n_i` from body `i` toward body `i+1`. The corresponding positive
force vector is

```text
f_i = mu_i n_i,       mu_i > 0.
```

Thus body `i` receives `f_(i-1)` and `-f_i`. If `g_i` is the positive sum of
the outward radial vectors of its circle loads, force balance is

```text
f_(i-1) - f_i = g_i.                                      (1)
```

All indices are cyclic. The planar cross product is positive for a
counterclockwise turn.

## 1. Every cyclic pair force has strictly positive origin torque

The ring theorem supplies

```text
5/4 < |c_i| < 25/16,
phi_i < arg(p_i) < phi_(i+1),
|arg(p_i)-phi_i| < pi/5,
|arg(p_i)-phi_(i+1)| < pi/5.
```

Fix one contact. Put `e=p_i/|p_i|`, let `t` be the counterclockwise
quarter-turn of `e`, and put `D=c_(i+1)-c_i`. The strict angular ordering
gives

```text
t dot c_i < 0 < t dot c_(i+1),       t dot D > 0.
```

Since `cos(pi/5)=(1+sqrt(5))/4 > 4/5`, both radial center projections obey

```text
1 < e dot c_i < 25/16,
1 < e dot c_(i+1) < 25/16.
```

Consequently `|e dot D|<9/16`. On the other hand, physical support at the
shared point gives

```text
n_i dot D = h_i(n_i) + h_(i+1)(n_i) >= 1,                 (2)
```

where `h_i` is the square's directional halfwidth. Every unit square has
halfwidth at least `1/2` in every unit direction.

If `t dot n_i <= 0`, the positive sign of `t dot D` would imply

```text
n_i dot D
 = (e dot n_i)(e dot D) + (t dot n_i)(t dot D)
 <= |e dot D| < 9/16,
```

contrary to (2). Therefore

```text
p_i cross n_i = |p_i| (t dot n_i) > 0.                    (3)
```

This conclusion uses the actual physical support normal; it is not a
replacement of that normal by a center-to-center direction.

There is also a quantitative version. Touching unit squares have center
distance at most `sqrt(2)`, so (2) and the same decomposition give

```text
t dot n_i > 7/(16 sqrt(2)).                               (4)
```

Indeed, the radial contribution is strictly less than `9/16` and the
tangential contribution is at most `sqrt(2) (t dot n_i)`.

## 2. One strictly positive torque is shared by all edges

Every circle force has zero torque about the origin. Torque balance on
body `i` therefore reads

```text
p_(i-1) cross f_(i-1) = p_i cross f_i.
```

There is a single common number

```text
tau = p_i cross f_i > 0                                  (5)
```

for every edge. Positivity follows from (3) and `mu_i>0`.

In particular no pair force line is radial. The conclusion holds for
every physical positive stress on this all-loaded ring, independently of
the convention used to choose normals at point-only corner contacts.

## 3. The force vectors form a strictly convex polygon

The outward circle-load resultant `g_i` has direction within

```text
beta = asin(1/(2R)) < pi/12
```

of the center ray `phi_i`, by the circle-vertex estimate in
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md). For the strict
bound, `1/(2R)<=20/79<sin(pi/12)`; after squaring, the last comparison is
equivalent to `sqrt(3)<10882/6241`, which follows by squaring again.

The successive center gaps lie in `(pi/5,2pi/5)`. Thus the directions of
the nonzero vectors `g_i` occur in the same cyclic order, and their
successive angular gaps lie strictly between

```text
pi/5 - pi/6 = pi/30
```

and

```text
2pi/5 + pi/6 = 17pi/30 < pi.
```

Equation (1) says that the consecutive edges of the force-vector polygon
with vertices `f_i` are `-g_i`. They close because summing (1) gives
`sum_i g_i=0`. Their directions turn strictly counterclockwise through one
full revolution, with every turn less than `pi`, so this polygon is
strictly convex and counterclockwise.

For completeness, fix one of its directed edges. The cross products with
the later edge vectors are first positive and then negative, with only
possible isolated zero values at the opposite direction. The successive
cross products of the fixed edge with displacements to later vertices
therefore first increase and then decrease to zero. Every nonincident
vertex lies strictly to its left. This proves convexity without assuming
that the origin lies inside the force polygon.

The subsequent theorem
[SEVEN_RING_FORCE_ORIGIN.md](SEVEN_RING_FORCE_ORIGIN.md) proves that the
origin lies strictly inside this polygon. In particular, each body's two
contact-force lines concur on the positive ray of its circle-load
resultant. No assertion that the concurrence point lies inside its square
is needed. Exclusion of the three inner unit squares remains open for a
general nonuniform ring. In particular, (5) must not be used as an
unproved hole-area estimate: the regular radial-side ring admits positive
stress and has hole area greater than three.
