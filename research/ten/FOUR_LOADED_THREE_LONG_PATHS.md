# Four loaded bodies cannot be joined by three width-two paths and one contact

**Status:** exact hand proof; the distance and angular inequalities have
received independent mathematical review. This closes one further case in
the fixed mixed-cycle inventory, not the remaining mixed components.

Consider a positive stress component whose whole body-pair graph is a simple
cycle in the radius window

```text
79/40 <= R <= 3/sqrt(2).
```

Suppose it has four loaded bodies, with the successive unloaded run lengths
`(2,2,2,0)` up to cyclic order. Such a component is impossible.

The transmission theorem in
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md) makes each of
the three length-two runs a pair of side transmitters. Each path has width
two. As explained in
[THREE_LOADED_LONG_CYCLES.md](THREE_LOADED_LONG_CYCLES.md), its two endpoint
centers therefore have distance at least three: the projected center
separation is the transmission width plus the two endpoint halfwidths,
each at least `1/2`.

## 1. A distance-three pair is nearly antipodal

Put `A=(sqrt(17)-1)/2`. Every square center has norm at most A. If two
nonzero center vectors have minor angle `delta<=4pi/5` and norms r,s, then

```text
|c_1-c_2|^2 = r^2+s^2-2rs cos(delta)
 <= r^2+s^2+2rs cos(pi/5)
 <= 2A^2(1+cos(pi/5))
 = A^2(5+sqrt(5))/2
 < (49/20)(29/8)
 = 1421/160
 < 9.                                                 (1)
```

Here `A^2=(9-sqrt(17))/2<49/20` follows from `sqrt(17)>41/10`, and
`(5+sqrt(5))/2<29/8` follows from `sqrt(5)<9/4`. Both radical comparisons
follow by squaring positive rational quantities. This argument allows
unequal center norms; it does not replace r and s by A in a term of
unknown sign.

Consequently any endpoint pair at distance at least three has minor
center angle strictly greater than `4pi/5`. Its directed angular increment,
read modulo `2pi`, can be written

```text
pi+epsilon,             |epsilon|<pi/5.              (2)
```

Loaded centers are nonzero in the stated radius window, so all these
angles are defined.

## 2. Three such jumps cannot end in a loaded contact

Order the four loaded bodies as `H_0,H_1,H_2,H_3`, with a width-two
transmission path between each successive pair and a direct positive
contact between `H_3` and `H_0`. By (2), their three path increments add,
modulo `2pi`, to

```text
3pi+epsilon_1+epsilon_2+epsilon_3
  = pi+epsilon_1+epsilon_2+epsilon_3  (mod 2pi),
|epsilon_1+epsilon_2+epsilon_3|<3pi/5.
```

Thus the minor angle between the centers of `H_0` and `H_3` is strictly
greater than `2pi/5`: the displayed representative lies strictly between
`2pi/5` and `8pi/5`.

But two touching loaded squares have minor center angle strictly less
than `2pi/5` in this radius window, by Section 4 of the cyclic stress
reductions. The direct contact `H_3-H_0` contradicts the preceding lower
bound. This excludes the component.

## 3. Finite-inventory entry

This theorem closes exactly the entry

```text
C20-M10-L04-B01-T01: LLSSLSSLSS.
```

The [fixed inventory](cycle_cases.json) retains the entry, while
[cycle_progress.json](cycle_progress.json) records the hand exclusion.
The other two four-loaded binary patterns of length ten, whose unloaded
run lengths are `(2,2,1,1)` in their two inequivalent cyclic orders, remain
outside this theorem. In particular the result does not exclude every
four-loaded ten-cycle.
