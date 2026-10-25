# A limit of the center-only obstruction for a translated block

The necessary center conditions used in
[TRANSLATED_BLOCK_OBSTRUCTION.md](TRANSLATED_BLOCK_OBSTRUCTION.md) do not
by themselves extend that theorem to an arbitrary two-coordinate translation.
Here is an exact obstruction to that proposed extension.

Translate the solid two-by-two block by `(1/40,1/40)`. Thus

```text
K = [−39/40,41/40]².
```

Its four unit-square centers are `(1/40±1/2,1/40±1/2)` and all lie
strictly inside the unit disk. Consider the following six additional
candidate centers:

```text
(0,31/20),          (31/20,0),
(−59/40, 1/2),     (−59/40,−1/2),
( 1/2,−59/40),     (−1/2,−59/40).
```

They satisfy all three center-only conditions:

* Their mutual distances are at least one. The two vertical neighbors and
  the two horizontal neighbors have distance exactly one. Every other
  pair is farther apart; the closest cross-pair has squared distance
  `2(39/40)²=1521/800>1`.
* Their distances from `K` are at least `1/2`. The top and right points
  have distance `21/40`; the four left and bottom points have distance
  exactly `1/2`.
* Their squared norms are at most `3881/1600`. This is less than `h²`,
  where `h=(sqrt(17)−1)/2` is the universal square-center bound in the
  containing disk of squared radius `9/2`: since `h<25/16` and
  `h²+h=4`, we have `h²>39/16=3900/1600`.

This is only a counterexample to the necessary-condition relaxation. It
does not assert that unit squares with these six centers can physically
complete the block in the target disk. An extension of the block theorem
must use further information, such as square orientations or the radial
localization available for a hypothetical ten-square packing.
