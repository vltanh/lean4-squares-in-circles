# Numerical survey of the unique-endpoint LSLSLD equation table

**Status: exploratory, not a proof.** The support table in
[ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md](ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md)
is exact. This note's numerical root search is not exhaustive and does
not certify roots, packing nonoverlap, or completion capacity.

The [survey script](explore_one_diagonal_two_side_normal_forms.py) retains
three endpoint types (strict/strict, vertical/strict, strict/vertical),
three common-source rows (E_A, E_B, V_V), and three possible outward
circle features of C (upper-left vertex, upper-right vertex, upper edge).
The last feature means both upper vertices lie on the circle and retains
nonnegative circle-load splits. These give 27 numerical equation rows.

For each row, the unknowns are R,u,z with h=−z. The search parameterizes
the full loaded-endpoint containment and strict D-height overlap ranges.
In a strict endpoint row it solves the endpoint force/torque identities
for the S direction. In a vertical row it solves them for the contact's
horizontal position; it does not replace that position by a corner.
The three equations impose the source contact row, the source circle
radius, and either circle-force alignment or the second circle radius.

The search's restriction `z>0`, equivalently `h<0`, covers the full
unique-endpoint family. If H_A>1, strict D-side overlap directly gives
`h<1−H_A<0`. Otherwise, at a strict corner endpoint, force and torque
give

```text
h=H_A*[(1−u)q+(H_A−1)p]/(u*q−H_A*p)<0,
```

because u>1, q>0, H_A<=1, and the denominator is positive. For a
vertical side-normal endpoint the same identities give
`h=H_A*((1−alpha)/u−1)<0`, since alpha>=0 and u>1. Thus no actual
unique-endpoint core is lost by restricting to positive z.

The numerical filters require the support inequalities, positive force
magnitudes, containment of C, and the indicated circle-force feature.
They do **not** check all six bodies' pairwise nonoverlap or transmitter
slides. Failed searches are not evidence of impossibility.

The saved run used seed 20261031 and 24 random starts per row:

```text
python explore_one_diagonal_two_side_normal_forms.py --starts 24 \
  --output one_diagonal_two_side_normal_forms_exploration.json
```

Only the following numerical roots survived those filters:

| D-endpoint supports | C source row | C circle feature | R | u | z |
| --- | --- | --- | --- | --- | --- |
| Strict / strict | E_A | Upper-left vertex | 2.03252994687835 | 1.79760252987725 | .622525630064957 |
| Strict / strict | E_B | Upper-right vertex | 2.03252994687835 | 1.61661103249585 | .622525630064971 |
| Strict / strict | V_V | Both upper vertices | 1.99993764192500 | 1.70710678118655 | .489383152153968 |

The first two rows are reflections of the previously recorded numerical
six-body candidate. The third is a symmetric algebraic candidate with

```text
u=v=(2+sqrt(2))/2,
p=r=(sqrt(2)−1)/2,
q=s=sqrt(1−p²),
H_A=H_B=[(2+q)²+1/4−u²]/[2(2+q)],
R²=u²+H_A²,
z=H_A*[u−1−(H_A−1)*(p/q)]/[u−H_A*(p/q)].
```

These formulas describe a solution candidate for the displayed contact
and stress equations; this note does not certify its full physical
realization. Its C center is numerically `(0,1.43642726989384)`.
The saved numerical residuals are below `2e-14`.

The next useful exact targets are exclusions or complete root bounds for
the vertical endpoint rows and the unique-circle V_V rows. If all roots
can be enclosed by a finite rational table, every interval and every
support boundary must be covered before using a completion certificate.
The radial D-endpoint branch remains a separate obligation. Neither
these search results nor the displayed three-row list changes a whole
case's status.
