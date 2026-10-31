# Five-center moment bound when the normal turns are at most a right angle

This is a conditional hand proof. For the cyclic separating normals
constructed in [FIVE_CENTER_MOMENT_REDUCTIONS.md](FIVE_CENTER_MOMENT_REDUCTIONS.md),
assume additionally that all five turns satisfy `gamma_i <= pi/2`.
Then the five-center moment is **strictly greater than four**.

The remaining normal fans with a turn greater than `pi/2` are not covered
here. Together with the plus classification in the reductions document,
this proves the desired moment bound for the cases stated above only.

## 1. Concave dual certificates

Use inequality (2) in the reductions document. For nonnegative rational
weights `lambda_i` and rational `d_i>=1`, define

```text
A_i = (1/2) min(lambda_(i-1),lambda_i),
B_i = A_i + lambda_(i-1) lambda_i/(2d_i),
C = sum [(1/2) max(lambda_(i-1),lambda_i)
         - (lambda_(i-1)^2+lambda_i^2)/(4d_i) - d_i+1].
```

Since `sin(gamma_i)+cos(gamma_i)>=1` on `[0,pi/2]`, that inequality becomes

```text
M >= F(gamma) := C + sum [A_i sin(gamma_i)+B_i cos(gamma_i)].       (1)
```

Every `A_i,B_i` is nonnegative. Consequently `F` is concave on
`[0,pi/2]^5`, and its minimum on any polytope in that box occurs at a vertex.

We use three certificates. The entries are indexed `0,1,2,3,4` cyclically.

| Certificate | `lambda` | `d` |
| --- | --- | --- |
| A | `(61/10,8/5,11/10,8/5,61/10)` | `(1,16/5,1,1,16/5)` |
| B | `(5/2,3/2,3/2,3/2,5/2)` | `(1,3/2,1,1,3/2)` |
| C | `(3/2,3/2,3/2,3/2,3/2)` | `(1,1,1,1,1)` |

Direct substitution gives the following coefficients. Their reflection
symmetry about index zero will reduce each vertex check to two positions.

| Certificate | `C` | `A` | `B` |
| --- | --- | --- | --- |
| A | `-65133/3200` | `(61/20,4/5,11/20,11/20,4/5)` | `(4331/200,93/40,143/100,143/100,93/40)` |
| B | `-95/24` | `(5/4,3/4,3/4,3/4,3/4)` | `(35/8,2,15/8,15/8,2)` |
| C | `-15/8` | `(3/4,3/4,3/4,3/4,3/4)` | `(15/8,15/8,15/8,15/8,15/8)` |

## 2. The two cases with a small turn

Let `m=min gamma_i`, and cyclically relabel so that `gamma_0=m`.
Because `sum gamma_i=2pi`, the four deficits
`pi/2-gamma_j`, `j=1,...,4`, are nonnegative and sum to `m`.

For a prescribed interval `l<=m<=h`, where `0<=l<=h<pi/4`, the domain is a
truncated simplex. Its vertices have `m=l` or `m=h`, and the whole deficit
`m` at one of the other four positions. In other words, the vertices are

```text
gamma_0=m,  gamma_j=pi/2-m,
gamma_i=pi/2 for i outside {0,j},
where m belongs to {l,h} and j belongs to {1,2,3,4}.                (2)
```

One can see this directly by first writing any deficit vector of fixed sum
`m` as a convex combination of the four coordinate deficit vectors, and
then interpolating each such vector between its endpoint values at `l,h`.
The condition that index zero is a minimum removes no point from this
domain: each other angle is at least `pi/2-m>m`.

For **Case A**, `0<=m<=pi/8`, use certificate A. For **Case B**,
`pi/8<=m<=pi/5`, use certificate B. By reflection symmetry, only `j=1,2`
need be checked at the vertices (2).

The following elementary bounds suffice:

```text
sin(pi/8)>382/1000,     cos(pi/8)>923/1000,
sin(pi/5)>587/1000,     cos(pi/5)>809/1000.                        (3)
```

For completeness, `1414/1000<sqrt(2)<1415/1000`, as verified by squaring.
Then

```text
sin(pi/8)^2 = (2-sqrt(2))/4 > 585/4000 > (382/1000)^2,
cos(pi/8)^2 = (2+sqrt(2))/4 > 3414/4000 > (923/1000)^2.
```

Likewise `2236/1000<sqrt(5)<2237/1000`; hence

```text
sin(pi/5)^2 = (5-sqrt(5))/8 > 2763/8000 > (587/1000)^2,
cos(pi/5) = (1+sqrt(5))/4 > 809/1000.
```

At a vertex (2), formula (1) reads

```text
F = C + sum_(i outside {0,j}) A_i
      + (A_0+B_j) sin(m) + (B_0+A_j) cos(m).                     (4)
```

All coefficients of the two trigonometric terms are positive. Substitution
of (3) into (4) gives the following exact rational lower bounds; at `m=0`
the listed value is exact.

| Certificate | `m` | `j` | Lower bound for `F` |
| --- | --- | --- | --- |
| A | `0` | `1` or `2` | `12803/3200 = 4+3/3200` |
| A | `pi/8` | `1` | `1730061/400000` |
| A | `pi/8` | `2` | `320201/80000` |
| B | `pi/8` | `1` | `4093/960` |
| B | `pi/8` | `2` | `101179/24000` |
| B | `pi/5` | `1` | `104293/24000` |
| B | `pi/5` | `2` | `25633/6000` |

Every entry is greater than four, by direct integer comparison. Concavity
therefore proves `M>4` throughout Cases A and B.

## 3. All turns are at least `pi/5`

In **Case C**, all angles belong to `[pi/5,pi/2]` and sum to `2pi`.
The vertices of this sliced box are the permutations of

```text
(pi/5,3pi/10,pi/2,pi/2,pi/2).
```

Indeed, at a vertex at least four coordinates are at a box endpoint.
Two coordinates at the lower endpoint would leave the sum at most
`2pi/5+3pi/2<2pi`, while all four at the upper endpoint leave the remaining
coordinate zero. Thus exactly one of those four is at the lower endpoint
and three are at the upper endpoint, forcing the fifth to be `3pi/10`.

Certificate C is permutation invariant. At any such vertex it gives

```text
F = 3/8 + (21/8)[sin(pi/5)+cos(pi/5)]
  > 3/8 + (21/8)(587/1000+809/1000)
  = 8079/2000 > 4.
```

Concavity proves the same strict inequality throughout Case C. The three
cases cover every five-angle fan whose turns are at most `pi/2`, completing
the stated conditional moment theorem.
