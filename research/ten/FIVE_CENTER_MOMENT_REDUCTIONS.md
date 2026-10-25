# Reductions for the five-center moment problem

The following are hand proofs. They do not yet prove the remaining moment
inequality. Let five unit squares have pairwise disjoint interiors, with
centers `c_i` satisfying `|c_i| <= 1`. The proposed inequality is

```text
sum_i |c_i|^2 >= 4.
```

Its equality candidate is the plus: one center at zero and four centers at
the unit vectors of a common square frame.

## 1. A nonextreme center forces the plus

Every pair of centers is at distance at least one, since each square
contains the open disk of radius `1/2` about its center.

Suppose one center `c` belongs to the convex hull of the others. Choose
nonnegative weights with `sum lambda_i = 1` and `c = sum lambda_i c_i`.
Then

```text
1 <= sum_i lambda_i |c_i-c|^2
   = sum_i lambda_i |c_i|^2 - |c|^2
   <= 1 - |c|^2.
```

Thus `c=0`. Every other center has norm exactly one, because its distance
from this center is at least one and its norm is at most one.

Two disjoint unit squares whose centers are exactly one apart have parallel
frames, and the center displacement is a unit edge vector. Indeed, a
separating unit normal `n` satisfies

```text
1 = |d| >= n dot d >= h_1(n)+h_2(n) >= 1,
```

where `h_i(n)` is the half-width of the corresponding square in direction
`n`. Equality forces `d=n` and `h_1(n)=h_2(n)=1/2`. A unit square has
half-width `1/2` precisely in its edge directions. Applying this to the
square centered at zero and each of the other four squares gives the four
distinct cardinal centers in its frame.

Consequently every configuration other than the plus has all five centers
as vertices of a strictly convex pentagon. In particular, no three centers
are collinear, and no center is zero.

## 2. Independent outward radial translations preserve disjointness

Fix two of the squares. A separating line gives a unit normal `n`, oriented
from the first square to the second, such that

```text
n dot (c_j-c_i) >= H,
H = h_i(n)+h_j(n) >= 1.
```

Since both centers have norm at most one,

```text
n dot c_i <= n dot c_j - H <= 1-H <= 0,
n dot c_j >= n dot c_i + H >= H-1 >= 0.
```

For any factors `s_i,s_j >= 1`, it follows that

```text
n dot (s_j c_j-s_i c_i)
  >= n dot (c_j-c_i)
  >= H.
```

Thus translating each square so that its center becomes `s_i c_i`, while
keeping its frame fixed, preserves this separating line direction.
The argument holds simultaneously for every pair and every independent
choice of the factors.

Equivalently, the open radial sweeps

```text
S_i^circ + {t c_i : t >= 0}
```

are pairwise disjoint. If a point belonged to two sweeps, it would lie in
the interiors of two independently translated squares, contradicting the
preceding argument.

## 3. Cyclic order of separating normals

Consider a configuration other than the plus, so all centers are nonzero.
Any two center rays make an angle at least `pi/3`. Indeed, for radii
`0<r,s<=1` and an angle `delta<pi/3`,

```text
|r e_0-s e_delta|^2 < r^2+s^2-rs <= 1.
```

The last inequality follows by maximizing the convex quadratic separately
over `r,s` in `[0,1]`; its maximum at the four corners is one. This would
contradict center separation.

Order the five center angles cyclically as `phi_i`. Their five successive
gaps `delta_i` therefore satisfy

```text
pi/3 <= delta_i <= 2pi/3,    sum delta_i = 2pi.
```

In particular, the origin is in the interior of their convex hull. For
each neighboring pair choose a separating unit normal `n_i` directed from
square `i` toward square `i+1`. Section 2 gives

```text
n_i dot c_i <= 0 <= n_i dot c_(i+1).
```

Because `0<delta_i<pi`, the normal's angle belongs to the closed interval
`[phi_i+pi/2, phi_(i+1)+pi/2]`, with the appropriate consecutive angle
lifts. These intervals are cyclically ordered. Thus the normal turns
`gamma_i = angle(n_(i-1),n_i)` can be chosen to satisfy

```text
0 <= gamma_i <= delta_(i-1)+delta_i <= pi,
sum gamma_i = 2pi.
```

Closed endpoints cause no problem, including when a center has norm one.

## 4. An explicit dual inequality for the moment

Choose any nonnegative numbers `lambda_i`. Define cyclically

```text
t_i = |cos gamma_i| + |sin gamma_i|,
a_i^2 = lambda_(i-1)^2 + lambda_i^2
        - 2 lambda_(i-1) lambda_i cos gamma_i,

g(a) = a^2/4       for 0<=a<=2,
       a-1         for a>=2.
```

Then the moment `M = sum |c_i|^2` satisfies

```text
M >= (1/2) sum min(lambda_(i-1)+lambda_i t_i,
                  lambda_(i-1) t_i+lambda_i)
     - sum g(a_i).                                      (1)
```

Here is a direct proof. Weight the five neighboring separation inequalities
by `lambda_i` and sum them. The center contribution becomes

```text
sum c_i dot f_i,
f_i = lambda_(i-1) n_(i-1) - lambda_i n_i,
|f_i| = a_i.
```

The two support contributions of square `i` have lower bound

```text
lambda_(i-1) h_i(n_(i-1)) + lambda_i h_i(n_i)
 >= (1/2) min(lambda_(i-1)+lambda_i t_i,
             lambda_(i-1) t_i+lambda_i).
```

To verify this support bound, vary the square's frame angle. Between
successive angles where one normal is parallel to a square edge, the
weighted sum of absolute sines and cosines is concave: its second
derivative is its negative. Its minimum is consequently at one of those
endpoints. Aligning either normal with an edge gives the two displayed
values.

Finally, `|c_i|<=1` gives

```text
f_i dot c_i - |c_i|^2
 <= max_(0<=r<=1) (a_i r-r^2)
 = g(a_i).
```

Combining these inequalities proves (1).

For any auxiliary numbers `d_i>=1`, a slightly weaker but useful version is

```text
M >= (1/2) sum min(lambda_(i-1)+lambda_i t_i,
                  lambda_(i-1) t_i+lambda_i)
     - sum [a_i^2/(4d_i) + d_i-1].                      (2)
```

This follows from
`a r-r^2 <= a^2/(4d)+(d-1)r^2 <= a^2/(4d)+d-1` for `r<=1`.
For fixed `lambda_i,d_i`, the right side of (2) is a concave function of
the five angles on the box `0<=gamma_i<=pi/2`: each support term is a
nondecreasing concave function of `cos gamma_i+sin gamma_i`, and each
remaining angle-dependent term is a nonnegative multiple of
`cos gamma_i`.

A sufficient remaining step is the following uniform inequality: for every
permitted five-angle fan, find weights making (1), or (2), at least four.
This sufficient condition is a relaxation and is not claimed to be
equivalent to the original geometric problem. No uniform choice or complete
analytic case analysis is claimed here.
