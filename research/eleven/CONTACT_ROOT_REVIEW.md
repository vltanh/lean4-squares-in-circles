# Independent review of the eleven-square contact root

Reviewed on 2026-10-23 at 12:46 UTC. The local root certificate and the
geometric feasibility argument pass this review. They establish a packing
family at the exact locally isolated squared radius `q_c`. They establish no
unrestricted lower bound or complete equality classification.

## Reviewed artifacts

| File | SHA-256 |
| --- | --- |
| `CANDIDATE_CONTACT_SYSTEM.md` | `ff7c0f52ce0fb256d183a52c0f5ffcb33eb6fbad68686c03060883050a39a330` |
| `contact_family.py` | `481ab25ecce404d45630dd43cdf89202c1e20bff803290391590c2926883ca31` |
| `isolate_contact_root.py` | `a6158c6040d1dc07074a7a16e3110a1a8e470c9e180d3452fec4260585bb7da4` |
| `RATIONAL_WITNESS.json` | `c9084cc20cc2d9d68afa6e209b9a0628c3c06b794474053c5aba0533fa7c0eb2` |

The standard-library checker ran successfully. The review examined its
interval operators, differentiated operators, domain guards, fixed-point
argument, omitted exact constraints, and remaining geometric inequalities.

## Interval arithmetic and root existence

For a nonnegative rational endpoint `x`, setting
`k = isqrt(floor(x*10^70))` gives
`k^2 <= x*10^70 < (k+1)^2`. Thus the implemented square-root endpoint
bounds are outward bounds. Addition, negation, endpoint multiplication,
reciprocal, squaring, and absolute-value operations enclose their real
counterparts. Reciprocal intervals are accepted only when they omit zero.

The differentiated product, quotient, square, and square-root rules are the
ordinary derivative rules with enclosing interval operands. In particular,
the square-root derivative divides by an interval enclosing `2*sqrt(x)`;
its zero-exclusion guard confirms strict positivity of each radical used
in differentiation. The formulas are continuously differentiable on an
open neighborhood of the entire closed root rectangle. The displayed
Jacobian intervals enclose their computed derivative intervals.

The fixed-point map is `T(x)=x-MF(x)`. A separate exact calculation, enumerating
the 16 endpoint matrices of the printed Jacobian rectangle, gave

`det(M) = -3047225245867307 / 5000000000000000`

and

`sup ||I-MJ||_infinity = 19541101 / 50000000000000 < 1/1000000`.

The supremum can be checked at endpoint matrices because the matrix infinity
norm is convex in each entry. The checked center residual bound
`|F_i(x_0)| < 10^-15` and `||M||_infinity < 2` imply

`||T(x)-x_0||_infinity < 3/10^15 < 1/10^9`

throughout the root rectangle. The vector mean-value integral gives both this
bound and the contraction estimate; it does not require one common scalar
mean-value point for all matrix entries. The rectangle is nonempty, closed,
convex, and complete in the infinity norm. Banach's theorem therefore gives
one fixed point in it. The nonzero determinant makes fixed points equivalent
to roots of `F`, proving existence and uniqueness in this rectangle only.

## Exact contacts and geometric completeness

The ten omitted corner equations were checked directly from the positive
radical definitions. The two corners of square 7 give
`(r+1/2)^2+1/4=q`; the two corners of square 10 give the same identity.
Square 9 gives `9/4+(w+1/2)^2=q`. The other five corner equations are the
successive definitions of `b,d,e,f,g`.

All fourteen omitted pair contacts were checked algebraically using the
directions in the note. In particular:

- `w*v^2+3*v+1-w=0` gives `w*C-S=K`, the `(7,9)` contact.
- The formula for `z` gives `w+(1-r)*S-z*C=K`, the `(8,9)` contact.
- `a+r*s'=k'` gives the `(0,10)` contact.
- `F_1=0` and `F_2=0` give exactly `(4,8)` and `(6,7)`.
- The remaining contacts are unit coordinate or frame-projection gaps.

The checker establishes positivity of `c,s,c',s',C,S`, as needed for the
stated support sums. The rational half-angle identities and multiplication
of rotation matrices give orthonormal physical frames.

The two slider constraints are exactly `h<=a` and `h>=H`. The checked strict
inequality `H.hi<a.lo` supplies a nonempty interval and preserves its closed
endpoints. Every allowed slider position lies in the larger interval hull
used by the remaining inequality checks.

The checker verifies all 34 remaining vertex inequalities with squared
radius slack greater than `1/2`, and all 39 remaining pair inequalities with
separator slack greater than `1/100`. A separate interval calculation
reconstructed the four vertices of each square and compared maximum and
minimum projected vertex bounds, rather than using the checker's support
sum formula. All 39 inactive pairs again had gap greater than `1/100`.

The pair list contains all 55 unordered pairs exactly once. Therefore the
coverage totals `10+34=44` vertices and `14+2+39=55` pairs account for every
physical containment and nonoverlap obligation. Convexity gives whole-square
containment; support separation gives disjoint open interiors, including
contact and slider endpoint cases.

## Scope of the accepted result

The result is an exact, locally isolated root on one selected contact branch,
and an explicit nonempty slider family of packings in its centered disk.
The derivative bound also implies local nonsingularity. Neither nonsingularity
nor this construction proves minimality even within a broader contact class.
The review does not establish that arbitrary eleven-square packings enter this
branch, that all globally optimal packings belong to this family, or that the
family is the unrestricted optimum. It also does not assert a unique least
enclosing circle or noncongruence of every slider parameter. No Lean source
or Lean kernel verification is part of this review.
