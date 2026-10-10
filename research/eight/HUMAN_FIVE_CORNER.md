# An analytic reduction of the five-corner optimization

## Status and scope

The lemmas below are pen-and-paper results about the projected five-corner
chain in `FIVE_CORNER_REDUCTION.md`. They do not assert that an arbitrary
packing of eight unit squares contains that chain. They do not use interval
subdivision, numerical minimization, or a Lean proof.

The principal new fact is that, **at each fixed tilt, the complete scalar
problem is strictly convex in its remaining position variable**. Thus its
position minimizer is unique throughout the full feasible domain. A second
lemma reduces optimization of the tilt at a fixed position to one explicit
quartic equation and the two endpoints.

These facts substantially simplify the conditional optimization problem.
They do not by themselves prove that the angle-dependent minimum has its
unique global minimum at the previously isolated candidate. That last angle
statement is still supplied only by the existing computational certificate.

## 1. A symmetric parametrization and the exact radical domain

Write `R = sqrt(q) < 2`. Rename the two positive downward corner heights

    u = -y,                 v = 2 - y3,

and put

    r = sqrt(R^2-u^2),       w = sqrt(R^2-v^2),
    U = sqrt(R^2-(2-u)^2),   V = sqrt(R^2-(2-v)^2).

The four original circle equations and the horizontal span three become

    U + V = 3.                                             (1)

In particular, exchanging `u` and `v` exchanges the left and right branches.
For `0 <= t <= pi/4`, abbreviate `c = cos(t)`, `s = sin(t)` and define

    k1 = 2 - c(r-1) + s*u,
    k2 = 1 + c*v - s(w-1).

The original defect is exactly

    F(R^2,-u,t) = k1^2 + k2^2 - R^2.                       (2)

Both `k1` and `k2` are positive throughout the radical domain. Indeed,

    k1 >= 2 - c(R-1) >= 3-R > 1,
    k2 >= 1 - s(R-1) > 0.

The second bound follows from `w <= R`, `v >= 0`, and `R < 2`.

### Lemma 1: the radical domain is one interval

The first three projected span requirements have a realization by the four
boundary points used in the reduction if and only if

    25/16 <= R < 2.

For such `R`, put

    L = 2*sqrt(R-1),
    a = 2 - sqrt(R^2-(3-L)^2).                              (3)

Then the complete radical domain is

    a <= u <= R,                                           (4)

and

    v(u) = 2 - sqrt(R^2-(3-sqrt(R^2-(2-u)^2))^2).           (5)

Here `v(a)=R`, `v(R)=a`, and `v` is a strictly decreasing involution.
For `R > 25/16`, all four radicals are positive in the open interval `(a,R)`;
only `w` vanishes at `u=a`, and only `r` vanishes at `u=R`.

#### Proof

The horizontal span three already forces `R>=3/2`, so the square root
in `L=2*sqrt(R-1)` is defined. Since `0 <= u <= R < 2`, the quantity
`2-u` is positive. The inner radical
`U` is increasing in `u`, and its largest possible value is

    U(R) = sqrt(R^2-(2-R)^2) = L.

Put `Y=sqrt(R^2-(3-U)^2)=2-v`. The requirement `0 <= v <= R` is
equivalent to

    2-R <= Y <= 2.

Because `Y<=R<2`, its upper bound is automatic. Its lower bound is
equivalent to

    (3-U)^2 <= R^2-(2-R)^2 = L^2.

Moreover `U<=R<2`, so `3-U>0`. Thus the only remaining condition is
`U >= 3-L`. Since `U` increases in `u`, solving this last inequality gives
exactly (3)-(4). Such an interval exists exactly when

    3-L <= L,

or `L>=3/2`, which is equivalent to `R>=25/16`.
This also proves that the radicals in (3) are defined whenever the interval
exists. The endpoint equalities follow by substitution. Equation (1) is
symmetric in `u,v` and determines either variable uniquely from the other;
this proves the involution assertion. Strict decrease also follows from
(1), since each summand is strictly increasing in its argument. At the
threshold `R=25/16` the domain is a single point, `u=v=R`.

For completeness, the lower bound `R>=25/16` also applies directly to any
four points satisfying the first three projected inequalities: the original
monotonic boundary replacement in `FIVE_CORNER_REDUCTION.md` supplies the
radicals above. It is not an additional boundary-contact assumption.

## 2. Global strict convexity for every fixed tilt

### Lemma 2

Fix `25/16 < R < 2` and `0 <= t <= pi/4`. Then

    u |--> F(R^2,-u,t)

is continuous and strictly convex on the full closed interval `[a,R]`.
Consequently it has exactly one minimizer on that interval. In particular,
checking a stationary position proves the global minimum at that *fixed*
tilt; there is no additional remote position branch to exclude.

#### Proof

It is convenient to prove the composition statements in the original
variable `y=-u`, since an affine change of variable preserves convexity.
Set

    x(y) = sqrt(R^2-(y+2)^2),
    b(y) = sqrt(R^2-(3-x(y))^2) - 2.

Thus `b(y)=y4=-v(-y)` and `-R <= b(y)<0`.

First, `x` is concave. The function

    x |--> sqrt(R^2-(3-x)^2)

is concave and increasing for the relevant range `x<3`. A concave increasing
function composed with a concave function is concave, so `b` is concave.
This composition claim follows directly by applying the two concavity
inequalities in order; it requires no differentiability at an endpoint.

Now

    k1(y) = 2+c - c*sqrt(R^2-y^2) - s*y

is strictly convex, because `c>0` and the upper semicircle is strictly
concave. The other positive quantity is

    k2(y) = phi(b(y)),
    phi(b) = 1+s - s*sqrt(R^2-b^2) - c*b.

On `[-R,0]`, `phi` is convex and decreasing. In the open interval,

    phi'(b) = s*b/sqrt(R^2-b^2) - c < 0,
    phi''(b) = s*R^2/(R^2-b^2)^(3/2) >= 0.

Continuity gives the same monotonicity and convexity on the closed interval.
A convex decreasing function composed with a concave function is convex:
concavity of `b` first reverses under the decreasing function `phi`, and
convexity of `phi` then gives the desired Jensen inequality. Hence `k2` is
convex.

Finally the function `x |--> x^2` is convex and strictly increasing on the
positive half-line. The positivity proved above implies that `k1^2` is
strictly convex and `k2^2` is convex. Their sum minus the constant `R^2` is
strictly convex. Compactness and continuity give existence of a minimizer;
strict convexity gives uniqueness.

### A differential form useful for later angle analysis

Inside the radical interval let

    p = (2-u)*V / (U*(2-v)) > 0.

Differentiating (1) gives

    v'(u) = -p.

The unique interior position minimizer therefore satisfies exactly

    k1 * (s + c*u/r) = k2 * p * (c + s*v/w).                (6)

No numerical stationarity hypothesis is used here. It is simply the
necessary and, by strict convexity, sufficient first-derivative equation.

If `sqrt(13)/2 <= R < 2`, this minimizer is interior for every allowed tilt.
For `t>0`, the derivative of (2) tends to `-infinity` at `u=a` because
`w -> 0`, and to `+infinity` at `u=R` because `r -> 0`. At `t=0`, the latter
limit still excludes `u=R`. To exclude the other endpoint, use the symmetric
point

    m = 2 - sqrt(R^2-9/4),      u=v=m.

Here `m<=1`, `r=w>=3/2`, and `v'(m)=-1`. At tilt zero,

    (1/2)*dF/du at u=m
       = (3-r)*m/r - (1+m)
       = 3*m/r - 2*m - 1 <= -1 < 0.

Strict convexity then puts the minimizer strictly to the right of `m`, so
it cannot equal the left endpoint. This proves the assertion, including the
whole neighborhood of the proposed sharp radius.

## 3. The remaining angle problem is one real variable

For `sqrt(13)/2 <= R < 2`, denote the unique interior minimizer of Lemma 2 by
`u_R(t)` and define

    M_R(t) = F(R^2,-u_R(t),t).

The second derivative `F_uu` is strictly positive in the open domain (the
proof above gives a strictly positive contribution from `k1`), so the
implicit-function theorem applies to (6). Thus `u_R(t)` is smooth in the
open tilt interval and has smooth local extensions at either endpoint.
The entire five-corner feasibility problem is equivalent to

    M_R(t) <= 0 for some t in [0,pi/4].

The envelope identities are

    M_R'(t) = F_t,
    M_R''(t) = F_tt - F_ut^2/F_uu,                          (7)

with the right sides evaluated at the unique minimizing position.
Consequently a human replacement of the existing full-domain certificate
can focus entirely on the sign changes of `M_R'`, or on the Schur complement
in (7). Proving joint convexity of `F` on its entire rectangle is unnecessary
and, in fact, is a stronger assertion than these lemmas provide.

For direct use,

    (1/2)*F_t = k1*((r-1)*s+u*c) - k2*(v*s+(w-1)*c).       (8)

Combining (6) and (8), every interior stationary pair with `h=tan(t)` obeys

    p*(1+h*v/w)*(u+h*(r-1))
       = (h+u/r)*((w-1)+h*v).                              (9)

This is a quadratic equation in `h` once the position is fixed. Equation
(9) is necessary when both partial derivatives vanish; by itself it does
not assert either partial derivative is zero. The original ratio `k1/k2`
in either (6) or (8) must also be retained.

## 4. An explicit quartic for optimizing the tilt at fixed position

This complementary elimination works at any fixed feasible `R,u`, including
a boundary position. Put

    z = tan(t/2),       D = 1+z^2,
    A0 = 3-r,          A1 = 2*u,       A2 = 1+r,
    B0 = 1+v,          B1 = -2*(w-1),  B2 = 1-v.

Then

    D*k1 = A0+A1*z+A2*z^2,
    D*k2 = B0+B1*z+B2*z^2.

Write

    N(z) = (A0+A1*z+A2*z^2)^2
         + (B0+B1*z+B2*z^2)^2 - R^2*(1+z^2)^2
         = n0+n1*z+n2*z^2+n3*z^3+n4*z^4,

where explicitly

    n0 = A0^2+B0^2-R^2,
    n1 = 2*(A0*A1+B0*B1),
    n2 = A1^2+B1^2+2*(A0*A2+B0*B2)-2*R^2,
    n3 = 2*(A1*A2+B1*B2),
    n4 = A2^2+B2^2-R^2.

Since `F=N/D^2`, differentiation gives

    D^3*F_z =
        n1 + (2*n2-4*n0)*z + 3*(n3-n1)*z^2
        + (4*n4-2*n2)*z^3 - n3*z^4.                      (10)

The fifth-degree terms cancel exactly. Thus every minimum over
`0<=t<=pi/4` at this fixed position occurs at `z=0`, at `z=sqrt(2)-1`, or at
a root of the explicit quartic (10) in between. If the quartic happens to
vanish identically, `F` is constant in the tilt and either endpoint already
supplies the minimum. This is a complete algebraic alternative to an angle
grid for the fixed-position subproblem.

## 5. Audit: what has and has not become a human proof

Established analytically in this note:

- The complete radical domain is one explicit compact interval.
- Its left/right exchange is an exact decreasing involution.
- Every fixed tilt has one and only one globally minimizing position.
- Near the proposed radius that position is interior and smooth in the tilt.
- The remaining global family problem is the one-variable envelope `M_R`.
- Fixed-position tilt minimization reduces to an explicit quartic and two
  endpoints; no interval box cover is involved in these reductions.

Still not established by these lemmas:

- A human proof that `M_R` has only the one candidate minimum, or that
  `M_R(t)>=0` at the candidate radius for every tilt.
- A human replacement of the existing contraction proof identifying the
  exact stationary root with the stated tiny rational isolating box.
- An unrestricted reduction from every eight-square packing to this
  five-corner chain.

The pre-existing full-domain certificate remains valid within its stated
conditional scope; none of its outputs is silently upgraded here to a
pen-and-paper argument. The immediate analytic target is a sign theorem
for (7)-(9), with the unique-position lemma removing the need to reason
about multiple position branches.
