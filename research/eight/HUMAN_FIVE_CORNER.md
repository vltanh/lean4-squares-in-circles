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
They also give the exact zero-tilt optimum, an analytic strict improvement
by tilting, and a global least-root polynomial characterization of the sharp
family radius. They do not identify that least root with the previously
isolated candidate. That identification is still supplied only by the
existing computational certificate.

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

## 5. A global curvature inequality in the tilt

### Lemma 3

Throughout the entire radical domain, for every `25/16 < R < 2` and
`0 <= t <= pi/4`,

    F_tt + 4*F > 91/45.                                    (11)

This is a global analytic inequality, including positions far from the
candidate. In particular, at every point with `F<=0`, one has `F_tt>0`.

#### Proof

Let `k=(k1,k2)` and `d=(2,1)`. Direct differentiation gives

    k_tt = d-k.

Moreover the sum of the squared lengths of the two orthogonal tilt
projections is

    |k_t|^2 + |k-d|^2
       = (r-1)^2+u^2+v^2+(w-1)^2
       = 2*R^2+2-2*(r+w).

Both terms on the left are needed in this identity. Combining it with
`F=|k|^2-R^2` gives

    F_tt/2 + 2*F = E,
    E = 6*k1+3*k2-3-2*(r+w).                               (12)

The elementary circle bounds

    r <= 2-u^2/4,       w <= 2-v^2/4

follow by squaring, using `R<2` and `0<=u,v<=R`. Substitution into (12)
gives

    E >= 4+(u^2+v^2)/2 + c*A + s*B,
    A = 3*u^2/2 + 3*v - 6,
    B = 3*v^2/4 + 6*u - 3.                                 (13)

The top span forces `B>0`. Indeed weighted Cauchy-Schwarz and `U+V=3`
give

    3 <= U^2+V^2/2
      < 4*u-u^2 + 2*v-v^2/2,

where the strict inequality uses `R^2<4` in both circle equations.
Rearranging shows

    B > (3/2)*(u^2+(v-1)^2) > 0.                            (14)

If `A>=0`, (13) gives `E>=4`. If `A<0`, use `c<=1`, `s>=0`, and (14)
to obtain

    E >= -2+2*u^2+v^2/2+3*v.                               (15)

Put `S=u+v`. Concavity of `x |--> sqrt(R^2-(2-x)^2)` and `U+V=3` imply

    S >= 4-2*sqrt(R^2-9/4) > 4-sqrt(7) > 4/3.

Completing the square gives the exact identity

    -2+2*u^2+v^2/2+3*v
       = (5/2)*(v-(4*S-3)/5)^2
         + (4*S^2+24*S-29)/10.

The last polynomial increases for `S>=0`; at `S=4/3` its value is `91/90`.
Thus (15) is strictly greater than `91/90`. This also holds in the earlier
case `E>=4`. Equation (12) proves (11).

### Corollary: the feasible tilts at a fixed position form an interval

Let

    theta = 2*(t-pi/8),       xi = tan(theta),
    G(xi) = F(R^2,-u,t)/cos(theta).

Here `-1<=xi<=1` and `cos(theta)>0`, including both endpoints. Twice
applying the chain rule gives

    G''(xi) = cos(theta)^3 * (F_tt+4*F)/4 > 0.

Thus `G` is strictly convex on the entire transformed angle interval. Its
nonpositive set is an interval, and multiplying by the positive cosine
does not change signs. This proves the corollary.

This is a statement for one fixed position. Separate convexity in position
and transformed tilt does **not** by itself prove joint convexity, or
convexity of the minimized envelope `M_R`. In particular it is not yet a
replacement for the sharp conditional lower-bound certificate.

## 6. Both tilt endpoints can be excluded analytically

### Lemma 4: the endpoint `t=pi/4` has positive envelope derivative

For `sqrt(13)/2 <= R < 2`,

    M_R'(pi/4) > 0.

Consequently `pi/4` cannot minimize the complete five-corner problem.

#### Proof

At the symmetric position `u=v=m`, one has `r=w` and `v'(u)=-1`.
At tilt `pi/4`, `k1-k2=1` and

    k1_u = -k2_u = (1+m/r)/sqrt(2).

Therefore `F_u(m,pi/4)>0`. Lemma 2 puts the unique minimizing position
strictly to the left of `m`; the decreasing involution then gives `u<v`
at that minimizer.

For a variable `x` in the open radical interval define

    rho(x) = sqrt(R^2-x^2),
    g(x) = sqrt(R^2-(2-x)^2),
    Phi(x) = rho(x)*g'(x)*(x+rho(x)-1)/(x+rho(x)).            (16)

This function is positive and strictly decreasing. To prove that assertion,
write `h=x+rho(x)>R>1`. Logarithmic differentiation yields

    Phi'(x)/Phi(x)
       = -x/rho(x)^2
         - R^2/((2-x)*g(x)^2)
         + (1-x/rho(x))/(h*(h-1)).                         (17)

For any `0<a<R`, the maximum of `a*(R^2-a^2)` is
`2*R^3/(3*sqrt(3))`. With `a=2-x`, this implies

    R^2/((2-x)*g(x)^2) >= 3*sqrt(3)/(2*R).

Also `h>=R` and `1-x/rho(x)<=1`, so the last term in (17) is at most
`1/(R*(R-1))`. Since `R>25/16` implies

    1/(R-1) < 16/9 < 3*sqrt(3)/2,

equation (17) is strictly negative.

It remains to connect (16) to the envelope derivative. At its minimizing
position, equation (6) at tilt `pi/4` says

    k1*(u+r)/r = k2*p*(v+w)/w,
    p = g'(u)/g'(v).

Substitute this equality into (8). The sign of `F_t`, and therefore the
sign of `M_R'`, is precisely the sign of

    Phi(u)-Phi(v).

All factors cancelled in taking this sign are positive: `k2,r,w,g'(v)`
and `u+r,v+w` are positive. Since `u<v` and `Phi` strictly decreases,
this difference is positive, as required.

### Lemma 5: the endpoint `t=0` is excluded near the candidate radius

For the entire rational squared-radius interval

    3915/1000 <= R^2 <= 979/250,                            (18)

one has

    99/100 < u_R(0) < 101/100,
    M_R'(0) < -1/10.                                       (19)

The previously isolated candidate squared radius is inside (18). This
lemma uses only the following displayed rational bounds and square
comparisons; it does not depend on running the isolation program.

#### Proof

At zero tilt put

    D0(u) = F_u/2 = (3/r-1)*u - (1+v)*p,
    p = (2-u)*V/(U*(2-v)).

The following bounds follow directly from (18) and the four circle
radicals. All terminating decimals in this table denote exact rationals.

| Fixed u | r | U | V=3-U | 2-v | v |
| --- | --- | --- | --- | --- | --- |
| 0.99 | [1.713,1.714] | [1.701,1.702] | [1.298,1.299] | [1.492,1.494] | [0.506,0.508] |
| 1.01 | [1.701,1.702] | [1.713,1.714] | [1.286,1.287] | [1.502,1.505] | [0.495,0.498] |

For example, at `u=0.99`, `r^2` lies in `[2.9349,2.9359]`, between the
squares of `1.713` and `1.714`. Also `(2-v)^2` lies in
`[3.915-1.299^2, 3.916-1.298^2]`, which is between the squares of `1.492`
and `1.494`. The other table entries follow in the same order by these
exact square comparisons.

Substitution gives the explicit rational inequalities

    D0(0.99)
      <= (3/1.713-1)*0.99
         - 1.506*(1.01*1.298)/(1.702*1.494)
      < -3/100,

    D0(1.01)
      >= (3/1.702-1)*1.01
         - 1.498*(0.99*1.287)/(1.713*1.502)
      > 1/50.

Each final comparison is a rational multiplication with positive
denominators. Strict convexity now puts the minimizer between these
positions.

Throughout that whole position interval, the same radical comparisons give

    r >= 1.701,      v >= 0.495,      w >= 1.912.

For the last bound use `v<=0.508` and
`w^2 >= 3.915-0.508^2 > 1.912^2`. At tilt zero, (8) therefore gives

    M_R'(0)/2
       = (3-r)*u - (1+v)*(w-1)
       <= 1.299*1.01 - 1.495*0.912
       = -0.05145 < -1/20.

This proves (19).

### Consequence

For every radius in (18), the minimum of the five-corner defect over both
variables is attained at an interior position and an interior tilt. Hence
all global minima obey the stationary equations. This is an analytic
endpoint reduction; uniqueness of the interior tilt remains to be proved.

## 7. An exact endpoint optimum and a least-root characterization

The following results supply an existence and global selection rule for the
sharp five-corner radius without using the candidate's tiny isolating box.
They do not identify the selected root with that candidate.

### Lemma 6: an elementary lower bound for every five-corner chain

Every chain in the stated angle range satisfies

    R >= 11/(4*sqrt(2)) > sqrt(13)/2.                       (20)

#### Proof

Orient the five consecutive edge requirements around
`P1,P2,P3,P4,P5,P1`. Their unit normals are

    n1=(0,1),     n2=(-1,0),    n3=(0,-1),
    n4=(s,-c),    n5=(c,s).

Summing all five inequalities with multiplier one, then applying the disk
support bound to each vertex, gives

    B <= R*D,
    B = 10+c+s,
    D = 3*sqrt(2)+sqrt(2-2*s)+sqrt(2-2*c).                  (21)

Indeed the coefficient of `Pi` in the sum is `n_(i-1)-n_i`, with cyclic
indices, and each corresponding dot product is at most the coefficient's
length times `R`. The displayed `D` is the exact sum of these five lengths.

Put `h=t/2`, `b=pi/8`, and `a=sqrt(2)-1=tan(b)`. Then

    B = 10+cos(2*h)+sin(2*h),
    D = sqrt(2)*(3+cos(h)+a*sin(h)).

The desired inequality `B/D >= 11/(4*sqrt(2))` is equivalent to

    J(h) = 7+4*cos(2*h)+4*sin(2*h)
             -11*cos(h)-11*a*sin(h) >= 0.

Here `J(0)=0`. With `delta=b-h`, differentiation and the angle addition
formulas give

    J'(h) = sin(delta)*(16*sqrt(2)*cos(delta)-11/cos(b)).

For `0<=delta<=b`, the factor in parentheses is at least

    (16*sqrt(2)*cos(b)^2-11)/cos(b)
       = (8*sqrt(2)-3)/cos(b) > 0.

Thus `J` increases on `[0,b]`, proving (20). The comparison with
`sqrt(13)/2` follows by squaring: `121/32 > 13/4`.

### Lemma 7: the exact zero-tilt radius

Among all five-corner chains with `t=0`, the smallest radius is

    R0 = sqrt(2257)/24,       q0 = 2257/576.                (22)

A nonzero tilt strictly improves this radius within the five-corner
family.

#### Proof of the exact endpoint radius

At tilt zero, combine the third and fourth projected inequalities to get

    P3.y-P5.y >= 3.

The remaining four-point requirements are

    P2.y-P1.y >= 2,     P3.y-P5.y >= 3,
    P2.x-P3.x >= 3,     P1.x-P5.x >= 3.                    (23)

Reflect in the horizontal axis and simultaneously exchange `P1` with `P2`
and `P3` with `P5`. Conditions (23) are unchanged. The coordinate-wise
average of the old and new configurations still satisfies (23), because
these constraints are linear, and still lies in the disk, because the disk
is convex. This averaged configuration has the form

    P1=(b,-h), P2=(b,h), P3=(a,k), P5=(a,-k),
    h>=1,      k>=3/2,   b-a>=3.

Consequently

    3 <= b-a <= sqrt(q-1)+sqrt(q-9/4).                    (24)

The sum of radicals strictly increases with `q`. At equality its two
summands have sum three and squared difference `5/4`, so they are `41/24`
and `31/24`. This gives exactly (22).

Equality is realized by

    P1=(41/24,-1),       P2=(41/24,1),
    P3=(-31/24,3/2),     P5=(-31/24,-3/2),
    P4=(-31/24,-1/2).

The first four displayed boundary points have squared norm `q0`; `P4` lies
strictly inside the disk. Every original five-corner inequality is an
equality. This proves the matching upper bound.

#### Proof of a strict improvement by tilting

Use the boundary parametrization, which is another valid realization at
this same endpoint optimum. Its parameters are exactly

    u=1,       v=1/2,       r=U=41/24,
    V=31/24,   w=sqrt(2113)/24,
    k1=31/24,  k2=3/2.

The fourth point in this boundary parametrization is
`P4=(-sqrt(2113)/24,-1/2)`; its different horizontal coordinate does not
change any constraint at zero tilt.

Equation (8) now gives the exact first derivative

    F_t(q0,-1,0)/2 = (134-3*sqrt(2113))/48 < 0.             (25)

The sign follows by squaring positive quantities:
`9*2113=19017 > 134^2=17956`. Thus at fixed `q0,u=1`, sufficiently small
positive tilts have `F<0`. All radicals at this configuration are strictly
positive, so continuity permits a simultaneous small decrease in `q` while
retaining `F<0`. The exact converse of the scalar reduction then supplies a
five-corner chain in a radius strictly below `R0`.

This is a strict improvement theorem for the projected family. It does not
assert that every nearby choice extends to eight disjoint full squares;
that is a separate construction check.

### Lemma 8: a globally selecting polynomial system

Let `R_hat` denote the smallest radius of any five-corner chain, allowing
all `0<=t<=pi/4`. Then the minimum is attained,

    121/32 <= R_hat^2 < 2257/576,                           (26)

and every minimizing scalar representative has an interior position and
an interior tilt. In particular `R_hat^2` is exactly the **smallest q**
selected by the following polynomial equalities and sign conditions.

Use nine real variables

    q,u,v,r,w,U,V,c,s,

with

    121/32 <= q < 2257/576,
    u,v,r,w,U,V > 0,       0 < s < c,

and impose the equations

    r^2+u^2=q,             w^2+v^2=q,
    U^2+(2-u)^2=q,         V^2+(2-v)^2=q,
    U+V=3,                c^2+s^2=1.                      (27)

Define the polynomial expressions

    k1=2-c*(r-1)+s*u,
    k2=1+c*v-s*(w-1).

The three further polynomial equations are

    k1^2+k2^2=q,                                          (28)

    k1*(s*r+c*u)*U*(2-v)*w
       = k2*V*(2-u)*(c*w+s*v)*r,                          (29)

    k1*((r-1)*s+u*c)
       = k2*(v*s+(w-1)*c).                               (30)

No interval subdivision or isolated decimal root is part of this selection
rule. The word **smallest** is essential.

#### Proof

There is at least one chain at `R0`, by Lemma 7. Restrict all five points to
the fixed disk of radius `R0`, the angle to `[0,pi/4]`, and the variable
radius to `[0,R0]`. The disk-containment inequalities and projected chain
inequalities are closed conditions in this bounded finite-dimensional
space. Hence compactness gives an attained least radius. Lemmas 6 and 7
prove (26).

At this least radius, choose the unique minimizing position for whichever
tilt occurs. By (20) and Lemma 2, that position is interior and all four
radicals are positive. The defect must equal zero. Otherwise continuity
would allow a small decrease in the radius while preserving a strictly
negative defect, contradicting minimality.

For clarity, radius monotonicity in this open domain can also be checked
directly. At fixed `u,t`,

    r_q=1/(2*r)>0,
    v_q=-3/(2*U*(2-v))<0,
    w_q=(1-2*v*v_q)/(2*w)>0.

Thus `k1_q<0`, `k2_q<0`, and

    F_q = 2*k1*k1_q+2*k2*k2_q-1 < -1.                     (31)

The tilt cannot be zero, since its sharp radius is `R0` and the true
minimum is strictly smaller. It cannot be `pi/4`: Lemma 4 would make a small
decrease in the tilt produce `F<0`, and continuity would then permit a
smaller radius. Both scalar variables are therefore interior. A strictly negative defect
at this radius would contradict its minimality, so the present point is
also a local minimum of the defect. Its first derivatives vanish, proving
(28)-(30); equation (29) is (6) multiplied by
the positive denominator `r*U*(2-v)*w`.

Conversely, every solution of (27)-(30) and the stated sign conditions is
a genuine five-corner chain. Indeed `r,w>0` and `q<4` force `0<u,v<2`;
positivity selects the four circle roots. Equation `U+V=3` then gives
exactly the radical domain of Lemma 1. The conditions `c^2+s^2=1` and
`0<s<c` select a tilt in `(0,pi/4)`, while (28) gives defect zero. The
converse construction in `FIVE_CORNER_REDUCTION.md` supplies the five
points. Its radius is necessarily at least `R_hat`.

The true minimum supplies a solution of this polynomial system, and every
solution supplies a chain. Therefore the least possible `q` in the system
is exactly `R_hat^2`, as claimed.

### Meaning of the least-root result

This is a complete global selection theorem for the conditional family,
with a polynomial characterization and a pen-and-paper proof. It still
leaves a distinct identification question: **is this least q the stationary
root previously isolated near 3.9155341375?** The existing full-domain
certificate answers yes computationally. The present argument does not
replace that last comparison by a human proof, and it does not prove that
all stationary roots in (26) coincide.

## 8. Audit: what has and has not become a human proof

Established analytically in this note:

- The complete radical domain is one explicit compact interval.
- Its left/right exchange is an exact decreasing involution.
- Every fixed tilt has one and only one globally minimizing position.
- Near the proposed radius that position is interior and smooth in the tilt.
- The remaining global family problem is the one-variable envelope `M_R`.
- Fixed-position tilt minimization reduces to an explicit quartic and two
  endpoints; no interval box cover is involved in these reductions.
- A global modified-curvature bound makes the fixed-position feasible tilt
  set an interval after an explicit change of variable.
- Both endpoint tilts are excluded near the candidate radius by fully
  displayed analytic and rational inequalities, so all global minima there
  are interior stationary points.
- The exact zero-tilt optimum is `sqrt(2257)/24`, and an explicit negative
  first derivative proves a strict improvement by nonzero tilt.
- The true sharp family radius exists and is attained at an interior
  stationary point; its square is the least q selected by (27)-(30) and
  their sign conditions.

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
