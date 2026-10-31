# Independent review: R0 weighted-Cauchy scalar reduction

Date: October 25, 2026.

**Outcome: PASS at hand-proof and exact-arithmetic scope.** This is a
separate source, algebra and domain review of
`ABC_R0_WEIGHTED_CAUCHY_REDUCTION.md` and
`ABC_R0_WEIGHTED_CAUCHY_CHECK.py`. The proposed replacement proves the
same whole-angle, unbounded-force-ratio scalar lemma used in
`ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md`. No additional physical
assumption is introduced. No Lean build or CI was run.

## 1. The entire small-ratio rectangle is genuinely table-free

I independently expanded both squared quotients. With the notation of
the source,

    p^2/a = a+dx+d^2x^2/(4a),
    q_s^2/b = b+dx(e+d)/e+d^2x^2(e+d)^2/(4e^2b).

Using d^2+e^2=1 gives exactly the two identities in its Section 2.
The discarded first residual is nonnegative. The second residual is
at most x^2/2, because d^2<=1/2, (e+d)^2<=2, e^2>=1/2 and b>=1.
The bound e+1/e<=3/sqrt(2) holds on e in [1/sqrt(2),1]. Thus the
two square-root comparisons have the correct directions. All quantities
being square-rooted or divided by are strictly positive.

For the resulting g(d), differentiation gives exactly

    g''(d)=x^2[B^(-3/2)-K A^(-3/2)]/4<=0,

because B>=A and K>1. Concavity therefore permits a lower bound by the
smaller endpoint value on the complete closed angle interval. The x=0
linear case is retained.

I checked both endpoint derivative estimates. For sqrt(A), the positive
quadratic convexity quantity is 4-r^2=7/2; its largest derivative on
[0,1] is sqrt(2-d)/2 at x=1. For sqrt(B), the quantities at d=r and
d=-r are respectively 8 and 2, so their smallest derivatives are r
and 2r at x=0. The comparison

    sqrt(2-r)<r+1/2

is equivalent to 2r>5/4; the other squared reserve is r+1/4>0.
Both monotonicity signs in the source are therefore strict.

The four rational square-root bounds at x=1 follow directly from
7/10<r<71/100, with positive sides before squaring. Their arithmetic
gives exactly 1119/4000 and 423/5000. The complete original scalar
expression is consequently greater than 423/5000 on 0<=x<=1,
|d|<=1/sqrt(2). No coefficient certificate or sampled configuration
is used in this part.

## 2. The large-ratio implication has no hidden sign assumption

For x>=1 the comparison weight satisfies

    rho=3/10-d/10-1/(8x)>3/10-3/40-1/8=1/10.

It is an auxiliary algebraic weight and does not replace an original
positive force or contact mean. Expanding the square

    (sqrt(rho)*q_s/sqrt(b)-t_s/sqrt(rho))^2

gives exactly the difference in the source's weighted-Cauchy inequality.
It is valid for both signs of t_s. If W>0, the strictly positive number
Kp/sqrt(a) exceeds |q_s/sqrt(b)+t_s|, which is at least
q_s/sqrt(b)+t_s. This proves the original strict scalar target, with no
assumption about that latter expression's sign.

## 3. Independent global denominator verification

Write D=Dn and E=En. Substituting the source's rational formulas directly,

    W = K^2 pp^2/(D aa)
        -(rd+rn)qq^2/(x D^2 E^2 bb)
        -(rd+rn)tt^2/(rn D^2).

Multiplication by M=x D^2 E^2 rn aa bb gives, term by term,

    M W = K^2 pp^2 bb E^2 rn rd
            -(rd+rn)rn qq^2 aa
            -(rd+rn)x tt^2 aa bb E^2 = J.

This is the full rational identity, not a check at selected values.
On the physical large-ratio domain, every factor of M is positive:
x>=1, D>0, E>0, aa=Da>0, bb=Db>0, and rn=rd*rho>0.
The source correctly uses the larger z rectangle only for a polynomial
positivity statement. It does not import unproved physical assumptions
from that enlargement.

## 4. Independent reconstruction of every coefficient and inverse

I wrote a separate dense bivariate rational-arithmetic implementation;
it did not call the production sparse-polynomial constructors to build
its own J. It reconstructed the polynomial directly from the displayed
definition and obtained degree (8,14), with precisely 128 nonzero power
coefficients. All 128 agree exactly with the production polynomial.

The independent implementation formed the reciprocal polynomial by
explicit multiplication of powers of 1-u. It then applied the entire
reverse substitution by multiplying x^(8-k)(x-1)^k and recovered every
coefficient of J exactly.

For the two rectangles it used explicit polynomial substitution and a
different Bernstein conversion: lower-triangular elimination against
the fully expanded one-variable Bernstein power bases, first in one
variable and then the other. This is independent of the production
direct binomial-sum formula. It reconstructed all 270 coefficients and
verified

- all 135 coefficients on [0,3/4] x [-5/12,5/12] exceed 1/200;
- all 135 coefficients on [3/4,1] x [-5/12,5/12] exceed 3/500.

In both cases, explicit expansion of the complete tensor Bernstein
basis recovers the entire transformed ordinary polynomial. Every
independently obtained Bernstein coefficient also agrees exactly with
the production formula. These are exact Fraction comparisons and full
identities; no floating-point pose or finite sampling supplies a sign.

The two closed rectangles cover every finite x>=1 after
u=1-1/x. Their common interface, u=0, the compactified endpoint u=1,
and both original physical angle endpoints are included. The small
ratio theorem includes x=1 as well. No original force-ratio tail or
boundary remains unproved.

## 5. Acceptance and precise reduction

The scalar replacement is accepted. It retains the same inequality
for every x>=0 and every |d|<=1/sqrt(2), so both genuine applications
in the original R0 block-pressure theorem remain valid without changing
its pressure reserve, angle interval, original forces, true degrees,
circle masks, owner choices, contact means, or completion squares.

The proof now needs 270 coefficient signs instead of 1,559: 1,289
fewer signs, a reduction of about 82.7%. It uses one polynomial and
two rectangles instead of three polynomials and seven rectangles.
The entire x<=1 region has no computational certificate. The x>=1
region still has an explicit finite exact-arithmetic certificate, so
this review does not call the complete R0 scalar proof table-free.

This replacement closes no new geometric case by itself and changes
no existing gate identifier or count. The original whole-ABC assembly
requires its separately saved source review. The unrestricted nine-square
bound, equality classification, older prerequisite-chain audit and Lean
verification are not asserted proved here.
