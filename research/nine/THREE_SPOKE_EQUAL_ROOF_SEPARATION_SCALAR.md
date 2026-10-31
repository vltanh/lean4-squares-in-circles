# An exact separation scalar for the equal-roof three-spoke row

Date: October 28, 2026. Author: hexagon.

**Status: complete exact scalar lemma, frozen for full independent
review.** This source has no packing or force equation as a premise.
Its two continuous rectangles are certified by explicit integer
polynomial products and exact rational Bernstein coefficients.
The geometric caller must establish the whole stated domain.

## 1. Complete scalar domain and conclusion

Let a,b,p be real numbers satisfying

    a>b>0, a^2+b^2=1,
    (a-b)/(a+b)<p<b/a,
    H=b+ap<1.

Put

    t=1-H,
    Delta=b-a+p(a+b),
    J=a(1-p)+t Delta,
    theta=t Delta/J,
    v=t/(1-pH),
    rho=(1-theta)(a-bp)-theta pH.

All these expressions have their literal stated meanings; in
particular no independent relaxation of theta or v is made.

**Lemma.** The exact scalar

    D0 = [rho+1-pt+(1-pv)/sqrt(1+v^2)]/sqrt(1+p^2)

satisfies

                         D0>21/10.                 (1)

First, H<1 implies p<(1-b)/a<1. Thus 0<p<1, t>0,
Delta>0, J>0, and 0<theta<1. Also

    1-pH-t=H(1-p)>0,

so 0<v<1. All denominators below are strictly positive on the
complete actual scalar domain. None of its limiting endpoints is
discarded from the auxiliary closed rectangles used to prove (1).

## 2. A rational lower bound with the original coupling retained

Using t+H=1 and H-b=ap gives the exact identity

    rho+1-pt = S,
    S=(1-p)+(1-theta)a(1+p^2)
      =(1-p)[1+a^2(1+p^2)/J]>0.                    (2)

For every x>=0, (1+x)^(-1/2)>=1-x/2, as follows either by
convexity or by differentiating the difference. Since 0<p,v<1
and 1-pv>0, both substitutions have the correct sign. Equations
(1)--(2) therefore reduce to the strict rational comparison

    D0 >= L,
    L=(1-p^2/2)[S+(1-pv)(1-v^2/2)]>21/10.          (3)

This uses two elementary radical lower bounds, not a squared
inequality with an unverified sign. We now prove the last inequality
over the entire domain by an exact finite polynomial certificate.

## 3. Two closed rectangles cover every actual pair

Set z=b/(1+a). Then

    A=1-z^2, B=2z, D=1+z^2,
    a=A/D, b=B/D,
    M=A+B, L0=A-B,
    p0=L0/M=(a-b)/(a+b).

The positive actual domain a>b is 0<z<sqrt(2)-1<5/12.
Its other two strict upper bounds are

    q1=b/a=2z/(1-z^2),
    q2=(1-b)/a=(1-z)/(1+z),
    p0<p<min(q1,q2).                               (4)

The function q1 is strictly increasing and p0 is strictly decreasing
on 0<z<sqrt(2)-1. Their derivatives have the respective signs of
2(1+z^2)/(1-z^2)^2 and -4(1+z^2)/M^2. At z=19/100,

    p0-q1=5213921/129538521>0.

The existence of p in (4) therefore forces z>19/100.

If b<=1/2, then z<=2-sqrt(3)<27/100 and q1<=q2. Put

    p=p0+w(q1-p0), 0<w<1.                           (5L)

Every such actual point lies in the closed lower rectangle

    19/100<=z<=27/100, 0<=w<=1.                     (6L)

If b>=1/2, then z>=2-sqrt(3)>1/4 and q2<=q1. Put

    p=p0+w(q2-p0), 0<w<1.                           (5U)

Every such actual point lies in the closed upper rectangle

    1/4<=z<=5/12, 0<=w<=1.                         (6U)

Both rows retain b=1/2. The slightly enlarged rectangles may contain
points outside the original scalar domain. We prove polynomial
positivity on their entire closures, and require denominator signs
only at the original points. The comparisons for the enlargement are

    3-(173/100)^2=71/10000>0,
    (7/4)^2-3=1/16>0,
    (17/12)^2-2=1/144>0.

Thus the two rows give an exhaustive, exact continuous cover.

## 4. The complete polynomial whose sign is certified

Use the integer polynomials A,B,D,M,L0 above. For the lower row
put (N0,K0)=(B,A); for the upper row put
(N0,K0)=(1-z,1+z). In the corresponding row define

    K=M K0,
    N=L0 K0+w(N0 M-L0 K0),
    HN=B K+A N,
    TN=D K-HN,
    DN=-L0 K+M N,
    JN=A(K-N)D K+TN DN,
    VN=D K^2-N HN.                                 (7)

Here p=N/K is exactly (5L) or (5U). Direct substitution, with no
estimate, gives

    H=HN/(D K),       t=TN/(D K),
    Delta=DN/(D K),  J=JN/(D^2 K^2),
    v=TN K/VN,       1-pv=D K(K-N)/VN,
    S=(K-N)[JN+A^2(K^2+N^2)]/(K JN).               (8)

On every actual point K,JN,VN are positive: K>0, J>0, and
VN=D K^2(1-pH)>0. Therefore the exact identity

    L-21/10 = P/(20 K^3 JN VN^3)                   (9)

reduces (3) to P>0. The complete integer polynomial is specified
without an omitted term by the following products:

    E = 2 VN^3[JN+A^2(K^2+N^2)]
           +D K^2 JN(2 VN^2-TN^2 K^2),

    P = 5(2K^2-N^2)(K-N) E -42 K^3 JN VN^3.        (10)

For verification of the factors in (9), before subtracting 21/10
the denominator of L is 4 K^3 JN VN^3. The numerator is exactly
(2K^2-N^2)(K-N)E. Multiplication by five and subtraction of
42 K^3 JN VN^3 gives (9)--(10).

## 5. Full rational Bernstein certificate

For the lower rectangle substitute z=19/100+(2/25)Z, w=W.
For the upper rectangle substitute z=1/4+(1/6)Z, w=W.
Both transformed variables range independently over [0,1].

The lower P has bidegree (54,11) and 647 nonzero monomials before
the affine substitution. The upper P has bidegree (43,11) and
434 nonzero monomials. Let n be the stated first degree and
m=11. If the transformed monomial coefficients are c_(k,l), the
tensor Bernstein coefficients are exactly

    beta_(i,j) = sum_(k=0..i,l=0..j)
       c_(k,l) binom(i,k)/binom(n,k) binom(j,l)/binom(m,l).
                                                               (11)

The following table gives every row bound, with no omitted index.
Its integer entries are

    floor(10 min_(0<=j<=11) beta_(i,j)).             (12)

Consequently every lower coefficient is at least 9/10 and every
upper coefficient is at least 115/10. Positivity is strict even on
the complete closed rectangle boundaries.

| i | Lower row floor | Upper row floor |
| --- | --- | --- |
| 0 | 87 | 115 |
| 1 | 93 | 151 |
| 2 | 99 | 190 |
| 3 | 105 | 232 |
| 4 | 112 | 282 |
| 5 | 119 | 340 |
| 6 | 126 | 407 |
| 7 | 120 | 485 |
| 8 | 114 | 575 |
| 9 | 108 | 679 |
| 10 | 102 | 798 |
| 11 | 96 | 935 |
| 12 | 91 | 1092 |
| 13 | 85 | 1272 |
| 14 | 80 | 1476 |
| 15 | 75 | 1709 |
| 16 | 70 | 1973 |
| 17 | 66 | 2272 |
| 18 | 61 | 2611 |
| 19 | 57 | 2993 |
| 20 | 53 | 3425 |
| 21 | 49 | 3911 |
| 22 | 45 | 4458 |
| 23 | 42 | 5071 |
| 24 | 39 | 5759 |
| 25 | 35 | 6529 |
| 26 | 33 | 7390 |
| 27 | 30 | 8351 |
| 28 | 27 | 9422 |
| 29 | 25 | 10614 |
| 30 | 23 | 11940 |
| 31 | 21 | 13412 |
| 32 | 19 | 15045 |
| 33 | 17 | 16853 |
| 34 | 16 | 18854 |
| 35 | 15 | 21064 |
| 36 | 14 | 23504 |
| 37 | 13 | 26193 |
| 38 | 12 | 29154 |
| 39 | 11 | 32410 |
| 40 | 10 | 35986 |
| 41 | 10 | 39910 |
| 42 | 10 | 44211 |
| 43 | 9 | 48919 |
| 44 | 9 | Not in upper degree |
| 45 | 9 | Not in upper degree |
| 46 | 9 | Not in upper degree |
| 47 | 9 | Not in upper degree |
| 48 | 9 | Not in upper degree |
| 49 | 9 | Not in upper degree |
| 50 | 10 | Not in upper degree |
| 51 | 10 | Not in upper degree |
| 52 | 10 | Not in upper degree |
| 53 | 11 | Not in upper degree |
| 54 | 11 | Not in upper degree |

The products (7),(10), the exact coefficient formula (11), and all
row bounds (12) are reproduced by the self-contained checker

    certificates/three_spoke_equal_roof_separation_scalar.py
    d3db3cf5278af57cac1dd5ddd66a7af88488a4f74d031857b96bb3f3c40707d2.

It constructs the polynomials from the displayed integer products,
performs the affine substitution with fractions, computes all 660
lower and 528 upper coefficients, and checks every printed row
floor. It imports no symbolic package or cached coefficient file.
All comparisons are exact rational operations; no floating-point
decision or sampled parameter is used.

Each tensor Bernstein basis polynomial is nonnegative on the closed
unit square, and their sum is one. The strictly positive coefficient
bounds therefore imply P>0 on both complete rectangles. Equations
(9),(3) prove (1) on the entire original scalar domain.

## 6. Literal use and limitation

The lemma retains the exact relation between theta and the other
parameters. It does not assert (1) for an arbitrary mean theta or
for a relaxed unrelated v. A geometric caller must derive a>b,
the lower p bound, both strict upper p bounds, and these exact
definitions from its full original equations.

The useful radius reserve in that caller is

                  21/10-25/12=1/60>0.

This source is only an exact real-algebraic lemma. It does not by
itself close a graph family, alter an application mean, choose a
normal, or replace any original physical force.
