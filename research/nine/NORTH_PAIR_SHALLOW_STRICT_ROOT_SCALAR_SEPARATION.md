# An exact scalar separation bound for the shallow strict North pair

Date: October 27, 2026.

**Status: complete exact hand inequality with a finite rational
coefficient certificate, submitted for full root and separate
independent review.** The certificate uses no numerical sample.
The complete identities, interval maps and coefficient rule are
given below so every positivity claim is an exact rational check.

Put

    Q=1105/256, a=9/16, K=121/1800,
    F(x)=sqrt(Q-(2-x)^2)=sqrt(a^2+4x-x^2).

## 1. The complete scalar statement

Suppose

    0<w<1/7, 0<v<13/50,
    c,s>0, c^2+s^2=1, c/s<1/4,
    v^2+w^2+2wc<K.                                  (1)

Then both strict inequalities hold:

    F(v)+s*F(w)+c*(1-w)<1+s,                         (2)

    s*[1-F(v)]-c*(1-v)>F(w)-1.                       (3)

These are inequalities on the original scalar data; no square,
circle corner or contact mean is reassigned by this lemma.

Let

    S=K-w^2-2wc.

By (1), 0<v<sqrt(S)<=sqrt(K)<13/50. The function F is
strictly increasing on this interval. Set

    B=1+s-s*F(w)-c*(1-w),
    p=c/s,
    B1=1+[1-F(w)-c]/s.

Inequality (2) follows if F(sqrt(S))<B. For (3), the
function F(x)-p*x is strictly increasing on [0,sqrt(K)]:
its derivative is

    (2-x)/F(x)-p> (87/50)/(25/12)-1/4>0.

Thus it suffices to prove F(sqrt(S))-p*sqrt(S)<B1.

We prove both comparisons exactly below.

## 2. Rational coordinates on a closed rectangle

Use the actual scalar w to set

    u=[F(w)-a]/w.

Since F is strictly concave, with F''=-Q/F^3<0,
its secant slope u decreases with w. Hence

    129/50<u<32/9.                                  (4)

For the upper bound use F'(0)=2/a=32/9. For the lower bound
use w<1/7 and the exact positive comparison

    F(1/7)^2-[a+129/350]^2=261/490000>0.

The defining circle identity gives the rational formulas

    D=1+u^2,
    W=4-(9/8)u,
    V=9/16+4u-(9/16)u^2,

    w=W/D, F(w)=V/D.                                (5)

Also use the actual half-angle parameter

    z=c/(1+s),
    E=1+z^2, J=1-z^2,
    c=2z/E, s=J/E, p=2z/J.

The original c/s<1/4 gives

    0<z<1/8.                                        (6)

We will check positivity on the larger closed rectangle

    129/50<=u<=32/9, 0<=z<=1/8.                       (7)

Throughout (7), W>=0 and 0<=W/D<1/6. Indeed the rational
function in (5) decreases for u>=129/50, and its value even
at u=5/2 is 19/116<1/6. Thus 0<F(w)<1 throughout the
rectangle. All denominators D,E,J are strictly positive.

For the original scalar data S>0. The following simple
bounds ensure that every later squaring is legitimate:

    B>1-c>=49/65>a,
    B1>1-p>=47/63>a,
    B1<1+1/s<=128/63,
    4-2B1*p>4-4096/3969>0.                           (8)

Here z<=1/8 gives c<=16/65, s>=63/65 and p<=16/63.
Only the original S>0 is used in the squaring steps; the
coefficient certificate itself will cover all of (7).

## 3. Two explicit rational polynomials

Define the following polynomials in u,z, using (5)--(6):

    N=2D-J*V-2z*(D-W),
    A=K*D^2*E-W^2*E-4z*W*D,

    L=N^2-a^2*D^2*E^2+A*E,
    P_E=L^2-16*A*D^2*E^3;                            (9)

    N1=2D-E*V-2z*D,
    L1=N1^2-a^2*D^2*J^2+A*E,
    M1=4*(D*J^2-z*N1),
    P_J=E*L1^2-A*M1^2.                              (10)

All coefficients are rational. Their bidegrees in (u,z) are
(8,8) and (8,10), respectively. Direct substitution gives

    S=A/(D^2*E),
    B=N/(D*E),
    B1=N1/(D*J),

    B^2-a^2+S=L/(D^2*E^2),

    B1^2-a^2+(1+p^2)*S=L1/(D^2*J^2),

    4-2B1*p=M1/(D*J^2).                              (11)

Consequently P_E and P_J are precisely the positive-denominator
numerators of the two squared comparisons we need.

The following section proves

    P_E>0 and P_J>0 throughout (7).                  (12)

## 4. Complete exact positive-coefficient certificate

For integers n>=0 define

    B_i^n(x)=binom(n,i)*x^i*(1-x)^(n-i).

Every such basis polynomial is nonnegative on [0,1], and
their sum over i is one. Thus a bivariate polynomial with
strictly positive coefficients in the product of these
bases is strictly positive on the whole closed unit square,
including all edges and corners.

For P_E use the two u intervals

    I_0=[129/50,2761/900],
    I_1=[2761/900,32/9].

For P_J use the single interval

    I=[129/50,32/9].

For each interval [l,h], substitute

    u=l+(h-l)x, z=y/8, 0<=x,y<=1.

Expand P_E in the product basis B_i^8(x) B_j^8(y),
and P_J in B_i^8(x) B_j^10(y).
The following integers are lower bounds for every coefficient
in the indicated row i, with the full column range j retained:

| i | P_E on I_0, all 0<=j<=8 | P_E on I_1, all 0<=j<=8 | P_J on I, all 0<=j<=10 |
|---:|---:|---:|---:|
| 0 | 35 | 132 | 35 |
| 1 | 210 | 57 | 385 |
| 2 | 425 | 107 | 690 |
| 3 | 601 | 343 | 595 |
| 4 | 684 | 845 | 771 |
| 5 | 636 | 1716 | 1755 |
| 6 | 408 | 3093 | 4363 |
| 7 | 207 | 5148 | 10017 |
| 8 | 132 | 8107 | 21148 |

For completeness, the exact coefficient rule specifying this
finite certificate is the following. If the substituted polynomial is

    sum_{k,l} a_kl*x^k*y^l,

then its coefficient in row i, column j of bidegree (n,m) is

    b_ij=sum_{k<=i,l<=j}
      a_kl * binom(i,k)/binom(n,k)
           * binom(j,l)/binom(m,l).                  (13)

Equations (5), (9), (10), the three displayed interval maps and
(13) determine every rational coefficient without any hidden
choice or approximation. The table is obtained by expanding
these explicit products and rounding each row minimum downward
to the displayed integer. Every resulting lower bound is positive.

Two exact minimum checks, useful for reproducing the arithmetic,
are

    min coefficients of P_E on I_0
      =1135083673703309156569/31640625000000000000;

    min coefficients of P_E on I_1
      =21360547852571065940500701449008187
         /374390624262448742400000000000000.

The first fraction is also the minimum for P_J on I.
Both exceed 35, and the second exceeds 57.
This is a finite rational coefficient identity followed by
nonnegativity of the displayed elementary basis polynomials.
It proves (12) on the full intervals, not merely at sampled
points. The shared u endpoint belongs to both closed intervals.

## 5. Recovering the two strict radical inequalities

By (8), B^2-a^2+S>0. Equations (9), (11), (12) imply

    (B^2-a^2+S)^2>16S,

so B^2-a^2+S>4sqrt(S). Therefore

    B^2>a^2+4sqrt(S)-S=F(sqrt(S))^2.

Both sides to be square-rooted are positive. Thus
F(sqrt(S))<B, proving (2).

For the second comparison, (8) likewise gives

    B1^2-a^2+(1+p^2)S>0,
    4-2B1*p>0.

Equations (10)--(12) imply

    B1^2-a^2+(1+p^2)S
       >(4-2B1*p)*sqrt(S).

Rearranging yields

    [B1+p*sqrt(S)]^2
       >a^2+4sqrt(S)-S=F(sqrt(S))^2.

Again all square roots and factors have their stated positive
signs, so F(sqrt(S))-p*sqrt(S)<B1. The monotonicity verified
in Section 1 transfers this to v, giving

    F(v)-p*v<B1.

Multiplying by the positive s and substituting B1 proves (3).

This completes the exact scalar lemma. The proof uses only
the inequalities in (1), elementary radical algebra, and the
fully specified finite rational coefficient certificate.
No numerical search, fitted polynomial, grid of test points
or changed physical pose is a premise.
