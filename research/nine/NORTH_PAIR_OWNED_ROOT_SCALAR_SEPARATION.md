# Exact scalar separation for the owned-root North pair

Date: October 27, 2026.

**Status: complete exact inequality with a finite rational coefficient
certificate, submitted for full root and separate independent review.**
This source uses the actual owned-root radius identity. It does not
import the different strict-root energy inequality.

Put

    Q=1105/256, a=9/16, e0=31/1875, d0=1+e0,
    F(x)=sqrt(Q-(2-x)^2)=sqrt(a^2+4x-x^2).

## 1. Complete statement

Suppose

    0<e<e0, 0<w<3/20, 0<v<13/50,
    c,s>0, c^2+s^2=1, p=c/s<3/10,
    X=1-e*s+w*c,
    v^2=(1+e)^2-X^2>0.                             (1)

Write z=c/(1+s) and t=z/w. The following two assertions hold.

First, if

    9/10<t<2                  when w<=1/25,
    9/10<t<3/2                when w>=1/25,          (2)

using the applicable range at the shared endpoint, then

    F(v)+s*F(w)+c*(1-w)<1+s.                        (3)

Second, if

    4/5<t<15/7,                                    (4)

then

    s*[1-F(v)]-c*(1-v)>F(w)-1.                      (5)

The original-force caller proves the appropriate ranges (2) or (4)
from its actual C2 equation. They are explicit hypotheses here.

For fixed w,c,s, the right side of the radius identity in (1)
increases strictly with e: its derivative is

    2(1+e)+2s*(1-e*s+w*c)>0.

Consequently v<sqrt(S), where

    X0=1-e0*s+w*c,
    S=d0^2-X0^2>0.

Also X0>=1-e0, so S<=4e0<169/2500 and sqrt(S)<13/50.
The function F is increasing on this whole interval.

Define

    B=1+s-s*F(w)-c*(1-w),
    B1=1+[1-F(w)-c]/s.

It suffices for (3) to prove F(sqrt(S))<B. For (5), note that

    d/dx [F(x)-p*x]=(2-x)/F(x)-p
      >(87/50)/(25/12)-3/10>0

for 0<=x<=sqrt(S). Thus it suffices to prove

    F(sqrt(S))-p*sqrt(S)<B1.                         (6)

Since w<3/20, F(w)<19/20. The original p<3/10 gives

    B>1-c>7/10>a,
    B1>1-p>7/10>a,
    B1<1+1/s<41/20,
    4-2B1*p>277/100>0.                              (7)

These signs justify every squaring below. Only the actual S>0
is needed; the coefficient certificate covers larger rectangles.

## 2. Rational coordinates and exact rectangles

Set u=[F(w)-a]/w. Strict concavity F''=-Q/F^3<0 implies
that u decreases with w. Its upper limit is F'(0)=32/9.
The exact comparison

    F(3/20)^2-[a+(51/20)*(3/20)]^2=141/160000>0

therefore gives

    51/20<u<32/9.

The circle identity gives the rational formulas

    D=1+u^2,
    W=4-(9/8)u,
    V=9/16+4u-(9/16)u^2,
    w=W/D, F(w)=V/D.                               (8)

The transition w=1/25 lies strictly between the parameters
79/25 and 19/6. Indeed (8) gives

    w(79/25)=2225/54928>1/25,
    w(19/6)=63/1588<1/25.

Thus (2) is covered by the following closed rectangles in (u,t):

    E0: [51/20,343/120] times [9/10,3/2],
    E1: [343/120,19/6] times [9/10,3/2],
    E2: [79/25,32/9] times [9/10,2].                 (9)

The first two cover the w>=1/25 range; the third covers
w<=1/25. The intentional overlap retains every transition point.
Condition (4) is covered by

    J0: [51/20,32/9] times [4/5,15/7].               (10)

All denominators used below are positive. The coefficient proof
itself does not need every point of these enlarged rectangles
to correspond to physical data.

## 3. Explicit rational polynomials

Temporarily treat u,z as independent variables and put

    E=1+z^2, J=1-z^2,
    c=2z/E, s=J/E,

    XN=(1-e0)*D+(1+e0)*D*z^2+2Wz,
    A=d0^2*D^2*E^2-XN^2,

    N=2D-JV-2z*(D-W),
    L=N^2-a^2*D^2*E^2+A,
    P_E=L^2-16*A*D^2*E^2;                           (11)

    N1=2D-EV-2zD,
    L1=N1^2-a^2*D^2*J^2+A,
    M1=4*(D*J^2-zN1),
    P_J=E^2*L1^2-A*M1^2.                            (12)

Their bidegrees in (u,z) are (8,8) and (8,12). Direct substitution
at the actual half angle z gives

    X0=XN/(DE), S=A/(D^2*E^2),
    B=N/(DE), B1=N1/(DJ),

    B^2-a^2+S=L/(D^2*E^2),

    B1^2-a^2+(1+p^2)*S=L1/(D^2*J^2),
    4-2B1*p=M1/(D*J^2).                             (13)

For the interval variable t=z/w, substitute z=tW/D and clear
the positive denominators:

    T_E(u,t)=D^8*P_E(u,tW/D),
    T_J(u,t)=D^12*P_J(u,tW/D).                      (14)

These are rational polynomials, of bidegrees (24,8) and (32,12).
Equations (8), (11), (12), (14) specify every coefficient exactly.

## 4. Full positive-coefficient certificate

For n>=0 let

    B_i^n(x)=binom(n,i)*x^i*(1-x)^(n-i).

These basis polynomials are nonnegative on [0,1] and sum to one.
For each rectangle [l,h] times [b,k] in (9)--(10), substitute

    u=l+(h-l)x, t=b+(k-b)y, 0<=x,y<=1.

Expand T_E/10^9 in the product basis B_i^24(x)B_j^8(y),
and T_J/10^12 in B_i^32(x)B_j^12(y). The table gives an
integer lower bound for every coefficient in row i, over the
entire indicated column range. A dash means that row is absent.

| i | E0, all j<=8 | E1, all j<=8 | E2, all j<=8 | J0, all j<=12 |
|---:|---:|---:|---:|---:|
|0|12|7|890|19|
|1|12|7|1141|19|
|2|12|7|1451|19|
|3|12|6|1830|18|
|4|11|6|2292|17|
|5|11|7|2853|15|
|6|10|10|3531|13|
|7|10|15|4349|15|
|8|9|23|5332|22|
|9|8|33|6509|43|
|10|7|48|7916|66|
|11|6|67|9594|86|
|12|5|92|11589|96|
|13|5|123|13957|82|
|14|4|163|16762|36|
|15|3|213|20080|40|
|16|2|274|23996|191|
|17|2|349|28612|650|
|18|2|440|34045|1691|
|19|2|550|40430|3774|
|20|3|682|47924|7655|
|21|4|841|56708|14550|
|22|5|1029|66993|26389|
|23|6|1254|79020|46204|
|24|7|1519|93071|78707|
|25|-|-|-|131165|
|26|-|-|-|214698|
|27|-|-|-|346218|
|28|-|-|-|551297|
|29|-|-|-|868416|
|30|-|-|-|1355206|
|31|-|-|-|2097639|
|32|-|-|-|3223474|

Here is the complete exact coefficient rule for reproducing the
certificate. If the substituted, normalized polynomial is

    sum a_kl*x^k*y^l,

its coefficient in row i, column j of bidegree (n,m) is

    b_ij=sum_{k<=i,l<=j}
      a_kl * binom(i,k)/binom(n,k)
           * binom(j,l)/binom(m,l).                 (15)

The four interval maps, explicit polynomial products and (15)
determine all coefficients without an auxiliary choice or numerical
approximation. Each displayed integer is the corresponding exact
row minimum rounded down. For example the unnormalized minimum
of T_E on E0 is

    381586426032083601744254664865238849237227746302587182127428458670962852562209
      /165122803181907315694208286720000000000000000000000000000000000000000,

which is greater than 2*10^9. The unnormalized minima on E1,E2,J0
are respectively greater than 6*10^9, 890*10^9 and 13*10^12.
Every coefficient is strictly positive. Thus T_E is positive on
all three complete E rectangles and T_J is positive on J0,
including every edge, corner and shared panel endpoint.

This is a finite rational polynomial identity and the elementary
nonnegativity of its basis. No sampled values or floating-point
certificate are premises of the proof.

## 5. Recover the strict radical inequalities

For the actual data, (7) and S>0 give B^2-a^2+S>0.
The positivity of T_E and the positive D imply P_E>0.
Equations (11)--(13) therefore give

    (B^2-a^2+S)^2>16S,
    B^2-a^2+S>4sqrt(S),
    B^2>a^2+4sqrt(S)-S=F(sqrt(S))^2.

Both sides are positive, so F(sqrt(S))<B. Monotonicity and
v<sqrt(S) prove (3).

For the J assertion, (7) and S>0 give both positive factors

    B1^2-a^2+(1+p^2)S>0, 4-2B1*p>0.

The positivity of T_J gives P_J>0, hence

    B1^2-a^2+(1+p^2)S>(4-2B1*p)*sqrt(S).

Equivalently

    [B1+p*sqrt(S)]^2>F(sqrt(S))^2.

All terms have their declared signs. Taking square roots gives
(6), and the monotonicity from Section 1 transfers it to v.
Rearranging proves (5).

This establishes both complete scalar assertions with the correct
owned-root radius identity and all endpoints of their stated ranges.
