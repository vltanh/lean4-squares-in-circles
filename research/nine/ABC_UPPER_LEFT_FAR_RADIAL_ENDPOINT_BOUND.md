# A uniform rational bound at the far-radial beta endpoint

Date: October 25, 2026.

**Status: complete scalar endpoint lemma; author, separate independent
reviewer and root full saved-source reviews passed. See
REVIEW_FAR_RADIAL_ENDPOINT_2026_10_25.md and the full accepted join in
REVIEW_ABC_FAR_RADIAL_AND_UUS_JOIN_2026_10_25.md.** This source proves the exact
endpoint bound needed after a separate monotonicity proof for a(beta,q).
It does not by itself prove that monotonicity, the whole ABC return, or
any roadmap gate.

Retain the original far-radial chart of
ABC_UPPER_LEFT_FAR_RADIAL_DOMAIN_WORKING_2026_10_25.md, with true
H4/A2/B2/C2, every original force, all original applications, and no
physical HB chord. Put

    q0=6241/1600 <= q <= 1105/256,
    K=sqrt(q-1/4), d=K-1.

The original strict far-radial interval has 3/2<beta<K. The endpoint
beta=K below is a scalar comparison coordinate only. Its degeneracies
are not assigned to any original packing body or application.

## 1. Exact endpoint expressions

At beta=K the continuous scalar formulas of that chart give

    H_B=1/2, M=d,
    t=(d^2-1/4)/(d^2+1/4),
    L=K*d/(d+t).

Define

    Rpoly(d)=d(2d+1)^2, T(d)=Rpoly(d)-1,
    A(d)=2d^2 Rpoly(d)/T(d)^2.

The exact endpoint identities are

    L=d+2d/T,
    a_end=1/2+(K^2-L^2)/2=d+1-A,
    b_end^2=q-a_end^2=1/4+2(d+1)A-A^2.                 (1)

For the first identity, the denominator of L after clearing d^2+1/4 is

    4d^3+4d^2+d-1=T,

and its numerator is d(d+1)(4d^2+1)=d(T+2). The remaining identities
follow by direct expansion, using T+1=Rpoly.

**Endpoint theorem.** For every q in the original radius interval,

    a_end>3/2,
    b_end^2>81/64.                                    (2)

## 2. A single enlarged scalar interval

The original radius window gives

    9/10<d<61/60<11/10.

Indeed q0-1/4=5841/1600>(19/10)^2, while
q-1/4<=1041/256<(121/60)^2. It is therefore enough to prove (2) on the
single larger interval 9/10<=d<=11/10.

On this interval T>0. Logarithmic differentiation of the positive A
gives exactly

    -A'/A = [(2d-1)Rpoly+10d+3]/[d(2d+1)T] > 0.      (3)

Thus A decreases. Its exact initial value satisfies

    A(9/10)=178605/573049<1/3,

the integer reserve being 573049-3*178605=37234>0. Consequently

    a_end=d+1-A>9/10+1-1/3=47/30>3/2.                (4)

We also have the stronger uniform derivative comparison

    -A'/A>2/3.                                       (5)

After multiplication by the positive denominator in (3), (5) is
equivalent to positivity of

    3[(2d-1)Rpoly+10d+3]-2d(2d+1)(Rpoly-1)
      =(-4d^2+4d-3)Rpoly+4d^2+32d+9.                (6)

Every bound in the following estimate holds on the entire enlarged
interval:

    Rpoly<=1408/125,
    4d^2-4d+3<=86/25,
    4d^2+32d+9>=1026/25.

The first and third expressions increase for positive d. The second
increases for d>=1/2. Its negative sign in (6) is handled explicitly.
Therefore the expression in (6) is at least

    1026/25-(86/25)(1408/125)=7162/3125>0.             (7)

This proves (5) without an interval table or a numerical extremum.

## 3. The endpoint b square decreases throughout that interval

Differentiating the last expression in (1), and using a_end=d+1-A,
gives

    (b_end^2)'=2A+2a_end A'
              =2A[1+a_end(A'/A)]<0,                 (8)

because A>0, a_end>3/2 and A'/A<-2/3. Thus a single rational endpoint
controls the complete interval. At d=11/10,

    T=1283/125,
    A=425920/1646089,
    b_end^2-81/64
      =721591680879/173414975738944>0.                (9)

This proves (2). The enlarged endpoint d=11/10 is outside the original
radius interval, which is harmless for this scalar monotonicity bound.
No contained unit is moved to it, and no physical feasibility is claimed
there.

The polynomial derivative identity (6), the endpoint identities (1),
and every rational comparison in (3)--(9) were checked by direct
expansion and exact Fraction arithmetic. No pose mesh or generated
coefficient certificate is used.

## 4. Exact conditional use in the original far-radial family

If a separate whole-domain proof establishes

    a(beta,q)<=a(K,q)=a_end
    for the entire original 3/2<beta<K interval,

then every original positive a satisfies

    b^2=q-a(beta,q)^2 >=q-a_end^2=b_end^2>81/64,
    b>9/8.                                           (10)

This conditional deduction changes no force, normal, mean, physical
mask, or original offset. It does not use a degree-two equation at H
or introduce a physical H/B contact. The two original genuine B and C
degrees remain two, with all radial C corner-weight endpoints retained.

The separate monotonicity premise in this section is indispensable;
this endpoint computation alone is not a proof of (10) for the whole
prefix. Neither (10) nor this source alone proves the remaining root
projection or block-pressure inequalities. No gate or accepted count
changes here, and no Lean compilation or CI was run.
