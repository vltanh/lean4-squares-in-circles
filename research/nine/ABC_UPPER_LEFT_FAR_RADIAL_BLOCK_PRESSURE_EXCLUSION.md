# Positive whole-block pressure excludes the entire radial-C far return

Date: October 25, 2026.

**Status: complete hand exclusion; author, root and separate independent
full saved-source, analytic/domain and direct-prerequisite reviews passed
on October 25, 2026. Both independent exact polynomial reconstructions
passed every forward/inverse identity. The complete UUS join is recorded
in REVIEW_ABC_FAR_RADIAL_AND_UUS_JOIN_2026_10_25.md.** Its full far-return theorem, joined with the earlier whole-feature
exclusions, closes the four original UUS gates named in that review.

Retain the original H--A--B--C--H cycle and intact H--X--Y--H petal,
with true H4/A2/B2/C2, all original positive pair magnitudes, original
application means, every physical square, and all three arbitrary
completion squares. The two petal tips retain their true degree-two equations. A and
B have one physical circle corner each, C has two physical circle corners
with nonnegative original weights of positive total, and H is physically
circle-clear. No physical H/B chord is assumed.

Work throughout

    q0=6241/1600 <= q=R^2 <= Q0=1105/256.

Suppose A has negative H-pressure, HA is the original H-owned singleton,
AB is the original B-owned upper-left singleton in A's ordered chart,
and BC uses the strict far B vertex with its original normal k_y<0.

**Theorem.** This entire radial-C far-return type is impossible. Every
original HC owner, shared mean and individual radial-C weight endpoint
is included. The contradiction uses the pressure of the true A/B block,
the true radial C load, and the intact petal. B is never assigned another
body's degree-two equation.

## 1. Original chart and the complete radial-C alternative

Use the actual chart in
ABC_UPPER_LEFT_FAR_RETURN_SUPPORT_WORKING_2026_10_25.md:

    zA=(a,b), a>b>3/5, a^2+b^2=q,
    x=a-1, P=(x,b-1), T=(x,b),
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    n=(u,v), j=(-v,u), 0<u<v, u^2+v^2=1,
    rho=u/v=c/[c+s(a/b-1)],
    H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    c_H dot zA<0.

These are the actual coordinates, not a normal choice depending on a
later stress. The true A2 concurrence gives the displayed rho. Write

    L=x s+b c, h=-x c+b s,
    k=-p f+t g, p,t>0, p^2+t^2=1,
    k_n=k dot n<0, k_j=k dot j.

The strict far BC point W and the original AB point T are distinct fixed
singletons. The previously compatible fixed-tip selection at unique B2
therefore makes BC C-owned. No selection theorem for radial C is used.

Put K=sqrt(q-1/4) and d=K-1. The owned radial-axis alternatives at C are
excluded by the outer-face support bound and the complete local inner-face
boundary-neighbor lemma in C7_FORCE_POLYGON.md, Lemma 2.1. The latter
contains every original side coordinate and requires only a physical
boundary neighbor, not a seven-cycle. Thus the remaining original C is

    C=[-1/2,1/2]k+[-K,-d]Jk,
    W=-(1/2)k-M Jk, d<M<K,
    M=det(W,k)>0.

The lower physical B-corner alternative epsilon_B=0 is already excluded
by Section 1 of ABC_UPPER_LEFT_FAR_RADIAL_DOMAIN_WORKING_2026_10_25.md.
For clarity, its complete scalar contradiction is short. Proper B
concurrence and zB=W+f-g imply t>p and

    K^2-M^2=2+p+t+2M(t-p)>2+2t>2+sqrt(2).

But M>d and K<121/60 give K^2-M^2<2K-1<91/30<2+sqrt(2).
The comparison includes every original C corner weight and does not
restrict the HC feature. Hence only epsilon_B=1 remains below.

## 2. Exact full epsilon_B=1 parametrization

Write the actual unique B circle corner as

    zB=beta f+H_B g, H_B>1/2,
    W=(beta-1)f+H_B g.

The entire remaining scalar domain has

    3/2<beta<K,
    H_B=sqrt(q-beta^2),
    M=sqrt(q-2beta+3/4),
    p=[(beta-1)/2+H_B M]/(M^2+1/4),
    t=[(beta-1)M-H_B/2]/(M^2+1/4),
    Z=M+t, L=beta M/Z, h=H_B-1,
    a=H_B+(beta^2-L^2)/2, b=sqrt(q-a^2),
    c=[L b-h(a-1)]/(L^2+h^2),
    s=[L(a-1)+h b]/(L^2+h^2).

Keep every original physical restriction, including a>b, c,s>0, the
strict B-side offset, k_y<0, all containment and nonoverlap conditions,
and the original negative A pressure. The scalar comparisons below may
enlarge that domain, but never claim that every enlarged parameter is a
physical pose.

Useful exact identities are

    H_B=Mp-t/2,
    beta=1+p/2+Mt,
    q=M^2+2Mt+5/4+p,
    L^2+h^2=q-2a+1.

The independently reviewed whole-interval lemma
ABC_FAR_RADIAL_A_MONOTONICITY_WORKING_2026_10_25.md proves that a(beta,q)
strictly increases with beta at fixed q. The independent rational endpoint
lemma ABC_UPPER_LEFT_FAR_RADIAL_ENDPOINT_BOUND.md then gives

    b>9/8.                                             (1)

In that endpoint proof, d is enlarged once to [9/10,11/10]; the final
strict squared reserve is 721591680879/173414975738944 above 81/64.
The beta=K comparison is not assigned to the original B mask. Also
a>b and q<=Q0 give b<sqrt(q/2)<3/2.

## 3. Whole-domain auxiliary bounds, without a root-pressure assumption

Put z=t/(1+p). The complete radial chart gives

    0<z<31/91, t<5/8,
    (1+t)/(2p)<M<p+1/2<3/2.                            (2)

These inequalities were independently checked in the monotonicity source.
For example M>d and K^2=M^2+2Mt+1+p give
d>(1+t)/(2p); d<61/60 then gives z<31/91. At M=p+1/2 the squared circle
radius exceeds 9/2, whereas the actual q<=Q0<9/2, proving its upper bound.

We need a simple sign in the later square-root comparison. Set

    A0=(L+6h)(q-a^2)-6La(a-1),
    B0=6L(a-1)-h(7a-1).

**Claim.** B0>0 on the whole original epsilon_B=1 far prefix.

First L, as a function of M at fixed p,t, is

    L=M(1+p/2+Mt)/(M+t),

and has positive derivative t(1+p/2+M^2+2Mt)/(M+t)^2. If H_B>=1,
then M>=(1+t/2)/p. Substituting this lower endpoint shows L>4/3:
after multiplication by positive factors the required difference is

    3-2p-t/2-pt+3t^2+8t^3
      >=1-3t/2+3t^2+8t^3
      =3(t-1/4)^2+13/16+8t^3>0.                        (3)

If H_B>=4/3, then M>=4/3 and

    2L-3=t[2M^2-3-Mz]/(M+t)>0,

because 2M^2-3>=5/9 and Mz<93/182, with reserve 73/1638.
Thus L>3/2 in this entire range.

Next H_B<11/8 in the original a>b domain. Otherwise the last bound gives

    a=H_B+(q-H_B^2-L^2)/2
      <q/2-5/8-(H_B-1)^2/2
      <=q/2-89/128<sqrt(q/2),

contrary to a>b. To verify the final strict comparison throughout the
whole radius window, q/2-89/128 is positive, and
q/2-(q/2-89/128)^2 decreases there. Its value at Q0 is
4759/262144>0.

If 0<h<=1/3, (3) gives h/L<1/4. If 1/3<h<3/8, the L>3/2 bound gives
the same comparison. For h<=0 the sign of B0 is immediate. In the other
cases, a>sqrt(q0/2)>11/8 yields x=a-1>3/8, and

    B0=L[6x-(h/L)(7x+6)]
       >L[(17/4)x-3/2]>3L/32>0.                        (4)

This proves the claim on the whole original prefix.

## 4. A uniform rho bound from one rational rectangle

The square-root chord on 9/8<=b<=3/2 gives

    b >= (8/21)b^2+9/14.                               (5)

Indeed this is exactly (b-9/8)(b-3/2)<=0 after rearranging. The original
rho identity shows that rho>6/7 is equivalent to

    b c-6s(a-b)>0.

Multiplication by the positive L^2+h^2 and substitution of the unchanged
c,s gives exactly

    (L^2+h^2)[b c-6s(a-b)]=A0+B0 b.

By (4)--(5), it is enough to prove

    J=A0+B0[(8/21)(q-a^2)+9/14]>0.                     (6)

The following whole-domain strip contains every original M,t:

    77/60-t+t^2/2 < M
      < 23/16-t+(88/161)t^2.                           (7)

For the lower bound, 1-p=t^2/(1+p)>=t^2/2 gives
(M+t)^2>=q0-9/4+3t^2/2. Subtracting (77/60+t^2/2)^2 leaves

    53/14400+t^2[13/60-t^2/4]>0

for t<5/8. For the upper bound, p>3/4 and q<=Q0 give
(M+t)^2<(23/16)^2+(11/7)t^2. The tangent upper bound for the positive
square root gives the right side of (7).

Section 9 gives a completely explicit polynomial construction for J on
the single rectangle obtained by writing M between these two endpoints
and z=t/(1+p) in [0,31/91]. All 780 normalized Bernstein coefficients
are strictly greater than 9/10. Their full exact values, defining
polynomial and inverse reconstruction are retained in the accompanying
certificate and standard-Python checker. Two independent constructions
checked every coefficient and every inverse identity. Thus (6) holds
on that entire enlarged rectangle, proving

    rho>6/7                                             (8)

for the whole original far-radial prefix.

## 5. Positive original root-normal projection and the low-q consequence

For fixed a>b>1, the expression

    P dot n=[(a-1)rho+b-1]/sqrt(1+rho^2)

strictly increases with rho in (0,1]. Its derivative numerator is
(a-1)-rho(b-1)>a-b>0. Hence (1),(8) give

    P dot n > [6sqrt(q-b^2)+7b-13]/sqrt(85).

The numerator is concave in b on [9/8,sqrt(q/2)], so its minimum occurs
at one of those two endpoints. At a=b, use a>11/8 and
39^2-16*85=161>0 to obtain a value greater than 1/2.
At b=9/8, decrease q to q0. The required endpoint is

    [6sqrt(527/200)-41/8]/sqrt(85)>1/2.

For an entirely rational check, sqrt(85)<461/50 and

    36*(527/200)-(1947/200)^2=3591/40000>0.

Both quantities being squared are positive. Thus

    P dot n>1/2, cn:=c_H dot n=P dot n-1/2>0.           (9)

The original negative A pressure also forces a smaller q interval.
Write c_H=zA-S_r, where S_r=(1,1)+n/2-(r-1/2)j. The exact endpoint
values of its convex squared norm are 5/2+2u and 5/2+2v, so

    |c_H|^2<5/2+2v-q.

Since (8) gives v<7/sqrt(85), this implies

    q<5/2+14/sqrt(85)<201/50.                          (10)

The last comparison follows from 196*625<1444*85. The entire original
r interval remains; no actual mean or H position is reset.

## 6. The original k_j is strictly negative on the entire reduced domain

Set x=a-1 and Dgeom=L^2+h^2=q-2a+1. Define the two rational expressions

    N0=L(q-a)x(pL-th)+h(ph+tL)(q-a^2),
    N1=L(q-a)(ph+tL)+hx(pL-th)-p Dgeom^2.                (11)

The actual A concurrence is qA=[L/(L+s)]zA, since its incoming B-normal
line has f coordinate L. Its displacement from P has positively
proportional direction n and f component c>0. Direct expansion gives

    sign(k_j)=sign((L+s)(ps+tc)-pb)
             =sign(N0+N1 b).                          (12)

For the second equality, multiply by Dgeom^2>0 and use
s=[Lx+hb]/Dgeom, c=[Lb-hx]/Dgeom. The constant and b coefficients are
precisely (11), using b^2=q-a^2. No sign or circle-corner alternative is
selected in this computation.

By (10), every original negative-pressure pose lies in the narrower strip

    77/60-t+t^2/2 < M
      < 4/3-t+(33/56)t^2.                              (13)

The lower bound is unchanged. For the upper bound use
q-9/4<177/100<(4/3)^2 and p>3/4 in the same square-root tangent argument
as in (7).

Section 10 supplies two explicit whole-rectangle polynomial certificates:

    N1<0,
    Nchord:=N0+N1[(8/21)(q-a^2)+9/14]<0.               (14)

They have respectively 351 and 1125 Bernstein coefficients, all strictly
greater than 9/10 after normalization by the positive constant
coefficient. The full exact packets and inverse identities were checked
by two independent constructions.

Since N1<0, the proved lower chord (5) has the needed reversed direction:

    N0+N1 b <=Nchord<0.

Equations (12)--(14) therefore prove

    k_j<0                                               (15)

throughout the entire original negative-A far-radial domain. This is a
whole scalar implication, not the deletion of a positive-k_j pose based
on a diagnostic sample.

## 7. The true A/B block has strictly positive H-pressure

Put cj=c_H dot j. The original zA satisfies

    zA dot n>0, zA dot j<0.

Together with (9) and c_H dot zA<0, this forces cj>0. Since the original
far feature has k_n<0, (9),(15) give

    c_H dot k=cn*k_n+cj*k_j<0.                         (16)

Let mu,gamma,eta>0 be the actual HA,AB,BC magnitudes. Set

    m_A=det(P,n)=-P dot j>0,
    M=det(W,k)>0.

The first sign follows directly from a>b>1 and 0<u<=v. The actual A2
and B2 force and origin-torque equations are

    F_A=mu n-gamma g,
    F_B=gamma g-eta k,
    mu*m_A=gamma*L=eta*M.

Their common interface force cancels only in the genuine block sum:

    F_A+F_B=gamma L(n/m_A-k/M).

Every coefficient is positive. By (9),(16),

    c_H dot(F_A+F_B)
      =gamma L[cn/m_A-(c_H dot k)/M]>0.                (17)

No equation at H or C was assigned to either of these tips. No pair
force, original application or mean was removed to obtain (17).

## 8. The full H4 equation contradicts the three positive pressures

Because C is physically radial and actually touches H,
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md gives

    c_H dot F_C>0

for its actual unequal circle weights, including either individual zero
weight. The intact HXY end triangle has actual resultant Mpetal with
c_H dot Mpetal>0 by BOWTIE_CELL_CLOSED.md, Section 2; that theorem permits
H's other positive neighbors.

Summing the true A/B/C equations identifies their whole resultant with
the two original outward pair forces at H in this cycle. The genuine
H4 equation is therefore

    F_A+F_B+F_C+Mpetal=0.

Taking its product with c_H contradicts (17) and the other two strict
positive pressures. This excludes the entire epsilon_B=1 radial far
domain. Section 1 already excludes epsilon_B=0, so both possible
physical unique B corners are covered.

## 9. Complete exact construction of the rho polynomial packet

The following definitions make the certificate independently
reconstructible. They are polynomials in lambda,z. Put U=1+z^2 and
d0=38640, and define

    m=49588U^2-77280zU+77280z^2
        +lambda(5957U^2+7200z^2),
    Znum=m+2d0 zU,
    Hnum=m(1-z^2)-d0 zU^2,
    betanum=d0 U^3+(d0/2)(1-z^2)U^2+2zm,
    qnum=m^2+4d0 z m U+(d0^2/4)(9+z^2)U^3,
    D=d0 U^5 Znum^2,
    Anum=Hnum U^2 Znum^2+z betanum^2(Znum+m),
    Bnum=qnum U^6 Znum^4-Anum^2.

The rational substitution is exactly

    M=m/(d0 U^2), H_B=Hnum/(d0 U^3),
    beta=betanum/(d0 U^3), q=qnum/(d0^2 U^4),
    a=Anum/D, b^2=Bnum/D^2,
    L=betanum*m/(d0 U^3 Znum).

As lambda varies over [0,1], M runs through the whole strip (7).
Define the polynomial

    Nrho=6betanum*m[(16Anum-9D)Bnum
                    +3D(Anum-D)(9D-14Anum)]
          +(Hnum-d0 U^3)Znum[4(67D-28Anum)Bnum
                              -27D^2(7Anum-D)].

Direct substitution gives the full cleared identity

    Nrho=42 d0 U^3 Znum D^3 J.                         (18)

All cleared factors are positive on the entire rectangle. The primitive
integer polynomial Nrho/64 has degrees (11,64) and 774 nonzero ordinary
monomials. For the sign proof normalize by its positive constant value;
equivalently set Grho=Nrho/Nrho(0,0). The constant is positive: at
lambda=z=0, the original J is exactly 10463/2400>0.

For any normalized packet G of degrees (m,n), substitute z=(31/91)w,
write G(lambda,(31/91)w)=sum a_rs lambda^r w^s, and define

    b_ij=sum_(r<=i,s<=j) a_rs
           *binom(i,r)/binom(m,r)*binom(j,s)/binom(n,s). (19)

The complete inverse identity is

    G(lambda,(31/91)w)
      =sum_(i=0..m,j=0..n) b_ij binom(m,i)binom(n,j)
          lambda^i(1-lambda)^(m-i) w^j(1-w)^(n-j).       (20)

For Grho, the exact minima in each i-row of floor(100*b_ij) are

    [92,99,106,113,121,129,137,145,153,162,169,130].

Thus every coefficient is greater than 9/10, so (20) proves G>0
throughout the entire closed unit square. This is one global polynomial
identity, with no subdivision of the original angle or offset domain.

## 10. Complete exact construction of the two k_j packets

For the narrower strip (13), use the same definitions and rational
identities as Section 9, but replace d0 and m by

    d0=420,
    m=539U^2-840zU+840z^2+lambda(21U^2+150z^2).

Define further

    Ln=betanum*m,
    hn=(Hnum-d0 U^3)Znum,
    Ld=d0 U^3 Znum,
    xnum=Anum-D,
    Wn=(1-z^2)Ln-2z hn,
    Vn=(1-z^2)hn+2z Ln,
    Dg=Ln^2+hn^2,
    Qa=qnum U Znum^2-d0 Anum,

    P1=U[Ln Qa Vn+d0 hn xnum Wn]-(1-z^2)Dg^2,
    P0=Ln Qa xnum Wn+d0 hn Vn Bnum,
    Pc=42U D P0+P1(16Bnum+27D^2).

Their exact rational identities are

    N1=P1/(U Ld^4),
    N0=P0/(Ld^4 D),
    Nchord=Pc/(42U Ld^4 D^2).                         (21)

Polynomial division is exact in

    G1=-P1/U^2, G2=-Pc/(16U^2).                       (22)

These integer polynomials have degrees (8,38) and (14,74), respectively,
and positive constant coefficients. Normalize each by its own constant
coefficient, and apply exactly (19)--(20) on the same whole rectangle.
The complete row minima of floor(100*b_ij) are respectively

    G1: [97,98,100,102,104,105,107,109,110],
    G2: [92,94,95,96,97,99,100,101,102,103,104,106,107,108,109].

Every one of the 351+1125 coefficients is greater than 9/10. Thus both
polynomials in (22) are strictly positive on the entire closed rectangle.
The positive denominators in (21) establish exactly (14).

## 11. Auditable artifacts, independent checks and scope

The complete exact data and reconstruction are saved beside this source:

* ABC_UPPER_LEFT_FAR_RADIAL_PRESSURE_CHECK.py;
* ABC_UPPER_LEFT_FAR_RADIAL_RHO_CERTIFICATE.json;
* ABC_UPPER_LEFT_FAR_RADIAL_KJ_COEFFICIENT_CERTIFICATE.json;
* ABC_UPPER_LEFT_FAR_RADIAL_KJ_CHORD_CERTIFICATE.json.

The checker uses standard Python integer/Fraction arithmetic. It rebuilds
the displayed polynomials, all 2256 coefficients, the stated sign bounds,
and every ordinary coefficient of the inverse identities. Its data are
exact rational numbers, not evaluations at sampled poses. A separate
reviewer independently rebuilt all three polynomials and every forward
and inverse coefficient calculation without invoking that checker or
reading its coefficient JSONs. The reduced k_j identities were also
verified against independently derived larger cleared numerators.

The contradiction covers the entire strict radial-C far feature with
k_y<0, both original B-corner alternatives, every HC owner, every
original shared mean, and both individual radial circle-weight endpoints.
It imposes no H/B contact and uses no equation from a fictitious triangle
HAB or HBC. The other already treated side/near/upward owner types must
be joined using their own complete sources before marking any larger
upper-left mask or parent gate closed.

No Lean compilation, CI, numerical pose sample, angle subdivision,
post-extraction normal selection, force splitting, or deletion of a
physical square is a premise of this theorem.
