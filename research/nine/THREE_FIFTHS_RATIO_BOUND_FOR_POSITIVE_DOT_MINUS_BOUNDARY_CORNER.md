# A three-fifths ratio bound for the positive-dot minus boundary corner

Date: October 28, 2026 UTC. Author: root continuation, with cycles' threshold suggestion and independent exact expansion.

**Status: complete proposed continuous scalar theorem, submitted for independent review.** Root derived the full monotonicity reduction and positive half-angle polynomial first at ratio5/8. Cycles suggested the stronger3/5 threshold. Root and cycles separately obtained the identical exact expansion and positive reserves at that threshold. A separate reviewer is required for the complete accepted proof.

## 1. Broad scalar statement

Let

    X>Y>0, X^2+Y^2=R^2, R>=2,
    K>0, L>=1/2, K^2+L^2=1,
    r=Y/X in(0,1),

    0<s<1,
    s>s0:=L/(L+Kr).

Suppose the actual algebraic minus point

    Z=(X-s+L-K,Y-1-K-L)

satisfies |Z|^2=R^2. Then

    r<3/5.                                         (1)

There is no upper-radius, force, degree, terminal-unit or physical-mask premise in this scalar statement. The closed L=1/2 endpoint is included. A physical caller must establish the stated L bound and side-parameter inequality separately.

## 2. The original circle deficit increases in s

Put

    A(s)=s+K-L, B=1+K+L.

The exact circle deficit is

    D(s;X,r)=2X[A(s)+rB]-A(s)^2-B^2.              (2)

The assumed circle equality is D(s;X,r)=0.

Since K,L>0 and K^2+L^2=1, one has K+L>1. Direct subtraction gives

    s0-(1-K)
      =K[L-r(1-K)]/(L+Kr)>0.

Thus A(s0)>1-L>0. Also L>=1/2 gives K<=sqrt(3)/2<7/8, so

    A(s)<1+K-L<11/8<sqrt(2)<X.                   (3)

The final X bound follows from X>Y and R>=2. The same inequalities hold along the entire comparison interval from s0 to the actual s. Consequently

    partial_s D=2[X-A(s)]>0,
    D(s0;X,r)<0.                                   (4)

All denominators and derivatives have their stated strict signs; no physical pose is moved in this scalar comparison.

## 3. A full-ratio derivative reduces every alleged r>=3/5 to one boundary

Suppose r>=3/5. Write

    A0(r)=K-L+L/(L+Kr),
    X0(r)=2/sqrt(1+r^2).

At fixed r, (2) increases strictly with X because A0+rB>0. Since X>=X0, it suffices to show

    D0(r):=2X0[A0+rB]-A0^2-B^2>0.                (5)

The comparison (3) remains valid for X0 throughout the closed enlarged interval3/5<=r<=1: X0>=sqrt(2)>11/8>A0>0.

Direct differentiation gives

    A0'=-LK/(L+Kr)^2>=-1/(4r),

    D0'(r)/2
      =X0/(1+r^2)*(B-rA0)+(X0-A0)*A0'.           (6)

The first inequality is exactly(L+Kr)^2>=4LKr. Because r<=1 and A0>0,

    B-rA0>=B-A0=1+2L-s0>2L>=1.

Using 0<X0-A0<X0 in (6) therefore gives

    D0'(r)/2
       >X0/(1+r^2)-X0/(4r)>0.                    (7)

For the last sign,4r-1-r^2 increases on[3/5,1] and has value26/25>0 at3/5. This is a whole-interval derivative argument, including L=1/2 and r=1 as comparison endpoints.

It remains to prove (5) at r=3/5.

## 4. One global positive polynomial at the comparison ratio

At r=3/5,

    X0=10/sqrt(34)>12/7,

with exact squared reserve50/17-144/49=2/833>0. Since the coefficient of X in(5) is positive, it suffices to use X=12/7.

Put t=K/(1+L). The entire actual domain L>=1/2 gives

    0<t<=1/sqrt(3)<3/5,
    K=2t/(1+t^2), L=(1-t^2)/(1+t^2).

Define the positive denominator and two exact numerators

    d1=1+t^2,
    d2=1+(6/5)t-t^2,
    d=d1*d2>0,

    N_A=(4/5)t+(22/5)t^2-(4/5)t^3-2t^4,
    N_B=2(1+t)d2.

Then A0=N_A/d and B=N_B/d. Exact expansion gives

    d^2*D( s0; X=12/7, r=3/5 )=P(t),

    P(t)=4/35-(152/175)t+(7404/875)t^2
           +(12784/875)t^3-(4976/875)t^4
           +(9544/875)t^5-(1956/175)t^6
           -(32/7)t^7+(20/7)t^8.                 (8)

Here is a short whole-domain positivity proof rather than an angle table. The first three terms form the exact completed square

    4/35-(152/175)t+(7404/875)t^2
       =(7404/875)*(t-95/1851)^2+1192/12957>0.    (9)

The remaining terms can be grouped as

    t^3*[12784/875-(4976/875)t
                    -(1956/175)t^3-(32/7)t^4]
        +(9544/875)t^5+(20/7)t^8.                (10)

On the entire enlarged interval0<=t<=3/5, the bracket is at least

    12784/875-(4976/875)*(3/5)
       -(1956/175)*(3/5)^3-(32/7)*(3/5)^4
       =179188/21875>0.                          (11)

Every remaining term in(10) is nonnegative. Equations(9)--(11) therefore prove P(t)>0 on the whole interval, including both comparison endpoints. No sampled orientation, numerical minimum or finite physical-pose certificate is used.

The positive denominator and strict X comparison give D0(3/5)>0. The full derivative(7) then gives D0(r)>0 for every alleged r>=3/5. Since X>=X0, this contradicts (4). The scalar theorem(1) follows.

## 5. Literal conditional physical use and proof boundary

The current positive-dot V-owned entry has its actual minus corner

    Z_W^-=(X-s+L-K,Y-1-K-L),
    s=1-tau,
    X>Y>1/2, X^2+Y^2=R^2,
    s>L/(L+K*(Y/X)).

For the last strict inequality, the exact actual geometry gives rho=a-(L/K)(b+tau)<1-(L/K)tau. Substitute the full unique V identity rho=1-r*s and tau=1-s. One obtains r*s>(L/K)(1-s), hence s>L/(L+Kr). This derivation needs no Y>=1 restriction from another comparison branch. Therefore every such original minus configuration that also satisfiesL>=1/2 hasY/X<3/5 by the present theorem.

The result does not by itself establishL>=1/2 for the entire physical minus feature. Nor does it give a terminal-port norm, occupied-pocket capacity or original-row closure. A later whole-feature proof must supply those remaining steps with all original equations and squares retained.

| Complete physical entry | SHA256 | Exact conditional use |
| --- | --- | --- |
| TERMINAL_HUB_AXIS_TIP_OWNED_POSITIVE_DOT_FULL_MASK_ENTRY.md | 1e9e597ad4b13995909cdac5d204b111d20ef305768fe6d44def11264e4a4c49 | Original unique-minus circle point and actual side/force identities; not needed for the self-contained scalar proof |

The entire new scalar theorem is proved in Sections1--4 without imported mathematical premises. Its physical entry is used only to state this literal conditional caller. All true degrees, physical corner ties, zero coefficients, original forces, selected normals and actual means remain untouched.

No original fine or coarse flag changes. No Lean compilation, CI, workflow, pose enumeration, numerical optimizer, changed application, fake tip, remote action or shared-ledger mutation was used.

