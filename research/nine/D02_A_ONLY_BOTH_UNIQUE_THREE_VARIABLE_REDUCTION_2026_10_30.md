# D02 L135: a bounded three-variable system retaining the full original circle equations

Date: 2026-10-30. Input: PR #11, `71d385e75adc1f5183d35a92dbe18c208dc32f2a`.

**Status:** complete exact necessary reduction for the whole original A-only
Type II side feature with both B and C physically unique-circle. This is a
certificate-discovery reduction, not a declaration that the whole feature has
been excluded. The accompanying five-core capacity theorem supplies an actual
completion obstruction when the resulting five core squares enter its stated
neighborhood. Global coverage of that neighborhood is a separate obligation.

The purpose of this reduction is to avoid a false computational target: the six
core force/torque/circle equations cannot simply be presumed infeasible below
the nine-square radius. All three completing squares must be excluded by a
physical capacity argument. The whole side family also retains the two radial
endpoint alternatives; those are outside the both-unique premise here.

## 1. Exact original domain

Use the complete original hypotheses and notation of
[TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md](TYPE_II_A_ONLY_WHOLE_TRANSVERSE_GAP_AND_EXACT_BOTH_UNIQUE_SIDE_MATRIX_2026_10_29.md).
The original six positive stars are unchanged:

    A:{V,D,B}, D:{A,V,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D are unloaded true3, N is unloaded true2, and V,B,C are loaded true2.
V,B,C have their actual unique physical circle corners. The selected normals,
applications and means, circle coefficients, all nine squares, and conditional
common-selection hypotheses remain. No statement here applies to loaded N.

In the actual A frame write

    East=(c,s), North=(-s,c),
    c=cos(alpha), s=sin(alpha), C=cos(beta), S=sin(beta),
    pi/4<alpha,beta<pi/2, pi/2<alpha+beta<3*pi/4,
    H=c*S+s*C, k=s*S-c*C, p=H-k, q=H+k.

Thus H>k>0 and H^2+k^2=1. The original scalars satisfy

    0<u<1,
    t=(S-s+s*u)/S in (0,1),
    omega=(1-u)*H/S in (0,1),
    u*(S-s+s*u)*(S-H+H*u)=p*(s-c)*S^2*(S-C).       (1)

In particular both factors after u on the left of (1) are strictly positive.

## 2. The hub root is unique; it adds no free dimension

For fixed original alpha,beta, put

    A(u)=S-s+s*u, B(u)=S-H+H*u,
    F(u)=u*A(u)*B(u)-p*(s-c)*S^2*(S-C).

On the domain u>0, A(u)>0, B(u)>0,

    F'(u)=A(u)*B(u)+u*s*B(u)+u*H*A(u)>0.          (2)

Consequently at most one original u solves (1). This is a uniqueness theorem,
not an assertion that every angle pair has a physically admissible root.

For interval bounds it is useful to use

    Fplus(u)=u*max(0,A(u))*max(0,B(u))
               -p*(s-c)*S^2*(S-C),  0<=u<=1.

It is nondecreasing. The subtracted constant is strictly positive; therefore
any zero occurs where u,A(u),B(u) are all positive, and there (2) makes the zero
unique. At u=0 its value is negative. At u=1 its value is

    S^2*(1-p*(s-c)*(S-C))>0,

because all three factors p,s-c,S-C lie in (0,1). Thus there is exactly one
root of Fplus on (0,1); the original u is that root. Some roots may fail the
additional original omega,t restrictions, which remain imposed. Exact interval
bisection may bound this root without adding u as an independent box dimension.
All endpoint comparisons can be non-strict: Fplus(v)<=0 implies u>=v and
Fplus(v)>=0 implies u<=v, by this uniqueness.

## 3. Bounded normalization with no division by a vanishing hub ratio

Scale all original positive force magnitudes by the same positive number so
that

    mu=u*t, rho=(s-c)*t, nu=(s-c)*p.              (3)

This is a permitted common scale, not a new certificate. Indeed the original
relations rho*u=mu*(s-c) and nu*t=rho*p determine exactly these positive ratios;
(1) is the unchanged V moment after substitution. All three numbers in (3)
are positive on the original domain.

Define

    Bn=(u*c+s-c,u*s), Cn=(t+p*k,p*H),
    PB=t*|Bn|, PC=(s-c)*|Cn|,
    b=-Bn/|Bn|,
    cvec=(-Cn.x,Cn.y)/|Cn|,
    wB=(b.y,-b.x), wC=(-cvec.y,cvec.x),
    Fv=(mu*c-nu*k,mu*s+nu*H), g=Fv/|Fv|.

These are exactly the original own axes and force magnitudes in the cited
source. All three normalized vectors have positive norm: Bn.x>0, Cn.y>0 and
Fv.y>0. No division by p, s-c, t, or a force-matrix determinant has occurred.
The actual roof circle corner is Z=R*g.

A useful necessary physical-corner inequality comes directly from V. Its
original North coordinate is R*nu*S/|Fv|>1/2. Since R^2<=Q=1105/256,

    4*Q*(nu*S)^2 >= |Fv|^2.                      (4)

Likewise its East coordinate gives

    4*Q*(mu+nu*C)^2 >= |Fv|^2.                    (5)

These non-strict necessary inequalities are safe at the upper radius endpoint.
They keep the actual unique-roof geometry when small normalized force factors
approach zero, and require no division by those factors.

## 4. Exact side direction and offsets from one additional bounded variable

Set a=tan(alpha/2), bhalf=tan(beta/2). Then

    sqrt(2)-1<a,bhalf<1,
    s=2*a/(1+a^2), c=(1-a^2)/(1+a^2),
    S=2*bhalf/(1+bhalf^2), C=(1-bhalf^2)/(1+bhalf^2).

The original strict both-unique cone has the direction

    d=(-1,w)/sqrt(1+w^2), 0<w<1.

For b=(-a0,-b0) and cvec=(-cX,cY), its exact strict sector is

    (a0-b0)/(a0+b0) < w < (cY-cX)/(cY+cX).        (6)

Here a0>b0>0. The positive upper endpoint follows from the original obtuse
both-unique cone, equivalently cX/cY<b0/a0<1. Every denominator in (6) is positive.
Equation (6) is the same as d.(wB-b)>0 and d.(wC-cvec)>0, after multiplication
by sqrt(1+w^2)>0.

Now use the original support difference and transverse coordinates:

    Delta=(-1-q,p-u), sigma=b.wC=cvec.wB>0,
    AB=Delta.cvec/sigma-1>0,
    AC=Delta.b/sigma-1>0,
    rB=d.cvec/sigma, rC=d.b/sigma,
    xB=rB-AB, xC=rC-AC,
    kB=d.(wB-b)>0, kC=d.(wC-cvec)>0.

The original genuine side offsets satisfy 0<xB,xC<1. Eliminating only the same
positive original return magnitude gives

    E1:=PB*xB*kC-PC*xC*kB=0.                     (7)

Conversely a point with all these strict conditions recovers a positive common
return magnitude from gamma=PB*xB/kB=PC*xC/kC. This converse concerns the listed
local algebra; it does not assert containment or nine-square feasibility.

The circle-corner budget and full original restrictions remain necessary:

    -b.y+cvec.y-q>0,
    b.cvec<0,
    79/40<=R<=sqrt(1105)/16.

## 5. Linearize the actual circle equations before eliminating the radius

Put nD=(-k,H), tD=(-H,-k), and retain the original displacement vectors

    DB=East+(1-omega)*North+(1,1),
    DC=East+North+nD+t*tD,
    EB=DB-b-xB*wB,
    EC=DC+cvec+xC*wC.

The original physical circle corners are exactly

    ZB=R*g-EB, ZC=R*g-EC.

Their circle equations expand without any square root or denominator:

    2*R*(g.EB)=|EB|^2,
    2*R*(g.EC)=|EC|^2.                          (8)

Both right-hand sides are strictly positive. For EB, its h coordinate is

    c-(1-omega)*s+1+a0+xB*b0 > c+a0>0.

For EC, its e coordinate is

    s+c+H-t*k+cY-xC*cX
      >s+c+(H-k)+cY-cX>0,

using s+c>1, p>0, cX<1 and cY>0. Thus g.EB,g.EC>0 at every actual point, and

    R=|EB|^2/(2*g.EB).                           (9)

Equality of the two circle radii is precisely the additional necessary equation

    E2:=|EB|^2*(g.EC)-|EC|^2*(g.EB)=0.           (10)

Unlike a virial radius, (9) is obtained from the actual original physical
corners. It cannot lose the circle origin.

## 6. Keep the full radial moment without a small force denominator

Use the original B-frame scalars

    gb=g.b, gw=g.wB, Db=DB.b, Dw=DB.wB,
    cd=d.b>0, sd=d.wB>0.

The cited complete source proves gb<0 and gw>0 on the entire surviving side
row. Multiply its exact original radial-origin moment formula by kB>0. It gives

    R*Dmom=Nmom,
    Dmom=(kB+xB*cd)*gw-xB*sd*gb>0,
    Nmom=Dw*(kB+xB*cd)-xB*sd*Db+xB*(1-xB)*cd.

Substituting (9), and multiplying only by 2*g.EB>0, gives

    E3:=|EB|^2*Dmom-2*(g.EB)*Nmom=0.             (11)

The exact necessary system is therefore **E1=E2=E3=0 in the three bounded
variables a,bhalf,w**, with the unique u of Section 2 and every stated original
sign, mask and physical constraint retained. No force-matrix determinant is
inverted. The three equalities are not themselves a nine-square exclusion.

## 7. Physical completion and the remaining global coverage obligation

Given any original solution, the five fixed actual squares are reconstructed
without using N's slider:

    P=R*g-East-North,
    RA=P+omega*North,
    QB=R*g-DB, QC=R*g-DC,
    V=P+[0,1]East+[0,1]North,
    A=RA-[0,1]h-[0,1]e,
    D=P-[0,1]nD+[-t,1-t]tD,
    B=QB+[0,1]b+[-(1-xB),xB]wB,
    C=QC+[-1,0]cvec+[-xC,1-xC]wC.

The exact certificate in
[FIVE_CORE_ROBUST_CENTER_COVER_CAPACITY_EIGHT_2026_10_30.md](FIVE_CORE_ROBUST_CENTER_COVER_CAPACITY_EIGHT_2026_10_30.md)
excludes every nine-square packing whose five reconstructed squares enter its
explicit vertex-neighborhood. Its four remaining squares are the actual N and
all three original completion squares, with arbitrary rotations and positions.
It therefore discharges a physical completion domain, not just a force system.

To close this entire both-unique feature, prove a finite cover of every original
solution of (1), (6), (7), (10), (11), and the retained physical inequalities by
those certified vertex-neighborhoods or other proved exclusions. A numerical
root, unresolved interval box or computation timeout does not give that cover.
No original fine/coarse flag is changed by this reduction alone.
