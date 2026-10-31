# The entire adjacent-C side after a strict B-owned BC contact

Date: October 25, 2026.

**Status: complete hand proof; independent root full-source, original-fan,
analytic and exact-arithmetic review passed on October 25, 2026. See
REVIEW_ABC_COMPLETE_ADJACENT_SIDE_2026_10_25.md. No gate, accepted count,
selected force, application mean or roadmap checkbox changes here.**

Keep the original H--A--B--C--H cycle, intact HXY petal, true
H4/A2/B2/C2, every original positive force and application, all nine
physical squares, and all three completion squares. Work on the entire
original interval q in [6241/1600,1105/256]. A,B,C are physically unique;
A has negative H pressure, HA is H-owned, AB is B-owned upper-left, and
BC is the strict B-owned singleton on B's minimum-f side.

The complete accepted circle-corner and HC fan is
ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md. The remaining C circle
corner is Q+e in that source. This manuscript excludes its entire
C-owned or shared HC side for beta>3/2, with every actual original
side mean and overlap endpoint retained. The same side for beta<=3/2
was already excluded by Section 5 of the accepted fan, so the join
closes this whole HC side feature. The strict R_0 endpoint remains a
separate obligation.

## 1. The original side and concurrence data

Use the unchanged original chart

    P=(a-1,b-1), T=P+e_y,
    zA=(a,b), a>b>3/5, a^2+b^2=q,
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    n=(u,v), j=(-v,u), 0<u<=v, u^2+v^2=1,
    H=P+[-1,0]n+[r-1,r]j, 0<r<1,
    E=n dot f=su+cv>0, D=n dot g=sv-cu,
    n=E*f+D*g, j=-D*f+E*g,
    L=T dot f, h=T dot g, W=h+1,
    zB=beta*f+W*g, beta,W>0, beta^2+W^2=q,
    tau=beta-L in (0,1), delta_B=1-tau,
    Y=eta=L W/beta=W(1-tau/beta),
    h<Y<W, ell=Y-h in (0,1),
    X=beta-1, Q=X*f+Y*g.

These are the actual B2 force and moment identities, with the original
BC normal -f and original application Q. In this proof beta>3/2, so
X>1/2. The upper radius endpoint gives the useful uniform bound

    0<W<23/16,                                  (1)

since 1105/256-9/4=529/256=(23/16)^2.

The complete adjacent C chart, unchanged from the accepted fan, is

    e=-S*f+C0*g, t=-C0*f-S*g,
    S,C0>0, S^2+C0^2=1,
    C=Q+[0,1]e+[0,1]t,
    zC=Q+e,
    theta>0,
    qC=Q-theta*f=Q+theta*S*e+theta*C0*t.

The original side application and its actual H-to-C normal are

    R=Q+theta*S*e+t,
    m=-t=C0*f+S*g.                              (2)

In particular all genuinely shared-HC means and either endpoint of
their original overlap interval are included in (2). No fixed-tip
selection is made on this side. Proper C concurrence gives
theta*C0<=1 and theta*S<1, though the main scalar comparison below
does not need these further restrictions.

The exact displacements following from (2) are

    (R-P) dot f=c-delta_B-C0-theta*S^2,
    (R-T) dot f=-(delta_B+C0+theta*S^2),
    (R-T) dot g=ell-S+theta*S*C0.                 (3)

The original negative-A prefix gives

    r>u.                                        (4)

For clarity, this input uses no C owner or beta restriction: Section
2.1 of ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md records the
degree-independent A/H calculation. At r=u the pressure is
q-aA-bB with

    A=1+(u-v)/2+uv, B=1+(u+v)/2-u^2,
    A^2+B^2=5/2+u-u^2+2uv<=15/4.

The pressure decreases with r. Completing two squares therefore
gives pressure at least (q-15/4)/2>=241/3200>0 for every r<=u,
which contradicts the actual negative pressure and proves (4).

## 2. A circle-only scalar comparison: C0>tau+1/2

We prove the stronger bound

    C0>tau+1/2.                                 (5)

It uses only the original B and adjacent C circle identities,
beta>3/2, (1), and the whole unit quadrant S,C0>0.

Put z=tau/beta. Since both actual circle corners have squared radius q,

    beta^2+W^2=|Q+e|^2
      =X^2+Y^2+1-2XS+2YC0.

As Y=W(1-z), this is exactly

    Y*C0-X*S=K,
    K=X+W^2*z*(1-z/2),                           (6)

or equivalently

    X(1+S)+W^2*z*(1-z/2)-W(1-z)*C0=0.           (7)

### 2.1. The complete actual interval has tau<1/2

Equation (6) gives K<Y, since C0<1 and X,S>0. At fixed beta,W,

    d(K-Y)/d tau=(W^2/beta)(1-tau/beta)+W/beta>0

on the whole actual interval 0<tau<1, beta>3/2. At tau=1/2,
the positive factor 8beta^2 times K-Y is the W-quadratic

    (4beta-1)W^2-4beta(2beta-1)W+8beta^2(beta-1).

Its leading coefficient is positive. Its exact discriminant is

    16beta^2*(-4beta^2+6beta-1)<0                (8)

for every beta>=3/2: the bracket equals -1 at 3/2 and decreases
thereafter. Hence K-Y>0 at tau=1/2 and for every larger actual tau.
This contradicts K<Y. Thus

    0<tau<1/2.                                  (9)

### 2.2. A single whole-rectangle positive polynomial

Suppose C0<=tau+1/2, and put

    C_*=tau+1/2,
    S_*=sqrt(1-C_*^2).

Both are nonnegative by (9), and the actual S>=S_*. Equation (7)
would then imply

    0>=F(beta,W,tau)
      :=(beta-1)(1+S_*)
          +W^2*(tau/beta)*(1-tau/(2beta))
          -W*(1-tau/beta)*C_*.                  (10)

We show that F is uniformly positive on the whole comparison domain
beta>=3/2, 0<=W<=23/16, 0<=tau<=1/2. At fixed W,tau its derivative is

    dF/d beta=1+S_*
      -(W*tau/beta^2)[W*(1-tau/beta)+C_*]
      >=1-(23/72)*(39/16)=85/384>0.              (11)

All factors have the stated signs on this entire domain. Thus it
suffices to bound F at beta=3/2. The concave semicircle has the chord
bound

    S_*>=sqrt(3)*(1/2-tau)>=3/4-(3/2)tau

throughout 0<=tau<=1/2. It follows that

    F(3/2,W,tau)>=J(W,tau),

    J=7/8-W/2
       +tau[-3/4+(2/3)(W^2-W)]
       +tau^2[(2/3)W-(2/9)W^2].                 (12)

This one polynomial is positive on the whole rectangle
0<=tau<=1/2, 0<=W<=23/16. Its complete exact bidegree-(2,2)
Bernstein identity is especially short. Put

    lambda=2tau, zeta=16W/23,
    B_i(t)=binom(2,i)*t^i*(1-t)^(2-i).

Then

    J=sum_{i=0}^2 sum_{j=0}^2 b_ij B_i(lambda) B_j(zeta),

where the rows indexed by i=0,1,2 are

    [ 7/8,   33/64,  5/32      ],
    [ 11/16, 5/24,   113/1536  ],
    [ 1/2,   1/48,   533/4608  ].              (13)

Every coefficient is strictly positive. The basis is nonnegative
and sums to one. The accompanying standard-library checker
independently reconstructs (12), all nine coefficients, the complete
inverse polynomial identity, and the exact discriminant (8).

Consequently F>0, contradicting (10). This proves (5), with no
sampled pose, discarded orientation, or modified C concurrence.
In particular

    delta_B+C0=1-tau+C0>3/2.                    (14)

## 3. The actual HC mean must lie on H's front n side

We include the complete front-side argument rather than assume an
H contact side. It applies to every beta, but only the present
beta>3/2 feature is needed here.

Suppose m dot n=C0*E+S*D<=0. Then D<0, and with z0=-D/E>0,

    z0>=C0/S,
    m dot j=S*E-C0*D>0.

Thus the actual R is on H's top-j support face, even at the equality
m dot n=0 and for every original shared mean. Its j displacement
from T is r-u. Set

    A_f=delta_B+C0+theta*S^2>0,
    B_g=S-theta*S*C0.

Equation (3) gives

    r-u=E[ell-B_g-z0*A_f]
      <=E[ell-B_g-(C0/S)*A_f]
      =E[ell-1/S-(C0/S)*delta_B]
      <E(1-1/S)<0.                             (15)

The theta terms cancel exactly; ell<1, delta_B>0, and S<1 supply
the strict signs. This contradicts (4). Therefore

    m dot n>0,
    R=P+t_H*j,
    r-1<=t_H<=r<1.                             (16)

This retains the full actual front-side mean whenever m dot j=0.

## 4. The full side return contradicts its support coordinate

Equations (3), (14), and (16) give

    -D*t_H=(R-P) dot f
      =c-delta_B-C0-theta*S^2<c-3/2<0.          (17)

If D<=0, the actual normal has m dot j=S*E-C0*D>0, so t_H=r>0.
Its f displacement -D*t_H is nonnegative, contrary to (17).

It remains to treat D>0, without any further sign subdivision. Then
(17) makes t_H>0 and gives

    t_H*D=delta_B+C0+theta*S^2-c>3/2-c.          (18)

On the other hand, by the original n and f coordinates,

    c+D=c(1-u)+s*v
      <=sqrt((1-u)^2+v^2)
      =sqrt(2-2u)<sqrt(2)<3/2.                  (19)

Thus 3/2-c>D. Equations (18)--(19) imply t_H>1, contradicting
t_H<1 in (16). This covers m dot j positive, negative, or zero;
the entire genuinely shared-HC mean interval remains in (16).

The whole beta>3/2 C-side feature is therefore impossible. Joining
the accepted beta<=3/2 side exit in
ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md closes the complete
C-owned or shared HC side after a strict B-owned minimum-f BC contact
with the adjacent C circle corner. The strict R_0 return is not
claimed excluded by this theorem, and no whole UUU gate is ticked.

No extra H/B edge, force reassignment, degree reduction, sampled
coefficient sign, Lean compilation, or CI run is a premise.
