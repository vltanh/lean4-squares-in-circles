# The North/North pair cannot have two tilted boundary tips

Date: October 27, 2026.

**Status: complete original-domain hand exclusion, submitted for full
root and separate independent review.** This closes the entire
two-tilted-boundary-frame case of the surviving unique/unique
North/North interface, for both actual B genuine-leaf types.

Keep the same nine actual squares and the original positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+E, 0<E<1/60,
    R^2=(2+E)^2+1/4<=Q_*=1105/256.

A is the sole AB side owner and has its actual outer-lower S leaf.
The accepted complete contact reductions leave the original
A-owned North AD application (-t_D,H), with

    t_D>0,       37/50<H<1.

B's actual axes and retained North BC point are

    j=(s,-c), f=(c,s),
    c,s>0, c^2+s^2=1,       p=c/s<1/4,
    P=(q,T) in the (j,f) frame,
    q>0,       17/20<T<=1.                            (1)

For the owned B leaf, these are precisely the tilted-C clauses of
ADJACENT_S_C4_OWNED_TILTED_LEAF_NORTH_CONTACT_REDUCTION.md.
For the strict B leaf, its separate complete reduction gives
p<1/4 and k<3/20; the actual identity
k-w=c[xi-wc/(1+s)]>0 gives w<3/20 and hence T=1-w>17/20.
No owned-leaf mean formula is imposed on the strict leaf.

C,D each have one physical circle corner. Both are assumed tilted
at their actual incoming North points. The common compatible
all-cycle-owner theorem applies because both actual root force
pairs are nonparallel and this is the unique/unique mask. Thus
CD has an actual side-axis owner, with its original mean unchanged.

## 1. The complete two actual tip frames

The local high vertical-port theorem gives C's actual frame,
circle corner and unique-corner inequalities in B coordinates:

    C=P+[0,1]u_C+[0,1]v_C,
    u_C=(a,b), v_C=(-b,a),
    a,b>0, a^2+b^2=1,
    Z_C=P+u_C=(q+a,T+b),
    q*b-T*a>1/2,       a/b<1/2.                       (2)

The same theorem, reflected horizontally at D's negative port,
gives in world coordinates

    P_D=(-t_D,H),
    D=P_D+[0,1]u_D+[0,1]v_D,
    u_D=(A,B), v_D=(-B,A),
    A,B>0, A^2+B^2=1,
    Z_D=P_D+v_D,
    t_D*A-H*B>1/2,
    B/A<1/2,       B<1/2,       A>8/9.              (3)

These are the complete physical tilted frames, derived from each
true C2 or D2 proper radial point with its actual boundary neighbor.
The axis-owned limits belong to the other separately stated frame
cases. Neither root is treated as a two-force unit.

We need the slightly sharper C bounds

    a<7/25,       b>24/25,       0<q+a<51/50.          (4)

Here is their full local proof. If a/b>=7/24, equation (2) yields

    Z_C.u_C=q*a+T*b+1
       >T/b+a/(2b)+1
       >(17/20)*(25/24)+7/48+1=65/32.

Also Z_C.v_C<-1/2. Thus
|Z_C|^2>(65/32)^2+1/4=Q_*+61/1024, a contradiction.
This proves the first two bounds in (4). Its actual circle height
T+b>181/100 and the exact reserve

    (51/50)^2+(181/100)^2-Q_*=3/32000

give the final bound.

In world coordinates write

    u_C=(e,f0),       v_C=(-f0,e),
    e=a*s+b*c>0,       f0=b*s-a*c>0.                 (5)

The last positivity follows from a/b<1/2 and p<1/4.

## 2. The full C2 and D2 equations leave exactly two CD owners

Let g be the actual unit normal from D toward C, gamma>0 its
original magnitude, and nu_C,nu_D>0 the original incoming
BC and AD magnitudes. The two full equations are

    F_C=nu_C*f+gamma*g,
    F_D=nu_D*e_y-gamma*g.                             (6)

Each F is its original positive circle force, along the actual
unique circle corner.

Projecting the first equation onto v_C gives

    F_C.v_C<0,       f.v_C=a>0,
    g.v_C<0.                                         (7)

Projecting the second onto u_D similarly gives

    F_D.u_D<0,       e_y.u_D=B>0,
    g.u_D>0.                                         (8)

If D owns CD, (8) leaves only g=u_D. If C owns CD, (7)
leaves only g=-v_C. Thus these two actual side directions
exhaust the original owner cover. No normal has been chosen
in place of the one in the certificate.

## 3. A useful strict height bound for D's original far-side mean

Suppose first that g=u_D. Its dot product with u_C is positive
by (3),(5), and its dot product with v_C is negative by (7).
Therefore C's actual minimum point is its vertex P+v_C.
The same actual point is D's full far-u_D-side mean:

    Q=P+v_C=P_D+u_D+z*v_D,       0<=z<=1.             (9)

The genuine D2 radial point is

    q_D=P_D+rho_D*e_y=lambda_D*Z_D,
    rho_D=(t_D*A-H*B)/(t_D+B)>0.                     (10)

The original CD line through (9) is parallel to u_D.
Comparing its v_D coordinate with (10) gives the exact
unchanged mean

    z=rho_D*A.                                       (11)

We prove the uniform bound

    B+rho_D*A^2>2/3.                                 (12)

The strict corner inequality in (3) says
t_D>(H*B+1/2)/A. For fixed A,B,H the expression in (10)
strictly increases with t_D, since its derivative is
B(A+H)/(t_D+B)^2>0. Consequently

    rho_D>A/[1+2B(H+A)]
           >A/[1+2B(1+A)].                           (13)

It suffices to show
B+A^3/[1+2B(1+A)]>2/3 for 0<B<1/2.
After multiplying positive denominators and using A^2=1-B^2,
this is equivalent to

    A*(3-4B+3B^2)>2+B-6B^2.

Since A>1-B^2 and the factor 3-4B+3B^2 is positive, the
difference is strictly larger than

    (1-B^2)*(3-4B+3B^2)-(2+B-6B^2)
      =(1-2B)^3*(1+B)+5B^4>0.

This proves (12) on the whole actual interval, without a
replacement value of the original side mean.

Equations (9)--(12) now give

    Q_y=H+B+rho_D*A^2
        >37/50+2/3=211/150.                          (14)

But the actual C vertex in (9) has world height

    (P+v_C)_y=(T+a)*s+(b-q)*c
       <1+7/25+1/8=281/200.                          (15)

Here T<=1, a<7/25, q>1/2 from (2), b<1 and c<p<1/4.
If b-q is negative, the bound is only stronger. The exact gap

    211/150-281/200=1/600>0

contradicts (9). This closes the entire D-owned case, including
every original z endpoint.

## 4. The C-owned mean is too high for D's actual right vertex

Now suppose g=-v_C=(f0,-e). By (8) it has positive u_D
component, while its v_D component is

    g.v_D=-f0*B-e*A<0.

Thus D's actual maximum point is its vertex P_D+u_D.
The full actual C side mean is

    Q=P_D+u_D=P+v_C+z*u_C,       0<=z<=1.             (16)

Keep C's unchanged proper radial point

    q_C=P+rho_C*f=lambda_C*Z_C,
    rho_C=(q*b-T*a)/(q+a)>1/[2(q+a)].                (17)

Its CD line is parallel to -v_C. Comparing u_C coordinates
in (16)--(17) forces

    z=rho_C*b>8/17,                                  (18)

where (4) was used in the strict inequality. This is the
actual original mean, not a chosen value.

In B's frame the actual point (16) therefore satisfies

    Q_j=q-b+z*a
       =(q+a)-b-a*(1-z)<3/50,
    Q_f=T+a+z*b>17/20+192/425.                       (19)

The actual B rotation has s>97/100 and c<1/4. Hence

    Q_y=s*Q_f-c*Q_j
       >(97/100)*(17/20+192/425)-3/200
        =1+42111/170000>6/5.                         (20)

Again a negative Q_j only strengthens the bound, and the
original z=1 endpoint is included.

The actual D vertex on the other side of (16) has height
H+B. D's actual opposite corner P_D+u_D+v_D has height
H+B+A and belongs to the containing disk. Therefore

    H+B<=R-A<25/12-8/9=43/36<6/5.                   (21)

This contradicts (20). Only the original actual corner was
used in (21); no numerical placement or alternate square
was introduced.

## 5. Exact complete shared frame conclusion

The full original equations and actual side-owner cover leave
only the two cases handled in Sections 3--4. Both have complete
contradictions, with their full original mean intervals retained.
Thus no actual North/North configuration can have both boundary
tips tilted in this unique/unique domain.

The two literal B-leaf callers were checked at the start.
No D radial-mask equation is used here, and no conclusion
about the separate C-axis/D-tilted or both-axis frames is
assumed. All nine physical squares, original forces, true
degrees, masks and weighted applications survive throughout.

No sampled pose, numerical certificate, normal reselection,
compilation, CI, remote action or shared-metadata edit is a
premise.

