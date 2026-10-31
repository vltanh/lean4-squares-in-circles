# A physical exterior support excludes the entire small-delta free-roof chart

Date: October 31, 2026 UTC. **Complete local hand theorem.**
The mixed free-roof/genuine-other-hub-perpendicular chart cannot have
delta<=pi/4. Its actual two exterior axes consequently make an acute
angle. This closes an entire angular feature, not the remaining side
channel or a whole original load row. No computer certificate, Lean
or CI is used.

## 1. Exact physical hypotheses and full D star

Use the actual geometric domain derived in Sections 1--2 of
`TWO_STRICT_FREE_ROOF_OTHER_HUB_PERPENDICULAR_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md`,
**before that source assumes anything about N**. In particular

    P=(d,1/2), Q=(d,-1/2),
    9/10<d<61/60,
    k=(C,S), v=(-S,C), C=cos(beta), S=sin(beta),
    0<beta<delta<pi/2,
    a=sin(delta), w=cos(delta),
    W-P=-a*k-w*v,
    t_D=a-S in (0,1), epsilon=C-w in (0,1).

P and W are adjacent strict vertices of the actual free-roof hub A.
The other actual A axis is b=-w*k+a*v. The unchanged D-to-V and
D-to-A forces are nu*k and gamma*v, with nu,gamma>0. D is an
unloaded true3 with its actual third neighbor C_*. Write C_* for
that square to distinguish it from C=cos(beta).

The complete D force and moment are

    F_(D,C_*)=-nu*k-gamma*v,
    gamma*(1-t_D)=nu*(1-epsilon).

The force exposes the actual strict D corner

    L=Q-k+(epsilon-1)*v.

Define the positive scalars and the original exterior normal

    A0=1+S-a>0,
    B0=1-C+w>0,
    r=nu/gamma=A0/B0,
    c_0=(r*k+v)/sqrt(1+r^2).                        (1)

The entire actual C_* lies in c_0.x<=c_0.L. Hence its opposite inner
support height is exactly

    H_C=-c_0.L
      =[r*(1-d*C+S/2)+(1+d*S-C/2+w)]/sqrt(1+r^2).  (2)

The physical unit-square support cap in the same disk gives

    H_C<=d.                                         (3)

It uses neither a C_* load nor a C_* own-axis assumption: every unit
center z obeys |z|<=d+1/2 and every directional halfwidth is at least
1/2. Thus the present theorem permits arbitrary true degrees, loads,
additional forces and physical circle masks at C_*, B and N. No
endpoint or N equation is used. The full unloaded D3 is essential.

## 2. A complete two-parameter lower bound when delta<=pi/4

Assume for contradiction 0<beta<delta<=pi/4. Then

    0<a<=w, a^2+w^2=1,
    r0:=(1-a)/w<=r<=1.                              (4)

For the upper bound, sin(theta)+cos(theta) is increasing on
[0,pi/4], so S+C<=a+w and A0<=B0.
For the lower bound, direct subtraction gives

    w*A0-(1-a)*B0=w*S-(1-a)*(1-C)>0.

Indeed S/(1-C)=cot(beta/2)>1 and w>1-a, the latter following
from a+w>1. This proves (4), including its harmless closed endpoints.

From (1) we also have

    S=a-1+r*B0>=a-1+r*w>=0.                        (5)

In (2), use d*C<=61/60, d*S>=9*S/10, C<=1 and r*S/2>=0.
Then (5) gives the exact lower comparison

    H_C >= [1/2+w+(9/10)*S-r/60]/sqrt(1+r^2)
         >= [A1+B1*r]/sqrt(1+r^2),                  (6)

where

    A1=w+(9/10)*a-2/5>0,
    B1=(9/10)*w-1/60>0.

The function f(r)=(A1+B1*r)/sqrt(1+r^2) has derivative

    f'(r)=(B1-A1*r)/(1+r^2)^(3/2).

It has no interior minimum on the interval [r0,1]. Thus it suffices
to bound its two endpoint values. This is a complete continuous
comparison, not a discretized parameter check.

## 3. The endpoint r=1 is uniformly above 61/60

At r=1,

    f(1)=[(19/10)*w+(9/10)*a-5/12]/sqrt(2).         (7)

The function 19*cos(delta)+9*sin(delta) is concave on [0,pi/4].
Its endpoint values are 19 and 14*sqrt(2)>19. Therefore

    f(1)>=89/(60*sqrt(2))>61/60.                    (8)

The last comparison is exact: 89^2=7921 exceeds 2*61^2=7442.

## 4. The endpoint r=r0 is uniformly above 61/60

Since a-1+r0*w=0, its lower comparison is

    f(r0)=[1/2+w-r0/60]/sqrt(1+r0^2).

The elementary half-angle identity
r0=tan(pi/4-delta/2) rewrites it as

    G(delta)=(1/2+cos(delta))*sin(pi/4+delta/2)
                  -(1/60)*cos(pi/4+delta/2).        (9)

This function is concave on [0,pi/4]. To verify the claim explicitly,
put z=pi/4+delta/2 and use the product-to-sum identity. Its second
derivative is

    G''(delta)=-(1/8)*sin(z)
                -(9/8)*sin(pi/4+3*delta/2)
                -(1/8)*sin(pi/4-delta/2)
                +(1/240)*cos(z)<0.                 (10)

All three displayed sine factors are positive in this closed
interval. Moreover sin(z)>1/2 and cos(z)<=1, so already the first
and last terms have sum less than -1/16+1/240<0.

At its left endpoint, (9) gives

    G(0)=89/(60*sqrt(2))>61/60.

At its right endpoint, 1/sqrt(2)>7/10,
sin(3*pi/8)>9/10 and cos(3*pi/8)<=1 yield

    G(pi/4)>(1/2+7/10)*(9/10)-1/60
             =319/300>61/60.                       (11)

These trigonometric comparisons are exact: 1/2>49/100 proves the
first, while sin^2(3*pi/8)=(2+sqrt(2))/4>17/20>81/100 proves the
second, using sqrt(2)>7/5. Concavity puts every value of G above
the smaller endpoint value. Thus f(r0)>61/60 throughout (4).

## 5. Complete support-cap contradiction

Sections 3 and 4 cover both possible minima in (6). Therefore every
actual configuration with 0<beta<delta<=pi/4 would satisfy

    H_C>61/60>d,

contradicting the physical support cap (3). We have proved the
whole-domain local conclusion

    delta>pi/4.                                     (12)

No actual unit, normal, support, circle split or original mean was
modified in the comparison functions. The circle and all nine actual
units remain unchanged. The result applies to loaded N as well as
unloaded N, because no equation at N was used.

## 6. The resulting actual exterior axes are acute

The actual physical A axis b=-w*k+a*v and the unchanged D exterior
axis c_0 in (1) satisfy

    b.c_0=(a-w*r)/sqrt(1+r^2).

By (1),

    B0*(w*r-a)
       =w*(1+S)-a*(1-C)-2*a*w
       =sin(delta+beta)-(2*a*w+a-w).                (13)

For pi/4<delta<pi/2, the quantity 2*a*w+a-w is strictly greater
than one. An exact proof compares the two nonnegative quantities
w*(2*a-1) and 1-a; their squared difference is

    2*a*(1-a)*(2*a^2-1)>0.

Since sin(delta+beta)<=1, (13) is strictly negative. B0>0 then gives
a-w*r>0. The k coefficients of b and c_0 have opposite strict signs,
so these unit axes cannot be parallel. Consequently

    0<b.c_0<1.                                      (14)

In the original mixed free-roof D02 caller, the full A3 and unchanged
singleton selector make AB physically shared with outward direction
b; the genuine D3 exterior singleton makes C own c_0. Thus (14) is
an actual acute angle between the two endpoint own axes there. This
scope does not invent an exterior b force at a higher-degree A.

## 7. A stronger whole-diagonal exclusion with arbitrary endpoint degrees

Restore the full original unloaded A3 and the unchanged common selector,
so that the actual AB is shared and the actual DC singleton is C_*-owned,
as proved in the geometric source's Section 2. Keep the actual positive
two-edge path B--N--C_*, where N is an unloaded true-degree-two diagonal
transmitter. The true degrees, loads, circle masks and all additional
forces of B and C_* may now be **arbitrary**.

The original diagonal-N geometry and the same initially common
incident-diagonal avoidance make both endpoints own the N direction.
Therefore B and C_* have parallel actual frames. They also own b and
c_0 respectively. These two own axes must then have dot product in
{-1,0,1}. This contradicts the whole-domain strict relation (14).

Thus the entire mixed free-roof/genuine-other-hub-perpendicular
diagonal bridge is impossible **without using any B or C_* equilibrium,
load or torque equation**. Every extra original endpoint force remains
present. The only force stars used are the actual full hub equations,
and the original N2 is used only to identify its genuine diagonal
transmitter type and unchanged endpoint ownership convention.

This corollary includes the entire original L135 diagonal feature and
extends to the same physical subgraph in larger six-through-nine-body
components with higher-degree endpoints. It does not convert a loaded
N or a higher-degree N into a transmitter. The original all-loaded-
endpoint proof remains valid at its own scope; the present corollary
strictly weakens its endpoint hypotheses.

## 8. What this theorem closes and what remains

The entire original angular sector delta<=pi/4 is excluded by an
actual contained-unit contradiction, across all original loads and
degrees outside the stated D3. The surviving mixed genuine
perpendicular feature has the precise restriction (12) and the acute
exterior axis relation (14). These are whole-feature hand theorems.

For the remaining unloaded side N, a complete positive-cone proof
for the original endpoint support difference, followed by the actual
radial endpoint or whole-nine capacity analysis, is still needed.
This source does not infer that strict support cone merely from the
acute axis relation. It also does not assume that a radial endpoint's
original side application is its side midpoint: a genuine original
mean still ranges over the full open unit side.

The separate entire diagonal-N exclusion is already proved in
`TWO_STRICT_FREE_ROOF_OTHER_HUB_PERPENDICULAR_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md`.
Neither theorem alone closes the full mixed feature, the whole L135
or L1345 load row, or a canonical coarse parent. No original ledger
flag changes here. Independent broad audit and formalization remain
separate.
