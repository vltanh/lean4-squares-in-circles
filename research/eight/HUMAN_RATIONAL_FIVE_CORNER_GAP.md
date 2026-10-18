# A rational hand certificate that the seven-ring radius is below the exact five-corner optimum

## Theorem

Let R_hat denote the globally least disk radius for the
projected five-corner family of FIVE_CORNER_REDUCTION.md,
characterized analytically by HUMAN_FAMILY_CLOSURE.md.

Then

    R_hat > 2473/1250 = 1.9784,
    R_hat^2 > 6115729/1562500 > 1957/500.             (1)

In fact

    (2473/1250)^2-1957/500=26/390625>0.              (2)

Thus the exact rational seven-exterior-square *winding
contact ring* of RATIONAL_SEVEN_EXTERIOR_CONTACT_CYCLE.md
has a strictly smaller radius than the **exact**
five-corner optimum. The comparison no longer uses the
decimal approximation to the Cantrell candidate.

This is a full pen-and-paper proof of a **conditional
family bound**, using just four rational weighted
support estimates and eight explicit integer checks.
It does not prove the unrestricted eight-square radius
R_8>=R_hat. The seven-ring construction lacks its eighth,
central square, as proved in HUMAN_RATIONAL_RING_POCKET_AREA.md.

## 1. A dual support inequality for five disk points

Write c=cos t, s=sin t, 0<=t<=pi/4.
The five projected corner inequalities are precisely those
in FIVE_CORNER_REDUCTION.md. Choose **any** four positive
rational weights a,b,d,e and give the fifth inequality
weight one. Summing the five weighted projections and
using the disk's support function gives, for every
feasible five-corner family of radius R,

    B(t) <= R*D(t),                                    (3)

where

    B(t)=2*a+3*b+2*d+e+2+e*s+c,
    D(t)=K+g1(t)+g4(t),

    K=sqrt(a^2+b^2)+sqrt(b^2+d^2)+sqrt(e^2+1),
    g1(t)=sqrt(a^2+1-2*a*s),
    g4(t)=sqrt(d^2+e^2-2*d*e*c).                      (4)

The elementary derivation by collecting the coefficients
of P1,...,P5 appears in HUMAN_FAMILY_ENCLOSURE.md,
section 1. Every coefficient is a fixed vector, and each
scalar product with a disk point is <=R times its Euclidean
norm. In particular (3) is valid for every disk point
configuration, whether any five-corner inequality is
strict or tight.

Put rho=2473/1250. We prove

    B(t)-rho*D(t)>0                                  (5)

for every relevant tilt. Equation (3) will then force
R>rho.

## 2. The whole admissible tilt range becomes short

The existing **hand-proof** analytic enclosure
HUMAN_FAMILY_ENCLOSURE.md proves that any feasible
five-corner chain with R^2<=9789/2500 satisfies

    0<=tan t<1/5.                                    (6)

The present rho satisfies rho^2<9789/2500, by direct
rational comparison. Therefore any putative chain
with R<=rho must obey (6). It suffices to exclude
the closed larger tilt interval

    0<=t<=arctan(1/5).                               (7)

Divide it into four consecutive closed intervals
whose tangent endpoints are

    [0,1/25], [1/25,1/10],
    [1/10,3/20], [3/20,1/5].                         (8)

Use the following **rational weights** on each interval.
All numbers in the table are exact fractions.

| Panel | a | b | d | e |
|---|---:|---:|---:|---:|
| 1 | 592/1000 | 1004/1000 | 1160/1000 | 1160/1000 |
| 2 | 619/1000 | 998/1000 | 1117/1000 | 1097/1000 |
| 3 | 646/1000 | 993/1000 | 1075/1000 | 1046/1000 |
| 4 | 669/1000 | 988/1000 | 1041/1000 | 1005/1000 |

## 3. Strict concavity makes endpoint checks sufficient

Fix one row of weights and set

    E(t)=B(t)-rho*D(t).

For a distance between two rotating planar vectors,

    g(t)=sqrt(A^2+B^2-2*A*B*cos(t-t0)),

straight differentiation gives, wherever g>0,

    g''(t)+g(t)/4
        =(A^2-B^2)^2/(4*g(t)^3)>=0.                 (9)

For g4 of panel 1, d=e and g4(0)=0; its explicit
form `2d sin(t/2)` is smooth for t>0 and
continuous at zero. Thus the interior derivative
argument and endpoint continuity still apply.

Equation (9) applies to g1 and g4. Hence

    E''(t) <= -(e*s+c)+(rho/4)*(g1+g4).             (10)

On the whole short tilt interval in (7),
each row has e>=1, so e*s+c>=s+c>=1.
The row maxima obey

    a<7/10, max(d,e)<=29/25<6/5,
    |d-e|<1/25,    t<1/5.

Therefore

    g1<=sqrt(1+a^2)<5/4,
    g4<=|d-e|+2*e*sin(t/2)
       <1/25+(6/5)*(1/5)=7/25.

Thus g1+g4<5/4+7/25=153/100<2.
Because rho<2, (10) yields

    E''(t)<-1+rho/2<0                             (11)

in each open panel interval. So E is strictly
concave and continuous on every closed panel.
It is enough to prove that E is positive at
**both endpoints** of each of the four panels.

No angle grid or interval partition beyond these
four analytically controlled intervals is used.

## 4. Eight exact integer endpoint certificates

Here are enough explicit integers to independently
check every endpoint by squaring positive rationals.
Set N=100000000. For a nonnegative rational x, define

    Floor_N(x)=floor(N*sqrt(x)),
    Ceil_N(x)=ceil(N*sqrt(x)).

Each value is established by the elementary
integer inequalities

    k^2<=N^2*x<(k+1)^2   (for a floor);
    (k-1)^2<N^2*x<=k^2   (for a ceiling),

with the obvious equality convention for exact
integer square roots. All x used below are
**rational**.

At an endpoint h=tan t, put

    C_h=Floor_N(1/(1+h^2)).

Then c>=C_h/N and s=h*c.
The five exact C_h values are

| h | 0 | 1/25 | 1/10 | 3/20 | 1/5 |
|---|---:|---:|---:|---:|---:|
| C_h | 100000000 | 99920095 | 99503719 | 98893635 | 98058067 |

For weights (a,b,d,e) from the indicated panel set

    B_N=floor[ N*(2a+3b+2d+e+2) +(e*h+1)*C_h ],

    K_N=Ceil_N(a^2+b^2)
         +Ceil_N(b^2+d^2)+Ceil_N(e^2+1),

    G1_N=Ceil_N(a^2+1-2*a*h*C_h/N),
    G4_N=Ceil_N(d^2+e^2-2*d*e*C_h/N),
    D_N=K_N+G1_N+G4_N.                            (12)

Because all a,d,e,h are positive and c>=C_h/N,
equations (4), (12) give the **certified directions**

    B(t)>=B_N/N,   D(t)<=D_N/N.                    (13)

The complete endpoint arithmetic is the following
small table. The final integer column is
`1250*B_N-2473*D_N`, calculated exactly.

| Panel | h | B_N | D_N | Positive integer |
|---|---:|---:|---:|---:|
| 1 | 0 | 1067600000 | 539331829 | 732386883 |
| 1 | 1/25 | 1072156387 | 541914846 | 40069592 |
| 2 | 1/25 | 1060604588 | 536007570 | 209014390 |
| 2 | 1/10 | 1066719276 | 539123134 | 147584618 |
| 3 | 1/10 | 1056611808 | 533997655 | 188559185 |
| 3 | 3/20 | 1061110046 | 536266539 | 200406553 |
| 4 | 3/20 | 1052701850 | 532012799 | 209660573 |
| 4 | 1/5 | 1056667738 | 533956932 | 359179664 |

For example, in panel 1 the constant radical ceiling
sum is K_N=423122362. At h=1/25, the two variable
radical ceilings are G1_N=114155239 and
G4_N=4637245, summing to
D_N=541914846. The lower bound B_N=1072156387
gives

    1250*B_N-2473*D_N=40069592>0.

Every other row is checked by identical fixed
rational squaring and integer addition. Thus
for every one of the eight endpoints,

    E(t)>=B_N/N-rho*D_N/N
         =(1250*B_N-2473*D_N)/(1250*N)>0.        (14)

Strict concavity (11) and continuity now imply
E(t)>0 on all four panels, hence on the whole
interval (7). This proves (5).

## 5. Complete the comparison with the seven-ring

Suppose a five-corner configuration were feasible
with radius R<=rho. By section 2 its tilt lies in
the range covered in sections 3--4. The weighted
disk-support inequality (3) would give

    B(t)<=R*D(t)<=rho*D(t),

contradicting the proved strict inequality (5).
Thus every feasible five-corner chain requires
R>2473/1250. The least one therefore satisfies
the first inequality (1). Since the minimum is
attained by the prior exact stationary-family theorem,
the same strict bound holds for R_hat.

Squaring rho and subtracting the seven-ring squared
radius yields the explicit positive rational gap (2).
The ring R^2=1957/500 is therefore genuinely below
the **exact** least five-corner radius.

The ring has no central unit and its exact interior
free area is smaller than one, so it cannot be promoted
to an eight-square counterexample. Conversely, this
comparison does not show that a radius between these
two values is impossible for **other** eight-square
contact patterns. The unrestricted lower bound
R_8>=R_hat is still open.
