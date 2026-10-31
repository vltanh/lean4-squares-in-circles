# Shared parallel-tip ports admit a whole left-cap matching theorem

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free geometric theorem and conditional capacity theorem, submitted for separate independent review.** The actual terminal port is allowed to lie to the right of the incoming tip's left side. Every physical terminal circle corner and every possible terminal contact owner is retained. A caller must separately establish the actual whole-cap and angular-routing premises of the capacity corollary.

## 1. Actual geometric statement, including the closed endpoints

Put

    Q=1105/256, rho=9/8, sigma=1/sqrt(2),
    r0=181/140.

Assume 2<=R<=sqrt(Q). In the unchanged disk D_R let the actual unit V be

    V=[-x,1-x] x [y-1,y],
    1/2<=x<=1, y>0,
    x^2+y^2=R^2.                                    (1)

Thus Z_V=(-x,y) is an actual physical circle corner. At x=1/2 both top corners are physical; no weight is prescribed.

Let T be any actual physical-boundary unit contained in D_R. Suppose it contains the actual point

    P=(-a,y-2), 0<a<=x,                              (2)

and that P is a minimum support point for a direction n with both coordinates strictly negative:

    n_x<0, n_y<0,
    n.(Z-P)>=0 for every Z in T.                     (3)

No force, degree, normal-selection or contact-type premise is made in this geometric theorem. If a caller uses its original normal and original application, those remain unchanged.

**Theorem A.** These actual premises imply:

1. x>9/16 and a>1/2.
2. Every physical circle corner Z of T satisfies Z_x<-a.
3. T's actual center has a unique angular lift theta_T in (90,270) degrees, with theta_T<230 degrees.
4. There is an actual point of the radius-rho circle in open V at an angle phi such that

       arg(Z_V)<phi<arg(Z_V)+20 degrees,
       theta_T<phi+100 degrees.                      (4)

The statement includes x=1, a=x and R=2 without perturbing any physical unit.

## 2. Exact height bounds and the lower port-coordinate bound

Equation (1) gives

    sqrt(3)<=y<121/60,
    -7/25<y-2<1/60,                                 (5)

because sqrt(3)>43/25 and

    (121/60)^2-(Q-1/4)=31/57600>0.

A boundary unit containing P has one actual circle corner within distance sqrt(2) of P. Therefore

    |P|>=R-sqrt(2)>=2-sqrt(2).                       (6)

The exact comparison sqrt(2)<99/70 gives

    (2-sqrt(2))^2>12/35.

Using (5)--(6),

    a^2>12/35-49/625
       =1/4+253/17500.

Hence a>1/2, with its sign supplied in (2).

In fact x>9/16. Otherwise y>=sqrt(943)/16>19/10, so |y-2|<1/10. Since a<=x,

    |P|^2<=81/256+1/100<12/35<(2-sqrt(2))^2,

contradicting (6). This excludes the whole short-coordinate interval, including x=1/2 and x=9/16. No terminal physical mask or circle weight is used.

## 3. Every actual T circle corner lies left of the actual port line

Suppose a physical circle corner Z of T has Z_x>=-a. Put w=Z-P. The actual support inequality (3) gives w_y<=0, including the case w_x=0. The diameter bound gives

    -a<=Z_x<=sqrt(2)-a,
    y-2-sqrt(2)<=Z_y<=y-2.

Since 1/2<a<=1 and sqrt(2)<3/2,

    |Z_x|<=1.

Since y>43/25 and sqrt(2)<10/7, (5) also gives

    |Z_y|<299/175.

Consequently

    |Z|^2<1+(299/175)^2
           =4-2474/30625<4<=R^2,

a contradiction. Thus every physical T circle corner is strictly left of x=-a. This is a statement about the whole physical circle mask, independent of individual coefficients.

The support is used exactly at the actual P in (2). No point is shifted to the line x=-x.

## 4. Terminal center and the complete bottom-face angle comparison

Let c_T be T's actual center. The unit circumradius and boundary status give

    |c_T-P|<=sigma,
    r_T:=|c_T|>=R-sigma>r0.                          (7)

Use sigma<17/24 and sigma<99/140. Equations (2),(5) and a>1/2 imply

    (c_T)_x<5/24, |(c_T)_y|<1.

If (c_T)_x>=0, its squared radius would be below (5/24)^2+1, whereas r_T>31/24. The exact difference is 5/8>0. Hence (c_T)_x<0, giving the unique angle lift theta_T in (90,270) degrees.

If its height is negative, (5),(7) give

    |(c_T)_y|/r_T<691/905<49/64<sin(50 degrees).

The rational reserve in the middle comparison is 121/57920. The last inequality is cos(40 degrees)>49/64. Thus theta_T<230 degrees. A nonnegative height satisfies this automatically.

Define the actual limiting angles

    phi_L=acos(-x/rho),
    phi_B=180 degrees-asin((y-1)/rho).               (8)

They lie in (90,180) degrees. Every phi between 90 degrees and min(phi_L,phi_B) is an actual radius-rho point in open V: its negative x coordinate is strictly between -x and 1-x, even at x=1, and its height is strictly between y-1 and y.

The complete bottom-face comparison is

    theta_T-phi_B<100 degrees.                      (9)

For precision, the four closed height intervals and their exact comparisons are as follows.

| Entire height interval | Actual terminal center bound | Actual bottom-face bound |
| --- | --- | --- |
| y<=9/5 | theta_T<230 degrees | rho*sin(50 degrees)>441/512>4/5>=y-1, so phi_B>130 degrees |
| 9/5<=y<=19/10 | |(c_T)_y|/r_T<127/181<1/sqrt(2), so theta_T<225 degrees | rho*cos(35 degrees)>rho*cos(36 degrees)>9/10>=y-1, so phi_B>125 degrees |
| 19/10<=y<=49/25 | |(c_T)_y|/r_T<113/181<77/120<sin(40 degrees), so theta_T<220 degrees | rho^2*sin(60 degrees)^2-(24/25)^2=4419/160000>0, so phi_B>120 degrees |
| y>=49/25 | R>101/50, r_T>919/700, and |(c_T)_y|/r_T<523/919<4/7<sin(35 degrees), so theta_T<215 degrees | rho^2*(197/240)-(61/60)^2=1211/230400>0 and cos(25 degrees)^2>197/240, so phi_B>115 degrees |

The height ratios need only be considered when the center has negative height. The respective port lower bounds are y-2>=-1/5, -1/10 and -1/25. In the last row,

    1/4+(49/25)^2-(101/50)^2=7/625>0.

All interval endpoints are included, and every final comparison is strict. The elementary trigonometric inequalities are the exact comparisons in the pinned two-circle source; no physical-two-circle force relation is imported.

## 5. Complete left-face angle comparison on the remaining interval

By Section 2 it remains only to consider 9/16<x<=1. Put

    y0(x)=sqrt(4-x^2),
    v0(x)=(2-y0(x)+99/140)/r0.

For negative center height, (5),(7) imply

    theta_T<180 degrees+asin(v0(x)).                (10)

This remains strict when R=2, because sigma<99/140 and r_T>r0 are strict. On the entire interval [9/16,1],

    y0>=sqrt(3)>43/25,
    0<v0<691/905<4/5,
    sqrt(1-v0^2)>3/5,
    r0>9/7.

Using radians for derivatives gives

    d/dx asin(v0(x))
       =x/[r0*y0(x)*sqrt(1-v0(x)^2)]
       <875/1161<8/9<=phi_L'(x).                   (11)

The exact strict reserve between the two rational derivative bounds is 157/1161.

At x=9/16,

    phi_L=120 degrees,
    y0=sqrt(943)/16>19/10,
    v0<113/181<sin(40 degrees).

The comparison angle in (10) is therefore below 220 degrees. Its difference from phi_L strictly decreases on the whole closed interval by (11). Thus

    theta_T-phi_L<100 degrees                       (12)

throughout the actual domain, including x=1. A nonnegative center height again satisfies the conclusion directly.

The scalar comparisons in Sections 4--5 reproduce the relevant complete continuous intervals from the wide-cap predecessor. They do not invoke that predecessor's different port-position or cap-line hypothesis.

## 6. A uniform twenty-degree entry margin from the actual V circle corner

The additional bound needed for the weaker cap line x=-a is

    min(phi_L,phi_B)<arg(Z_V)+20 degrees.            (13)

Write

    arg(Z_V)=90 degrees+alpha,
    x=R*sin(alpha), y=R*cos(alpha).

Since 0<x<=1 and R>=2,

    0<alpha<=30 degrees.

The point rho*Z_V/R is in open V: its left coordinate is strictly inside, its right coordinate is negative and 1-x>=0, and its vertical drop from Z_V is less than R-rho<1. Thus

    arg(Z_V)<min(phi_L,phi_B).                       (14)

We prove (13) by checking that the radius-rho point at angle arg(Z_V)+20 degrees is strictly outside V across its left or bottom face. These are comparisons of actual points, not replacement force directions.

The exact elementary bounds used here are

    15/16<cos(20 degrees)<47/50,
    sin(20 degrees)>17/50,
    cos(40 degrees)<77/100,
    sqrt(3)/2>173/200.                              (15)

For completeness, cos(40 degrees)>49/64 gives cos(20 degrees)^2>113/128>(15/16)^2, with last reserve 1/256. The polynomial f(z)=4z^3-3z is strictly increasing for z>1/2. At 77/100,

    f(77/100)+1/2=4033/250000>0,

while f(cos(40 degrees))=-1/2, proving the upper bound. At 47/50,

    f(47/50)-1/2=73/31250>0,

while f(cos(20 degrees))=1/2, proving its upper bound. The sine bound follows from

    1-(47/50)^2-(17/50)^2=1/1250>0.

The last bound in (15) follows from 3-(173/100)^2=71/10000>0.

If 0<alpha<=20 degrees, then

    sin(alpha+20 degrees)/sin(alpha)
       =cos(20 degrees)+cot(alpha)*sin(20 degrees)
       >=2*cos(20 degrees).

Since

    2*rho*cos(20 degrees)>135/64>25/12>R,

with rational reserve 5/192 in the middle comparison, the candidate's negative horizontal coordinate has magnitude strictly greater than x. It is outside V across the left face.

If 20 degrees<=alpha<=30 degrees, put

    g_R(alpha)=(R-rho*cos(20 degrees))*cos(alpha)
                  +rho*sin(20 degrees)*sin(alpha).

It is positive and concave on this whole angle interval, and it increases with R. Hence its minimum is at least the smaller endpoint value of g_2. The bounds (15) give

    g_2(20 degrees)
       =2*cos(20 degrees)-rho*cos(40 degrees)
       >1+7/800,

    g_2(30 degrees)
       >(2-rho*(47/50))*(173/200)
           +(9/16)*(17/50)
       =1+521/80000.

Thus g_R(alpha)>1 throughout. Equivalently the candidate's height

    rho*cos(alpha+20 degrees)<R*cos(alpha)-1=y-1

is strictly below V's bottom side. This proves (13), including alpha=20 and alpha=30.

Combining (9),(12),(13),(14), choose phi sufficiently close below min(phi_L,phi_B), while above arg(Z_V). It is an actual open-V point and satisfies both strict inequalities in (4). Theorem A is proved over its complete domain.

## 7. Conditional capacity with the actual weaker cap line

Keep the actual V,T above and all other original units in an interior-disjoint contained packing. Suppose a collection of actual extra squares E is independently known to satisfy

    the whole E is contained in {z:z_x<=-a},

    arg(Z_V)<=theta_E<=theta_T+15 degrees,           (16)

where theta_E is its actual center angle on the same lift. These are actual routing premises. A caller must obtain them from its complete occupied embedding and original equations.

**Theorem B.** There is at most one such extra.

Every square has horizontal halfwidth at least 1/2, so

    (c_E)_x<=-a-1/2<-1,
    |c_E|>1.

The actual center of T also has radius greater than r0>1. Thus the closed centered forty-degree arc theorem applies to every E and T: each contains the entire closed radius-rho arc of halfwidth20 degrees in its open interior. Distinct units have minor center separation strictly greater than40 degrees.

Let phi be the actual V point from Theorem A. If theta_E<=phi, then (16),(4) give

    0<=phi-theta_E<20 degrees.

The point phi would lie in both open E and open V, impossible. Consequently theta_E>phi, and the same argument gives the strict stronger gap

    theta_E-phi>20 degrees.                         (17)

If theta_E>=theta_T, (16) gives a gap at most15 degrees between actual E and T centers, again impossible. Thus theta_E<theta_T.

If two extras have theta_1<theta_2, the full centered arcs and (17) give

    theta_1-phi>20 degrees,
    theta_2-theta_1>40 degrees,
    theta_T-theta_2>40 degrees.

All these are minor gaps because theta_T-phi<100 degrees. Their sum contradicts that strict matching bound. This proves the entire conditional capacity theorem.

The use of the actual twenty-degree entry margin (13) is essential: when a<x, a center bound from the cap line alone does not automatically place an extra center after phi_L. No such stronger cap or angle statement is assumed.

## 8. Exact inputs and scope

| Complete source | SHA256 | Operative use |
| --- | --- | --- |
| ADJACENT_CIRCLE_TIP_WIDE_LEFT_CAP_INNER_ARC_MATCHING.md | 14ca7fbac82fb74b698ab17df01eb1783ce558e75fa8b5a528bbb8fb7bba76c1 | Continuous scalar method of Sections 3--6, reproduced above on the present complete port domain; neither its a>x premise nor its stronger cap line is assumed |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Exact elementary trigonometric comparisons only, in Sections 8 and 13 |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Complete actual centered forty-degree arcs, only in Theorem B |

The new port lower bound, all-physical-corner cap, complete entry-angle estimate and conditional capacity argument are proved above. The geometric theorem uses no force equation, degree, normal selection, circle coefficient or terminal owner. The routing corollary does not by itself identify an original graph pocket.

No original gate is changed. No pose sampling, orientation mesh, optimization, computational exclusion certificate, changed force or mean, normal reselection, Lean compilation, CI, workflow, commit or remote action was used.

