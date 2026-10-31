# Every perpendicular D-side return with b at most one half has a hand bridge exclusion

Date: October 31, 2026 UTC.

**Status: complete hand exclusion of the whole 0<b<=1/2 interval.**
In the original physical-two West/strict, A-owned perpendicular
singleton AD feature, suppose the exterior return at D is on its
opposite side, with its full original mean. Every such configuration
with b<=1/2 is impossible. One uniform actual A-frame projection
excludes all side transmitters; the already proved radius-free
diagonal lemma excludes every diagonal transmitter.

The full B/C loaded equations are not used. All original endpoint
degrees, loads, circle masks and means are retained, as are the
three completing units. The larger interval b>1/2 is not excluded
by this manuscript. No original-row closure is claimed.

## 1. Complete original chart and unchanged hand inputs

Keep the entire original same-nine physical packing and the complete
A3,D3,V2,N2 stars. A,D,N are unloaded, V is loaded and has two
physical circle corners. The side-transmitter classification at N
uses its entire original true-positive-degree-two star; B,C may
have arbitrary other original edges and forces.

The hand chart and original D-side-return identities are Sections
1--2 of
`PHYSICAL_TWO_PERPENDICULAR_SINGLETON_WHOLE_SIDE_RETURN_EXCLUSION_2026_10_30.md`,
which derive them from the preceding complete hand perpendicular
singleton sources. Its generated cover and resulting inequalities
are not used here. Retain

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,1/2-H), 1/2<H<=1,
    h=(c,-s), e=(s,c), c=cos(alpha), s=sin(alpha),
    A=P+[-1,0]*h+[-ell,1-ell]*e,
    W=P-x_A*h-ell*e,
    v=W-Q=-a*h+b*e=(-u,Y_D),
    w_D=-b*h-a*e=(-Y_D,-u),
    D=Q+[0,1]*v+[0,1]*w_D,
    a^2+b^2=1, u=a*c-b*s>0, Y_D=a*s+b*c>0.

The actual A and exterior support coordinates are

    X=1-x_A=1-a+H*s in (0,1),
    Y=1-ell=1+b-H*c in (0,1),
    m=mu/gamma=X/Y,
    p=sqrt(1+m^2), f=(-m*h+e)/p,
    K=P-h+Y*e.

The original C application is the whole original D-side mean

    L=Q+w_D+z*v,
    z=u*a/c in (0,1),
    f_C=w_D=-b*h-a*e.

Thus K is minimum-f support in the actual B, and L is
minimum-f_C support in the actual C. No endpoint owner or side
mean is changed. The complete original full force and torque
identities give

    q=gamma/nu=u/b>0,
    B0=d*s+c/2,
    H-1/2=m*q*B0.                              (1)

The preceding complete hand large-angle exclusion gives c>3/4,
so s<2/3 and

    0<T:=tan(alpha)<sqrt(7)/3<9/10<1.          (2)

Only this already proved hand angle exit is needed from the earlier
scalar restrictions. In particular the hand proof below does not
use a generated bound on the return ratio or a generated pose.

Keep all nine original units when invoking the current analytic
R>2 theorem: `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`,
Sections 1--3, with `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`,
Sections 2--6, and its accepted join
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3.
Its printed radial measure has mass 8997/1000<9 and assigns at
least one to every contained open unit. No historical computational
mass certificate is used. Hence d>14/15. The original upper
radius and all physical V coefficient endpoints remain assumptions.

From now on assume the whole interval

    0<b<=1/2, a=sqrt(1-b^2)>=sqrt(3)/2>6/7.     (3)

## 2. One exact projection will exclude every side N

The complete whole-square support-span lemma gives

    min_B e-coordinate >=K.e-m/p,
    max_C e-coordinate <=L.e+b.

It includes original supported vertices, side points and full
means. In the actual hub chart,

    (K-L).e=1+a+(1-z)*b.

Therefore the entire B-to-C e gap is at least

    1+a-z*b-m/p=1+J_b(T)-m/sqrt(1+m^2),
    J_b(T)=a*(1-a*b+b^2*T).                    (4)

The last equality uses z=a*(a-b*T). To exclude every original
side transmitter, it suffices to prove the whole-domain inequality

    J_b(T)>m/sqrt(1+m^2).                      (5)

Indeed its unchanged full N2 would give original applications
T_N in B, U_N in C with |T_N-U_N|=1. Their e projection cannot
exceed one, whereas (4)--(5) make every such projection greater
than one. This argument uses the actual whole squares, not only
a chosen pair of support vertices.

## 3. Two original upper bounds for m

The complete V equation (1), H-1/2<=1/2 and d>14/15 give

    m< m_V(b,T)
      =b*(1+T^2)/[(a-b*T)*(1+(28/15)*T)].        (6)

All denominators are positive. In fact for every comparison
0<b<=1/2 and 0<=T<=9/10,
a-b*T>=sqrt(3)/2-9/20>0.

The purely geometric ratio X/Y increases with H, since its
H derivative has positive numerator s*(1+b)+c*(1-a).
Thus the actual upper bound H<=1 also gives

    m<=(1-a+s)/(1+b-c).                        (7)

Both (6) and (7) concern the same original force ratio. Neither
is an independently selected contact or coefficient.

For fixed T, m_V strictly increases in b: the derivative of
b/(a-b*T) is 1/[a*(a-b*T)^2]>0. In contrast J_b(T)
strictly decreases in b on the whole comparison domain (2)--(3).
For a direct check,

    J_b(T)=a-b+b^3+a*b^2*T,
    dJ_b/db=-b/a-1+3*b^2+T*(2*a*b-b^3/a).

The T coefficient is positive for b<=1/2. Replace T by its
strict upper bound one and multiply by a>0; the resulting bound is

    a*(dJ_b/db)<(1-3*b^2)*(b-a)<0.             (8)

Also J_b(T) increases with T. These are scalar comparisons
throughout positive denominators, not motions of physical squares.

## 4. Three exact continuous intervals cover T>=1/16

By (6)--(8), it is enough in this sector to compare the largest
m_V and the smallest J, both at b=1/2. Their values are

    m_V(1/2,T)
       =(1+T^2)/[(sqrt(3)-T)*(1+(28/15)*T)],
    J_(1/2)(T)=sqrt(3)/2-3/8+(sqrt(3)/8)*T.

Use the rational lower bounds sqrt(3)>17/10 and
sqrt(3)/2>173/200. Define the positive quadratic

    D(T)=(17/10-T)*(1+(28/15)*T).

The following exact hand table covers the whole closed interval
[1/16,9/10]. In a row with bound m_V<A/B, the polynomial
A*D(T)-B*(1+T^2) is strictly concave, so its positive endpoint
values prove the inequality everywhere on that row.

| Entire T interval | A/B | Left endpoint reserve A D-B(1+T^2) | Right endpoint reserve | Uniform lower bound for J_(1/2) |
| --- | --- | --- | --- | --- |
| [1/16,1/2] | 4/7 | 5507/19200 | 53/100 | J>1/2 |
| [1/2,3/4] | 5/7 | 57/20 | 37/80 | J>7/12 |
| [3/4,9/10] | 17/20 | 751/100 | 31/125 | J>13/20 |

The J bounds follow from its monotonicity in T and the single
lower bound sqrt(3)/2>173/200. The three corresponding left
endpoint lower bounds are respectively

    1289/2560>1/2,
    957/1600>7/12,
    2087/3200>13/20.

All three comparisons with the normalized force are strict:

    (4/7)/sqrt(1+(4/7)^2)=4/sqrt(65)<1/2,
    (5/7)/sqrt(1+(5/7)^2)=5/sqrt(74)<7/12,
    (17/20)/sqrt(1+(17/20)^2)=17/sqrt(689)<13/20.

Their positive squared integer comparisons are 64<65,
3600<3626, and 115600<116441. Since m/sqrt(1+m^2)
strictly increases with positive m, this proves (5) throughout
the entire T>=1/16 sector. Every table endpoint is retained;
the table certifies three concave quadratic inequalities over
whole intervals, not sampled square poses.

## 5. The whole interval 0<T<=1/16

First (6) gives a convenient further comparison throughout this
small-T interval:

    m_V(b,T)<b/a.                              (9)

To verify it, after positive cross-multiplication the needed
difference is

    (a-b*T)*(1+(28/15)*T)-a*(1+T^2)
       =T*[(28/15)*a-b-((28/15)*b+a)*T]>0.

Indeed (3) gives (28/15)*a-b>11/10, while
((28/15)*b+a)*T<2/16=1/8. Thus (9), and hence
m/sqrt(1+m^2)<b, holds for every original T in this interval.

### 5.1. The whole interval 0<b<=12/25

Both J_b(0) and J_b(0)-b decrease in b by (8). At b=12/25,
a=sqrt(481)/25>7/8; the squared reserve is 159/40000.
Consequently

    J_b(T)-b>=J_(12/25)(0)-12/25
       =sqrt(481)/25-13272/15625
        >7/8-13272/15625=3199/125000>0.

Together with (9), this proves (5) on the whole indicated interval.

### 5.2. The whole interval 12/25<=b<=1/2

Now use (7), s<T<=1/16, c<1, and a>6/7:

    m<(1-6/7+1/16)/(12/25)
       =575/1344<1/2.

At the same time, (8) and positivity of T give

    J_b(T)>=J_(1/2)(0)
             >6/7-3/8=27/56>9/20.

Finally 1/sqrt(5)<9/20, since 1/5<81/400. Thus

    m/sqrt(1+m^2)<1/sqrt(5)<9/20<J_b(T),

which proves (5) on this final sector. The exact joining boundary
b=12/25 and the entire T=1/16 boundary are retained by both
applicable arguments.

Sections 4--5 prove (5) for all the original parameters (2)--(3).
The side-transmitter alternative is therefore completely excluded.

## 6. The same whole b interval excludes every diagonal N

Use D's actual positively oriented frame

    h0=-v=a*h-b*e, e0=-w_D=b*h+a*e.

The C support direction is exactly -e0. The actual B direction is

    f=-A_f*h0+B_f*e0,
    A_f=(a*m+b)/sqrt(1+m^2)>0,
    B_f=(a-b*m)/sqrt(1+m^2)>0.

For completeness the second sign follows directly, without a
generated inequality:

    a*Y-b*X=a-b+2*a*b-H*(a*c+b*s)
              >=a-b+2*a*b-1>0.

Here a*c+b*s<=1. The last difference is
b*[(2*a-1)-b/(1+a)], which is positive using a>6/7,
b<=1/2. Thus A_f^2+B_f^2=1 with both coefficients positive.

Put j_D=1-z>0. The unchanged support difference is

    K-L=-(X+a*j_D-b)*h+(1+a+b*j_D)*e
        =-E*h0+G*e0,
    E=a*X+b+j_D>0,
    G=1+a-b*X.                                 (10)

Since X=1-a+H*s<1-a+2/3, (3) gives

    G>1+a*(1+b)-(5/3)*b
       >13/7-(17/21)*b
       >=61/42>sqrt(2).                        (11)

The final squared reserve is 61^2-2*42^2=193>0.
Also the original A-frame e projection in (10) gives

    |K-L|^2> (1+a)^2>(13/7)^2>3.              (12)

The complete radius-free diagonal obstruction in Section 2 of
`PHYSICAL_TWO_PERPENDICULAR_SINGLETON_WHOLE_SIDE_RETURN_EXCLUSION_2026_10_30.md`
now applies at its literal hypotheses: E>=0, G>sqrt(2),
|K-L|^2>3, the actual B and C support directions, and the
unchanged full N2 with its initially selected incident-diagonal
avoidance. That section proves all signs of the diagonal direction
and all original support ties by hand; no later generated inequality
from that source is used here. Thus the whole diagonal alternative
is impossible as well.

## 7. Complete interval conclusion and precise remainder

An unloaded true2 N has exactly its original side or diagonal
alternative. Sections 2--5 and Section 6 exclude both for the
entire interval 0<b<=1/2, retaining all actual original means,
endpoint circle masks and extra positive forces at B,C. All nine
units stay present in the hand radius input. No B or C degree-two
equation has been used or manufactured.

The preceding complete large-component hand theorem already
excluded b>=16/25. Therefore the only still unproved part of this
particular D-side-return family after the present result is

    1/2<b<16/25,

with all its original force, moment, containment, return-ratio and
bridge conditions still retained. This is an honest remaining
interval, not a claim that it is realizable. The opposite-D-vertex
return is a different original feature and is not assigned the
side-return torque or mean here.

No generated pose cover, externally checked exclusion, numerical
root, replacement mean, normal reselection, Lean/Lake build or
CI is an input or operation of this hand proof. Preliminary
attacking-direction checks suggested the projection to study;
the proof consists entirely of the displayed full-domain algebra,
three concave polynomial comparisons and the existing hand
diagonal lemma.
