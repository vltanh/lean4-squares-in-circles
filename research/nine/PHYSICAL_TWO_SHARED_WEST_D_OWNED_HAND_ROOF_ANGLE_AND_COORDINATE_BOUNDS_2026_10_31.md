# Shared-West D-only roofs have angle below thirty degrees and height coordinate above eleven twenty-fifths

Date: October 31, 2026 UTC.

**Status: complete hand whole-chart inequalities.** In the original
same-nine shared-West D-only chart, the actual A roof satisfies

    0<alpha<pi/6, 11/25<y<1.

The proof retains the full shared DV mean. It uses the original
A3/D3/V2 equations and just one actual contained point of B.
No equation at B,C,N and no generated cover is used.

## 1. Actual chart and hand radius input

Keep all nine original squares. The complete hand radius-two
exclusion is `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`,
Sections 1--3, with its current fixed values and derivative from
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections 2--6.
The accepted complete dependency join is
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3.
It gives every contained open unit square at least one under the
same radial measure of mass 8997/1000<9. The historical evaluators
and generated boxes are not premises here. This application keeps
the original nine units and yields R>2, hence

    2<R<=sqrt(1105)/16<21/10,
    d=sqrt(R^2-1/4)-1, 14/15<d<61/60.          (1)

Use exactly the original chart and full identities printed in
`PHYSICAL_TWO_SHARED_WEST_D_OWNED_HAND_DIAGONAL_EXCLUSION_AND_SIDE_CONE_2026_10_31.md`,
Section 1. Only its hand chart is needed for this proof, not its
return-mask conclusions. In particular

    c=cos(alpha), s=sin(alpha), 0<alpha<pi/4,
    F=c-s, Sigma=c+s, 0<ell<1, y=1-ell,
    B0=d*s+c/2,
    m=mu/gamma=F/y, n=nu/gamma,
    n*(j-1/2)=m*B0,
    n*(1-j+ell*c)=1-ell*s,
    1/2<j<=1.                                (2)

The actual B-owned inward direction and contact are

    b=(-m*c,1+m*s)/sqrt(1+2*m*s+m^2),
    K=(d-c+y*s,1/2+s+y*c).

Because K is a minimum-b support and b is an actual own axis,
K+b is an actual point of B and belongs to the unchanged disk.
In particular its ordinary height is at most R.

## 2. The original full mean gives a single useful monotone bound

The last two equalities in (2), with j<=1, imply

    2*m*B0<=n<= (1-ell*s)/(ell*c).

Set L0=2*B0*c and r=y/F=1/m. Since 1-ell*s<1, we get

    F*L0*(1-y)<y,
    r> L0/(1+L0*F).                            (3)

This is a necessary bound from the unchanged original mean, not
an independent choice of a force ratio. The exact height of the
same actual point K+b is

    Y=1/2+s+c*F*r
                      +(s+r)/sqrt(c^2+(s+r)^2).      (4)

For fixed alpha, both r-dependent terms on the right strictly
increase with r.

## 3. Every angle at least thirty degrees violates actual containment

Suppose pi/6<=alpha<pi/4. By d>14/15,

    L0=c^2+2*d*s*c
       >1/2+(1/2)*cos(2*alpha)+(14/15)*sin(2*alpha)
       >=43/30.                              (5)

The last comparison is an elementary concavity bound on
2*alpha in [pi/3,pi/2]: the function displayed there has strictly
negative second derivative, so its minimum is at an endpoint.
At pi/2 it is 43/30; at pi/3 it is
3/4+7*sqrt(3)/15>43/30, already using sqrt(3)>3/2.

Put k=43/30 and r0=k/(1+k*F). Equations (3)--(5) give r>r0.
For the remaining scalar comparisons write

    g=s+c*F*r0=(s+k*F*Sigma)/(1+k*F),
    v=s+r0.

The entire interval 0<F<sqrt(3)/2-1/2<3/8 is covered by the
following two exact comparisons.

### 3.1. The interval 0<F<=1/5

Here Sigma^2=2-F^2>=49/25, so Sigma>=7/5,
s>=3/5 and c<=4/5. Moreover

    r0>=215/193>11/10, v>17/10.

Thus

    v/sqrt(c^2+v^2)>17/sqrt(353)>9/10,        (6)

where the final positive squared comparison is
28900>81*353=28593. Also

    (1+k*F)*(g-7/10)
       =(Sigma-7/5)/2+F*(k*(Sigma-7/10)-1/2)
       >=(151/300)*F>0.                      (7)

Equations (4), (6), (7), and r>r0 now imply

    Y>1/2+7/10+9/10=21/10>R.

### 3.2. The interval 1/5<=F<3/8

In this interval s>=1/2, c^2<=3/4, and
Sigma>34/25. The last bound follows from
Sigma>= (sqrt(3)+1)/2 and sqrt(3)>43/25.
Also

    r0>344/369>9/10, v>7/5.

Therefore

    v/sqrt(c^2+v^2)>14/sqrt(271)>17/20,       (8)

with the exact squared reserve
196*400-289*271=81>0. For the other summand,

    (1+k*F)*(g-3/4)
       =(Sigma-3/2)/2+F*(k*Sigma-1/2-3*k/4)
       >-7/100+(1123/3000)*F
       >=73/15000>0.                         (9)

Thus (4), (8), (9) give again

    Y>1/2+3/4+17/20=21/10>R.

Both full intervals contradict containment of the unchanged actual
point K+b. We have proved

    alpha<pi/6.                               (10)

The common endpoint F=1/5 is retained in both comparisons, and
the strict original endpoints F=0 and alpha=pi/4 were never
introduced as admissible configurations.

## 4. A concavity comparison gives y>11/25

Suppose instead that ell>=14/25, equivalently y<=11/25.
The original inequality before (3) gives

    F*L0<= (1-ell)*(1-ell*s)/ell.

For fixed s<1/2, the right side is
1/ell-1-s+ell*s and has derivative -1/ell^2+s<0.
Hence

    F*L0+(11/25)*s<=11/14.                   (11)

But d>14/15 gives a strict lower bound for the left side:

    F*L0+(11/25)*s
       >J(alpha)
        =(c-s)*(c^2+(28/15)*s*c)+(11/25)*s.

On the entire interval 0<=alpha<=pi/6, expand it exactly as

    J(alpha)=(17/60)*cos(alpha)
             +(43/60)*cos(3*alpha)
             +(197/300)*sin(alpha)
             +(13/60)*sin(3*alpha).

All four coefficients are positive. Its second derivative is
strictly negative on this interval, since alpha and 3*alpha lie
in [0,pi/2] and the cosine-alpha term is strictly positive.
Thus J is strictly concave and is at least the smaller endpoint
value. Those exact values are

    J(0)=1,
    J(pi/6)=(85*sqrt(3)+327)/600
              >943/1200>11/14.

The first strict comparison uses sqrt(3)>17/10; the second has
the integer reserve 943*14-11*1200=2. Consequently J(alpha)>11/14
throughout the whole interval, contradicting (11). Therefore

    ell<14/25, y>11/25.                       (12)

This proves both asserted original inequalities. The comparisons
vary scalar formulas only; they do not move a square, replace an
original mean, or assume a stress on comparison geometries.

## 5. Direct exterior-pocket entry

The actual owned B direction, in A's frame, is

    b=(-M*h+e)/sqrt(1+M^2),
    M=(m+s)/c>1,
    x=M*y=1-ell*tan(alpha).

Equations (10)--(12) also give the strict elementary reserve

    x+y-1=y-ell*tan(alpha)
       >11/25-(14/25)*(3/5)=13/125>0,

using tan(alpha)<1/sqrt(3)<3/5. Thus the original upper roof
has precisely the m>1, y>11/25 and x+y>1 inputs of the already
proved two-face comparison-circle gap lemma, with its symbol m
replaced only notationally by M. The accompanying actual pocket
routing and full endpoint masks must still be checked at the
literal caller; this source supplies the whole scalar domain and
does not infer an empty pocket from an inequality alone.
