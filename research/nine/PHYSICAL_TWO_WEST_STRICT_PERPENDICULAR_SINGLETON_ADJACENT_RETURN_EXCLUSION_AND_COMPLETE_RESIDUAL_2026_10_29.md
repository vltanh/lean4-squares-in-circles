# Perpendicular singleton roofs: an adjacent-return exclusion and the exact residual

Date: October 29, 2026 UTC. Author: roofs continuation.

**Status: complete proposed hand theorem, awaiting independent review.**
This source excludes the entire adjacent exterior-corner return at the
nonowning hub in the physical-two West/strict roof. It also excludes,
for every exterior owner and original mean, the full interval in which
the strict roof has horizontal component at most 3/4. The two exact
remaining return rows are preserved. No whole D02 row is declared closed.

## 1. Complete original setting

Keep all nine actual interior-disjoint units, their disk about O=0,
all original positive forces, actual normals, full shared means,
physical circle masks and individual zero circle coefficients. Work in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60.

The actual entire positive neighborhoods are

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A,D are unloaded true3; V is loaded true2 with TWO PHYSICAL circle
corners. B,C have arbitrary actual degrees, loads, orientations, masks
and further forces; all their equations remain. Use the original
West/strict physical-two chart

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, 1/2<H<=1,
    h=(c,-s), e=(s,c), c,s>0, c^2+s^2=1.

The original A-to-V normal h is A-owned and strict at V, with
magnitude mu>0; D-to-V is East with magnitude nu>0.
The original AD magnitude is gamma>0.

The exact feature considered is a physical singleton AD owned by A
alone, with its A axis perpendicular to h. Its sign is necessarily -e:
the other sign would put the actual Q of D beyond max_A e>=e.P,
whereas e.Q=e.P-H*c<e.P.

The strict original singleton convention makes both A applications
relative side-interior points. Thus the actual A and original AD point
are

    A=P+[-1,0]*h+[-l,1-l]*e, 0<l<1,
    W=P-x*h-l*e, 0<x<1.                            (1)

No shared mean was reset. Positive-length shared AD is a separate
already treated feature, not included in this singleton theorem.

**Theorem A:** the adjacent D exterior-vertex row below is impossible
for every c,s,d,t and every original positive force ratio.

**Theorem B:** the full feature is impossible for c<=3/4, for every
D exterior support row and every original exterior mean.

## 2. The actual D side and complete A3 equations

D cannot own its East roof normal: its frame would then be the world
frame, and its strict max-e vertex W would lie on max_D x=d.
But (1) gives W_x=d-x*c-l*s<d. Hence Q is a strict D vertex
and DV is physically singleton. W is a different strict D vertex.
They cannot be opposite because strict normals at opposite square
vertices have negative dot product, whereas East.e=s>0.
They are adjacent.

Write their unit side as

    v=W-Q=-a*h+b*e=(-u,v_y),
    a=H*s+x>0, b=H*c-l>0,
    a^2+b^2=1,
    u=a*c-b*s>0, v_y=a*s+b*c>0.                    (2)

Here b>0 follows from W's strict max-e support relative to Q;
u>0 follows also from W_x<d. In particular b<c and a>s.
The other inward unit edge at Q has negative East component and is

    w=(-v_y,-u), D=Q+[0,1]*v+[0,1]*w.             (3)

The vector v and its scalar vertical component v_y are distinct
notations throughout.

The full original A3 gives

    F_B=-mu*h+gamma*e,
    K=P-h+(1-l)*e,                                (4)

where K is the actual uniquely exposed A corner for AB.
Its entire torque about P is

    gamma*x-gamma+mu*(1-l)=0.

Consequently the actual ratio is

    r=gamma/mu=(1-l)/(1-x)
      =(1-H*c+b)/(1-a+H*s)>0.                     (5)

The real exterior B contains the whole segment K+[0,1]*f, where

    f=F_B/|F_B|=(-h+r*e)/sqrt(1+r^2),
    f_y=(s+r*c)/sqrt(1+r^2).                      (6)

This is a fact about the actual B: at its minimum-f support point,
the inward own components of a unit normal belong to [0,1].
At a side interior the normal is the inward own axis; at an endpoint
the vertex argument applies. Zero components preserve the full side
coordinate. Thus K+f belongs to B regardless of B's contact owner,
physical mask, true degree or any side-mean interpretation.

## 3. Exhaustive exterior D support and the new adjacent identity

The full unloaded D3 gives

    F_C=-nu*East-gamma*e,
    F_C.v=nu*u-gamma*b,
    F_C.w=nu*v_y+gamma*a>0.                       (7)

Therefore its actual C application is exactly one of

| Original sign | Actual D support point or mean |
| --- | --- |
| nu*u-gamma*b<0 | Q+w, adjacent to Q |
| nu*u-gamma*b>0 | Q+v+w, opposite Q |
| nu*u-gamma*b=0 | Q+w+z*v, with full original 0<=z<=1 |

No original side mean is identified with a corner in the final row.
In the first row, D's entire torque about Q is

    -gamma*a-nu*u+gamma*b=0,
    gamma*(b-a)=nu*u>0.                           (8)

Hence, for the whole adjacent-return row,

    0<s<a<1/sqrt(2)<b<c<1.                       (9)

The rest of Theorem A uses only (5),(6),(9) and H<=1.

## 4. Uniform adjacent-return direction bounds

The ratio in (5) decreases strictly with H: its derivative has
negative numerator -c*(1-a)-s*(1+b).
At H=1 its numerator exceeds its denominator, since

    (a-s)-(c-b)>0,
    c-b=(a-s)*(a+s)/(c+b)<a-s.

Thus r>1. Also l>0 gives H>b/c, so

    r<1/(1-a+b*s/c)<=c/s.

For the final inequality use
(s/c)*(1-b)<(a/b)*(1-b)<1-a, the last step equivalent to a<b.
The function f_y in (6) increases with r for 1<=r<=c/s, and
f_x<=0. Thus

    f_y>=(s+c)/sqrt(2)>=1/sqrt(2).                (10)

For a sharper bound put

    D0=1-a+s, N0=1-c+b,
    X=-c*D0+s*N0, Y=s*D0+c*N0.

Both D0,N0 are positive, X<=0, Y>0, and monotonicity gives

    f_y>=Y/sqrt(X^2+Y^2).                         (11)

### 4.1. All 4/5<=b<=9/10

Here 2/5<a<=3/5. Direct expansion gives

    Y+(4/3)*X
      =c*(1-4/3+(4/3)*a+b)
       +s*(1+4/3-a+(4/3)*b)
       +s^2-c^2-(8/3)*c*s.

The two bracketed coefficients are at least 1 and 14/5. Therefore

    Y+(4/3)*X
      >=c*(1-c)+s^2+s*(14/5-(8/3)*c)>0.

With X<=0 this implies Y>(4/3)*|X| and

    f_y>4/5.                                     (12)

### 4.2. All 1/sqrt(2)<b<=4/5

Now 3/5<=a<1/sqrt(2). If s>=5/16, the increasing function
s+sqrt(1-s^2), for s<1/sqrt(2), gives

    f_y>=(5+sqrt(231))/(16*sqrt(2))
         >63/(50*sqrt(2))>8/9.                  (13)

Here sqrt(231)>379/25, and the last positive squared reserve is
3969/5000-64/81=1489/405000.

If s<=5/16, hold s,c fixed, vary a from 3/5 to its actual value,
and put b=sqrt(1-a^2). For G=Y+2*X,

    dG/da=(2*c-s)-(a/b)*(c+2*s)
          >=c-3*s
          >=(sqrt(231)-15)/16>0.

At a=3/5,b=4/5 its exact value is

    G=c*(1-c)+4*s*(1-c)+s^2>0.

Thus Y>2*|X| and

    f_y>2/sqrt(5)>8/9,                            (14)

where 4/5-64/81=4/405. This covers the full interval.

## 5. The whole adjacent-return contradiction

From (4), H<=1 and (9),

    K_y=1/2+s+c*(1-H*c+b)>1/2+b,                 (15)

because the difference after replacing H by 1 and subtracting
1/2+b is s+(1-c)*(c-b)>0.

For b>=9/10, (10),(15) give
(K+f)_y>7/5+1/sqrt(2)>209/100.
For 4/5<=b<=9/10, (12),(15) give
(K+f)_y>1/2+4/5+4/5=21/10>209/100.
For 1/sqrt(2)<b<=4/5, (13)--(15) give
(K+f)_y>1/2+1/sqrt(2)+8/9>209/100.

For the last comparison, 209/100-25/18=631/900 and
1/2-(631/900)^2=6839/810000>0. The three intervals cover (9),
including all joining endpoints. The actual B point K+f is above
209/100, whereas

    (209/100)^2-1105/256=8271/160000>0.            (16)

This proves Theorem A. No exterior equation, special V force ratio,
chosen mean or numerical angle search is used.

## 6. The full interval c<=3/4, with every D return retained

Return to the entire original domain of Sections 1--3, without (8).
Equations (1)--(5) give

    l<H*c<=c, r>1-c,
    1-x=1-a+H*s>H*s, 0<r<2/s,
    K_y>1/2+s+c*(1-c).                            (17)

### 6.1. All 0<c<=2/5

Here s>9/10. The original support in B's direction is

    h_A(f)=(A0+r*A1)/sqrt(1+r^2),
    A0=1-d*c+s/2,
    A1=d*s+c/2+1-l.

The entire radius window and (17) imply

    A0>1-(61/60)*(2/5)+9/20=313/300>61/60>d,
    A1>d*s+1-c/2>81/100+1-1/5=161/100>d.

Hence h_A(f)>d because (1+r)/sqrt(1+r^2)>1.
Every actual contained unit beyond a unit-normal support h satisfies
h<=d: its center has radius at most d+1/2 by the exact farthest-corner
bound |q|^2+|q|+1/2, and its half-width is at least 1/2.
The real B beyond this support is therefore impossible.

### 6.2. All 2/5<=c<=3/5

Here s>=4/5, c*(1-c)>=6/25, 0<r<5/2. Thus K_y>77/50 and

    f_y>=(4/5+(2/5)*r)/sqrt(1+r^2)>2/3.

For the last comparison, the squared difference is a concave
quadratic with endpoint values 44/225 and 4/225 at r=0,5/2.
Consequently (K+f)_y>77/50+2/3=331/150>R.

### 6.3. All 3/5<=c<=3/4

Now s>=sqrt(7)/4>13/20, so (17) gives

    1/4<r<40/13, K_y>107/80,
    f_y>(13/20+(3/5)*r)/sqrt(1+r^2)>3/4.

The last squared difference is the concave quadratic
-7/50+(39/50)*r-(81/400)*r^2. Its values at 1/4 and 40/13 are
271/6400 and 2897/8450, both positive. Thus

    (K+f)_y>167/80,
    (167/80)^2-1105/256=33/800>0.

These intervals cover all 0<c<=3/4 and all original D return
rows, proving Theorem B without changing an exterior mean.

## 7. The exhaustive retained perpendicular-singleton remainder

A survivor must have c>3/4 and one of exactly two rows:

**Opposite D vertex:** nu*u-gamma*b>0, with actual C point Q+v+w.
The complete D torque gives

    nu*(u-v_y)=gamma*b>0,
    a*(c-s)>b*(c+s).                              (18)

**D-owned exterior side:** nu*u=gamma*b, with full original point or
mean Q+w+z*v, initially 0<=z<=1. The complete D torque gives

    z*(nu*v_y+gamma*a)=gamma*a.                    (19)

Thus its actual original z is strictly between 0 and 1. Both endpoints
were retained before this deduction and fail the full torque equation;
none was selected or discarded in advance.

These necessary domains are not asserted realizable. Every V, B, C
and remaining-unit equation stays intact. In particular the original
physical-two V2 retains

    mu*c+nu=k*(d+1), mu*s=-k*eta,
    nu*t=mu*(d*s+c/2),
    k>0, -1/2<=eta<=1/2.

Whole-data reflection covers the opposite individual-zero coefficient.
The physical-two mask is never treated as a unique physical corner.

## 8. Literal callers, dependencies and honest credit boundary

In both D02.L135 and D02.L1345 retain rim A--V--D--C--N--B--A
and chord AD with A=0,V=1,D=2,C=3,N=4,B=5. A,D remain unloaded
true3 and V,B,C loaded true2. N remains unloaded true2 in L135 and
loaded true2 in L1345. No equation at N is used or shortened; all
three actual completing units remain.

The graph reflection exchanges A,D and B,C together and transports
every normal, physical mask, mean and force. At the original A-only
perpendicular singleton, Theorem A excludes the whole adjacent-return
row and Theorem B excludes every return with c<=3/4. The exact two
rows of Section 7 remain open. Other AD owners, physical-two charts
and unique-circle types remain separate. No original fine/coarse
flag, whole D02 row, global prerequisite or equality claim changes.

The exact operative inputs are:

| Complete input | Exact use |
| --- | --- |
| PHYSICAL_TWO_CORNER_LOADED_TRIANGLE_TIP_TRANSVERSE_PORT_EXCLUSION_AND_INNER_FACE_DOMAIN_2026_10_29.md | Original West/strict chart, whole radius/physical-mask entry |
| PHYSICAL_CONTACT_STRESS.md | Full A3/D3 force and torque, actual support and original strict singleton convention |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | Literal D02 graph/load roles and all three actual extras |

The neighboring shared-AD feature is separately covered in
PHYSICAL_TWO_CORNER_WEST_STRICT_ROOF_SHARED_PERPENDICULAR_HUB_INTERFACE_COMPLETE_EXCLUSION_2026_10_29.md.
Its result is not used in the singleton proof.

All new geometry, force identities, full continuous comparisons and
actual-point arguments are printed above. This source adds no selector,
reselects no extracted normal and does not repair the still-open global
common-selection compatibility premise. It requires complete independent
review before adoption.

No frozen source, metadata, ledger, original flag or remote state was
changed. No pose search, angle mesh, packing certificate, Lean/Lake,
CI/workflow dispatch, external comment/message or merge was used.

