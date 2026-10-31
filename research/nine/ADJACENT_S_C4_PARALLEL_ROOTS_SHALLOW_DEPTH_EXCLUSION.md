# Parallel adjacent S roots: a shallow outer leaf excludes the whole unique-corner interface

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root
and separate independent review.** This excludes the entire
unique/unique physical boundary mask with both roots owning AB, both
genuine leaves at their strict outer lower vertices, and the smaller
root depth at most 1/8. It retains every actual boundary frame and mean.

Keep all nine units and the original positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

The exact necessary-domain theorem is
ADJACENT_S_LEAF_C4_PARALLEL_ROOT_LEAF_REDUCTION.md. Normalize its
actual AB normal to East and its common cycle moment to be positive.
The attachment reflection permits the following complete chart:

    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q_*=1105/256,
    X=1-h, Y=1+h, -epsilon<h<=0,
    A=[-X,h] times [-v,1-v],
    B=[h,Y] times [-w,1-w],
    X^2+v^2=Y^2+w^2=d^2,
    0<v<=w<13/50, v<=1/8,
    P_AB=(h,-k), 0<k<=v.
                                                               (1)

In particular h=(v^2-w^2)/4. The genuine leaf vectors are
(-X,-v) and (Y,-w), and both original roots have nonparallel
nonleaf force pairs. C,D have one physical circle corner each,
with positive total load. The complete compatible theorem
ADJACENT_S_LEAF_C4_ALL_NONPARALLEL_PAIRS_SIDE_OWNER_SELECTION.md
therefore supplies at least one actual side-axis owner of every
cycle edge. It does not fix any mean. A strict vertex contact
owned by the other square lies in that square's relative side
interior: a point-only vertex/vertex axis endpoint is excluded
by the original strict point-normal convention.

We use the original boundary-neighbor degree-two theorem, with its
actual scopes. At C or D its two lines meet at a positive radial
point q=lambda Z. Under the present unique physical mask,

    q belongs to the same unit, 0<lambda<=1,
    q=P+rho*n, rho>=0                                  (2)

at an actual incoming normal n and application P. The other real
neighbor is physical boundary, as required by
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1. No corresponding
statement is assigned to A or B.

## 1. A uniform high vertical-port fact for the real loaded tips

Let a true loaded two-force unit T have its other neighbor physical
boundary, one physical circle corner, and an actual incoming North
normal at

    P=(t,H), t>0, H>37/50.

Its original radial point in (2) lies on the vertical ray above P.
The following statements concern every physical frame and actual mean.

If T owns the North axis, its unique circle corner is its upper-right
corner (T0,H+1), with T0>1/2. Indeed the upper row is farther than
the lower, and the radial point has positive horizontal coordinate.
Its actual center is (T0-1/2,H+1/2).

Otherwise P is the strict lowest vertex. Write

    T=P+[0,1]f+[0,1]j,
    f=(c,s), j=(-s,c), c,s>0, c^2+s^2=1.

Since P.f>0, its circle corner is either P+f or P+f+j.
The opposite possibility is impossible. To see this directly, if
Z=P+f+j, the vertical radial point and lambda<=1 first force c>=s.
Put M=c-s>=0 and N=c+s. Then

    Z=(t+M,H+N), lambda=t/(t+M), t*N>=H*M,
    |Z|^2>=(M^2+N^2)*(1+H/N)^2
             >=(sqrt(2)+H)^2>R^2.

The last inequality uses H>37/50>11/15 and R<25/12. This is also
the reflected local argument of
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md, Section 8;
it includes M=0 and zero proper distance. Thus

    Z=P+f,
    t*s-H*c>1/2.                                      (3)

The inequality is strict because equality would give two physical
circle corners. Moreover

    c/s<1/2, s>2/sqrt(5)>8/9, c<1/2.                   (4)

For otherwise (3) gives

    P.f>H/s+(c/s)/2
          >=(37/50)*(sqrt(5)/2)+1/4>133/125,
    R^2>(258/125)^2+1/4
          =Q_*+774759/4000000,

using sqrt(5)>11/5. This proves (4).

We will also need the actual center-angle bound

    pi/3<theta_T<pi/2.                                (5)

Its center has positive horizontal coordinate by (3), and its height
exceeds H+1/2>31/25. Its horizontal coordinate is less than 2/3.
For the axis-owned case, a contrary center would give a real corner
with squared norm at least

    (7/6)^2+(87/50)^2
        =Q_*+104119/1440000.

For a tilted T, such a center would instead give

    |Z|^2>=(2/3+(c+s)/2)^2+(37/50+s)^2.                (6)

On 0<=c<=1/sqrt(5), s=sqrt(1-c^2), the right side is concave
as a function of c. After expansion its nonconstant terms are

    -c^2+(2/3)c+(2/3+74/50)s+(1/2)c*s.

Both s and c*s are concave on this interval; for the latter,
the second derivative is -c(3-2c^2)/(1-c^2)^(3/2).
Its minimum is therefore at an endpoint. At c=0 it is the
preceding strict bound. At c=1/sqrt(5), use sqrt(5)<9/4:
the two positive coordinates exceed 4/3 and 733/450,
respectively. Thus (6) is strictly above

    (4/3)^2+(733/450)^2
        =Q_*+1485871/12960000.

This proves the horizontal center bound. Since sqrt(3)<7/4,
its center height >31/25 exceeds sqrt(3) times its horizontal
coordinate <2/3. This gives (5).

Reflecting the horizontal coordinate gives the full negative-port
form. For P=(-s0,H), s0>0, a tilted unit has

    f=(a,b), j=(-b,a), a,b>0, a^2+b^2=1,
    Z=P+j=(-s0-b,H+a),
    s0*a-H*b>1/2,
    b/a<1/2, a>8/9, b<1/2.                            (7)

The owned-axis case retains its whole actual horizontal side mean.

## 2. Neither root can use its outward upper vertex

This argument treats the two roots symmetrically. Let its outward
horizontal leaf distance be x, its depth z, and its common AB mean
depth k. Thus x>59/60, 0<z<13/50, 0<k<=1/8 and k<=z.
At a strict outward upper vertex, the full true-root force and
moment give the positive outward-to-upward normal ratio

    r=x*(z-k)/[z*(1-z+k)], 0<r<x/(1-z).                (8)

The actual upper vertex has outward horizontal coordinate x and
height 1-z. Its inward unit normal segment into the boundary neighbor
therefore has a real endpoint with squared norm

    d^2+2-2z+2S,
    S=(x*r+1-z)/sqrt(1+r^2).                           (9)

Such a unit segment is contained in any actual unit at a minimum
support point, including a vertex: its inward normal's two
nonnegative own-axis coefficients are each at most one.

S is increasing for 0<=r<x/(1-z). If z<=43/240, then

    S>=1-z>d-3/8+z.

If z>43/240, the original k<=1/8 gives

    r>x*(z-1/8)/z>(59/60)*(13/43)>1/4.

Thus, using sqrt(17)<25/6,

    S>(59/240+37/50)*4/sqrt(17)
       >1183/1250>541/600>d-3/8+z.

The middle strict rational reserve is 671/15000. In both cases
(9) exceeds R^2=d^2+2d+5/4. This excludes the whole outward
upper-vertex feature without a boundary-owner assumption.

The full root vertical force components are positive, so only
North or the inward strict upper vertex remains at each root.

## 3. The deeper root B must use its actual North side

The inward B feature would be Northwest at

    Q_B=(h,1-w).

It is a strict B vertex, so C owns that normal. The original strict
point convention makes Q_B relative-interior to C's supporting
side. Consequently a small open half-neighborhood in the Northwest
direction lies in C. It contains points strictly to the left and
strictly below Q_B.

But these points are in the interior of A: 1-w<=1-v, while
1-w>-v. This remains true when v=w, because points below the
common upper vertex enter A. The actual interiors would overlap.
Thus B's only surviving contact is North, with its unchanged
full moment and force fixing the original mean to

    P_BC=(t,H_B), H_B=1-w>37/50,
    t=k*Y/w>0, |F_BC|=mu*w/Y,                          (10)

where mu>0 is the actual AB magnitude. The actual mean gives
t<=Y<=1. Section 1 applies to the real C, so its center angle
is strictly greater than pi/3.

## 4. The shallow root A cannot use its inward Northeast vertex

This feature is at Q_A=(h,H_A), H_A=1-v>=7/8. D owns its
incoming Northeast normal n, with r=n_x/n_y>0. The full A3
equations at the original applications give

    r=[X*k+h*v]/[v*(1-v+k)]<=X<61/60.                 (11)

Indeed k/(1-v+k)<=v and h<=0. Its actual minimum support is

    u=Q_A.n>1/2.

For a direct exact bound, the numerator H_A+h*r is greater than
7/8-61/3600 and sqrt(1+r^2)<3/2, giving u>3089/5400>1/2.
The perpendicular coordinate Q_A.Jn=-h*n_y+H_A*n_x is positive.
Since D has one physical circle corner, the usual actual owned-side
radial calculation gives

    Z_D=(u+1)n+W*Jn,
    c_D=(u+1/2)n+(W-1/2)Jn,
    W>0.

Because R^2<=Q_*<9/2 and u+1>3/2, W<u+1. Hence

    det(Z_D,c_D)=(W-u-1)/2<0.

The actual D center is clockwise from its actual circle corner.
Both have positive height; the center height is at least H_A-1/2.
The proper ray q_D=Q_A+rho*n, rho>=0, lies clockwise from
Q_A, because n is Northeast whereas h<=0. Therefore

    theta_D<arg(Q_A)
       <=pi/2+arctan(2/105)
       <pi/2+pi/18=5*pi/9.                            (12)

The last inequality follows from arctan(2/105)<2/105<1/6<pi/18.

The original positive common cycle moment gives the counterclockwise
minor-center order C before D, as in the full common-domain and
circle-spoke theorems. Since both centers have positive height,
their ordinary angles satisfy theta_C<theta_D. But (5) and (12)
give a separation strictly less than

    5*pi/9-pi/3=2*pi/9,

contradicting the strict physical boundary-center separation.
This excludes the complete inward Northeast feature.

## 5. Both actual root contacts are North

We have now proved the full surviving root chart

    P_AD=(-s,H_A), s=k*X/v>0, H_A=1-v>=7/8,
    P_BC=(t,H_B), t=k*Y/w>0, H_B=1-w>37/50.
                                                               (13)

Every original side mean is retained. Put

    G=H_A-H_B=w-v>=0, Delta=s-t>=0.

If both C,D own the North axis, all four cycle frames are parallel.
The complete accepted theorem
ADJACENT_S_LEAF_C4_ALL_PARALLEL_FRAMES_COMPLETE_EXCLUSION.md
applies directly to the same original means and nine units.

For every other case Section 1 gives the exact possible physical
circle corners. Write N for the original unit normal from D to C,
and S for its actual application. From the two unchanged radial
rays,

    q_D=S-rho_D*N, q_C=S+rho_C*N,
    rho_D,rho_C>=0.                                    (14)

The points have horizontal coordinates -s and t, respectively,
so rho_D+rho_C>0 and N_x>0. The original force equations give
the same sign. If Z_D=(-X_D,Y_D), Z_C=(X_C,Y_C), then

    q_D=(-s,s*Y_D/X_D),
    q_C=(t,t*Y_C/X_C).                                 (15)

All four displayed positive corner coordinates below are actual.

## 6. D parallel, C tilted

The actual D rectangle and circle corner are

    D=[-T,1-T] times [H_A,H_A+1],
    Z_D=(-T,H_A+1), 1/2<T<15/16.                       (16)

The upper bound follows from
T^2<=Q_*-(15/8)^2=205/256<225/256. For the tilted C,

    C=(t,H_B)+[0,1](c,e)+[0,1](-e,c),
    Z_C=(t+c,H_B+e), c,e>0, e<1,
    t*e-H_B*c>1/2.

Thus t>1/2. Also Y_D>Y_C; equal actual radii give T<t+c.
Since s>=t, (15) implies q_D,y>q_C,y, and (14) forces N_y<0.
The actual CD application on D is consequently its lower-right
vertex

    S=(1-T,H_A).

The full C2 force has negative component on its actual axis
j_C=(-e,c), because Z_C.j_C< -1/2. The incoming North force
has positive j_C component. Thus N.j_C<0, so the original
C-to-D support is its far-j_C side. Every actual point on that
side is at distance at least one from (t,H_B).

But the real S has

    |S_x-t|<15/16, |S_y-H_B|=G<13/50,
    |S-(t,H_B)|^2<225/256+169/2500
                     =1-8559/160000<1.

This contradiction includes both endpoints of the C supporting side.

## 7. C parallel, D tilted

Now C's actual circle corner is (T_C,H_B+1), with T_C>1/2,
and its x interval is [T_C-1,T_C]. Write the tilted D as

    D=(-s,H_A)+[0,1]f+[0,1]j,
    f=(a,b), j=(-b,a),
    Z_D=(-s-b,H_A+a),
    s*a-H_A*b>1/2, b/a<1/2, a>8/9.                   (17)

If N_y>0, its C support is the lower-left vertex. The side-owner
selection then makes N=f, the only positive-positive D axis.
Its D mean has height at least H_A+b>H_B, impossible at that
C vertex. If N_y<0, its C support is the upper-left vertex;
the only possible D-owned axis is -j. Its mean has height at
most H_A+b, whereas

    H_A+b-(H_B+1)=G+b-1<13/50+1/2-1<0.

Thus only N=East remains. Its D application is the strict right
vertex (-s,H_A)+f. The genuine D radial point has height H_A+b,
so (15) gives

    s*(a-b)=b*(H_A+b),
    s*a-H_A*b=b^2*(H_A+a)/(a-b)>1/2.                  (18)

The last expression increases with b for 0<b<1/2 and H_A>0.
For example its logarithmic derivative is

    2/b-b/[a*(H_A+a)]+(1+b/a)/(a-b)>0

on the present interval; already 2*a*(H_A+a)>b^2.
At b=3/8 and H_A=1 it is less than 1/2, because

    9*(8+sqrt(55))<32*(sqrt(55)-3),
    168^2<23^2*55.

Since H_A<1, (18) therefore implies b>3/8. Consequently
a<15/16 and b/(a-b)>2/3. Equation (18) also gives

    R^2=(H_A+a)^2*(1+[b/(a-b)]^2)
       >(127/72)^2*(13/9)
        =Q_*+33163/186624.

This actual circle-corner contradiction excludes the horizontal case.
All C means and every original D proper-distance endpoint were kept.

## 8. Both loaded tips tilted: full four-axis contact cover

Use the two actual frames

    D=(-s,H_A)+[0,1]f_D+[0,1]j_D,
    f_D=(a,b), j_D=(-b,a),
    C=(t,H_B)+[0,1]f_C+[0,1]j_C,
    f_C=(c,e), j_C=(-e,c).

Section 1 gives

    a^2+b^2=c^2+e^2=1,
    a,e>8/9, b,c<1/2,
    Z_D=(-s-b,H_A+a), Z_C=(t+c,H_B+e),
    s*a-H_A*b>1/2, t*e-H_B*c>1/2.                    (19)

In particular s,t>1/2. When G>0, the original means in (13) give

    Delta= k*G*[1+(v+w)^2/4]/(v*w)
       >G/(2*X*w)>G,                                 (20)

because 2*X*w<(61/30)*(13/50)=793/1500<1. When G=0,
we have h=0 and Delta=0.

Since N_x>0 and some endpoint owns N, the exhaustive original
normal list is

    N=f_D, N=f_C, N=-j_D, or N=-j_C.                   (21)

No side mean is discarded in this list.

### 8.1. N=f_D, with the whole D mean

C's actual minimum is its left vertex (t,H_B)+j_C. Hence for
the unchanged D mean z in [0,1],

    (-s,H_A)+f_D+z*j_D=(t,H_B)+j_C,
    c=G+b+z*a>=b+G.

Thus e<=a and Y_D=H_A+a>=H_B+e=Y_C. Equal radii give
X_D<=X_C. Since s>=t, (15) yields q_D,y>=q_C,y. This
contradicts (14), since the actual N_y=b is strictly positive.
The conclusion includes equality in the displayed height comparison.

### 8.2. N=f_C, with the whole C mean

D's actual maximum is its opposite vertex, whereas C's minimum
lies on (t,H_B)+[0,1]j_C. Equality of the original heights would
require

    G+a+b=z*c, 0<=z<=1.

The left side exceeds one and the right side is below 1/2.

### 8.3. N=-j_D, with the whole D mean

C's actual minimum is its opposite vertex; D's maximum is on
(-s,H_A)+[0,1]f_D. The actual heights would give

    G+z*b=c+e, 0<=z<=1.

The left side is below 13/50+1/2<1 and the right side exceeds
one. This is impossible.

### 8.4. N=-j_C, with the whole C mean

The actual D point is its right vertex and the actual C point
is on its entire far-j_C side:

    (-s,H_A)+f_D=(t,H_B)+j_C+z*f_C,
    s+t=a+e-z*c,
    G+b=c+z*e, 0<=z<=1.                               (22)

Put delta=b-c. The last equation gives delta>=-G.
If delta<=0 and G>0, (20) gives

    X_D-X_C=Delta+delta>=Delta-G>0,
    Y_D-Y_C=G+a-e>=G>0,

contradicting equal circle radii. If G=0 and delta<=0, (22)
instead forces delta=z=0, a=e and s=t=a. This endpoint is
also physically impossible. Its actual circle corner has norm

    (a+b)^2+(H_A+a)^2.

For b<=1/4, a>24/25, so this exceeds

    1+(367/200)^2=Q_*+8131/160000.

For b>=1/4, a>8/9, so it exceeds

    (41/36)^2+(127/72)^2=Q_*+1907/20736.

Thus the original z=0 endpoint has been excluded by actual circle
geometry, not by omitting it from the contact cover.

It remains delta>0. Then a<e and X_D>X_C. Equality of the
two actual circle radii gives

    (Delta+delta)*(s+t+b+c)
       =[delta*(b+c)/(a+e)-G]*(H_A+H_B+a+e).

Since Delta,G>=0, it follows that

    s+t<=(H_A+H_B)*(b+c)/(a+e).                        (23)

But the two strict unique-corner inequalities in (19) imply

    s+t>H_A*b/a+H_B*c/e.

The difference between the latter expression and the right side
of (23) is

    (b*e-a*c)*(H_A/a-H_B/e)/(a+e)>0,

because b>c, a<e and H_A>=H_B. This is the required strict
contradiction. It retains the full original z range and uses
the actual common circle rather than a sampled configuration.

## 9. Exact whole shallow-depth join

Section 2 excludes both outward root vertices. Section 3 forces the
deeper root's North side, including equal-depth and common-corner
limits. Section 4 excludes the other root's inward vertex using
the full original C2/D2 radial data and physical center order.
Thus both contacts are the actual North means in (13).

The parallel/parallel case is the accepted whole all-parallel
theorem. Sections 6 and 7 exclude each mixed boundary orientation.
Section 8 exhausts the complete both-tilted original owner cover,
including all side means and the common-vertex endpoint. Therefore
the entire original unique/unique, both-AB-owned, strict-outer-leaf
domain with min(v,w)<=1/8 is impossible.

The complementary min(v,w)>1/8 domain is the separate complete
physical capacity theorem
TWO_PARALLEL_ROOTS_OUTER_RADIAL_LEAVES_CAPACITY.md. This source
does not silently apply the present small-k argument there. The
horizontal genuine-leaf endpoints remain a separate original
feature type. All nine units, true degrees, selected positive
forces, actual normals and actual means survive every reduction.
No compilation, CI, numerical pose, remote action or shared-metadata
edit supplies any step of the proof.
