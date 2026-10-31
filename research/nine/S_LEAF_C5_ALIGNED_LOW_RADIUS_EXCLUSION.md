# The entire aligned low-radius S-leaf C5 with four boundary bodies is excluded

Date: October 27, 2026.

**Status: complete hand theorem, submitted for full root and separate
independent review.** The proof retains the full true root star,
every original application and circle mask, all four actual boundary
bodies, and the other three original units. Its reusable endpoint-angle
lemma does not use any force or degree at the two boundary neighbors.

## 1. Original scope and the complete root-normal cover

Keep the original nine physical units and compatible selected certificate.
Suppose the positive component is

    H--B_1--B_2--B_3--B_4--H,       H--L,

where L is a genuine S leaf, H has true degree three, and all four
B_i are physically circle-touching. The exact original load family
has all four B_i loaded and of true degree two, but the geometric
path argument below only uses their physical boundary status and
actual contacts.

Consider the entire strict-low aligned root domain

    2<R<sqrt(17)/2,
    d=sqrt(R^2-1/4)-1,       14/15<d<1,
    a=1-d,                  0<a<1/15,
    L=[d,d+1] times [-1/2,1/2],
    H=[-a,d] times [h-1,h],  0<=h<=1.                 (1)

The accepted same-nine radius theorem supplies R>2. The real root
is physically clear by the genuine-leaf theorem. Its unchanged full
force and origin-moment equations are

    alpha e_x+mu n_B+nu n_D=0,
    mu det(P_B,n_B)+nu det(P_D,n_D)=0,
    alpha,mu,nu>0.                                    (2)

Reflect the entire configuration vertically so h>=1/2. Put
r=R-sqrt(2). Every point of a physical boundary unit has norm at
least r. The exact bounds

    r^2>(2-sqrt(2))^2>12/35,
    a^2+1/4<1/225+1/4<12/35                         (3)

use sqrt(2)<99/70. Thus no point of H's left side with height in
[-1/2,1/2] can belong to a boundary neighbor.

An East normal would put its neighbor wholly in x>=d; the sharp
contained-unit cap makes that neighbor exactly the real L. This
force-free equality theorem is Section 1 of
FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md. It applies throughout
(1), and excludes any other East contact.

If h=1/2, the negative horizontal force required by (2) would
have an ineligible left-side application. If both other normals
were horizontal, they would both be West; their original
application heights would be positive by (3), and their two
positive origin moments could not sum to zero. Therefore h>1/2
and the two actual vertical force components have strict opposite
signs. Name D as the downward neighbor.

A negative horizontal component of n_D would put its port at
(-a,h-1), contrary to (3). A positive horizontal component would
put it at (d,h-1), in the relative interior of the real leaf's
inner side. The actual inward normal segment of D then enters
int(L), impossible. This includes every support owner and every
mean endpoint. Consequently the complete remaining normal cover is

    n_D=-e_y,
    n_B=(-c_B,s_B),       c_B,s_B>0, c_B^2+s_B^2=1,
    P_B=(-a,h),
    P_D=(x,h-1),          -a<=x<=d.                    (4)

The point bound (3) forces x>0, and in fact x>3/10, since

    x^2>12/35-1/4=13/140>9/100.

The full unchanged torque and force equations give

    h c_B-a s_B=x s_B,
    c_B/s_B=(x+a)/h.                                  (5)

Also P_B belongs to a boundary unit, so

    h^2>12/35-1/225>(29/50)^2,
    h>29/50.                                          (6)

The last rational reserve is 317/157500. No equation at B or D
has been used.

## 2. The lower boundary unit is genuinely tilted

Write b=h-1, so -1/2<b<=0. Suppose D owns its top support.
Then its actual square is

    D=[z,z+1] times [b-1,b],       x-1<=z<=x.

Its vertical interior overlaps that of the real L. Horizontal
nonoverlap therefore forces z+1<=d: the other option z>=d+1 is
incompatible with z<=x<=d. Since x>3/10 and d>14/15, every
horizontal corner magnitude is at most d, and every vertical
magnitude is less than 3/2. Hence

    |corner|^2<d^2+9/4<d^2+2d+5/4=R^2.

Thus D cannot be boundary in this entire aligned case.

Its actual maximum-y point is consequently a unique vertex, exactly
the original P_D in (4). There are c,s>0 with c^2+s^2=1 such that

    D=P_D+[0,1](c,-s)+[0,1](-s,-c).                  (7)

This retains both possible tilts, without ordering c and s.
In particular H intersect D is the singleton P_D, even if
the original root owns its normal.

If x+c>d, the actual edge P_D+t(c,-s) crosses x=d at t=(d-x)/c.
At that crossing it cannot have height greater than -1/2,
because immediately afterward it would enter int(L). Therefore

    (d-x)s >= (h-1/2)c,
    x<=d-(h-1/2)(c/s).                                (8)

Equality is kept: the edge may pass through the real leaf's
inner lower corner. If x+c<=d, no screen inequality is assumed.

## 3. The full physical leaf screen forces h<2/3

Suppose h>=2/3. Then |b|<=1/3, and the original boundary port gives

    x^2>12/35-1/9=73/315>(12/25)^2.                   (9)

If x+c<=d, every horizontal corner magnitude in (7) is at most d,
while every vertical magnitude is at most 1/3+sqrt(2)<7/4.
Thus all four squared norms are less than

    d^2+49/16<R^2,

since 2d+5/4>187/60 and 187/60-49/16=13/240.

Now assume x+c>d and use (8). The original point and its left
adjacent corner have horizontal magnitude at most d and vertical
magnitude at most 4/3, so are strictly inside the circle.

For the right adjacent corner, put t=h-1/2>=1/6. The elementary
whole-angle bound

    c(1-t/s)<2/3                                      (10)

follows as follows. On its positive part the maximum as a function
of s is (1-t^(2/3))^(3/2); since t>1/8, this is less than
3sqrt(3)/8<2/3. On the nonpositive part the inequality is immediate.
If s<=4/5, its squared norm is below

    (d+2/3)^2+(17/15)^2<R^2.

After subtracting R^2, the bound is
-(2/3)d+431/900<-129/900. If s>=4/5, then c<=3/5 and
1-t/s<=1-t<=5/6. Its squared norm is below

    (d+1/2)^2+(4/3)^2<R^2,

whose difference from R^2 is 7/9-d<0.

Only the opposite corner remains:

    Z=(x+c-s,b-c-s).

If c<=s, its horizontal magnitude is at most d, and the earlier
7/4 vertical bound excludes it. Suppose c>s, and put k=c/s>1.
Equations (8)--(9) give

    1<k<(d-12/25)/t<78/25.                            (11)

The first coordinate of Z is positive. Increasing its upper bound
in (8) by lowering h to 2/3, and likewise increasing the absolute
negative vertical coordinate, gives

    |Z|^2 <= F_d(k),

    F_d(k)=[d-k/6+(k-1)/sqrt(1+k^2)]^2
             +[-1/3-(k+1)/sqrt(1+k^2)]^2.

For fixed k in (11), F_d(k)-R^2 is strictly decreasing in d:
its derivative is

    2[-k/6+(k-1)/sqrt(1+k^2)-1]<0.

It therefore suffices to show, on 1<=k<=78/25,

    F_(14/15)(k)<3589/900
                 =(29/15)^2+1/4.                    (12)

Here is one exact global concavity calculation. Write F=F_(14/15).
Direct differentiation gives

    F''(k)/2=1/36-N(k)/(1+k^2)^(5/2),
    N(k)=(43/10)k+(31/30)k^2-4/15.

The difference N(k)-(1+k^2)^2/5 is concave on this interval:
its second derivative is 19/15-(12/5)k^2<0. Its two endpoint
values are 64/15 and 953582/5859375, both positive.
Since sqrt(1+k^2)<33/10, we obtain

    F''(k)/2<1/36-2/33=-13/396,
    F''(k)<-1/16.                                     (13)

At k=2,

    F(2)=556/225+16/(5sqrt(5))<391/100,
    F'(2)=-1/5+19/(75sqrt(5)),
    -9/100<F'(2)<0.

The first bound uses sqrt(5)>67/30, with rational reserve
73/12060. The derivative bounds follow from 2<sqrt(5)<9/4;
the reserve against -9/100 is 7/2700.

The Taylor upper bound from (13), followed by completing a square,
now gives every k in (11)

    F(k)<=F(2)+F'(2)(k-2)-(k-2)^2/32
          <=F(2)+8F'(2)^2
          <9937/2500<3589/900.

The last reserve is 73/5625. This proves (12). Every actual D
corner is therefore strictly inside the circle when h>=2/3,
a contradiction. Together with (6),

    29/50<h<2/3.                                      (14)

This conclusion used only actual physical geometry, the full root
normal cover, and the real L. No original corner mask or normal
was prescribed.

## 4. The original singleton selection makes B own its root normal

This is an application of the general true-radial-leaf-root selection
proved in Section 4 of ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md,
with its radius-independent determinant re-established explicitly.

Both root applications in (4) are fixed distinct physical points:
P_B is a true H vertex and P_D is the true D vertex from Section 2.
The latter normal m=-e_y is the fixed H axis. For a possible free
vertex/vertex normal n at P_B, the full true H3 equations require

    det(e_x,n)det(P_D,m)-det(e_x,m)det(P_B,n)=0,
    det(W,n)=0,
    W=det(P_D,m)e_x-det(e_x,m)P_B
       =(-(x+a),h) !=0.                               (15)

For each fixed physical pose and these candidate singleton features,
(15) excludes only finitely many directions in the original strict
free-normal interval. Before multiplier extraction, include all such
leaf/root/feature assignments in the finite physical prelist.
The same open dense conditions are compatible with all earlier
nonradial, matched-junction and uncrossing choices. The two points
are distinct, so their junction parameters are not identified.
No extracted mean or weight is used to choose a normal: P_D is fixed
by the actual D vertex already at the pose level.

Uncrossing preserves surviving point normals and only adds actual
shared-side forces; thinning only deletes atoms. A surviving free
HB is therefore impossible in this compatible necessary certificate.
Its actual normal is strict Northwest at H, so cannot be an H axis.
Thus it is an actual B side axis.

This argument does not import the d>1 specialization of the old
caller's coordinates. It uses exactly the displayed nonzero
determinant at the actual strict-low true H3 star. It needs no
force, load, mask or degree at B or D.

## 5. The upper boundary center is before pi/2+atan(2/9)

Put n=(-c_B,s_B), j=(-s_B,-c_B), and retain B's entire original
side mean:

    B=P_B+[0,1]n+[-rho,1-rho]j,       0<=rho<=1.

Define

    N=P_B dot n=a c_B+h s_B>0,
    K=-P_B dot j=h c_B-a s_B=x s_B>0.                 (16)

By (14), N,K<|P_B|<7/10. Both physical circle corners must be on
the outer n-face. The outer corner with j coordinate 1-K-rho
has squared norm less than

    (17/10)^2+1=389/100<4<R^2,

because |1-K-rho|<1. Hence B has precisely the other physical
circle corner, with

    R^2=(N+1)^2+(K+rho)^2.

This derives the physical mask without a two-force or proper-ray
premise. Its center is

    X_B=-a-c_B/2+(rho-1/2)s_B,
    Y_B=h+s_B/2+(rho-1/2)c_B>h-1/2>0.                (17)

We prove X_B>-(2/9)Y_B. Suppose otherwise, and set b_0=2/9,
k=c_B/s_B. Increasing rho increases the displayed circle norm.
At the comparison value for which the center lies on
X_B=-b_0 Y_B, its height is

    Y_*=(a k+h+(1/2)sqrt(1+k^2))/(1+b_0 k).

The assumed inequality puts the actual rho at or below that value.
Consequently

    R^2 <=(1+b_0^2)Y_*^2+L(k)Y_*+1/2,
    L(k)=((1+b_0)k+1-b_0)/sqrt(1+k^2)
         <=sqrt(170)/9.                              (18)

This comparison is valid even when its auxiliary rho lies beyond
the actual side interval: the unchanged actual rho is smaller,
and K+rho is positive. It does not replace a physical application.

Equation (5), x<=d and a+d=1 give hk=x+a<=1.
Thus 0<k<50/29 and h<=min(2/3,1/k).

For 0<=k<=3/2, replace a by 1/15 and h by 2/3 in Y_*.
The derivative numerator is

    1/15-(2/9)(2/3)+(k-2/9)/(2sqrt(1+k^2)).

It is strictly increasing, so the comparison function has at most
one interior critical point, a minimum. Its maximum is at an
endpoint. The larger endpoint is k=3/2, giving

    Y_*<=23/40+3sqrt(13)/16.

For 3/2<=k<=50/29, use h<=1/k. The derivative numerator is

    1/15-(4/9)/k-1/k^2
                  +(k-2/9)/(2sqrt(1+k^2))
       <1/15+1/2-(4/9)(29/50)-(29/50)^2
        =-619/22500<0.

This comparison decreases from the same value at k=3/2.
Therefore, over the entire original domain,

    Y_*<2003/1600,
    L(k)<326/225,

using sqrt(13)<361/100 and sqrt(170)<326/25.
Equation (18) gives the exact contradiction

    R^2<820816093/207360000
        =4-8623907/207360000<4.

Thus X_B>-(2/9)Y_B. With the actual center angle beta in (0,pi),
we have proved

    beta<pi/2+atan(2/9).                              (19)

All side endpoints rho=0,1 are included. No neighbor degree or
positive individual circle-weight condition was used.

## 6. The lower boundary center is after 3pi/2+atan(5/8)

First its actual center has positive horizontal coordinate.
The force-free geometric lemma in Section 3 of
FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md applies literally:
a unit with top support in [-1/2,0], containing a positive-x
top point, and center x<=0 has every squared corner norm at
most 9/4+sqrt(2)<4. Our boundary D cannot have that property.

Write its actual center as (X,-Y), with X,Y>0. In (7),

    g=1-h<21/50,
    Y=g+(c+s)/2.

Suppose X/Y<=r_0:=5/8. The exact farthest-corner formula is

    R^2=X^2+Y^2+1/2+Xc+Ys+|Yc-Xs|.                  (20)

For fixed Y,c,s this is convex in X, so its maximum on
[0,r_0Y] is at an endpoint. At X=0, put u=c+s<=sqrt(2).
Its value is

    g^2+2gu+(3/4)u^2+1/2
      <(21/50)^2+3(21/50)+2
       =8591/2500<4.

At X=r_0Y, the coefficient of Y in (20) is

    r_0 c+s+|c-r_0 s|.

If c<s, exchanging c and s can only increase this coefficient.
Indeed the increase is 2r_0(s-c) when c>=r_0s, and
2(1-r_0)c when c<r_0s. The value of Y is unchanged.
This is only an inequality between scalar comparison values,
not a reorientation of D.

It suffices therefore to bound the larger comparison with c>=s.
Put u=c+s in [1,sqrt(2)], v=c-s=sqrt(2-u^2), and G=21/50.
Increasing g to G increases (20). The resulting whole-angle
upper bound is

    F(u)=(1+r_0^2)G^2+1/2
           +(2+r_0^2)G u+(3+r_0^2)u^2/4
           +r_0 G sqrt(2-u^2)
           +(r_0/2)u sqrt(2-u^2).                    (21)

This function is strictly concave on [1,sqrt(2)].
For 1<=u<sqrt(2),

    F''(u)=(3+r_0^2)/2
       -r_0[2G+u(3-u^2)]/(2-u^2)^(3/2).

The derivative of the bracketed quotient is

    [6+6Gu]/(2-u^2)^(5/2)>0.

At u=1 the resulting second-derivative upper bound is
217/128-71/40=-51/640<0.

Use the rational point u_0=151/109, whose companion square root
is 31/109. Direct exact substitution gives

    F(u_0)=58822573/14851250<397/100,
    F'(u_0)=73199/1351600,       0<F'(u_0)<3/50.

The reserves are 273779/29702500 and 7897/1351600.
Also sqrt(2)<99/70 and 99/70-u_0=221/7630<3/100.
The global concave tangent bound therefore gives

    F(u)<=F(u_0)+F'(u_0)(u-u_0)
          <397/100+9/5000=19859/5000<4.             (22)

The endpoint u=sqrt(2) follows by continuity. Both endpoints of
the convex X comparison are below four, contradicting (20).
Consequently X/Y>5/8. Its actual center angle gamma satisfies

    gamma>3pi/2+atan(5/8).                            (23)

Again the entire D frame, original contact point and physical mask
were retained. No equation at D or at its other neighbor was used.

## 7. Three actual boundary contacts cannot span these endpoint angles

The purely physical angular-neighbor theorem
CIRCLE_CONTACT_ANGULAR_ORDER.md orders the four actual boundary
path centers. The real leaf center has direction zero. Its
direction cannot lie between any touching boundary pair.
The two endpoint angles (19), (23) therefore force the original
three-edge path to follow the western interval from beta to gamma.
Its two internal centers occur in that interval in their path order.

Every physical boundary center z has

    |z|>=R-1/sqrt(2)>2-1/sqrt(2),
    |z|^2>9/2-2sqrt(2)>5/3,

where sqrt(2)<17/12 gives the last comparison.
If a physical boundary contact had minor center angle at least

    theta=acos(2/5),

its squared center separation would exceed
2(5/3)(1-2/5)=2. This contradicts the actual contact bound
|c_i-c_j|<=sqrt(2). Hence every one of the three path gaps
is strictly less than theta, so

    gamma-beta<3theta.                                (24)

On the other hand (19), (23) give

    gamma-beta>pi+atan(5/8)-atan(2/9)
               =pi+atan(29/82).                       (25)

These inequalities are incompatible. Indeed pi/3<theta<pi/2,
and the triple-angle identities give

    tan(3theta-pi)=9sqrt(21)/118.

The desired strict comparison is exact:

    (29*118)^2-(82*9)^2*21=272560>0,
    3theta-pi<atan(29/82).

This contradicts (24)--(25), proving the entire strict-low
aligned S1234 family impossible.

## 8. Exact reusable and original scope

Sections 1--6 prove the two endpoint-angle bounds for any actual
true degree-three aligned S root at 2<R<sqrt(17)/2 with both other
neighbors physically boundary, in the same compatible singleton
selection class. Their degrees, masks and other forces may be
arbitrary. The original D point is fixed only after its physical
nonalignment is established, and all B mean endpoints remain.

Section 7 additionally requires the real three-edge path consisting
of four physical boundary units. It may not be invoked for a path
with an unloaded or physically clear intermediate unit. The original
S1234 graph has precisely that path, so its full application is
literal. All three arbitrary completion units remain present;
they are used only through the accepted same-nine R>2 reduction.

The critical aligned endpoint d=1 and the full high aligned range
are separately covered by
ALIGNED_S_LEAF_ROOT_TWO_BOUNDARY_NEIGHBORS_EXCLUSION.md.
The tilted ranges have their separately complete ordered-root and
physical-capacity sources. No whole-family or coarse status is
changed by this manuscript before its full reviews and exact join.

No original pose, mean or extracted force is changed. No numerical
scan, Lean compilation, CI, remote edit or shared-metadata edit is
a premise of this proof.

