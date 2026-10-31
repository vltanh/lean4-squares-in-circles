# A far support cap excludes parallel endpoints of a three-boundary path

Date: October 27, 2026.

**Status: complete new geometric lemma and original C5 parallel/critical
application, awaiting independent and root review.** No original fine or
coarse gate is closed by the remaining necessary root-domain result.

Work with the same actual interior-disjoint unit squares in

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, epsilon=d-1.

Whenever epsilon is used below, 0<=epsilon<1/60 is assumed. Every
physical circle corner is retained. The statements in Sections 1--3
are force-free and impose no graph degree or circle-weight convention.

## 1. A contained unit beyond support 59/60 has a narrow center cone

Let T be an actual contained unit and let n be a unit vector such that

    n.x >= 59/60 for every x in T.                         (1)

Write its actual center as X n+Y Jn. Then

    X>=89/60, |Y|<1/5,
    angle(c_T,n)<atan(12/89)<2pi/45.                       (2)

The weak first bound retains an axis-aligned equality support in (1);
the transverse estimate still gives the strict angular conclusion.

Choose the two actual side axes so their absolute n components are
c,s with c>=s>=0 and c^2+s^2=1. Put k=c+s. The n width is k.
The farthest n-support vertex and containment give

    59/60+k<=R<1039/500,
    k<821/750.                                          (3)

The exact squared reserve for the last radius comparison is

    (1039/500)^2-1105/256=6711/4000000>0.

On [1/sqrt(2),1], c+sqrt(1-c^2) is decreasing. If c<=199/200,
then

    k>=(199+sqrt(399))/200>821/750,

because sqrt(399)>299/15, with squared reserve374/225.
Consequently

    c>199/200, s<1/10, c-s>179/200.                       (4)

Reflect across the n line so Y>=0. The literal four-vertex cover
gives an actual vertex whose n-coordinate is at least 59/60+c
and whose Jn-coordinate is at least Y+(c-s)/2.

For clarity, in the side orientation where the far n vertex is
also the higher of the two far vertices, use that vertex: its
coordinates are at least (59/60+c+s,Y+(c-s)/2). In the other
orientation use the upper of the two vertices on the side beyond
n-coordinate 59/60+c: its height is Y+(c+s)/2. These two
possibilities include s=0 and every translation of the actual unit.

If Y>=1/5, (4) therefore gives an actual vertex with squared norm

    >(59/60+199/200)^2+(1/5+179/400)^2
     =1105/256+1199/72000,

a contradiction. Thus |Y|<1/5. Also X>=59/60+k/2>=89/60.
It follows that the center angle is less than atan(12/89).
Finally

    atan(12/89)<12/89<31/225<2pi/45,

using pi>31/10 and the exact middle reserve59/20025.
This proves (2) with every own-axis and support endpoint included.

## 2. A parallel direct contact and one-unit channel cannot meet the
## endpoints of a three-boundary path

Suppose B,M,C are distinct physical boundary units with the actual
contacts B--M and M--C. Suppose, for one actual unit vector n and
some h>=-epsilon,

    n.x>=h       on B,
    n.x>=h+1     on C.                                  (5)

Then this configuration is impossible.

Indeed the actual B center has n component at least h+1/2>
29/60. The sharp contained-unit center bound is

    |c_B|<91/60.

Thus its angle from n is strictly less than2pi/5, since

    cos(angle(c_B,n))>29/91>5/16>cos(2pi/5),

where the middle reserve is9/1456 and
cos(2pi/5)=(sqrt(5)-1)/4<5/16. The actual C satisfies (1),
so its center differs from n by less than2pi/45. Their minor
center separation is therefore strictly less than

    2pi/5+2pi/45=4pi/9.                                 (6)

But the actual boundary path puts M between B,C in their circular
order. Each adjacent gap is strictly greater than2pi/9 by
CENTERED_INNER_ARC.md. Their sum is the minor endpoint gap:
each touching gap is less than arccos(9/25)<5pi/12, so the
sum is less than pi. These are the complete physical order
facts proved in THREE_BOUNDARY_PATH_RESULTANT_CONE.md.
Consequently that same endpoint gap is greater than4pi/9,
contradicting (6).

No equation at B,M,C or an unweighted circle mask was used.
In particular (5) need not arise from a stress channel; it is
a sufficient physical pair of supporting half-planes.

## 3. An opposite high port cannot reach such a path endpoint

Assume now d>=1. Let B,M,C be as in Section 2. Suppose B contains
a point P with

    |P_x|<1/30, 29/30<|P_y|<=1,

and C satisfies (1) for a normal n whose direction differs by
less than1/59 from the vertical direction opposite to P_y.
Then this configuration is impossible.

Every physical boundary center in this radius range has norm

    |c_B|>=R-1/sqrt(2)>27/20.

Also |c_B-P|<=1/sqrt(2). Hence |(c_B)_x|<3/4, since
1/sqrt(2)<43/60. Its y component has the sign of P_y because
29/30>1/sqrt(2), and its magnitude exceeds1: otherwise its
center norm would be at most sqrt(1+9/16)=5/4<27/20.
Thus its angle from the P_y vertical is less than atan(3/4)<2/3.
The latter exact comparison follows from

    atan(3/4)
       <=3/4-(3/4)^3/3+(3/4)^5/5
       =2/3-151/15360.

Section 1 puts the actual C center within12/89 of n.
Their minor center separation is therefore greater than

    pi-2/3-12/89-1/59
      >111/50+24241/393825.                             (7)

Here pi>31/10 was used in the last exact comparison.
The high-radius two-edge boundary-path estimate in
THREE_BOUNDARY_PATH_HIGH_RADIUS_ANGLE_BOUND.md instead makes
that endpoint center separation less than111/50. Its center
estimate remains strict at d=1, as does |c_B|>27/20 above.
This is the contradiction.

## 4. Exact original C5 load123 S-leaf applications

Retain the whole original selected component

    A--B--M--C--U--A, A--L,

with B,M,C positively circle-loaded, U the actual unloaded
degree-two transmitter, A of true degree three, and L the
genuine S leaf. These are original labels A=0,B=1,M=2,C=3,U=4.
Keep all six core squares and all three original extras, all
original forces, owners, physical masks, zero individual circle
weights and actual means.

Normalize the actual leaf as

    L=[d,d+1] x [-1/2,1/2], p_AL=(d,0).

A contains the actual inward normal segment from p_AL of length
one. Thus if d<1 it contains O. The real A--U--C channel has
width w in {1,sqrt(2)} and actual support h=h_A(n), with

    h+w<=d.

At d<1 this contradicts h>=0. At d>=1, the actual point
epsilon e_x in A gives h>=-epsilon; hence w<=d+epsilon<31/30,
so w=1 and

    -epsilon<=h<=epsilon.                               (8)

### 4.1. Every parallel root-pair alternative is excluded

If the two actual root cycle forces are parallel, full A force
balance makes their line horizontal. A force toward +e_x is
impossible: the sharp support-equality theorem makes any actual
unit beyond the leaf support d the same radial unit L. Therefore
both actual cycle normals equal -e_x.

The direct B support and the real U-channel C support are exactly
(5), with n=-e_x and h=h_A(n). Section 2 excludes them.
This treats both aligned and tilted A, every actual side mean
and all radius endpoints. In particular no radial concurrence
is assigned to a parallel root.

### 4.2. The entire critical radius d=1 is excluded

A strictly tilted genuine S root at d=1 contains O in its open
interior, so h>0 contradicts (8). An aligned root has form

    A=[0,1] x [-b,a], a,b>=0,a+b=1.

If a,b>0, h=0 forces n=-e_x, and full A force balance makes
the other root cycle normal also -e_x. Section 4.1 applies.

It remains that O is a vertex of A. Reflect so A=[0,1]^2.
The zero support condition permits n in the closed southwest
quadrant. If n is strictly southwest, its actual A port is O
and its origin moment is zero. The common original cycle moment
would therefore be zero, which is impossible: B,M,C are genuine
loaded degree-two bodies, their pair lines are nonparallel,
their radial concurrences are proper, and the actual B--M
contact gives a nonzero common moment of the sign of
det(F_B,F_C). The detailed local argument is exactly Section 2
of D_LEAF_C5_THREE_CONSECUTIVE_LOADS_EXCLUSION.md before its
D-root sign comparison; it uses no equation or root geometry at A.
The full A leaf moment is zero, so its real torque transports
this same moment around the whole cycle.

For n west, full force balance gives the parallel case.
For n south, full force balance makes the actual A-to-B normal
strict northwest; its actual A port is P=(0,1).
The endpoint C has minimum south support1. Section 3 applies
with P=(0,1) and exactly vertical n, giving a contradiction.
These exhaust the critical support cone, including its axes.

### 4.3. A whole aligned channel half-plane is excluded

At d>1 put

    A=[epsilon,d] x [-b,a], a,b>=0,a+b=1.

The parallel case is already excluded. Suppose the actual
channel normal has n_x>=0. Its vertical component is nonzero;
reflect so n_y>0. Since h=d n_x+a n_y<=epsilon,

    0<=n_x<1/60, n_y>59/60,
    a<1/59, b>58/59>29/30.

Full A force balance makes the actual A-to-B normal have both
components negative. Its actual port is P=(epsilon,-b),
which satisfies Section 3. The angle of n from north is
less than1/59, using atan(n_x/n_y)<1/59.
C has minimum n support1+h>=1, so Section 3 excludes the
whole n_x>=0 domain.

Thus every remaining aligned member has, after reflection,

    n_x<0, n_y>0, m_y<0.                                (9)

No sign for m_x has been assumed or concluded here.

### 4.4. The negative-second-axis channel of a tilted root is excluded

Use the complete genuine tilted chart

    A=(d,0)+[0,1]f1+[0,1]f2,
    f1=(-a,-b), f2=(-b,a),
    a>=b>0,a^2+b^2=1.

Suppose the actual channel normal is n=-f2=(b,-a).
Its support is db<=epsilon, so b<1/60,a>59/60.
The full A3 force equation makes the other root normal have
positive components along both f1 and f2. Its actual port is

    P=(d-a-b,a-b).

Here |P_x|<1/30 and 29/30<P_y<1. Indeed
-b<=d-a-b<epsilon+(1-a), and
1-a=b^2/(1+a)<1/3600.
The channel axis differs from south by less than1/59, and C
has minimum n support1+db>=1. Section 3 excludes this whole
axis alternative, with the actual U shared mean unchanged.

## 5. Scope

The new local theorem excludes complete parallel/direct-channel
endpoint configurations with a real three-boundary path. Its exact
C5 consequences exclude all d<=1, all parallel root cycle pairs,
all aligned n_x>=0 channels, and the stated tilted negative-axis
channel. They are necessary-domain improvements inside the
existing original M6.B5L.C5.L123.S family, not closure of that
whole family or a new fine ID. The reflected234 image is covered
by reflecting the same original physical data.

Every step used actual supports, physical units or complete local
equations at their true degrees. In particular M's positive load
has not been replaced by an unloaded transmitter. No sampled pose,
changed mean, new selected normal, Lean compilation or CI is used.

