# A radial boundary tip excludes the parallel North neighbor of an owned S root

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root
and separate independent review.** This closes the C-parallel part
of the one-owner, owned-B-leaf, radial-D North/North interface.
It keeps the actual root and loaded-body equations, every side
mean and both individual D circle weights.

Retain the same nine physical units and the original positive
component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q_*=1105/256.

A alone owns AB. C has one physical circle corner. D has two
physical circle corners, so it is the actual radial S unit in
its own direction. We use the exact North/North domain of
ADJACENT_S_C4_OWNED_TILTED_LEAF_NORTH_CONTACT_REDUCTION.md.

In the world frame the actual root and its genuine leaf satisfy

    A=[-X,h] times [-v,1-v],
    X=1-h, X^2+v^2=d^2, |h|<=epsilon,
    P_AB=(h,-k), 0<k<v<13/50.

With its actual axes j=(s,-c), f=(c,s), c,s>0 and c^2+s^2=1,
B has the owned far-axis genuine S leaf and the actual chart

    B=[epsilon,d] times [-w,1-w] in its (j,f) frame,
    h=epsilon*s-w*c,
    k=epsilon*c+w*s.

Both original outer normals are North in their respective root
frames, with the whole original application means

    P_AD=(-t_D,1-v), t_D=X*k/v>1/2,

    P_BC=(t,T) in B's frame,
    T=1-w, t=epsilon+w*s/c=k/c,
    0<=w*s/c<=1.                                     (1)

No mean in (1) is replaced by an endpoint. The complete North
reduction already proves

    0<w<3/20, p=c/s<3/10.                             (2)

We assume here that C owns the North BC axis, and hence is parallel
to B. The other actual C frame is excluded in
RADIAL_BOUNDARY_TIP_NORTH_PAGE_TILTED_NEIGHBOR_EXCLUSION.md.

## 1. Exact consequences of the actual radial D point

The radial-boundary theorem gives

    t_D^2+(1-v)^2=d^2+1/4.

Therefore, without changing the actual AD mean,

    k^2=v^2*[1+(2v-3/4)/(d^2-v^2)]
       >F(v),

    F(v)=v^2*(1/4+2v-v^2)/(1-v^2).                   (3)

The strict inequality follows from d>1 and 2v-3/4<0.
F is strictly increasing on 0<v<13/50: its positive bracket
has positive derivative
(2+2v^2-3v/2)/(1-v^2)^2.

The actual two root identities also give

    v^2+2wc=2epsilon*(1+s)+epsilon^2-h^2
             <241/3600,

    w^2=k^2-epsilon^2+h^2>=k^2-epsilon^2,
    w<=k.                                           (4)

The actual side-mean interval in (1) gives p>=w. Thus c>=ws.
From p<3/10 we also have s>93/100; the exact squared reserve is

    1/(1+(3/10)^2)-(93/100)^2=57259/1090000>0.

Consequently (4) implies

    v^2+(93/50)*w^2<241/3600.                         (5)

We claim the useful uniform bounds

    v<179/1000, k<(4/5)*v, w<179/1250.                (6)

If v>=179/1000, equations (3)--(4) give

    w^2>F(179/1000)-1/3600>939/50000.

The second comparison has exact reserve
2384933/322653000000. But then the left side of (5) exceeds

    (179/1000)^2+(93/50)*(939/50000)
       =241/3600+1231/45000000,

a contradiction. This proves the first assertion in (6).

Since v<179/1000<9/50 and d<61/60, the exact ratio in (3) gives

    k^2/v^2
      =1-(3/4-2v)/(d^2-v^2)
      <1-(39/100)/(61/60)^2
      =2317/3721<16/25.

The last reserve is 1611/93025. Now w<=k proves the remaining
assertions in (6).

## 2. The original CD owner cover forces a particular real C corner

Write D's actual radial direction in world coordinates as

    e_D=(-sigma,chi), sigma,chi>0, sigma^2+chi^2=1.

Its original AD corner identity is

    1-v=d*chi-sigma/2.                                (7)

It follows that

    sigma<3/10, chi>19/20.                            (8)

Indeed, if sigma>=3/10, then
chi<=sqrt(91)/10<191/200, whence

    1-v<(61/60)*(191/200)-3/20
         =9851/12000<821/1000,

contrary to (6). The chi inequality then follows by squaring.

In B's actual frame put

    eta=sigma*s+chi*c,
    zeta=chi*s-sigma*c.

The radial and transverse D axes and the actual other inner
corner of D are

    e_D=(-eta,zeta), n_D=(zeta,eta),
    Q_D=d*e_D+(1/2)*n_D.                              (9)

Equations (2),(8) imply eta,zeta>0 and

    eta/zeta
       <[(6/19)+(3/10)]/[1-(6/19)*(3/10)]
       =117/172<3/4.

Thus eta<3/5<4/5, and

    zeta+eta/2>1.                                    (10)

For the last inequality, square its positive sides:
1-eta^2>(1-eta/2)^2 is equivalent to
eta*(1-5eta/4)>0.

The complete high North-port fact in Section 1 of
ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md
applies to the actual C2, whose other neighbor D is physical
boundary. Since C owns North, its actual full square and unique
circle corner are

    C=[Z-1,Z] times [T,T+1],
    Z_C=(Z,T+1), Z=sqrt(R^2-(T+1)^2)>1/2.              (11)

This is a conclusion from C's true radial concurrence and unique
physical mask. It is not an imposed orientation or circle corner.

Every actual cycle edge has a side-axis owner by the separate
mixed-mask theorem
ADJACENT_S_C4_ONE_OWNER_RADIAL_MASK_ALL_CYCLE_OWNERS.md.
The complete actual D-to-C cover is its transverse side normal
n_D at Q_D+z*e_D, 0<=z<=1, or a strict normal at Q_D between
-e_D and n_D. All these normals have positive j coordinate.

If D owns CD, then N=n_D has both coordinates positive. Its
minimum point on the actual C is the lower-left vertex of
height T<1. But the actual D-side mean has height

    d*zeta+eta/2+z*zeta>zeta+eta/2>1,

by (9)--(10). This is impossible, with z=0 and z=1 included.

Thus C owns CD. Its four own axes, together with the strict
positive j coordinate of the original D-to-C normal, leave only
the positive j axis. D then uses its strict other inner corner
Q_D, and C uses its actual left-side mean. Comparing only their
actual horizontal coordinates in (9),(11) forces

    Z=1-d*eta+zeta/2.                                (12)

We next show that the actual circle corner in (11)--(12) lies
outside the containing circle. No equation at D is shortened
and no position on C's left side is chosen.

## 3. The range t<1/2

Since t=k/c, this range gives c>2k. From (4),

    v^2+4kw<241/3600.                                (13)

If v>=147/1000, the increasing function in (3) gives

    k>537/5000, w>53/500.

For complete exact checks,

    F(147/1000)-(537/5000)^2
       =4440231/1528735937500>0,

    F(147/1000)-1/3600-(53/500)^2
       =210335087/8805519000000>0.

The second comparison also uses (4). Thus the left side of
(13) would exceed

    (147/1000)^2+4*(537/5000)*(53/500)
       =241/3600+9097/45000000,

a contradiction. Therefore

    v<147/1000, w<147/1250.                           (14)

Equation (7) now implies sigma<13/50. Otherwise
chi<=sqrt(2331)/50<483/500 would give

    1-v<(61/60)*(483/500)-13/100
         =25563/30000<853/1000,

contrary to (14). Hence chi>24/25. With p<3/10,

    eta/zeta
      <[(13/48)+(3/10)]/[1-(13/48)*(3/10)]
      =274/441.

Consequently

    eta<53/100, zeta>169/200.                         (15)

For the first bound the exact squared reserve is

    (53/100)^2-(274/441)^2/[1+(274/441)^2]
       =6425613/2695570000>0.

The second follows from
1-(53/100)^2-(169/200)^2=203/40000>0.

The actual corner (11)--(12) therefore satisfies

    Z>1-(61/60)*(53/100)+(169/400)=2651/3000,
    T+1>2353/1250.

It follows that

    |Z_C|^2
      >(2651/3000)^2+(2353/1250)^2
       =Q_*+7101259/900000000.

This contradicts its actual circle membership throughout
the whole range t<1/2.

## 4. The range t>=1/2 and v<4/25

The mean formula in (1) gives

    p=w/(t-epsilon)<60w/29.

Together with (6) and v<4/25,

    w<16/125, p<192/725.                              (16)

Equation (7) implies sigma<11/40. To verify the full endpoint
comparison exactly, if sigma>=11/40, then

    chi<=sqrt(1479)/40,
    sqrt(1479)<38459/1000.

The latter square comparison has reserve 94681/1000000.
Consequently

    1-v<(61/60)*(38459/40000)-11/80
         =2015999/2400000<21/25,

contrary to v<4/25. The final reserve is 1/2400000.
It follows that chi>24/25.

Using (16) in the actual axis transformation,

    eta/zeta
      <[(55/192)+(192/725)]/[1-(55/192)*(192/725)]
      =76739/128640.

Hence

    eta<103/200, zeta>171/200.                        (17)

The respective squared reserves are

    (103/200)^2-(76739/128640)^2/[1+(76739/128640)^2]
       =2480480716089/897484948840000>0,

    1-(103/200)^2-(171/200)^2=3/800>0.

The actual corner (11)--(12) now has

    Z>10847/12000, T+1>234/125.

Thus

    |Z_C|^2
      >(10847/12000)^2+(234/125)^2
       =Q_*+145241/28800000,

again impossible.

## 5. The range t>=1/2 and v>=4/25

The actual A radius and (3) sharpen two coordinates:

    h>-1/240, k>7/60.                                (18)

For the first use X^2=d^2-v^2 and

    (241/240)^2-[(61/60)^2-(4/25)^2]
       =163/480000>0.

For the second use monotonicity in (3) and

    F(4/25)-(7/60)^2=12637/18270000>0.

The actual orthogonal change of coordinates for B gives the exact
identity

    h+k*p=epsilon*sqrt(1+p^2).                        (19)

If p>=1/5, then (18) gives a left side greater than 23/1200.
But p<3/10 makes the right side less than
(1/60)*(21/20)=21/1200. This contradiction proves

    p<1/5.                                          (20)

Combining (8),(20),

    eta/zeta
      <[(6/19)+(1/5)]/[1-(6/19)*(1/5)]
      =49/89.

Therefore

    eta<49/100, zeta>87/100.                          (21)

The exact squared comparisons have reserves

    (49/100)^2-(49/89)^2/[1+(49/89)^2]
       =386561/51610000>0,

    1-(49/100)^2-(87/100)^2=3/1000>0.

Using the uniform w<179/1250 from (6), the same real corner
satisfies

    Z>5621/6000, T+1>2321/1250,

and hence

    |Z_C|^2
      >(5621/6000)^2+(2321/1250)^2
       =Q_*+1007627/112500000.

This is the final contradiction.

## 6. Exact conclusion and endpoint scope

The three ranges in Sections 3--5 exhaust the original mean t
and actual root depth v. Equality t=1/2 belongs to Sections 4--5;
equality v=4/25 belongs to Section 5. All strict bounds derive
from actual containment or epsilon<1/60, rather than deleting a
side-mean endpoint.

Section 2 covered both possible actual owners of CD. Therefore
the entire stated owned-B-leaf, radial-D, C-parallel North/North
interface is impossible. Together with the separately proved
tilted-C exit, it exhausts every physical C frame in this
original owned-B North/North domain.

All original A3/B3/C2/D2 forces and torques, actual support owners,
original means, zero individual D circle weights and the same
nine physical squares are retained. The only calculations are
exact inequalities on their necessary coordinates. No numerical
pose, orientation assignment, shortened loaded equation,
normal reselection after extraction, compilation, CI, remote
action or shared-metadata change is used.

