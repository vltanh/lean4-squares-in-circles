# Whole-unit projection bridges and perpendicular singleton return intervals

Date: October 29, 2026 UTC. Author: root-triangles continuation.

**Status: complete proposed hand theorems, awaiting independent review.**
This source proves a projection obstruction for one actual unit square
joining two actual exterior returns. Applied to the physical-two
West/strict perpendicular-singleton roof, it excludes every original D
return when the vertical component of its upper edge is at most 11/50,
and excludes the whole D-owned exterior-side row when that component is
at most 3/11. A separate direct reuse of the already proved upper-return
bounds excludes every row with b>=1/sqrt(2). The exact residual is retained;
no entire D02 load family is declared closed.

All nine actual squares, original positive edges and forces, actual
normals, full shared means, physical masks and individual zero circle
coefficients remain. No true degree is reduced and no new selector is
chosen.

## 1. An exact one-sided projection bound for one actual unit

Let h,e be an oriented orthonormal frame, let r>0, and put

    f=(-h+r*e)/sqrt(1+r^2).

Let an actual unit square B have an actual minimum-f support point or
support mean K. Thus f.X>=f.K for every X in B; K belongs to the entire
physical support face, with any original endpoint or interior mean kept.
Then

    min_B(e.X) >= e.K-1/sqrt(1+r^2).              (1)

To prove this without assigning a new side mean, first suppose the
support is a vertex. Write B=K+[0,1]*i+[0,1]*j, where i,j are its actual
inward orthonormal unit edges. Their f components are nonnegative.
At most one of i,j has a negative e component: if both did, their
nonnegative cone could not contain f, whose e component is positive.
For any inward edge i with e.i=-v<0, its nonnegative f component forces
h.i<0 and

    sqrt(1-v^2)>=r*v, hence v<=1/sqrt(1+r^2).

The square's full e decrease from K is therefore at most that amount.
Equality and zero inward coefficients are included in this argument.

If the support is a side, the actual inward normal is f and its actual
unit tangent has absolute e component 1/sqrt(1+r^2). Retain the complete
original mean coordinate along that side. Its distance to either side
endpoint is at most one, while displacement into the square in the f
direction increases e. This proves (1) for the entire closed side,
including both endpoints. Equivalently one can choose a support-face
endpoint and retain the original tangent coordinate explicitly.

Reflecting e gives the corresponding statement: for k>0 and an actual
unit C with minimum support at L in direction

    g=(-h-k*e)/sqrt(1+k^2),

the entire square satisfies

    max_C(e.X) <= e.L+1/sqrt(1+k^2).              (2)

These two statements do not use a circle, loads, the squares' other
contacts, their degrees, or a choice of an owning feature.

## 2. The actual one-unit bridge obstruction

Keep B,C,K,L,f,g as above. Suppose an actual unit square N physically
touches both B and C. Choose actual points X in B intersection N and Y
in C intersection N. Every actual unit square has e width at most
sqrt(2), by |e.i|+|e.j|<=sqrt(2) for its own orthonormal edges. Hence

    e.(X-Y)<=sqrt(2).

Equations (1),(2) give the necessary inequality

    e.(K-L) <= sqrt(2)
                +1/sqrt(1+r^2)+1/sqrt(1+k^2).   (3)

Thus a strict reversal of (3) excludes the entire actual B--N--C bridge.
This compares the full squares, not merely selected points or their
centers. N can have any load, physical circle mask, degree, or other
forces. B,C can also have arbitrary degrees and loads. The two contacts
with N may have any actual owners and original shared means. If B and C
already overlap, the original packing is of course impossible as well;
no separation assumption beyond the original packing is manufactured.

## 3. Complete original perpendicular-singleton roof equations

Use the full physical-two West/strict roof from the frozen source cited
in Section 8. In its actual world frame,

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60,
    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-t), 0<t<=1/2,
    H=t+1/2, h=(c,-s), e=(s,c),
    c,s>0, c^2+s^2=1.

The actual entire positive neighborhoods are A:{V,D,B}, D:{V,A,C},
V:{A,D}; A,D are unloaded true3 and V is loaded true2 with two physical
circle corners. The physical singleton AD is owned by A alone, with
normal -e from A. Preserve the actual strict singleton parameters

    A=P+[-1,0]*h+[-l,1-l]*e, 0<l<1,
    W=P-x*h-l*e, 0<x<1,
    v=W-Q=-a*h+b*e=(-u,y),
    a=H*s+x>0, b=H*c-l>0, a^2+b^2=1,
    u=a*c-b*s>0, y=a*s+b*c>0,
    w=-b*h-a*e=(-y,-u), D=Q+[0,1]*v+[0,1]*w.

Here y is the scalar called v_y in the previous roof source. The actual
positive original magnitudes on AV,DV,AD are mu,nu,gamma. Put

    r=gamma/mu, q=gamma/nu.

The complete A3 equations, including its moment, are

    F_B=-mu*h+gamma*e,
    K=P-h+(1-l)*e,
    r=(1-l)/(1-x)=(1-H*c+b)/(1-a+H*s).          (4)

K is the actual uniquely exposed A corner on the real AB contact.
Consequently B has its actual minimum support at K in direction f from
Section 1. No B equation or contact is removed.

The complete D3 force is

    F_C=-nu*East-gamma*e
        =-nu*c*h-(nu*s+gamma)*e,
    F_C.v=nu*u-gamma*b,
    F_C.w=nu*y+gamma*a>0.

Every actual original C point or full side mean can therefore be written

    L=Q+w+z*v, 0<=z<=1,                         (5)

where z=0 in the adjacent-vertex row, z=1 in the opposite-vertex row, and
the entire original z in [0,1] is retained when D owns the C support side.
Thus C has minimum support at L in the actual direction g from Section
1 with

    k=(s+q)/c>q.                                (6)

The full D torque about Q, retaining the original z, is

    -gamma*a-(nu*u-gamma*b)+z*(nu*y+gamma*a)=0,

or equivalently

    q*[b-(1-z)*a]=u-z*y.                        (7)

For z=1 this is exactly q=(u-y)/b, with u>y; for the D-owned side the
force equation is q=u/b, and (7) fixes the original z, rather than
selecting it, as

    z=q*a/(y+q*a)=u*a/c, 0<z<1.                (8)

Both endpoints in (5) were retained before this strict conclusion. The
identity b*y+a*u=c follows by expanding the original frame coordinates.

The physical-two V2, with both original circle coefficients retained,
has the exact moment equation

    nu*t=mu*(d*s+c/2).

It gives the useful full-domain strict estimate

    nu/mu=(d*s+c/2)/t>=2*d*s+c>c+s>1,
    r=(nu/mu)*q>q.                              (9)

Here d>9/10>1/2 and (c+s)^2=1+2*c*s>1; no individual circle weight is
assumed positive. The other complete V2 equations remain those in the
original source and are not replaced by (9).

Finally, all actual points give

    e.(K-L)=1+a+(1-z)*b.                        (10)

The whole bridge necessary inequality is therefore

    1+a+(1-z)*b <= sqrt(2)
                  +1/sqrt(1+r^2)
                  +c/sqrt(c^2+(s+q)^2).        (11)

This is a continuous full-mean obstruction on every original return.
For the D-owned side specifically k=a/b, so its sharper exact version is

    1+a-z*b-1/sqrt(1+r^2) <= sqrt(2).           (12)

No assertion of realizability is made when these necessary inequalities
hold.

## 4. Every return with 0<y<=11/50 is excluded

Because u,y>0 and u^2+y^2=1, write u=cos(theta), y=sin(theta), with
0<theta<pi/2. Similarly c=cos(phi),s=sin(phi). The original b>0 gives
0<phi<theta, and hence

    a=cos(theta-phi)>u,
    0<b=sin(theta-phi)<y.                       (13)

For y<=11/50 one has

    u^2>=2379/2500>1521/1600, hence u>39/40.

In particular u-z*y>=u-y>0 for the entire original z in [0,1]. The
positive q in (7) forces b-(1-z)*a>0, which is at most b. Therefore

    q=(u-z*y)/(b-(1-z)*a)
      >=(u-y)/b>(u-y)/y=u/y-1>151/44.           (14)

The last inequality uses y<=11/50 and u>39/40. By (6),(9), both r and k
are larger than 151/44. Consequently

    1/sqrt(1+r^2)+1/sqrt(1+k^2)
       <88/sqrt(24737)<14/25.                  (15)

The second comparison follows from

    (14/25)^2-88^2/24737=8452/15460625>0.

Equations (10),(13)--(15) show that the gap between the entire actual
units B and C in direction e is strictly greater than

    1+39/40-14/25=283/200>sqrt(2),
    (283/200)^2-2=89/40000>0.

The original actual unit N cannot touch both. This proves the whole
interval 0<y<=11/50 for all original D support rows, including every
closed side mean and the joining endpoint y=11/50.

## 5. Every D-owned exterior side with 0<y<=3/11 is excluded

Retain the complete side row, including the original mean determined by
(8). Its actual force equation gives q=u/b. By (13), q>u/y. Together
with (6),(9), this yields

    1/sqrt(1+r^2)+1/sqrt(1+k^2)
       <2/sqrt(1+(u/y)^2)=2*y.                 (16)

For y<=3/11,

    u^2>=112/121>576/625,
    112/121-576/625=304/75625>0,

so u>24/25. The full whole-square projection gap is therefore strictly
greater than

    1+a+(1-z)*b-2*y
       >1+24/25-6/11=389/275>sqrt(2),
    (389/275)^2-2=71/75625>0.

Again the actual N cannot span that gap. This includes the entire side
row at y=3/11 and all original positive force ratios and means; no C or
N load assumption was used in the geometric obstruction.

## 6. Every return with b>=1/sqrt(2) is already excluded by the upper return

This consequence uses no additional D torque assumption. In the original
chart b<c and s<a. If b>=1/sqrt(2), then

    0<s<a<=1/sqrt(2)<=b<c<1.                    (17)

The upper-return argument in Sections 4--5 of the frozen perpendicular
singleton source uses precisely (4), H<=1, and these inequalities. Its
scalar bounds remain valid at a=b=1/sqrt(2), as checked below.

For completeness, r decreases with H and at H=1 satisfies r>1, since

    c-b=(a-s)*(a+s)/(c+b)<a-s.

Also l>0 gives H>b/c and

    r<1/(1-a+b*s/c)<=c/s.

The final comparison follows from
(s/c)*(1-b)<(a/b)*(1-b)<=1-a. Thus the actual B direction has f_x<=0 and
f_y>=(s+c)/sqrt(2). Put

    D0=1-a+s, N0=1-c+b,
    X=-c*D0+s*N0, Y=s*D0+c*N0.

Then X<=0, Y>0, and f_y>=Y/sqrt(X^2+Y^2). The full continuous bounds
proved by expansion in the cited source are

    b>=9/10:                 f_y>=1/sqrt(2),
    4/5<=b<=9/10:           Y+(4/3)*X>0, hence f_y>4/5,
    1/sqrt(2)<=b<=4/5:      f_y>8/9.             (18)

There is no missing equality endpoint in the last row. If s>=5/16, its
proof uses (s+c)/sqrt(2)>8/9. If s<=5/16, it varies a from 3/5 to its
actual a<=1/sqrt(2), and uses

    d(Y+2*X)/da
      =(2*c-s)-(a/b)*(c+2*s)>=c-3*s>0.

At a=3/5,b=4/5 the value is
c*(1-c)+4*s*(1-c)+s^2>0. All estimates include a/b=1, so (18) includes
the exact endpoint a=b=1/sqrt(2). The middle row is the same unchanged
expansion Y+(4/3)X>0 on 4/5<=b<=9/10 from that complete source.

The actual point K+f belongs to the real B by its physical support
property. In the entire range (17),

    K_y>1/2+b,

because the positive difference after setting H=1 is
s+(1-c)*(c-b). The three intervals (18) therefore give

    (K+f)_y>209/100>R,
    (209/100)^2-1105/256=8271/160000>0.

The least last-row comparison is
1/2+1/sqrt(2)+8/9>209/100; it has the exact positive reserve
1/2-(631/900)^2=6839/810000. Thus every original return with
b>=1/sqrt(2), including its equality endpoint, is impossible.

## 7. Literal callers and the exact retained remainder

In D02.L135 and D02.L1345 keep the actual rim

    A--V--D--C--N--B--A

and the actual chord AD, with A=0,V=1,D=2,C=3,N=4,B=5. A,D are the
original unloaded true3 hubs; V,B,C are the original loaded true2 units.
N remains unloaded true2 in L135 and loaded true2 in L1345. The actual
B--N--C edges are retained, and all three additional actual units and
all their equations remain. Their poses and contacts are unrestricted.
The bridge lemma does not contract N or replace it by a smaller body.

Combining the previous full adjacent-return and c<=3/4 exclusions with
the complete intervals proved here leaves only these necessary rows
in this particular perpendicular-singleton feature:

| Original D exterior support | Exact additional surviving conditions |
| --- | --- |
| Opposite D vertex | c>3/4, 11/50<y<1/sqrt(2), z=1, q=(u-y)/b>0 |
| D-owned C side | c>3/4, y>3/11, 0<b<1/sqrt(2), q=u/b, z=u*a/c in (0,1) |

Both rows must also satisfy every original equation and physical
constraint, as well as the full necessary projection inequality (11)
and, in the side row, (12). These are not realizability assertions.
Whole-data reflection transports the complete rows and all physical
circle coefficients. No other AD owner or physical-two roof chart is
included by changing labels inside a fixed chart.

This is a larger complete continuous feature exclusion, not a closure
of either entire D02 load family, any coarse cell, the nine-square proof,
or the still-open common-selection compatibility premise.

## 8. Exact inputs and scope of the proof

The original full geometry, original forces and literal caller are in

    PHYSICAL_TWO_WEST_STRICT_PERPENDICULAR_SINGLETON_ADJACENT_RETURN_EXCLUSION_AND_COMPLETE_RESIDUAL_2026_10_29.md
    SHA256 f3718c86a99ef196eba1ee875b66375582a0fc588f10275ec171c442e46780dd.

Its complete Sections 4--5 supply only the already printed continuous
upper-return comparisons reused in Section 6, with the equality endpoint
verified explicitly above. The physical contact stress convention and
the six-body graph/load cover remain those of its exact source chain.

The prior center-based bridge source is

    ACTUAL_CENTER_BRIDGE_REACH_AND_PERPENDICULAR_SINGLETON_ROOF_NEAR_PARALLEL_EXCLUSION_2026_10_29.md
    SHA256 8b73232e774201fedb5eec884672bdb431de09b7452c4636f19d7e232c06faf9.

It is unchanged and is not needed for the new projection proof.

No original force, mean endpoint, physical-zero mask, unit or remaining
equation was discarded. No numerical pose search, angle mesh, packing
certificate, Lean/Lake compilation, CI action, ledger/metadata change,
external message or remote write was used. Complete independent review
is required before adoption.
