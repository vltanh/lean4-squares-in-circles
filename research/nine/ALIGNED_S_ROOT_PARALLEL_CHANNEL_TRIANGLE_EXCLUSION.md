# An aligned S root cannot have a parallel side channel and the house triangle

Date: October 28, 2026.

**Status: complete fresh hand proof of the entire aligned-root,
leaf-parallel-channel interface of house hub-TC.S, submitted for full
independent and root review.** Both channel directions, all radii,
every actual C/D/T frame, physical circle mask and original side mean
are covered. The perpendicular channel has a separate accepted proof;
oblique channels and tilted genuine roots are not claimed here.

## 1. Original graph, full degrees, and actual channel chart

Retain the original positive graph

    AT, DT, AD, AB, BC, CD, AL,
    A4/T2/D3/B2/C2/L1.

The only positively circle-loaded units are T,C,L. L is A's genuine
S leaf. A,B,D have zero total circle load; an individual physical
circle contact of zero weight is not discarded. All nine actual
interior-disjoint unit squares remain in the disk, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1.

Assume A is parallel to its genuine S-leaf axis, and B's unchanged
side channel is parallel to that axis. Rotate the actual notation
so the real leaf points East. Its complete physical chart is

    A=[d-1,d] x [-b,a], a,b>=0, a+b=1,
    L=[d,d+1] x [-1/2,1/2].                         (1)

The genuine leaf force at A is positive East and acts at (d,0).
No other A force is omitted. The physical D bypass makes the actual
unloaded B2 a side-normal channel of width one. An East channel
would place C in x>=d+1, contrary to the sharp contained-unit support
bound d. Thus its original normal from A is West.

Its far C support is then 2-d<=d, so d>=1. Write

    d=1+epsilon, 0<=epsilon<1/60,
    R^2=(2+epsilon)^2+1/4.                          (2)

The strict upper epsilon bound follows directly from the declared
radius cap. In particular the parallel-channel assumption has already
excluded every strict-low radius; the critical equality is retained.

Reflect vertically so that D is below the actual B. The complete
bypass theorem gives the unchanged chart and application means

    B=[epsilon-1,epsilon] x [z,z+1],
    P_AB=(epsilon,q), P_BC=(epsilon-1,q),
    max_D y<=z<=q,             -b<=q<=a.            (3)

The full local theorem
`SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md`
applies with longitudinal West and transverse North: its support
height is -epsilon, its actual B,C,D degrees are precisely B2/C2/D3,
and T is boundary. It gives

                          q>0.                    (4)

This invocation retains the original q=0 D3 endpoint proof and both
parallel and nonparallel C alternatives. Its independent review is
a direct dependency of the present new proof.

The aligned A/B intersection on x=epsilon has positive side length.
Otherwise it would be a singleton vertex pair whose selected West
axis does not strictly expose both vertices. The original singleton
convention excludes that case before extraction. Therefore

                    z<a,   max_D y<a,   a>0.       (5)

## 2. Complete A4 routing with the actual triangle retained

Let v,w be the actual unit normals from A toward D,T. The channel
normal n is West. First

                          n dot v>=0.              (6)

Indeed, at the actual AD point P, D minimizes v. If n dot v<0,
the complete unit support-span lemma would give
max_D n dot(X-P)<1. But P belongs to A, whereas an actual CD point
belongs to C beyond the full channel width one. Its n projection
is at least h_A(n)+1, while n dot P<=h_A(n). This is a contradiction.
No D force equation or boundary status is used in (6).

Consequently v_x<=0. If v were an A-owned North or South axis,
the actual A-D-T triangle would give v dot w>=0. Dotting the full
original A4 force equation with v would then have a strictly positive
AD term and a nonnegative AT term; the East leaf and West AB terms
vanish. This is impossible. Thus an owned v can only be West.

A strict Northwest AD would apply at (epsilon,a), contradicting
max_D y<a. The only remaining strict v is Southwest, at
(epsilon,-b). Full A4 vertical balance then gives w_y>0. An A-owned
North w has negative dot product with v, forbidden by the physical
triangle's side-owner theorem. A strict Northeast w would use the
opposite A vertex from AD, which the full physical triangle support
argument forbids. The sole surviving positive-y feature is therefore
strict Northwest at (epsilon,a).

If instead v is West, full A4 vertical balance gives w_y=0. An East
w would put the contained boundary T beyond x=d. The sharp support
equality case makes it exactly the already occupied genuine leaf L,
impossible for distinct actual units. Hence w is West.

This complete original owner/feature routing leaves just

    AD Southwest, AT Northwest;   or   AD West, AT West.          (7)

All owned normals above retain their original application means.
Neither an A3 surrogate nor a D2 equation has been used.

## 3. Actual C/T circle-resultant signs eliminate the first row

Write F_C,F_T for the full outward radial circle resultants, including
all their original individual weights. At a nonparallel loaded C2,
the conditional proper-concurrence theorem places its radial point
on the incoming horizontal line y=q. Its radial factor is positive,
so (4) gives (F_C)_y>0. This use requires no boundary neighbor:
nonparallelity is explicitly assumed in this row.

If C's pair forces are parallel, the local parallel-load classification
makes both outward normals East and its circle resultant West. Thus
(F_C)_y=0. Only that local classification is used; the full-component
simple-cycle theorem is not assigned to this house graph.

Summing all original force equations of the six-body component cancels
every internal pair force. The genuine leaf circle resultant is a
positive East vector, and hence

                         (F_T)_y=-(F_C)_y<=0.       (8)

In the first row of (7), the actual AT point is (epsilon,a), with
a>0, and w is Northwest. If T is nonparallel, its proper radial
point is (epsilon,a)+rho*w, rho>=0, and has positive y. If T is
parallel, its circle resultant points along w, again with positive y.
Both contradict (8). The only surviving A normals are

                           v=w=West.               (9)

If C were parallel here, (8) would make F_T horizontal. T's actual
incoming outward normal toward A is East. Full T2 then makes its
other pair normal horizontal, so the local parallel classification
applies to T as well. Its West radial direction would give maximum-x
inner support -d or -(R-sqrt(2)), both strictly negative. But its
actual maximum-x support at A is epsilon>=0. This is impossible.

Therefore C and T are both nonparallel. Their original proper radial
points give

    (F_C)_y>0, (F_T)_y<0,
    P_AT=(epsilon,t),       -b<=t<0.                (10)

Every physical two-corner mask is still allowed. No assertion that
its concurrence is inside its square is made in this section.

## 4. A force-free boundary-port bound forces q<1/4

The actual T has maximum x equal to epsilon and contains the actual
West A application (epsilon,t), with -b<=t<0. These facts and its
physical boundary status imply

                        b>3/4,
                 a<1/4,   0<q<1/4.                (11)

Here is the complete orientation proof. If T is aligned, it is
[epsilon-1,epsilon]x[u,u+1], with t-1<=u<=t. Every corner has
absolute x coordinate at most one and absolute y coordinate at most
b+1. If b<=3/4, its squared norm is at most65/16<17/4<=R^2.

Otherwise its unique rightmost vertex is P=(epsilon,-v),
0<v<=b, and its two inward axes are (-c,s),(-s,-c), c,s>0,
c^2+s^2=1. The four squared norms are bounded respectively by

    epsilon^2+v^2,
    epsilon^2+v^2+1,
    epsilon^2+(v+1)^2,
    epsilon^2+1+(v+1)^2.                            (12)

For the last one expand exactly as
epsilon^2+v^2+2-2*epsilon*(c+s)+2*v*(c-s), and use
epsilon>=0 and c-s<=1. The other three bounds follow by the same
direct expansions. If b<=3/4, all are less than

    1/3600+65/16=17/4-337/1800<R^2.

Thus no corner would touch the circle, proving (11). This argument
uses every actual T orientation and does not restrict its circle mask.

## 5. Complete physical C-mask reduction

Use orthonormal coordinates with transverse world y as the first
coordinate and longitudinal West as the second. The actual incoming
C port and supporting half-plane are

    P=(q,H),       H=1-epsilon>59/60,
    C subset {second coordinate>=H}.                (13)

Its norm satisfies

                   |P|^2=H^2+q^2<d^2+1/4.         (14)

A contained unit with two physical circle corners is a radial S
square: in its own center coordinates equality of two farthest corner
norms makes one center component zero, and the remaining radial
coordinate gives exactly [d,d+1]e+[-1/2,1/2]Je. The containing
radius excludes the center-zero/four-corner case. Every boundary
point outside the relative interior of that radial inner side has
norm at least sqrt(d^2+1/4). Thus (14) forces P to lie in that
relative side interior. Its original incoming axis then identifies
e as North in (13), and its actual support H must equal d.

Consequently a physical two-corner C is possible only at

    epsilon=0, d=1,
    C=[-2,-1]x[-1/2,1/2] in world coordinates.       (15)

The two circle weights in (15) remain entirely original and need not
be equal. This is the separate critical row of Sections 7–9.

## 6. Every unique-circle C is impossible at the full original port

For the unique physical circle mask, conditional nonparallel
properness puts the radial point inside C. This inside clause is
used only here. The following elementary high-port calculation is
restated so no boundary-neighbor premise is silently transferred.

If C owns North in (13), its unique physical circle corner is its
upper-right corner (Z,H+1), because the proper point has positive
first coordinate q. Hence

    Z=sqrt(R^2-(H+1)^2)=sqrt(1/4+8*epsilon),
    q >= H*Z/(H+1).                                 (16)

The latter follows directly from the unchanged incoming ray
P+rho*North, rho>=0, and its positive radial direction. The right
side of (16) is at least1/4. After squaring positive quantities, the
exact difference is

    (1-epsilon)^2*(1/4+8*epsilon)-(2-epsilon)^2/16
      =epsilon*(124-253*epsilon+128*epsilon^2)/16>=0.             (17)

The bracket is positive on 0<=epsilon<1/60, since it is greater
than124-253/60. This contradicts q<1/4, including epsilon=0.

Otherwise P is C's strict minimum vertex. Write its inward axes as
f=(c,s), j=(-s,c), c,s>0, c^2+s^2=1. Since P dot f>0,
its sole circle corner is P+f or P+f+j. In the opposite case put
M=c-s,N=c+s. The inside positive radial point on the vertical ray
forces M>=0 and q*N>=H*M. Therefore

    R^2=(q+M)^2+(H+N)^2
        >=(M^2+N^2)*(1+H/N)^2
        >=(sqrt(2)+H)^2>R^2,

a contradiction. The final strict comparison follows from
sqrt(2)+H>7/5+59/60=143/60>25/12>R. This also covers M=0 and
zero proper distance.

For the remaining adjacent circle corner Z=P+f, the actual opposite
corner Z+j must be strictly inside, because the physical mask is
unique. Thus Z dot j<-1/2, or q*s-H*c>1/2. It implies q>1/2,
again contradicting (11). This exhausts all actual C owners, side
means and unique-circle frames.

## 7. The critical radial C fixes every possible D incoming feature

Retain the whole remaining row (15), with all original circle weights.
Equation (10) and full C2 give that its actual normal g from C to D
has g_y<0. By (9), D has maximum x equal to zero. Consequently
every D point has x>=-sqrt(2)>-2, and the bottom-left C vertex cannot
be an actual CD point. A horizontal g is excluded by g_y<0.

If g were South, D's maximum-y support would have to contain a point
of C's bottom side x in[-2,-1], y=-1/2. For tilted D its top vertex
has x strictly between -1 and0, impossible. For aligned D its whole
top side has x in[-1,0]; the only possible point is (-1,-1/2).
That would be a singleton pair of aligned vertices with an axis
normal, forbidden by the unchanged strict singleton convention.

It follows that the actual g is strictly Southeast and

                         P_CD=(-1,-1/2).            (18)

For an aligned D, its actual Northwest support at (18) gives

                         D=[-1,0]x[-3/2,-1/2].      (19)

For a tilted D, write its unique right vertex as P_D=(0,y_D) and
its inward axes as

    f=(-c,s), j=(-s,-c), c,s>0, c^2+s^2=1.

Its actual Northwest CD normal has positive dot product with f,
so its support lies on P_D+f+[0,1]j. The first coordinate -1 is
strictly between -c-s and -c; hence (18) is in that side's relative
interior. D genuinely owns its original CD normal f, and the original
side mean eta is fixed by the actual contact:

    eta=(1-c)/s=s/(1+c),
    P_CD=P_D+f+eta*j,
    y_D=-1/2-eta.                                   (20)

Because the unchanged AD point P_D belongs to A, y_D>=-b>=-1.
Thus

                     eta<=1/2,
                       c>=3/5, s<=4/5.             (21)

Weak inequalities suffice below. In fact a>0 makes the first one
strict. No circle equation or fictitious D2 concurrence was used.

## 8. Elementary support facts for the actual T at x=0

At the critical radius T has maximum x zero and its actual AT
application is (0,t), -1<=t<0. The following statements include all
its frames and every owned support mean.

If an outward normal has nonnegative x and strictly positive y,
every maximizing T point has height at least t. If its x is strictly
positive as well, every maximizing point has x>-1. For an aligned
T the first statement is its top row, and a strict Northeast normal
uses its upper-right vertex. For tilted T write

    T=(0,t)+[0,1](-a_T,b_T)+[0,1](-b_T,-a_T),
    a_T,b_T>0, a_T^2+b_T^2=1.                       (22)

The normal's dot product with the second inward axis is strictly
negative. Its maximizing points therefore have second own coordinate
zero, yielding x in[-a_T,0] and y>=t. This proves both statements,
including a zero first normal coordinate and all owned endpoints.

Also no outward supporting normal at a maximum-x T point can have
negative x component. At a unique right vertex both bounding outward
axis normals have positive x components; an aligned max-x side or
its endpoints gives the same weak conclusion.

These are purely physical facts, not T2 equations or circle-mask
restrictions.

## 9. Full D3 excludes both critical D frames

### 9.1. The aligned D row

Let alpha>0 be its whole DA force magnitude, and let its DC force
be nu*(-u,v), u,v>0. Full original D3 makes the DT force

                      F=(nu*u-alpha,-nu*v).         (23)

Its second component is strictly negative. In chart (19), a positive
first component puts its actual DT application at (0,-3/2). T's
opposite normal is Northwest at a maximum-x point, impossible by
Section 8. A negative first component puts the application at
(-1,-3/2); its T normal is Northeast, whose actual support has x>-1.
For zero first component the whole original DT bottom-side mean has
height -3/2, while the actual North T support has height at least
t>=-1. All three alternatives are impossible.

### 9.2. The tilted D row: all three actual DT features

Use (20), retain its entire original eta, and write the full DA and
DC forces as alpha*East and nu*f. Then

    F_DT=(nu*c-alpha,-nu*s),
    F_DT dot j=alpha*s>0,
    F_DT dot f=alpha*c-nu.                           (24)

These exact full-D3 equations leave precisely the opposite vertex,
the whole far j-normal side, or the bottom vertex.

If alpha*c>nu, the application is P_D+f+j, with x=-c-s<-1.
Equation (24) also has strictly negative first component, so the
opposite T normal is Northeast. Section 8 gives x>-1, a contradiction.

If alpha*c=nu, the original DT mean is
P_D+j+lambda*f, 0<=lambda<=1. Torque about P_D, using the actual
CD mean P_D+f+eta*j, gives

    0=-nu*eta+lambda*alpha*s,
    lambda=c*eta/s=c/(1+c).                          (25)

Thus the actual DT height is

    y_D-c+lambda*s
      =-1/2-c-(1-c)*eta <=-11/10<-1.                 (26)

The opposite T normal is -j=(s,c), strictly Northeast. Its support
height must be at least t>=-1 by Section 8. This excludes the whole
original side interval through its unchanged torque; no mean was
chosen or moved.

Finally suppose alpha*c<nu. The actual DT point is P_D+j, with

                x=-s,  y=y_D-c<=-11/10<-1.          (27)

Its T normal has strictly positive y. If its x component were
nonnegative, Section 8 would contradict (27). Hence that normal
is strictly Northwest.

An aligned T would maximize this normal at its upper-left vertex
x=-1, whereas -s>-1, impossible. For tilted T use the complete
frame (22). A Northwest outward normal has strictly positive dot
product with its first inward axis, so every maximizing point has
first own coordinate one. In particular the actual point in (27)
has x<=-a_T. Therefore

                    a_T<=s<=4/5,   b_T>=3/5.        (28)

The four actual T corner squared norms, using -1<=t<0, are bounded by

    t^2<=1,
    1+t^2+2*b_T*t<=2,
    1+t^2-2*a_T*t<=2+2*a_T<=18/5,
    2+t^2+2*t*(b_T-a_T)
       <=3+2*max(a_T-b_T,0)<=17/5.                  (29)

Every number is strictly less than the actual critical R^2=17/4.
T would be circle-clear, contradicting its original positive circle
load. This proves the last critical alternative with every physical
T mask retained.

## 10. Exact whole-interface conclusion and dependencies

The parallel-channel directions East and West, strict-low and
high/critical radii, full A owner cover, every C mask, and both
critical D frames have now been exhausted. The entire original
house hub-TC.S interface with A aligned to its genuine leaf and
B's channel parallel to that axis is impossible. The real L and
all three arbitrary extras remain. No canonical motion, completion
capacity assertion, D2 substitution, changed force, or changed mean
is used. Oblique channels and tilted-root charts remain separate.

The exact operative sources are:

| Source | SHA-256 | Literal use |
| --- | --- | --- |
| `FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md` | `7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d` | Original house hub-TC.S graph, degrees and loads |
| `UNIT_BYPASS_NORMAL_CHANNEL.md` | `d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8` | B width one and full actual transverse separation |
| `SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md` | `5a1607a588e45d0702c46c3d74074561f31109dccc0b8f94c665991cd4a9f5ee` | Full q>0 theorem, with all q=0 D3 and parallel-C endpoints |
| `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` | `7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282` | Only Lemma 1.1: conditional nonparallel C2/T2 properness; unique-mask inside clause |
| `SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md` | `cd2a8c765c181ac803d8ee1c8672d1a8ceea3591248cbca449ef3653b4be6ebe` | Only Section 1's local parallel-load classification, not its whole-component theorem |
| `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` | `6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb` | Only Section 1 sharp physical support/equality and Section 2 opposite-vertex triangle obstruction |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | `ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac` | Full physical support-span and owned triangle dot-product facts |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a` | Original strictly exposing singleton convention |

The high-port calculation of Section 6 is restated in full; no
boundary-neighbor premise of an older loaded-tip caller is imported.
The critical radial mask is proved separately and never assigned the
unique-corner inside-concurrence clause. All formulas in (12),
(17), (20), (25) and (29) were checked by exact expansion. No sampled
pose, Lean compilation, CI step, shared ledger or remote update is
part of this source.

The common positive-mean source is now fully independently accepted in
`REVIEW_SIDE_CHANNEL_UNLOADED_TRIANGLE_POSITIVE_MEAN_HEXAGON_2026_10_28.md`,
SHA-256 `3077224a609df530e0db2887186729bdfd7db0706dde55f8905564d72c6579f6`.
The present whole parallel-channel proof requires its own separate
independent and root audits; none is inferred from that prerequisite.
