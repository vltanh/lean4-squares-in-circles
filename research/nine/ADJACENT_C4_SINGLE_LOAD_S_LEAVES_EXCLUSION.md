# Two adjacent S leaves cannot occur in the single-load four-cycle

Date: October 27, 2026.

**Status: complete hand original-family proof, submitted for full root
and separate independent review.** The compatible finite physical
preselection used in Section 4 is proved explicitly. It is imposed
before extracting a certificate, never by rotating an existing force.
No shared coarse or fine label is changed.

Keep the original nine physical unit squares, the common radius/Phi
minimizer, and a compatible minimum-positive-original-scalar-atom
certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

The positive component is the original C4 A--B--C--D--A with
genuine S leaves L at A and M at B. C is positively circle-loaded;
D has zero circle load. The true degrees are A3,B3,C2,D2,L1,M1.
All three other original physical squares remain arbitrary and
present. Every real normal, actual application mean, physical circle
mask and individual zero weight remains.

**Theorem.** The entire original family

    M6.B4L2.C4.ADJACENT.LC.SS

is impossible. The proof keeps the true B3 equation and does not
make B into a transmitter or a boundary unit.

## 1. The complete first-root support reduction

Both genuine roots meet D_epsilon and are physically circle-clear.
The true D2 is a normal transmitter; its actual channel A--D--C
has width one by UNIT_BYPASS_NORMAL_CHANNEL.md, since the real B
physically touches both endpoints. All actual transverse means
remain unchanged.

For its outward A direction n and support h, the actual C lies
beyond n.z>=h+1. The sharp contained-unit center bound gives

    |c_T|<=d+1/2,
    h+1<=d.                                             (1)

If d<1, O belongs to the genuine root A closed, so h>=0 contradicts
(1). Hence d>=1 and epsilon=d-1. At the actual AB edge, the genuine
B point epsilon e_M gives the other support bound

    h_A(n_AB)<=n_AB.(epsilon e_M)<=epsilon.              (2)

The original AD support also satisfies h<=epsilon by (1). The
complete support-only theorem GENUINE_LEAF_ROOT_SMALL_NONLEAF_SUPPORTS.md
therefore makes the genuine A leaf direction an own side axis.
Normalize its actual chart as

    L=[d,d+1] times [-1/2,1/2],
    A=[epsilon,d] times [-b,a],
    a,b>=0,       a+b=1.                                (3)

Sections 4--5 of RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md
now apply to the two actual nonleaf forces solely through (1),(2)
and the full A3 force and torque equations. Those sections use
neither a channel nor boundary status at the other endpoint once
the two support inequalities are established; their later boundary
comparison is not imported here. For precision, their conclusions
at the present true root are the following exhaustive alternatives.

* Both actual nonleaf normals are west. Their real application
  heights t,u retain the complete equation mu t+nu u=0.
* After vertical reflection, the actual AB and AD normals are

      n_AB=(-cos(phi),sin(phi)),
      n_AD=(-cos(psi),-sin(psi)),
      phi,psi>0,       sin(phi),sin(psi)<=4epsilon,
      phi,psi<pi/36.                                  (4)

  Their actual A applications are the two left vertices
  (epsilon,a),(epsilon,-b), with a,b>0, and

      a=tan(phi)/(tan(phi)+tan(psi)),
      b=tan(psi)/(tan(phi)+tan(psi)).                   (5)

The strict-west conclusion follows from the old proof's complete
force-and-torque support cover, including its vertical-normal and
shared-side endpoint cases. In (4),(5) the original vertical
balance and origin moment are respectively

    mu sin(phi)=nu sin(psi),
    mu a cos(phi)=nu b cos(psi).

The angle bound follows from the larger of a,b being at least
one half and h_A(n_i)<=epsilon; both sines are at most 4epsilon.
At epsilon=0 the second alternative is therefore impossible.

## 2. Uniform geometry of the actual loaded endpoint cap

These physical facts will be used repeatedly, with no equation or
circle-mask restriction at C beyond the stated actual channel.
Use coordinates X along n_AD, toward C, and Y perpendicular to
it. The actual C lies in

    X>=1+h,       -epsilon<=h<=epsilon.

The lower bound on h follows from A's real point epsilon e_L.
Every center has norm below 91/60. The C center consequently has

    X_C>=3/2-epsilon>89/60,
    |Y_C|^2<(91/60)^2-(89/60)^2=1/10,
    |Y_C|<1/3.                                         (6)

Its direction is within pi/12 of n_AD, since

    X_C/|c_C|>89/91>cos(pi/12).

The full square's directional width w in the channel direction
also satisfies

    1<=w<=1+4epsilon<16/15.                             (7)

Indeed X_C>=1+h+w/2 and X_C<=d+1/2 give this directly.
If theta is the angle between the channel's reverse direction
(outward from C toward A) and the nearest actual own axis of C,
then |theta|<=pi/4 and

    cos(theta)+|sin(theta)|=w<16/15,
    |sin(theta)|<1/14,       cos(theta)>13/14.            (8)

For the second line, the increasing function z+sqrt(1-z^2) on
[0,1/sqrt(2)] at z=1/14 is greater than 16/15: its exact
comparison reduces to 195*225>209^2. At a corner supported
strictly between that own axis and its adjacent positive-Y axis,
the corner's Y coordinate exceeds the center's by at least

    (cos(theta)-|sin(theta)|)/2
      =sqrt(2-w^2)/2>sqrt(194)/30>23/50.                (9)

The final comparison is 194>(69/5)^2. Reflection gives the
corresponding statement on the other transverse side.

The complete physical angular-cap lemma in Section 1 of
FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md gives, for every C point,

    |Y|<(13/20)X.                                      (10)

Its premise X>59/60 follows from X>=1-epsilon. At the unchanged
channel application on C, X=1+h<=1+epsilon, so its actual
transverse coordinate has absolute value less than 793/1200.

Finally, C and the real S leaf M are distinct physical boundary
units. Their center directions must differ by strictly more than
2pi/9, by CENTERED_INNER_ARC.md. Thus any proposed M direction
whose angular distance from n_AD is at most pi/8 is impossible:
(6) would make their mutual angle less than

    pi/8+pi/12=5pi/24<2pi/9.                           (11)

We will also use an explicit three-angle version of this comparison
when the AB and AD axes differ. Every use concerns their actual
physical circle contact, not a circle-weight symmetry.

## 3. The complete critical radius

Let d=1, so epsilon=0. Section 1 makes both A normals west and
the actual channel gives C subset {x<=-1}. Equality in the sharp
contained-unit support bound forces

    C=[-2,-1] times [-1/2,1/2]=S(-e_x).                 (12)

This is a physical equality conclusion, not a fictitious leaf
equation at C.

The genuine root B contains O closed and lies in x<=0. If B did
not own the horizontal side axis, its maximum-x support would be
its unique vertex O. The actual AB point would be O. A's complete
parallel moment equation would also put its AD application at O,
so D contains O. The side transmitter D has x interval [-1,0].
An origin in the relative interior of its right side would occupy
the entire left half-neighborhood and overlap B. Thus D has an
origin vertex and occupies one of the two left quadrants. The
right-angle sector of B at O lies wholly in the left half-plane
and avoids that quadrant. It must be exactly the other left
quadrant, which makes B aligned after all. This is a contradiction.

Hence B=[-1,0] times [k,k+1], with -1<=k<=0. A genuine radial
S support of norm one on this rectangle can only point west, or
point vertically when B has the appropriate origin vertex. West
would give M=C in (12), impossible for distinct units. In the
vertical alternative reflect so B=[-1,0] times [0,1] and M points
north. Its contact with C in (12) has positive vertical length,
so the actual BC normal is west. The actual BA normal is east.
Those two forces cannot balance its positive north leaf force.
This completes d=1 with every original AB/AD mean retained.

## 4. The precise compatible owner reduction in the nonparallel case

We now work at d>1. We record the physical selection extension
needed for (4); no selected force is subsequently changed.

At any genuine radial-leaf root with exactly two other positive
forces, let their distinct singleton applications be q,s, and
suppose each relevant free-contact vertex is noncollinear with
the actual radial leaf direction e. The full three-force and
origin-moment equations imply the necessary determinant identity

    D(n,m)=det(e,n)det(s,m)-det(e,m)det(q,n)=0.           (13)

For a free normal n, with m not parallel to e, this is

    det(W,n)=0,
    W=det(s,m)e-det(e,m)q !=0.                          (14)

Noncollinearity of q with e proves W!=0. The identity therefore
excludes only finitely many directions in that free normal's
open strict interval. If m is parallel to e, the force equation
would make n parallel as well, another finite-direction exclusion.
If both contacts are free, the parameters at q and s are
independent physical junction parameters; (14) proves the joint
polynomial is nonzero on their product interval.

Before extraction, include all such physically specified leaf
assignments, roots and pairs of distinct singleton contacts in
the finite physical prelist. As in
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md, Section 3,
these finite open dense exclusions are imposed simultaneously
inside the existing strict, nonradial and matched-junction normal
domain. Opposite pairs at one junction share only that junction's
parameter, and do not identify the parameters at q!=s. The
argument needs no boundary or degree condition at the two other
neighbors. The boundary premise in that older source was used
only to establish the present explicit noncollinearity condition.
No mean is selected. Uncrossing retains surviving point normals
and adds only shared-side forces; conic thinning only deletes
atoms. Thus this compatible necessary certificate retains the
stated exclusion at every surviving true three-force star.

Apply it to (4). The AB and AD applications are the distinct
left A vertices at heights a and -b, both nonzero. If AB were
vertex/vertex its actual normal would be free: it is nonaxis at
A, and the existing strict point convention excludes an axis
endpoint at B. Equation (13) is nontrivial, with coefficient
proportional to a sin(psi) !=0. Hence AB must be side-owned by
B. The actual AD normal already is a D side axis because D is
the real side transmitter. No boundary status has been assigned
to B or D to reach this conclusion.

## 5. The entire nonparallel case

Use B's actual owned AB axis as the positive x direction toward
A, and its counterclockwise perpendicular as y. Put

    delta=phi+psi,
    kappa=epsilon cos(phi)-a sin(phi),
    t=epsilon sin(phi)+a cos(phi).

The real AB point is (kappa,t), and B owns the x axis, so

    B=[kappa-1,kappa] times [k,k+1].                    (15)

Because B has its actual epsilon-near point, its right support
satisfies -epsilon<=kappa<=epsilon. The real C channel application
and the actual outward normal of C toward D are

    P_D=(kappa+sin(phi)-cos(delta),
         t-cos(phi)-sin(delta)),
    v=(cos(delta),sin(delta)).                          (16)

The real C lies on v.z<=v.P_D. Formula (16) uses the actual
one-unit channel reserve and no new mean.

If M's radial support is on B's far left side or either far left
vertex, its direction g has

    -g_x >= (1-epsilon)/d>59/61>cos(pi/12).              (17)

An own west leaf also has this angular bound. The last comparison
follows from sqrt(3)<26/15, which makes cos^2(pi/12)<14/15,
and 15*59^2>14*61^2. C's center is within pi/12 of the channel
direction, that direction is at angle delta<pi/18 from west,
and (17) puts M within pi/12 of west. Their mutual angle would
be less than pi/12+pi/18+pi/12=2pi/9. This contradicts their
physical boundary separation.

A right own-axis leaf has support at most epsilon<d and is
impossible. The remaining actual radial supports in (15) are a
north or south own-axis support, or a near-right vertex. A near-
right vertex can expose its radial normal only if kappa>=0.
Its vertical magnitude is sqrt(d^2-kappa^2)>1. The lower-facing
possibilities would put all of B strictly below y=0, whereas
t>0 in (16). Thus only the upper-facing possibilities remain:

    0<=kappa<=epsilon,
    0<k<=epsilon,
    g_y>0,       0<=g_x/g_y<epsilon.                    (18)

For the vertex case k=sqrt(d^2-kappa^2)-1 and g_x=kappa/d;
for the north side case k=epsilon and g_x=0. These are all
original owner endpoints, not an assumption of an aligned leaf
relative to B.

We need two useful strict bounds. First, the actual channel port
in the original A frame has transverse coordinate
-epsilon sin(psi)-b cos(psi). Equation (10) gives

    b cos(psi)<793/1200.

Since sin(psi)<=4epsilon<1/15, cos(psi)>199/200. Therefore

    b<793/1194<2/3,       a>1/3,
    t>199/600.                                         (19)

Second, write T=tan(phi)+tan(psi). Equations (5) and kappa>=0
give a^2 T<=epsilon. The original AD support bound gives

    b^2 T<=epsilon(1+sec(psi))
             <(201/100)epsilon.

Since sqrt(201/100)<71/50, adding the positive square roots yields

    T<(121/50)^2 epsilon<14641/150000<1/10,
    sin(delta)<1/10,       cos(delta)>99/100.             (20)

Keep the actual B force magnitudes mu>0 toward A and alpha>0
toward its genuine M. Its full third force is

    -(mu e_x+alpha g)

toward C. Both components are strictly negative by (18), so its
actual B application is exactly the lower-left corner

    Q=(kappa-1,k).                                      (21)

B's full origin torque gives the exact slope of the opposite
force on C:

    slope(mu e_x+alpha g)
       =(t-k)/(1-kappa+t g_x/g_y).                      (22)

Here 0<t<d<61/60. Equations (18),(19) imply

    3/10 < 1134/3661
            < slope(mu e_x+alpha g) <61/59<2.           (23)

Indeed t-k>63/200 and the denominator is less than
1+(61/60)(1/60)=3661/3600. The upper bound uses the positive
denominator 1-kappa>=1-epsilon.

Choose C's own outward axis nearest v in (16). Its angle omega
relative to B's x axis is delta+theta, with theta as in (8).
From (8),(20),

    |sin(omega)|<1/10+1/14=6/35,
    cos(omega)>(99/100)(13/14)-(1/10)(1/14)=1277/1400,
    |tan(omega)|<240/1277<1/5.                          (24)

The true force direction in (23) lies strictly above this own
axis and strictly below its adjacent upper axis. For a negative
omega that upper-axis slope exceeds five, while (23) is below
two; a nonnegative omega makes the conclusion immediate. Thus
the actual point Q is C's upper corner in that owned frame.
There is no owner or mean equality left at these strict angles.

Its transverse coordinate relative to v is

    Y_Q=(1-kappa)sin(delta)+k cos(delta)<7/60.            (25)

Equations (9),(25) force

    Y_C<7/60-23/50=-103/300<-1/3,

contradicting the exact cap (6). This completes the entire
nonparallel A case.

## 6. The parallel case: full initial cover at the genuine B root

It remains that both A normals are west. Keep their original
heights t,u and magnitudes mu,nu>0:

    p_AB=(epsilon,t),       p_AD=(epsilon,u),
    mu t+nu u=0,
    C subset {x<=epsilon-1},
    P_D=(epsilon-1,u) in C.                             (26)

In this frame (6) reads

    (c_C)_x<=epsilon-3/2,
    |(c_C)_y|<1/3,
    |u|<(13/20)(1-epsilon)<13/20.                       (27)

B's maximum x coordinate is epsilon. We first handle B owning
that axis. It then has rectangle [epsilon-1,epsilon] times
[k,k+1]. Every far-left genuine S direction has angle below
pi/12 from west, as in (17), and contradicts (6) and physical
boundary separation. Own east or west leaf supports cannot
equal d. The remaining north/south or near-right-vertex leaf
forms, after reflection, have

    0<k<=epsilon,
    g_y>0,       g_x>=0,
    t>=k>0,       u<0.                                 (28)

The real BC force is strictly southwest, so its B port is
Q=(epsilon-1,k). Q and P_D are distinct points of C's maximum-x
support, forcing C to own this side axis. If Q is in a relative
interior of that side, its actual normal toward B is horizontal,
contradicting B's nonzero vertical leaf force. Otherwise Q is
its upper endpoint, since P_D is below it. The actual center of
C then has y coordinate k-1/2< -29/60, contradicting (27).
Thus B cannot own the x axis in the remaining parallel case.

Write its full tilted frame, with rightmost vertex equal to the
actual AB application, as

    P=(epsilon,t),
    B=P+[0,1]f+[0,1]j,
    f=(-c,-s),       j=(-s,c),
    c,s>0,       c^2+s^2=1.                             (29)

The actual point P belongs to A, so -1<=t<=1. A genuine S leaf
at P would require |t|=sqrt(1+2epsilon)>1 and is impossible.
A leaf at the opposite vertex has -g_x>59/61 and is excluded
by the same boundary-center comparison. The adjacent side
normals -f,-j have radial support at most sqrt(1+epsilon^2)<d,
and are impossible too. Reflect vertically, exchanging c,s
when needed, so the surviving leaf has g_y>0. The complete
remaining cover consists of just two actual forms:

    V: p_M=P+j,       g=(epsilon-s,t+c)/d;
    S: g=j,          p_M=d j on the far j side.          (30)

For V, the radius and the genuine outward support condition give

    t^2+2ct=2epsilon(1+s),
    t>0,       t<epsilon(1+s)/c.                        (31)

To check the sign rather than discard the other quadratic root:
that root has t<-2c. If s>=epsilon/2 it violates the required
support inequality epsilon c+t s>=0; if s<epsilon/2 then c>1/2
and it violates t>=-1. Thus (31) is the entire vertex domain.
For S the exact side support gives

    t=epsilon(1+s)/c>0.                                (32)

If c<1/4, then s>sqrt(15)/4>29/30. In either form (30),

    -g_x>57/61>14/15>cos(pi/8).

This contradicts (11). The exact first radical comparison is
15/16>(29/30)^2; the last follows from sqrt(2)<57/40 in
cos^2(pi/8)=(2+sqrt(2))/4. Hence

    c>=1/4,
    0<t<2/15,
    u<0.                                               (33)

The B center in (29) has x coordinate epsilon-(c+s)/2 and y
coordinate t+(c-s)/2. Thus |(c_B)_y|<2/3. Its x coordinate
exceeds C's by more than 3/4. If the real normal from C to B
had nonpositive x component, its projection of c_B-c_C would
be strictly less than one, by (27),(33). But the sum of the two
unit-square directional halfwidths is at least one and is a lower
bound for that actual center projection. This is impossible.
The C-to-B normal therefore has positive x component. Its y
component is positive by B's full force equation and g_y>0.

Consequently the B-to-C force is strictly southwest. Its dot
product with f is strictly positive in both forms (30), so its
actual B support has the full possible form

    Q=P+f+lambda j,       0<=lambda<=1.                 (34)

The endpoint lambda=0 has x=epsilon-c>epsilon-1 and cannot
belong to C. The remaining side and far-vertex alternatives are
handled separately with their unchanged actual equations below.

## 7. Parallel A with a genuine vertex S root B

Keep form V and put

    E=epsilon c+t s>0,
    F=1+t c-epsilon s>0.

Let alpha>0 be the actual leaf magnitude at B, and retain mu>0
for its real BA force in (26). Moment about P, including the
actual radial leaf at P+j, gives

    mu(-s+lambda c)+(alpha/d)[F-(1-lambda)E]=0.           (35)

If (34) is a genuine side support, its normal has zero j component,
so alpha/mu=s d/F. Substitution into (35) gives

    lambda=s E/(c+t)<s/(1+c).                           (36)

The strict inequality follows from

    E(1+c)<c+t,
    epsilon(1+c)+t<1/30+2/15=1/6<1.

But reaching C's half-plane in (26) requires c+lambda s>=1,
or lambda>=(1-c)/s=s/(1+c). This contradicts (36), including
both original endpoints of the side mean.

Thus Q is the far vertex P+f+j. Equation (35) yields

    z=s-c>0,       w=c+s>6/5,
    alpha/mu=z d/F,
    Q=(epsilon-w,t-z).                                 (37)

The real C-to-B force has positive x,y components whose ratio is

    X/Y=c(w+t-epsilon)/[z(t+c)].                        (38)

Since Q is its supporting point on C, whereas P_D in (26) is
also an actual point of C, (38) gives

    u<=t-z-(X/Y)(w-1)
      <2/15-K(w),
    K(w)=[185-61w-32w^2]/[92 sqrt(2-w^2)].              (39)

Here c/(c+t)>15/23, epsilon<1/60 and z=sqrt(2-w^2) were used.
The condition w>6/5 follows from c>=1/4 and s>c; its minimum
is at c=1/4, where s=sqrt(15)/4>19/20.

For completeness, the derivative of K has the sign of

    32w^3+57w-122,

which is increasing and already equals 212/125>0 at w=6/5.
Thus on 6/5<w<sqrt(2),

    K(w)>K(6/5)=1643/(460 sqrt(14))
          >1643/1725>9/10,                             (40)

using sqrt(14)<15/4. Equations (39),(40) make u<-23/30,
contradicting |u|<13/20 in (27). This covers the entire V form.

## 8. Parallel A with a genuine side S root B

Keep form S, so g=j and (32) holds. In the own frame (29) the
real leaf application is P+t f+j; indeed
epsilon c+t s=t by (32). The complete moment about P is now

    mu(-s+lambda c)+alpha(1-t)=0.                       (41)

At a side support in (34), alpha=mu s, so

    lambda=s t/c.

Reaching C would require t>=c/(1+c)>=1/5, contradicting t<2/15.
This also retains every actual side-mean endpoint.

At the far vertex, (41) instead gives z=s-c>0 and

    alpha/mu=z/(1-t),
    X/Y=(w-t/c)/z,
    Q=(epsilon-w,t-z).                                 (42)

Using t/c<8/15, the same original supporting inequality between
Q and P_D gives

    u<2/15-K_1(w),
    K_1(w)=(38-23w)/(15 sqrt(2-w^2)).                   (43)

Its numerator is positive on w<sqrt(2). The exact identity

    (38-23w)^2-193(2-w^2)=2(19w-23)^2

proves K_1(w)>=sqrt(193)/15>9/10. Thus (43) again makes
u<-23/30, contrary to (27). The entire S form is excluded.

## 9. Exact original-family conclusion

The original low radius is excluded by the real channel support,
the critical radius by its exact support equality and full B3
equation, and the strict-high radius by the complete nonparallel
and parallel covers above. Every original S-root pose, leaf-side
mean, contact owner, private circle mask and individual zero
circle weight is included. The true C and D equations are never
substituted for one another, and the genuine B3 is never reduced
to a channel or made physically boundary.

This closes exactly M6.B4L2.C4.ADJACENT.LC.SS, subject to the
stated full-source reviews. The reversed mixed LC assignment is
handled separately, and no double-load or whole C1.4.b2 conclusion
is asserted by this source alone. Its Sections 1--2 and the
nonparallel compatible owner selection have their explicitly
stated local scopes for those separate exact callers.

No numerical pose, post-extraction normal change, altered
application, Lean compilation, CI, remote mutation or shared-ledger
edit is used.
