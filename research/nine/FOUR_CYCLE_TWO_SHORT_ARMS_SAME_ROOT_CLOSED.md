# A four-cycle cannot carry two short arms at the same root

Date: October 27, 2026.

**Status: complete hand original-attachment theorem, submitted for full
root and separate independent review.** No shared coarse or fine label
is changed. The two auxiliary geometric lemmas below are proved in
full rather than imported with a stronger numerical threshold.

Keep all nine original physical unit squares, the common compatible
selected radius/Phi-minimizer pose and minimum-positive-original-
scalar-atom certificate, and the window

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),       1/2<r<2/3.

The original positive component has the eight bodies and edges

    H--B--C--D--H,
    H--X--L,
    H--Y--M.

Their true positive degrees are H4, B2, C2, D2, X2, Y2, L1, M1.
The original ninth physical square stays arbitrary and present.
Retain every actual application mean, fixed normal, physical circle
mask, individual zero corner weight and extra zero-stress contact.

**Theorem.** This entire C4 attachment is impossible, for every
original leaf type, actual arm width, private load mask and radius.

This is the same-root two-short-arm C4 attachment in C1.4.b4.
It does not assign degree two to a body with an additional chord,
and it is not by itself a whole-coarse-cell closure.

We use the elementary physical bounds

    |c_T|<=d+1/2<91/60,
    |P|>=r for every point P of a physical boundary unit T.       (1)

The first follows from the farthest actual corner of a contained
unit, as in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1.
The second follows from a real circle corner and the unit's diameter
sqrt(2). Neither requires a positive weight at every circle corner.

## 1. Both actual arms must be S/side

The real roots X,Y of the genuine leaves L,M are physically clear,
and their true degree-two equations make them genuine unloaded
normal transmitters. If e is one arm's real radial leaf direction,
its unchanged applications are

    p_XL=r_L e,       p_HX=(r_L-w)e,
    r_L=r for D, r_L=d for S,       w in {1,sqrt(2)},
    H subset {z:e.z<=r_L-w}.                                    (2)

For a D leaf the actual root contains O openly. In the side-normal
case its longitudinal interval [r-1,r] straddles zero. Its transverse
zero cannot be an endpoint: that would make the positive contact a
singleton vertex/vertex contact with a forbidden own-axis normal at
the root. In the diagonal case both own coordinates of the leaf
port are r/sqrt(2) in (0,1), again placing O in the root's interior.
For an S/diagonal arm the same calculation has d/sqrt(2) in (0,1),
so O also belongs to the actual root openly. These are the original
radial geometries; no force or contact is changed.

Suppose one arm has such an origin-interior root. If the other is
also D or S/diagonal, the roots overlap immediately. If the other
is S/side with d<=1, its actual radial interval [d-1,d] and its
unchanged transverse interval containing zero put O in that root
closed, also an overlap. In the remaining S/side case d>1, its
actual application on H is epsilon e. From any actual supporting
point P of a unit square with outward unit normal n, the whole
segment [P-n,P] belongs to that square: in its own axes each
nonzero component of n points out through the corresponding
supporting side and has absolute value at most one. Thus

    [epsilon-1,epsilon]e subset H,

and O belongs to H closed. This overlaps the distinct origin-interior
arm root. All these alternatives are impossible. Both original arms
are consequently S/side, with distinct real leaf directions e_1,e_2.
Equal directions would give identical physical radial S leaves.

At d<1 both actual side roots X,Y contain O closed. Neither can
contain it openly, so each has O in a relative side interior. Their
occupied local half-planes must be opposite. Their actual leaf axes
are tangent to that common line, hence e_2=+/-e_1. Equal directions
were excluded; opposite directions in (2) give

    h_H(e_1)=d-1,       h_H(-e_1)=d-1.

Their sum would be the positive width of H in direction e_1, but
it is 2(d-1)<0. This excludes the whole strict-low domain.

## 2. The critical and high actual root charts

At d=1 both real arm applications on H are O. Their directions
are distinct, so O cannot be in a relative side interior of H,
which has only one outward unit normal there. It is a vertex.
Choose its actual own frame so that

    H=[-1,0]^2.

The two arm normals lie in the closed northeast normal cone and
are distinct. Their positive weighted sum W has both coordinates
strictly positive: a zero coordinate would force both unit normals
to be the same cone boundary ray. The actual point O makes H
physically circle-clear by (1). Its full, unchanged H4 equation is

    N+W=0,       W_x,W_y>0,                              (3)

where N is the sum of the real H-to-B and H-to-D forces.

For d>1 put epsilon=d-1. The real applications are epsilon e_i.
If e_1 is not an own side axis of H, choose its positive own
coordinates e_1=(a,b), a,b>0. Its actual exposed vertex is
(epsilon a,epsilon b). The two adjacent outward own-side heights
are strictly between zero and epsilon, while the other two are
greater than 1-epsilon>epsilon. Thus no own-axis normal can have
the required second radial support height epsilon. Another strict
vertex cannot have norm epsilon either: distinct vertices are at
least one apart while the two proposed points are at most 2epsilon
apart; the same vertex would make the directions equal. This is
the complete vertex/side feature cover. Both e_i must therefore
be own side axes. They cannot be opposite, since the resulting
width would be 2epsilon<1, and cannot be equal. They are adjacent.

Rotate and reflect the actual own frame, without changing O, to get

    e_1=e_x,       e_2=e_y,
    H=[epsilon-1,epsilon]^2,
    N=-alpha e_x-beta e_y,       alpha,beta>0.            (4)

H is physically clear because its actual arm points have norm
epsilon<r. Equation (4) is its full four-force equation; both real
arm forces are present. In both (3) and (4), O belongs to H closed,
the two coordinates of N are strictly negative, and R>2.

## 3. The complete original private-load cover

The following cover concerns the true B2,C2,D2 bodies, not a
subgraph obtained by deleting any force at H.

If all three are unloaded, summing their three actual force
equations gives N=0, contradicting (3) or (4).

If only B is loaded, C,D are an unchanged two-transmitter chain
from H to B. Its positive longitudinal reserve is the sum of
their actual widths, at least two. Its two endpoint supports
strictly separate H and B, contradicting their real positive
contact HB. Reflection covers a sole D load.

If only C is loaded, B,D are the two true unloaded channels with
the same endpoints H,C. Sections 1--2 of
TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md prove that their real
widths are one, their directions agree and H owns their common
side axis. Those local conclusions impose no restrictions on the
other forces at H. Their sum N must be along that own side axis,
contradicting its two strictly negative own-frame components.

If precisely B,C are loaded, the true D2 is a normal channel from
H to C with reserve at least one. The real boundary unit B touches
both endpoints, and H meets D_epsilon. The complete physical
near-endpoint/channel/boundary-detour theorem in
FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md, Theorem 4.1, excludes this
configuration. Its far-endpoint degree and force aggregate are
unrestricted; R>2 was already obtained in Section 2. Reflection
covers precisely C,D loaded.

Only the masks with B,D loaded remain; C may be unloaded or loaded.
We keep this distinction in the next exact local input.

When C is loaded, Sections 1--3 of
ROOTED_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE.md give the following
facts from the three true private equations: opposite parallel
root normals are impossible; a nonparallel root pair has actual
concurrence

    q=-tN,       t>0.                                   (5)

When C is unloaded, Sections 2--5.2 of
ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md give
the same facts, using the actual width-one B--C--D channel and
the complete loaded B2/D2 equations. Only that local endpoint,
channel and negative-concurrence proof is used. Its separate
forbidden-ray premise and subsequent one-improper conclusion are
not imported.

In a same-direction parallel root pair, the true endpoint
concurrences and the zero root-pair moment put the actual ports
at strictly opposite transverse heights. This is the local
straddling step before the forbidden-ray invocation in Section 4
of the first source or Section 5.1 of the second. The ports are
distinct, so their common support is an actual H side. Their
direction is N/|N|, again impossible by (3),(4). Thus the root
pair is genuinely nonparallel and (5) holds.

## 4. Every actual root port is strictly proper

Write the original root applications and normals as

    P_i=q+l_i n_i,       |n_i|=1,

where the coefficients l_i initially have arbitrary signs. Both
ports belong to the real physical boundary neighbors B,D, so
|P_i|>=r by (1).

At the critical radius, (3),(5) put both coordinates of q strictly
positive, and its unique closest point in H=[-1,0]^2 is O. At
high radius, (4),(5) also put both coordinates of q strictly
positive. If q lies outside H, its unique closest point in H is

    (min(q_x,epsilon),min(q_y,epsilon)),

whose norm is at most sqrt(2)epsilon<r. If q lies inside H, its
own norm has the same bound.

If some l_i<0, then q lies on the strict outward normal ray from
P_i. The supporting inequality gives, for every x in H,

    |P_i+lambda n_i-x|^2
      >=lambda^2+|P_i-x|^2,       lambda>0.

Consequently P_i would be the unique closest point of H to q.
This is impossible when q belongs to H, and otherwise contradicts
the preceding small-norm closest point and |P_i|>=r. A zero l_i
would either put q in H at a point of norm below r or put a point
of H outside H. Hence every actual port is strictly proper:

    P_i=q+l_i n_i,       l_i>0.                          (6)

At d=1, every coordinate of P_i-q is strictly negative. Thus
both actual normals are strictly southwest and expose the same
far vertex (-1,-1) of H. Their two nonparallel force lines would
intersect at that vertex, not at the northeast q. This is a
contradiction. The critical domain is complete.

For the remaining strict-high domain reflect both coordinates
in (4)--(6). Write

    K=[-epsilon,A]^2,       A=1-epsilon>59/60,
    q=(-s_1,-s_2),       s_1,s_2>0,
    P_i=q+l_i n_i,       l_i>0,
    sum_i mu_i n_i=(alpha,beta),       mu_i,alpha,beta>0.  (7)

K is the unchanged physical H in this reflected own frame.

## 5. No contained unit can touch the far corner of K

We prove the geometric fact at the exact strength required in (7).
Let P=(A,A), A>=59/60. A unit T with disjoint open interior from
K and containing P has

    |c_T|^2>=2A^2+1/2.                                  (8)

P cannot belong to int T, since int K approaches it. If P is a
vertex of T, its inward right-angle sector avoids the open
southwest quadrant occupied locally by K. Its two inward unit
axes can therefore be written

    u=(cos(theta),sin(theta)),
    v=(-sin(theta),cos(theta)),
    -pi/2<=theta<=pi/2.

This interval is the full sector cover, including tangencies.
The actual center is P+(u+v)/2, so

    |c_T|^2=2A^2+1/2+2A cos(theta)>=2A^2+1/2.

If P is in a relative side interior of T, its inward unit normal
must have two nonnegative coordinates: otherwise its local open
half-plane would meet the southwest quadrant. Exchange coordinates
to write that normal as (c,s), c>=s>=0, c^2+s^2=1. The actual
center is

    c_T=P+(c,s)/2+tau(-s,c),       |tau|<=1/2.

Its normal coordinate is A(c+s)+1/2 and its tangential absolute
coordinate is at least max(A(c-s)-1/2,0). If A(c-s)>=1/2,

    |c_T|^2 >= [A(c+s)+1/2]^2+[A(c-s)-1/2]^2
             =2A^2+2As+1/2>=2A^2+1/2.

If A(c-s)<1/2, then A(c+s)>sqrt(2A^2-1/4), giving

    |c_T|^2>[sqrt(2A^2-1/4)+1/2]^2
             =2A^2+sqrt(2A^2-1/4)>2A^2+1/2.

This proves (8) for every support owner and endpoint. But

    2(59/60)^2+1/2-(91/60)^2=481/3600>0,

contradicting the actual center bound (1). Therefore no other
original contained unit can contain the far corner P of K.
This statement needs no force, load or normal selection at T.

## 6. The proper ports force the opposite square around two far faces

Suppose first that s_1>epsilon in (7). Every point P of K then
has P_x-q_x>0, so by (6) both actual root normals have positive
x component. If either had positive y component, its actual
support would be the forbidden far corner (A,A). Thus both
y components would be nonpositive, contradicting the positive
y component of their full sum in (7). The reflected argument
excludes s_2>epsilon. Hence

    0<s_1,s_2<=epsilon.                                 (9)

The near-near vertex (-epsilon,-epsilon) has norm below r and
cannot be a boundary-neighbor port. At a negative own-axis near
face, strict properness fixes the transverse coordinate at the
corresponding coordinate of q, so that port also has norm at
most sqrt(2)epsilon<r. The far corner is excluded by Section 5.
The full remaining feature cover consists of exactly two groups:

* the right far face, with actual own-axis mean (A,-s_2), or
  its lower endpoint (A,-epsilon), with n_x>0,n_y<=0;
* the top far face, with actual own-axis mean (-s_1,A), or
  its left endpoint (-epsilon,A), with n_y>0,n_x<=0.

These means follow from (6); they have not been chosen or replaced.
Since the actual weighted sum has both coordinates positive,
one actual neighbor is in each group. Name B the right one and
D the top one.

For an own-axis B port, every physical B point has x>=A. For
its mixed endpoint the actual normal in (6) is proportional to
(A+s_1,s_2-epsilon), so its exact outward half-plane gives

    x>=A+eta(y+epsilon),
    eta=(epsilon-s_2)/(A+s_1),       0<=eta<epsilon/A.

Every contained point has y>=-R. Since R<21/10, in both cases
every actual B point satisfies

    x>A-epsilon R/A
       >59/60-(21/10)/59
        =671/708>189/200.                               (10)

The exact last reserve is 97/35400. The reflected calculation
gives y>189/200 for every actual D point. The original C touches
both B and D, whence

    max_C x>189/200,       max_C y>189/200.               (11)

Meanwhile K contains [0,59/60]^2. We finish with a full elementary
separating-axis calculation at this exact numerical threshold.

## 7. A unit cannot pass around that smaller square within the center disk

**Geometric lemma.** No unit square T with |c_T|<91/60, disjoint
open interior from [0,59/60]^2, can satisfy both inequalities in
(11). This strengthens the threshold 24/25 in Section 4 of
FOUR_CYCLE_SIDE_ARM_TILTED_ROOT_EXCLUSION.md; the complete altered
constants and every separating-axis case are checked here.

Put A_0=59/60, t=189/200, M_0=91/60. The common coordinate
width w of T obeys 1<=w<=sqrt(2), and its center coordinates obey

    c_x,c_y>t-w/2>7/30.                                 (12)

Indeed sqrt(2)<17/12 gives t-17/24=71/300>7/30.
The separating-axis theorem for rectangles supplies an own axis
of one of the two squares. All possible orientations follow.

For a coordinate axis, the negative side is ruled out by the
positive maxima in (11). If T is to the right, then

    c_x>=A_0+w/2,       c_y>t-w/2.

The lower squared sum is increasing for w>=1, since A_0>t.
Consequently

    |c_T|^2>(A_0+1/2)^2+(t-1/2)^2,
    (89/60)^2+(89/200)^2-M_0^2=3921/40000>0.

The upper-side case is symmetric.

Otherwise an outward own unit axis n of T separates it from the
smaller square, giving

    c_T.n>=A_0(n_x^++n_y^+)+1/2.                        (13)

Two nonpositive components are impossible by (12). For a mixed
axis write n=(a,-b), a>0,b>=0; exchange coordinates for the other
mixed case. Now w=a+b and

    c_x>=A_0+1/(2a)+(b/a)c_y
        >=A_0+1/2+(b/a)(7/30).

Since c_x<M_0, this gives b/a<1/7, hence w<8/7. Therefore

    c_y>t-4/7=523/1400,       c_x>=89/60,
    (89/60)^2+(523/1400)^2-M_0^2=77529/1960000>0.

Finally take n=(a,b) with a>=b>=0, after exchanging axes. Equation
(13) and the center bound give

    w=a+b<61/59,
    ab=(w^2-1)/2<120/3481.

As a>=1/sqrt(2)>7/10, this implies b<1200/24367<1/20 and
a>99/100. Equation (12) yields

    c_y>t-61/118=5051/11800>107/250;

the exact final reserve is 3/59000. Using c_y<M_0 in (13),

    c_x>=A_0+1/(2a)+(b/a)(A_0-c_y)
        >89/60-(5/99)(8/15)
         =8651/5940>131/90.

Thus

    |c_T|^2>(131/90)^2+(107/250)^2,
    (131/90)^2+(107/250)^2-M_0^2=31351/20250000>0.

All separating axes, including equality and own-axis endpoints,
are excluded. This proves the geometric lemma. It uses only the
actual square and center bound, with no force or circle-load
assumption on T.

Apply it to the unchanged C in (11), which is disjoint from the
smaller square inside K and satisfies (1). This is the final
contradiction in both remaining private-load masks.

## 8. Exact conclusion and reusable local outputs

Section 1 covers all genuine S/D types and real side/diagonal
arm widths, including the entire strict-low radius range. Sections
2--4 retain the true H4 equation, exhaust all eight private-load
masks up to cycle reflection, and close the critical radius. The
high case is excluded by Sections 5--7 for the actual unchanged
middle unit C at either of its original loads. Every original
mask, zero individual weight, side mean and ninth square remains.
The complete specified C1.4.b4 C4 attachment is therefore closed,
subject to the stated full-source reviews.

The two physical lemmas in Sections 5 and 7 may be used at their
explicit graph-free scopes. The root conclusions in Sections 2--4
require the displayed actual arm equations and true private
degrees; no chord, additional root force or loaded channel may
be discarded to manufacture those hypotheses.

No numerical pose, normal reselection, coefficient certificate,
Lean compilation, CI, remote action or shared-ledger edit is used.
