# A genuine D-leaf root leaves room for at most one other unit near the origin

Date: October 27, 2026.

**Status: accepted after full root and separate independent review.** See
`REVIEW_D_LEAF_ROOT_TWO_NEAR_ORIGIN_UNITS_ROOT_2026_10_27.md` and
`REVIEW_D_LEAF_ROOT_TWO_NEAR_ORIGIN_UNITS_ROOTED_BLOCKS_2026_10_27.md`.
The root may have arbitrary
true positive degree and every original additional force. This also
excludes every D-containing type whenever three distinct genuine
leaf roots coexist, including the H5 hub-leaf layout of C2.33.b3.

Keep all nine original physical unit squares, their disjoint open
interiors, the same compatible selected certificate and radius
window

    79/40<=R<=sqrt(1105)/16.

Suppose a genuine D leaf E has actual root G. In the strict
high-radius domain put

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,
    r=R-sqrt(2),       s=1-r.

Suppose two distinct actual units K_1,K_2, both different from G,
meet the closed disk D_epsilon. No force, degree or load assumption
is made on those two units.

**Theorem.** This physical situation is impossible.

## 1. The actual shallow D-root chart contains a full semicircle

The complete genuine D-leaf/root classification gives, after
rotating the actual leaf east,

    G=[-s,r] times [a-1,a],       0<a<1,
    p_GE=(r,0).

The actual leaf is the unit diamond with inward vertex (r,0):

    E={ (x,y): |x-(r+1/sqrt(2))|+|y|<=1/sqrt(2) }.

This root chart permits arbitrary extra forces at G. In particular
O is in int G. Throughout the present d>1 domain,

    129/200<r<2/3,       s>1/3.                       (1)

For the first bound use R>sqrt(17)/2>103/50 and
sqrt(2)<283/200. For the second, the exact upper radius
gives R<52/25, while sqrt(2)>106/75, so r<2/3.

Choose actual x_i in K_i with |x_i|<=epsilon. Each is outside
int G: any point of a distinct closed square in int G would
force interior overlap, since its own interior approaches it.
Since both horizontal G margins r,s exceed epsilon, one
vertical margin is at most epsilon. Reflect vertically so

    0<a<=epsilon.                                    (2)

Set rho=4/15. The entire closed lower semicircle of radius
rho is contained in G: its horizontal coordinates lie strictly
between -s and r by (1), its lowest height exceeds a-1 by
(2), and all its heights are at most zero<a.

Neither K_i can be E, since every point of the actual leaf has
x>=r>epsilon. We will find a point strictly inside both E and
one of these other actual units.

## 2. The complete small-circle and separating-axis observation

We use exactly the force-free geometric argument of Sections
2--3 of
`INTACT_PETAL_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md`.
Its needed input is only an original unit containing the
closed eastern semicircle of radius rho and two other
interior-disjoint units meeting D_epsilon. The intact-petal
geometry is not used in those sections. Here is the complete
observation, with its actual support bounds.

At each real small point choose the two own-axis directions
toward its square's center. Each has at least a half-unit
of room, so the physical square contains that quarter-square.
Put beta=arcsin(1/16). The closed radius-rho arc from
phi+beta to phi+pi/2-beta lies in the square's open interior:
both projections exceed epsilon because
rho sin(beta)=1/60>epsilon, and both are less than
rho+epsilon<1/2. The two arcs are disjoint and lie in the
open western semicircle outside the occupied original unit.

Order them from north to south. Their original own-axis
directions satisfy

    pi/2-beta<=phi_+<=pi/2+3beta,
    pi-3beta<=phi_-<=pi+beta,
    |phi_++pi/2-phi_-|<=2beta.

The two selected west axes thus differ by at most 2beta.
Neither of these horizontal original axes can separate the
squares: each unit's actual half-unit west segment makes
its projection interval contain [-1/4,-1/8] in its interior.
The exact reserve uses cos(2beta)=127/128 and
epsilon<1/60. The square separating-axis theorem therefore
supplies one of the two actual upward axes, with the lower
square below the upper square. The real small point of the
upper square bounds the lower square's support on that
actual separating axis by epsilon.

For the lower square K, let its actual right/up own axes be

    R=(cos(theta),sin(theta)),
    N=(-sin(theta),cos(theta)),
    -3beta<=theta<=beta.

Write its two true coordinate intervals as
[h_R-1,h_R] and [h_N-1,h_N]. Its original small point and
its selected west half-segment give

    -epsilon<=h_R<=1/2+epsilon,
    h_N>=-epsilon.

The actual upward separating axis may belong to the other
unit. Write it A N+B R, with A>=127/128 and |B|<1/8.
The actual point on K's upper own face with the small
point's R coordinate gives

    h_N<=(144/127)epsilon<1/50.                       (3)

This completes the observation, including every arc endpoint,
square contact limit and either square's separating axis.
The exact angular bounds also give

    cos(theta)>49/50,       |sin(theta)|<3/16.         (4)

All these are facts about the original physical square axes;
no contact normal or actual mean is selected or altered.

## 3. Reflecting that observation supplies an actual northeast square

Apply the preceding observation after the orthogonal reflection

    (x,y) -> (-y,-x).

It sends G's occupied lower semicircle to the eastern
semicircle. Reflect its selected lower square back. The
result is one of the original K_i, now denoted K, with
actual right/up axes e_R,e_U satisfying (4), possibly with
theta replaced by -theta. Its original own intervals are

    [l_R,l_R+1],       [l_U,l_U+1],

where (3) and the other support bounds give

    l_R<=epsilon,       l_R+1>49/50,
    l_U<=epsilon,       l_U+1>=1/2-epsilon>29/60.       (5)

Explicitly l_R=-h_N and l_U=-h_R. Thus no orientation
agreement between K_1 and K_2, or between K and G, has
been assumed. The reflection only translates the exact
original support inequalities into the useful quadrant.

## 4. A fixed interior point of the real D leaf also lies inside K

In the unchanged D-root coordinates define

    q=(r+1/4,1/5),       X=r+1/4.

Equation (1) gives

    179/200<X<11/12.

The point is strictly inside the actual D leaf E. Indeed
its horizontal advance from E's inward vertex is 1/4,
while its height is 1/5<1/4; equivalently its diamond
inequality has exact strict slack 1/20.

Use the actual axes e_R,e_U from Section 3. Equations
(4) and the last bounds give the following strict reserves:

    q.e_R > (179/200)(49/50)-(1/5)(3/16)
             =2099/2500>epsilon,
    q.e_R < 11/12+(1/5)(3/16)
             =229/240<49/50;

    q.e_U > (1/5)(49/50)-(11/12)(3/16)
             =193/8000>1/60>epsilon,
    q.e_U < 1/5+(11/12)(3/16)
             =119/320<29/60.                         (6)

Combining (5)--(6), both actual own coordinates of q are
strictly between the original side supports of K. Therefore
q belongs to int K. But q also belongs to int E, and K is
distinct from E. This contradicts the original disjoint
open interiors and proves the theorem.

## 5. Complete consequence for three distinct genuine leaf roots

Suppose the original packing has three distinct genuine
leaf roots and at least one carries a D leaf. That D root
contains O openly. For d<=1, every other genuine leaf
root contains O closed, giving immediate physical overlap.

For d>1, any other D root would again overlap at O. Every
remaining genuine S root contains its actual inward radial
point epsilon e, so the other two distinct physical roots
meet D_epsilon. Sections 1--4 exclude them. Consequently

    three distinct genuine leaf roots cannot coexist
    if at least one of their leaves is D.             (7)

This statement permits arbitrary actual degrees and further
forces at all three roots. In particular it closes the
entire D-containing type domain of triangles HAB,HCD with
genuine leaves at H,A,C, where H has true degree five.
It does not delete H's own leaf force or assert an opposite
pair equation there. Its all-S high-radius domain remains
separate.

All nine original physical units and all actual positive
forces, circle atoms, normals and means remain. After the
accepted genuine D-root chart, the argument is purely
physical semicircle order, separation on an original axis,
and a fixed strict interior point. No intact-petal premise,
numerical pose, new scalar certificate, normal reselection,
Lean compilation, CI or shared-ledger mutation is used.

