# A length-three arm and a direct leaf at distinct triangle roots are impossible

Date: October 26, 2026.

**Status: accepted complete whole-layout exclusion after full root review in REVIEW_LONG_ARM_DIRECT_LEAF_ROOT_2026_10_26.md and separate review in REVIEW_LONG_ARM_DIRECT_LEAF_TRIANGLE_ROOTED_BLOCKS_2026_10_26.md.** The potentially loaded long-arm root
retains its full actual circle force throughout. No original label is
changed by this source.

## 1. Full original graph and inherited geometry

Keep all nine original physical unit squares, with

    79/40<=R<=sqrt(1105)/16.

The positive component is the triangle A,B,C, a genuine three-edge
pendant path A--U--V--L, and a genuine direct leaf M at B. The internal
bodies U,V are genuinely unloaded of exact positive degree two. This is
the surviving selected-certificate scope after the previously proved
bridge splitting and outside-fork reductions. The two arbitrary
completion squares remain in place. A has its original two triangle
forces, its actual bridge force, and any original circle load. Nothing
is deleted from its equation.

Use `ROOTED_TRIANGLE_LENGTH_THREE_ARM_GEOMETRY.md`, with independent
review `REVIEW_LENGTH_THREE_ARM_GEOMETRY_GLOBAL_2026_10_26.md`. Its complete
width and leaf cover, and its whole physical P exclusion at the critical
radius, give

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,
    rho=1-epsilon=2-d,
    a=2-epsilon=3-d.                                      (1)

Rotate the actual long leaf direction east. Its original application
at A is p=(-rho,0), and its force on A is alpha e_x, alpha>0.
The actual long root and first internal body are

    A=[-a,-rho] times [b_-,b_+],
    b_-=t-1/2, b_+=t+1/2, |t|<1/8,
    U=[-rho,epsilon] times [u-1/2,u+1/2], |u|<=1/2.        (2)

In particular

    b_-<-3/8<0<3/8<b_+,
    O in U,
    a>119/60,
    |c_X|<=d+1/2<91/60                                   (3)

for every original unit center c_X. Every transverse slider and actual
side mean remains as given. If A has positive circle load it has the
unique physical corner identified in the long-arm source; the argument
below uses its full actual circle resultant G_A, with zero origin
moment, and never replaces it by the eastward bridge force.

The untouched triangle tip C is loaded. Otherwise its exact degree-two
equation would give opposite outward normals, putting A and B beyond
opposite support faces of C and preventing their required physical
contact. Write its original nonzero circle resultant as F_C, retaining
every physical corner and every individual zero weight.

The direct-leaf root B is physically circle-clear by the radial bridge
theorem. A genuine D leaf at B would put O in the open interior of B:
its radial inner vertex lies in a relative side interior of B, with
longitudinal coordinate r=R-sqrt(2) strictly between zero and one. That
would overlap U, which contains O. Thus M is S, with actual direction v,
original force beta v on B, beta>0, and actual support point

    p_M=d v in B.                                        (4)

The inward unit segment from d v belongs to B, including every tilted
or aligned support feature. Hence epsilon v belongs to B, so B meets
the closed disk D_epsilon. This uses the genuine direct leaf and does
not assign its formula to the long root A.

## 2. Two central bodies occupy opposite vertical sides

Every point of a unit square is within sqrt(2)/2 of its center. Since
U contains O and B meets D_epsilon, using sqrt(2)/2<17/24 gives

    |c_U|<29/40,       |c_B|<epsilon+17/24<29/40.          (5)

Also c_Ux=epsilon-1/2<-11/40. The physical AB contact lies in
x<=-rho=epsilon-1, so

    c_Bx<=epsilon-1+sqrt(2)/2<-11/40.                     (6)

Consequently both horizontal center coordinates belong to
(-29/40,-11/40), giving

    |c_By-c_Uy|^2
       >=1-|c_Bx-c_Ux|^2
       >1-(9/20)^2
       > (7/8)^2.                                       (7)

Here center distance is at least one because the open radius-1/2
incircles of distinct physical unit squares are disjoint. Since
|c_Uy|<=1/2, equation (7) implies either c_By>3/8 or c_By<-3/8.
Reflect the entire configuration vertically if necessary to take

    c_By>3/8,       every point of B has y>-3/8.            (8)

The second conclusion follows from sqrt(2)/2<3/4. The reflection keeps
the entire range of the A and U sliders in (2), and retains both possible
signs of A's original circle load.

Let n be the actual unit normal from A to B, with actual application P.
Because B meets D_epsilon and lies on the far side of this supporting
line, its height satisfies

    P dot n<=epsilon.                                    (9)

Every vertical A-side normal has support height above 3/8. Every
west-facing left-vertex normal has support height at least the smaller
of a and |b_-| or b_+, also above 3/8; the west side itself has height a.
All violate (9). Therefore n_x>0, and P belongs to A's right wall.
By (8) it cannot be the lower-right vertex. The complete remaining AB
feature cover is

    n=e_x, P=(-rho,y), b_-<=y<=b_+;
    or P=(-rho,b_+), n_x>0, n_y>0.                        (10)

This includes every right-side endpoint mean. In particular n_y>=0.

## 3. No actual unit neighbor can touch a left vertex of A

We use a simple radius-free corner-center fact. Let a unit square have
a vertex P whose inward orthonormal axes are e_x,e_y. If a distinct
interior-disjoint unit T touches it at P with an actual outward normal
n=(-s,-t), where s,t>=0 and s^2+t^2=1, write w=c_T-P. Then

    |w|<=sqrt(2)/2,
    n dot w=h_T(n)>=1/2.                                 (11)

The first statement uses P in T; the second is T's supporting
half-width. If w_x+w_y were positive, then

    n dot w
      =-(s+t)(w_x+w_y)/2+(t-s)(w_x-w_y)/2
      < |t-s| |w_x-w_y|/2
      <=1/2,                                            (12)

since |w_x-w_y|<=sqrt(2)|w|<=1. This contradicts (11).
Thus

    (c_T-P) dot (e_x+e_y)<=0.                            (13)

Rotation and reflection give the same result for any actual corner and
its two inward axes. It includes axis normals and side-axis endpoints;
no vertex/vertex normal is selected or changed.

At A's lower-left corner P=(-a,b_-), equation (13) gives

    c_Tx+c_Ty<=-a+b_-<-119/60-3/8=-283/120.

At its upper-left corner it gives

    c_Tx-c_Ty<=-a-b_+<-283/120.

Both contradict (3), because

    |c_Tx +/- c_Ty|<=sqrt(2)|c_T|< (3/2)(91/60)=273/120.  (14)

Thus neither left vertex is an actual contact with another unit, for
any of its normal-cone features. A west-side-interior contact is also
impossible: the neighbor would lie in x<=-a and its center would have
x<=-a-1/2<-91/60. We have exhausted the whole left interface.

Therefore the actual AC contact is either on the right wall, or has a
vertical top/bottom side normal. A bottom normal would put all of C in
y<=b_-<-3/8, while B lies strictly in y>-3/8 by (8); then B,C could not
touch. The only remaining alternative to a right-wall AC contact is

    m=e_y, Q=(x,b_+), -a<=x<=-rho.                       (15)

We next exclude all of (15), with its complete mean interval.

## 4. The possible top-side contact contradicts the full equations

Let the positive AB and AC magnitudes be mu,nu. The original A equation
is exactly

    G_A+alpha e_x+mu n+nu m=0.                           (16)

All its circle atoms and its bridge have zero origin moment. About the
actual bridge application p=(-rho,0), the circle system has moment
rho (G_A)_y; this is true for its full original resultant, including
G_A=0. The bridge itself has zero moment about p.

### 4.1 A strictly exposed upper-right AB contact is impossible

Suppose the second alternative of (10) holds, and (15) holds for AC.
The vertical component of (16) gives

    (G_A)_y=-mu n_y-nu<0.

The three remaining moments about p are

    circle:  rho (G_A)_y<0,
    AB:     -b_+ mu n_x<0,
    AC:     (x+rho)nu<=0.

Their sum cannot vanish. This excludes this whole feature alternative
without assuming A circle-clear or replacing its circle load.

### 4.2 An A-owned right-side AB mean is impossible as well

It remains that n=e_x, P=(-rho,y), while m=e_y and Q=(x,b_+).
Origin moment at A gives

    -mu y+nu x=0,       y=nu x/mu<0.                     (17)

In particular the common directed triangle moment H is nonzero: the
AC force has nonzero origin moment nu x because x<=-rho<0.

At all three triangle bodies retain their complete external aggregates

    F_A=G_A+alpha e_x,   F_B=beta v,   F_C.

Each external system has zero origin moment. The full local theorem
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md`, accepted in
`REVIEW_RADIAL_TRIANGLE_NONCOLLINEAR_GLOBAL_2026_10_26.md`, makes these
three aggregates nonzero and noncollinear. The already accepted
`RADIAL_TRIANGLE_CONCURRENCE.md` therefore gives a positive multiple of
the actual aggregate at every nonparallel triangle root. Its purely
physical proper-port relation retains all actual means.

The B cycle pair cannot be parallel. Its normal toward A is -e_x, and
the two outward normals of a physical unit-square triangle, if parallel,
must have the same sign. Parallelism would therefore give v=e_x from
the full B equation. The genuine S leaves M and L would then be the same
physical square, impossible. Thus B has a genuine positive concurrence
q_B, and the proper AB port has

    q_B=P+s e_x, s>=0,       q_B=tau_B beta v, tau_B>0.

By (17), its y coordinate is negative. Consequently

    v_y<0.                                              (18)

At C there are two complete alternatives. If its cycle pair is parallel,
both its outward normals point downward, because the CA normal is -e_y.
Its full circle resultant is vertical, so (F_C)_x=0. If its pair is
nonparallel, its positive concurrence q_C satisfies the proper CA relation

    q_C=Q+s' e_y, s'>=0,
    q_C=tau_C F_C, tau_C>0.

Hence (q_C)_x=x<0 and (F_C)_x<0. In all cases

    (F_C)_x<=0.                                        (19)

Equation (16) now reads F_A=-mu e_x-nu e_y. Summing the true triangle
equations gives F_A+beta v+F_C=0, and (19) implies

    beta v_x=mu-(F_C)_x>0.                              (20)

Thus the actual S support point p_M=d v in B is strictly southeast:
its x coordinate is positive and its y coordinate negative. But (6),(8)
bound every such point of B by

    0<(p_M)_x<c_Bx+sqrt(2)/2
                 <-11/40+17/24=13/30,
    0<-(p_M)_y<3/8.

Consequently

    |p_M|^2<(13/30)^2+(3/8)^2=4729/14400<1,              (21)

contrary to |p_M|=d>1. This excludes every A-owned right-side AB mean
when AC has a top-side normal, including every endpoint mean.

Sections 3--4 prove that both actual triangle contacts on A lie on its
right wall, with normals of strictly positive horizontal component.

## 5. The actual moments put the bridge between the triangle ports

Write the two original A ports as

    P_1=(-rho,y_1),   P_2=(-rho,y_2),

with their actual outward normals n_1,n_2. For a right-wall support
having n_x>0, its origin moment has sign opposite to the port height:

* On a right-side axis, n=e_x and det(P,n)=-y.
* At the upper-right vertex, y=b_+>0 and n_y>0, so
  det(P,n)=-rho n_y-b_+ n_x<0.
* At the lower-right vertex, y=b_-<0 and n_y<0, so
  det(P,n)=-rho n_y-b_- n_x>0.

These are all features. In particular zero moment occurs only for the
axis normal e_x at the actual point p=(-rho,0).

The full origin-moment equation at A is the positive weighted sum of
these two moments equal to zero; its circle atoms and its radial bridge
contribute zero. Therefore either both moments vanish, or the two port
heights have strictly opposite signs.

If both vanish, P_1=P_2=p and both normals are e_x. The actual distinct
squares B,C,U all contain p and lie in the right half-plane x>=-rho.
At p each has a tangent cone of angular width at least pi/2. Three
interior-disjoint such cones cannot lie in a semicircle of width pi.
This is already an actual local overlap contradiction, including every
possible side-interior or endpoint realization at U.

It remains to consider the full nonzero-moment alternative. Relabel the
two triangle ports only for this geometric argument so that

    y_-<0<y_+,
    P_-=(-rho,y_-), P_+=(-rho,y_+).                       (22)

The original bridge application p lies strictly between the two original
triangle applications on A's right side. We next show that their contact
triangle would have to contain the entire actual unit U.

## 6. The contact triangle cannot contain U

Choose the unchanged actual common BC application Q. It belongs to both
B and C, including when it is an endpoint or an actual shared-side mean.
The segments P_+Q and P_-Q belong respectively to those two convex
squares. The segment P_-P_+ belongs to A.

First, Q cannot lie to the left of the line x=-rho. If Q_y>=0, the
segment from P_- to Q immediately enters the open interior of A: its
horizontal direction is left, its vertical direction is strictly up,
and P_- is either on the relative interior of the right side or at its
lower endpoint. If Q_y<=0, the segment from P_+ to Q instead immediately
enters A's open interior. In either case a point of B or C lies in the
open interior of A. Interior points of that same unit occur arbitrarily
near it, giving forbidden overlap. Thus Q_x>=-rho.

If Q_x=-rho and Q_y>0, the lower-port square contains a vertical segment
through p with p in its relative interior. Because A occupies the left
half-plane locally at p, that square must have p in a relative side
interior and occupy the right half-plane locally. It then overlaps U
near p. If Q_y<0, the upper-port square gives the same contradiction.
If Q_y=0, then Q=p and B,C,U all contain p to the right of A; the same
three-cones-in-one-semicircle argument used in Section 5 excludes it.
This covers every collinear and coincident-contact degeneration.

We must therefore have

    Q_x>-rho.

The triangle T=conv(P_-,P_+,Q) is now nondegenerate. Its base is on A's
right wall, with p strictly inside the base segment. The actual U lies
to the right of that wall and has p on its left side, perhaps at an
endpoint of that side. Hence some points of its open interior arbitrarily
close to p lie in the open interior of T.

Every boundary segment of T lies in one of A,B,C. The open interior of
U is disjoint from all three whole squares: an interior point of U on
even the boundary of another square would give overlap in a small
neighborhood. It follows that the whole open interior of U lies inside
T. Indeed if it also had a point outside T, the segment joining that
point to the already obtained interior point would lie in the convex
open interior of U and cross a boundary segment of T, a contradiction.

But the base length of T is at most one, and its height is at most
sqrt(2), because Q and either base endpoint belong to the same unit
square. Therefore

    area(T)<=sqrt(2)/2<1=area(U).                         (23)

The required containment is impossible. This contradiction excludes the
entire remaining nonzero-moment case.

## 7. Whole-family conclusion and exact dependencies

Every original width, leaf type, root slider, circle load, contact owner,
actual mean and zero/nonzero triangle moment has been covered. The
genuine length-three arm either has its already excluded critical P
geometry, or its complete chart (1)--(3). A second genuine direct leaf
must be S; the D case overlaps the actual first internal body. The
central-center separation forces the stated B side, the whole root
feature cover forces both triangle contacts onto A's right wall, and
the original moments then force an impossible unit in the contact
triangle or an impossible common-point angular cover.

Thus the full sole-triangle attachment distribution (3,1), with its two
arbitrary original completion squares, is impossible in the stated
selected-certificate scope. No force at A was omitted or assigned a
degree-two or leaf-only equation. The only concurrence use occurs in
Section 4.2, where nonzero H is proved from the actual top-side contact
and the complete external aggregates meet the new noncollinearity
theorem's hypotheses. Parallel B and C alternatives are explicitly
retained and handled there.

This source supplies the last length-three/direct-leaf attachment
exclusion. Its use in an entire coarse-cell assembly still requires
the existing graph, stress-selection and other-attachment joins.
No numerical pose sample, Lean compilation, CI or remote action is used.
