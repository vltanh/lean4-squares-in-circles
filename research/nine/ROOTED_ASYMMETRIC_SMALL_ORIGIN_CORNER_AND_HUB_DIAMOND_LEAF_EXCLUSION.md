# An asymmetric small origin corner has at most two boundary neighbors, and the whole mixed hub-diamond leaf row is excluded

Date: October 27, 2026.

**Status: complete proposed uniform geometric theorem and entire original
C2.34.b2 hub-diamond AP row, frozen for full root and separate independent
review.** No original gate, shared ledger, source acceptance header or
remote branch is changed.

All nine actual closed unit squares, their disjoint open interiors and
the common compatible selected physical certificate remain. Every
original force, physical circle mask, individual zero weight, true
degree, selected normal and actual application mean is retained. The
first theorem is force-free.

## 1. A complete asymmetric physical theorem

Suppose the actual containing circle is centered at O and

    sqrt(17)/2 <= R <= sqrt(Q), Q=1105/256.

Let an actual unit H have own coordinates

    H=[-a,1-a] times [-b,1-b],
    0<=a<=1/60, 0<=b<=1/20.                         (1)

**Theorem 1.** At most two distinct actual physical boundary squares
can touch H.

A physical boundary square has an actual point on the containing
circle; its circle multiplier may be zero. No selected edge, degree,
force, contact-normal convention or boundary equation is assumed in
Theorem 1. All shared-side contacts and weak endpoints are included.

We prove that every such neighbor center belongs to one of the two
rectangles

    C_SE=(9/8,91/60) times (-7/10,3/20),
    C_NW=(-2/3,9/40) times (23/20,91/60).             (2)

Each has diameter strictly less than one. The proof sharpens the
lower transverse-center estimate of
ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md; its previous
1/40 hypotheses are not assumed for this new theorem.

For every contained unit center C,

    |C|<M=91/60,                                    (3)

because its greatest squared corner radius is at least
|C|^2+|C|+1/2, and M^2+M+1/2-Q=31/57600>0. If the unit is
physical boundary, then

    |C|^2 >= (sqrt(17)/2-1/sqrt(2))^2
           =19/4-sqrt(17/2)>183/100.                (4)

Here sqrt(17/2)<73/25 has exact squared reserve 33/1250.
Every actual point p of a unit has |p-C|<=1/sqrt(2). Distinct
actual unit centers have distance at least one, from their open
radius-1/2 inscribed disks.

We also use the complete elementary support fact: if p is a
minimum-n support point of an actual unit and n is a unit vector,
then p+n belongs to that unit. In its own frame, every nonzero
component of n points inward from the relevant support endpoint
and has magnitude at most one. At a side point this is the same
unit-width assertion. Thus all feature and mean endpoints satisfy it.

## 2. Two complete contained-wall estimates

For any actual contained unit E we prove both implications

    E subset {x>=59/60}  =>  |C_E,y|<3/20,
    E subset {x>=19/20}  =>  |C_E,y|<9/40.            (5)

The first estimate agrees with the previously reviewed 59/60 wall
theorem. Both are proved here with the same complete two-tilt cover.

Write E's frame magnitudes c>=s>=0, c^2+s^2=1. Its x width is
c+s. Since R<133/64,

    c+s<=R-19/20<361/320.

The function s+sqrt(1-s^2) increases for 0<=s<=1/sqrt(2).
If s>=1/7 it is at least (1+4sqrt(3))/7, which exceeds
87/77>361/320: sqrt(3)>19/11 and the latter rational reserve
is 43/24640. Therefore

    s<1/7, c>=1-s^2>=1-s/7.                         (6)

Let the wall height be A_0 and suppose C_E,y>=q. For the two
possible tilt signs there is, respectively, an actual upper far
corner with coordinate lower bounds

    (A_0+c, q+(c+s)/2),
    (A_0+c+s, q+(c-s)/2).

Every displayed coordinate is positive. By (6) their squared norms
are at least, respectively,

    (A_0+1-s/7)^2+(q+1/2+3s/7)^2,
    (A_0+1+6s/7)^2+(q+1/2-4s/7)^2.                 (7)

For A_0=59/60,q=3/20, the constant term minus Q is
2287/57600. The first expression has linear coefficient -1/105
and positive quadratic coefficient 10/49, so its excess over Q is
strictly greater than

    2287/57600-1/735=108223/2822400>0.

The second has positive linear coefficient 93/35 and quadratic
coefficient 52/49, so is also greater than Q.

For A_0=19/20,q=9/40, the constant term minus Q is 3/256.
The two linear coefficients are 9/140 and 88/35, respectively;
their quadratic coefficients are again 10/49 and 52/49. Both
expressions are greater than Q throughout the entire interval.

Containment is contradicted in every case. Reflection handles
C_E,y<=-q. This proves (5) for arbitrary actual frames and wall
positions, including an aligned frame and physical side endpoints.

## 3. A full lower-center estimate for a downward corner contact

We first record a geometric calculation used in all lower-endpoint
cases. Suppose p=(A,-b), |A|<=1, 0<=b<=1/20, and an actual
unit has p as its highest vertex, with inward edges

    (r,-t), (-t,-r), r,t>=0, r^2+t^2=1.

If its center obeyed C_y<=-b-13/20, then

    u=r+t>=13/10, |r-t|=sqrt(2-u^2).

The point p and either adjacent vertex have norm less than
41/40+1=81/40<sqrt(17)/2. Indeed |p|<=sqrt(401/400)<41/40.
The opposite vertex has squared norm at most

    3+b^2+2sqrt(2-u^2)+2bu
       <=3+1/400+2sqrt(2-u^2)+u/10
       <=1253/400+sqrt(31)/5 <17/4.                 (8)

The function 2sqrt(2-u^2)+u/10 decreases on
[13/10,sqrt(2)], as its derivative on the open interval is
-2u/sqrt(2-u^2)+1/10<0. Continuity includes the last endpoint.
The final exact square-root comparison is

    (447/400)^2-31/25=1409/160000>0.

Thus none of its four actual vertices could touch the circle.
Every physical boundary unit in this highest-vertex situation satisfies

    C_y>-b-13/20.                                    (9)

We now prove the same bound for a physical boundary unit E at a
strict southeast contact with an actual root corner

    p=(A,-b), 19/20<=A<=1, 0<=b<=1/20.

The root's open tangent quadrant is northwest and the actual
separating normal toward E is n=(c,-s), c,s>0. This covers every
original contact independently of any stress.

### 3.1. Every E-vertex feature

The open right-angle tangent sector of E avoids the root's open
northwest quadrant. Its two inward edges therefore either both
have nonnegative x component or both have nonpositive y component.
This is the full interval cover for a right-angle sector disjoint
from that open quadrant; axes belong to the same closed alternatives.

In the first alternative write the inward edges (r,-t),(t,r),
r,t>=0, r^2+t^2=1. The opposite actual vertex has squared norm

    A^2+b^2+2+2A(r+t)-2b(r-t)
       >=(19/20)^2+2+2(19/20)-1/10
       =Q+2471/6400>Q.

Thus this alternative is impossible. In the second alternative
E has p as a highest vertex, and (9) applies. This includes every
side endpoint as a vertex feature.

### 3.2. Every relative side-interior feature

If p lies in a relative interior of an E side, that side owns the
normal. Put j=(s,c), so the actual center has the exact form

    C=p+n/2+k*j, -1/2<k<1/2.

Suppose C_y<=-b-13/20. Then k<0. Write t=k+1/2; thus
0<t<1/2 and

    s+c-2tc>=13/10.

Both c and s are strictly greater than1/3: otherwise their sum
is at most (1+2sqrt(2))/3<13/10. Using sqrt(2)<17/12 gives

    0<t<7/40.                                       (10)

The four actual vertices are

    p+t*j, p-(1-t)*j,
    Z_+=p+n+t*j, Z_-=p+n-(1-t)*j.

The first two have norm less than81/40<sqrt(17)/2. The third has

    |Z_+|<=|p|+sqrt(1+t^2)<41/40+41/40=41/20
            <sqrt(17)/2.                            (11)

For the last vertex, if s<=4/5, the derivative of its squared
norm as a function of t is

    2(p.j-1+t)<=2(s-1+t)<-1/20.

Its value is therefore at most the value at t=0. That value is
exactly the opposite-vertex expression bounded in (8), since
s+c>=13/10. This is an algebraic comparison of actual expressions,
not a substituted square or a new circle contact.

If s>4/5 then c<3/5. The same actual Z_- satisfies

    0<19/20+1/3-1 < Z_-,x
       <1+3/5-4/5+7/40=39/40<1,
    |Z_-,y|<1/20+sqrt(2)<3/2.

Consequently |Z_-|^2<13/4<17/4. Every actual corner is again
strictly inside the circle, contradicting physical boundary status.
This proves (9) for the entire side-interior alternative as well.

### 3.3. The whole south-axis feature

At a south-axis contact E lies below y=-b. If it has a horizontal
top side, C_y=-b-1/2 and (9) is immediate. Otherwise the actual
contact is its unique highest vertex. For any root side satisfying
[-a,1-a] with 0<=a<=1/20, the contact has |p_x|<=1. The full
highest-vertex argument (8) applies, including either axis endpoint.
Thus (9) holds for south-axis contacts too, with no choice of a new
mean or contact point.

## 4. Complete upper and longitudinal center bounds

For a strict southeast contact at p=(A,-b), consider the two
parameter ranges

    I:  A>=59/60, b<=1/20, q=3/20, L=7/10, D_0=9/8;
    II: A>=19/20, b<=1/60, q=9/40, L=2/3, D_0=23/20.

Section 3 gives C_y>-L. We prove C_y<q. In a surviving E-vertex
case both inward edges point nonpositively downward, so C_y<0.
In the side-interior case, suppose instead C_y>=q. The same actual
side slider gives

    k=(C_y+b+s/2)/c>0,
    Z=C+(n+j)/2,
    Z_x=A+c+(k+1/2)s,
    Z_y=C_y+(c-s)/2.

Since c+s^2/(2c)=(c+1/c)/2>=1,

    Z_x>=A+1+(C_y+1/2)s>=A+1+(q+1/2)s.             (12)

For s>=1/2 this is at least91/40>R. For 0<s<=1/2 use
c>=1-s^2 and s^2/2<=s/4 to obtain

    Z_y>=q+1/2-3s/4>0.

Thus the squared norm is at least

    (A+1+(q+1/2)s)^2+(q+1/2-3s/4)^2.                (13)

Its linear and quadratic coefficients are positive. At s=0 its
excess over Q is at least2287/57600 in range I and3/256 in range
II, by Section 2. This contradicts containment. Hence C_y<q in
both ranges, with all side and vertex features exhausted.

Using the actual p in |C-p|^2<=1/2 and the strict boundary norm
(4) gives

    C_x > [133/100+A^2+b^2-2bL]/(2A).              (14)

In either range K_b=133/100+b^2-2bL>1. The expression
(A^2+K_b)/(2A) decreases for A<=1, and its value at A=1
decreases with b in the displayed interval. Therefore

    range I:  C_x>181/160>9/8,
    range II: C_x>8309/7200>23/20.                  (15)

The exact reserves in the final comparisons are1/160 and29/7200.
Together with (3), all strict southeast contacts have their centers
in the respective desired rectangles.

For an east-axis contact, (5) gives |C_y|<q and the whole unit is
beyond the wall A. Its center has C_x>=A+1/2>D_0. Thus the same
rectangle contains it, including all actual shared-side means.

For a south-axis contact, Section 3 gives -L<C_y<=-1/2. By (4),

    C_x^2>183/100-L^2>D_0^2.

The respective exact reserves are119/1600 and227/3600. At any
actual contact, C_x>=p_x-1/sqrt(2)>-1/20-17/24>-D_0, so the
negative branch is impossible. This gives C_x>D_0, and again the
same rectangle, with no frame alignment or load premise.

## 5. Exhaustion of all actual normals and the two-neighbor conclusion

For H in (1), its southeast corner and east/south axial features
satisfy range I and put every corresponding neighbor in C_SE.
Interchanging x and y puts its northwest corner and north/west
axes into range II. Their centers belong to C_NW.

A strict southwest normal exposes (-a,-b), whose norm is at most
sqrt(10)/60<1/2. Such a point cannot belong to a physical boundary
unit, whose points have norm at least R-sqrt(2)>1/2.

A strict northeast normal exposes W=(1-a,1-b). The physical
support fact in Section 1 puts W+n in its actual neighbor, whereas

    |W+n|^2>=2(19/20)^2+1+2(19/20)
             =Q+2487/6400>Q.

This is impossible. The two strict corners and four axes already
treated, together with these two excluded corners, cover every
actual separating normal and every physical contact feature.

The two rectangles have squared diameters

    diam(C_SE)^2=12613/14400=1-1787/14400<1,
    diam(C_NW)^2=13385/14400=1-203/2880<1.

Distinct actual units have centers at least one apart. Each rectangle
therefore permits at most one physical boundary neighbor, proving
Theorem 1 in its full force-free scope.

## 6. The actual small vertex in the remaining oblique triangle interface

Return to the unchanged original radius window
79/40<=R<=sqrt(1105)/16 and selected certificate. Suppose H contains
O openly, H-A-B-H is an actual triangle, A has precisely its two
triangle forces and a genuine leaf, and B has true degree two.
Let P be a third distinct actual near unit meeting D_epsilon. We use
no equation, degree or force at P in this section.

B is loaded because its two neighbors already touch. The genuine
A leaf is S, with d=1+epsilon>1 and0<epsilon<1/60. A is circle-clear.
Consider the remaining interface where AH is A-owned and H's frame
is oblique to A. There are two complete A possibilities: A's leaf
and pair are aligned/parallel, or its leaf is strictly tilted.

Use actual A axes with the A-to-H normal east. In both cases H has
the actual strict minimum-x vertex

    V=(-delta,-Y), 0<delta<=epsilon, Y>0,
    H=V+[0,1]u+[0,1]v,
    u=(s,c), v=(c,-s), s,c>0, s^2+c^2=1.            (16)

The following exact local coordinates come from the complete A/B-only
proofs in ROOTED_ONE_PRIVATE_LEAF_TRIANGLE_TERMINAL_FOUR_BLOCK_EXCLUSION.md,
Sections 3--4.1, SHA256
02b1a5d7525e2cc8d02044b9f842479217009ce33f8ff9149139e5e0a4c8f87e.
No terminal-four-block equation or its final shallow-strip consequence
is used here.

For the aligned parallel A pair,

    A=[-d,-epsilon] times [-b_0,1-b_0],
    delta=epsilon, 0<Y<=b_0<9/25,
    actual AB wall height y>16/25,
    |V|<11/30.

Its two original wall means strictly straddle zero; they are unchanged.
All actual B frames lie wholly above height1/2, as in the complete
wall proof. In particular their physical circle masks were covered
before using a B equation.

For tilted A, the complete genuine-leaf concurrence and A-owned
coordinates give

    A=[-1-delta,-delta] times [-beta,1-beta],
    0<delta<epsilon, 0<Y<=beta<11/60,
    |V|<11/60.

The A-owned top AB feature puts B wholly above1-beta>49/60.
At a strict upper-right AB vertex its normal is proportional to
(1-t*a_0,1-t*b_0), where a_0>=b_0>0 is the real leaf direction
in A's frame and t>=0 is the real concurrence parameter. Thus its
unit components satisfy0<n_x<=n_y and n_x<=1/sqrt(2). A unit with
a minimum-n support point W then has minimum height at least
W_y-n_x: at a vertex its only downward edge has vertical magnitude
at most n_x, and at a side the full tangential interval has that
same vertical span. Therefore the whole actual B lies above
49/60-1/sqrt(2)>0. This includes every owner, free normal and endpoint.

In either case let S be A's actual lower-right vertex. Then

    |V|<=|S|,
    every other A vertex has norm greater than3epsilon,
    every other H vertex has norm at least1-|V|>3epsilon.           (17)

The fully reviewed three-near-unit angular theorem in
ROOTED_ORIGIN_TRIANGLE_ALIGNED_NONPARALLEL_SECOND_LEAF_EXCLUSION.md,
Sections 1--3, SHA256
b897cade602a3e256516dcf344b122360c256b1bb234ec0417b53bdbe308dab4,
is force-free: if H contains O openly and H,A,P are distinct actual
units meeting D_epsilon, then it is impossible for every H vertex
and every A vertex to have norm greater than3epsilon. H would occupy
more than pi radians on that circle, A more than2pi/3, and P more
than pi/3, with disjoint open arcs. Its full nearest-side, nearest-
vertex and origin-containing alternatives include every P feature.

If |V|>3epsilon, (17) makes all H vertices far. That theorem would
give an A vertex of norm at most3epsilon; by (17) it must be S.
But |V|<=|S|, a contradiction. Hence the unchanged actual HA vertex
satisfies

    |V|<=3epsilon<1/20.                              (18)

Use H's own x direction v and y direction u. Since O is in int H,

    H=[-sigma,1-sigma] times [-w,1-w],
    sigma=-V.v=delta*c-Y*s in (0,epsilon],
    w=-V.u=delta*s+Y*c in (0,3epsilon].              (19)

Thus the entire actual H satisfies Theorem 1. The same local routing
also puts its genuine B port on the minimum-v side: V is too small
for a boundary unit; V+[0,1]v lies below height zero; the opposite
strict H vertex is excluded by the physical triangle support-span
lemma; and a positive H-axis normal has negative scalar product with
the west HA normal, contrary to the side-normal triangle theorem.
The only remaining features are the minimum-v side and its upper
endpoint. This routing observation is not used to give any decorated
private vertex a degree-two equation.

## 7. Complete original hub-diamond AP row

The exact remaining original row in
ROOTED_C2_34_TWO_BRIDGES_THREE_DOMAIN_REDUCTION.md, SHA256
8918c0e3e77cbc9f90899a29ebd2233c87858a00ecf1e0ffca2a684ccdd5cb0a,
has the positive triangle HA,HB,AB, the hub-rooted diamond

    HK, HP, HQ, KP, KQ,

and one genuine leaf at each of A and P. These are eight original
positive bodies, with the ninth actual physical unit retained. Their
true degrees are

    H5, A3, B2, K3, P3, Q2, and the two leaf1 stars.

The complete origin theorem
ROOTED_DECORATED_TRIANGLE_AND_PRIVATE_LEAF_FOUR_BLOCK_ORIGIN_STRUCTURE.md,
SHA256 e77c19d2afefb96f4919788d5d69f987377d7b90b299037c0c35a1c717cd8968,
gives O in int H, every other closed unit origin-free, and both
genuine leaves S. In particular the actual P meets D_epsilon and
is distinct from H,A. No private force or H circle atom was removed
to obtain that conclusion.

The entire A feature and frame cover is now exhausted as follows.

* If A is aligned and its pair is nonparallel, the complete b897cade
  second-leaf theorem excludes it, with P's real leaf and full degree.
* If the A pair is parallel and H shares A's frame, use
  ROOTED_PARALLEL_DECORATED_TRIANGLE_THIRD_NEAR_UNIT_EXCLUSION.md,
  SHA256 989eae4dd32e7c48617b3e908b149daf847ed1292f484e48eb1e87fb75561426.
  This needs only the actual third near unit P.
* For tilted A, the complete feature cover in 02b1a5d7 Section 1
  leaves its strict two-vertex P/W alternative or the A-owned AH
  alternatives. The strict two-vertex alternative is excluded at
  origin-only scope by
  GLOBAL_CLOSURE_ORIGIN_ROOT_TILTED_TWO_VERTEX_TRIANGLE_EXCLUSION.md,
  SHA256 a0cec94cf05ae1ac7984f08cb0c3c764f0ae534439821af3af35304acd22c7aa.
  Its normal preselection and full true A3/B2 equations are unchanged.
* In the tilted A-owned alternatives with H parallel, use
  ROOTED_TILTED_PARALLEL_TRIANGLE_SECOND_LEAF_EXCLUSION.md,
  SHA256 6f40f89dde97f8c333ee12026873efb09453dd6bfafb621dc5e5d80fc178cbd1.
  This retains P's actual leaf and true degree three.

Both aligned-parallel and tilted-A-owned alternatives with H oblique
are precisely Section 6. There H has at most two physical boundary
neighbors by Theorem 1. But the original graph has three distinct
such neighbors B,K,Q. B2 and Q2 are loaded because each has two
already touching neighbors. K has its full actual degree three
with neighbors H,P,Q, including the original neighbor edges HP,HQ.
The complete NO_UNLOADED_DIAMOND_HUB.md theorem therefore forces K
to be loaded, without any degree or load condition on H or P.
All three retain their full original circle systems.

This contradicts Theorem 1. The entire original hub-diamond AP row
is excluded, with every physical mask, owner, slider, zero weight
and completion unit retained. Neither P3 nor H5 has been treated
as a terminal tip, and no root circle resultant has been split.

The original C4 AP and page-diamond AP rows remain separate complete
obligations. This source does not declare the whole C2.34.b2 coarse
cell closed or assert the unrestricted bound or equality theorem.
No numerical pose, Lean build, CI, workflow, remote mutation or
shared-ledger edit is used.
