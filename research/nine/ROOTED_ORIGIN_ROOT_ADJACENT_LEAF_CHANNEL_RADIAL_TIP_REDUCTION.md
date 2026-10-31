# A root-adjacent leaf channel forces a physical radial-S loaded tip

Date: October 27, 2026.

**Status: complete proposed uniform reduction, frozen for full source
review. The surviving radial-S family is not excluded here.** No
original gate, shared ledger, physical force or remote is changed.

Keep all nine actual units, the common compatible selected certificate,
and the already chosen minimum-Phi radius-minimizing packing, in
79/40<=R<=sqrt(1105)/16. Put

    d=sqrt(R^2-1/4)-1, epsilon=max(d-1,0), M=91/60.

## 1. Exact actual scope

The original positive graph contains H-X-U-V-H. The private X has
exactly these two cycle edges and one genuine leaf L. U is positively
circle-loaded and has true positive degree two. V is unloaded and has
true positive degree two. The actual H contains O in its open interior;
all its other positive forces remain arbitrary.

**Reduction theorem.** The leaf L is S, d=1+epsilon>1. The pair at X
is nonparallel, and its positive proper concurrence lies in X. In
particular the whole aligned exterior-concurrence alternative tau>d
is impossible. The physical circle mask of U is necessarily radial S:
U has its two adjacent far-side circle corners, with both original
weights retained and either individual weight permitted to vanish.
No equality or symmetry of those weights is inferred.

A more explicit surviving chart is given below. This is a complete
physical-mask reduction, not an assertion that U is a genuine leaf,
that U's two forces are parallel, or that the entire original family
is already impossible.

The complete genuine-leaf geometry gives that X is physically clear.
Since O lies openly in H, every other actual closed unit avoids O.
Thus the D leaf and S with d<=1 are excluded without a load deletion,
and L is S with

    0<epsilon<1/60, dist(O,X)<=epsilon,
    c_L=(d+1/2)e_L, |c_L|=d+1/2.

## 2. Actual channel, canonical contact, and its moment sign

UNIT_BYPASS_NORMAL_CHANNEL.md applies to the true unloaded V, whose
endpoints H,U have the actual unit bypass X. Its full width and
transverse-separation theorem gives, after reflection,

    V=[a-1,a] times [alpha,alpha+1],
    H subset {y<=alpha}, U subset {y>=alpha+1},
    X subset {x>=a+g}, g>=0.                         (1)

The unchanged actual V applications are (m,alpha) and
(m,alpha+1), with m in [a-1,a]. H open at O gives alpha>0.
The universal contained-neighbor support bound gives alpha+1<=d.
Consequently

    0<alpha<=epsilon, h=alpha+1>1,
    a+g<=epsilon, a<1/2.                             (2)

No side mean has been centered.

The empty-gap canonical translation in
GLOBAL_CLOSURE_ADJACENT_LEAF_C4_SINGLE_TRANSMITTER_EXCLUSION.md
Section 4 applies after relabeling its transmitter as V and its
transverse bypass as X. Its proof uses only the actual width-one
channel, the actual four-cycle, the empty four-ring region, and
a<1/2. The source's earlier special force argument to prove that
inequality is not needed here: (2) already gives it.

For clarity, if g>0, the open rectangle
(a,a+g) times (alpha,alpha+1) is on the bounded side of the actual
four-ring. It contains no other whole unit by the complete
four-ring hole theorem at a true unloaded degree-two vertex and
the retained point-normal convention. Moving only V a sufficiently
small distance right enters only this empty rectangle, decreases
its maximal corner radius and its center norm, and preserves all
other physical units. This contradicts the fixed minimum of Phi.
Thus

    g=0, min_X x=a, and X physically touches V.       (3)

The physical contact in (3) carries no new positive force.

Every contained unit center has norm less than M. The actual unit U
lies beyond y=h>1, so GENERAL_FAR_WALL_59_60_SQUARE_BOUNDS.md gives

    |(c_U)_x|<3/20, (c_U)_y>3/2,
    C>99/100, 0<=S<1/10, C^2+S^2=1,                 (4)

where C,S are the larger and smaller projections of its own frame.
Also V's upper-left corner is (a-1,h), so

    a> -5/6,                                       (5)

since h>1 and (11/6)^2+1>1105/256.

Write k for the directed actual force moment around H-X-U-V-H.
The complete private equations at X,U,V make these four moments
equal: X's real leaf moment and U's full circle moment are zero.
The equation at H is not shortened.

The value k is nonzero. Otherwise XU is a radial physical contact
between the origin-free genuine leaf root X and another origin-free
unit, contrary to ROOTED_ORIGIN_FREE_RADIAL_CONTACT_EXCLUSIONS.md
Section 3.

At the actual physical XV contact choose the common horizontal
separator pointing from V to X. Its application Z has Z_y>=alpha>0.
If k<0, the physical triangle X-U-V-X has three strictly negative
directed geometric line moments: its two original moments have
that sign and det(Z,e_x)=-Z_y<0. The exact geometric circuit theorem
ROOTED_GEOMETRIC_TRIANGLE_MOMENT_CIRCUIT_EXCLUSION.md applies with
outside origin-interior H. It permits this specified unstressed
physical contact without changing any original positive normal or
force. This is impossible. Therefore

    k>0, m<0.                                       (6)

The second conclusion follows at V->H, whose actual force is a
positive multiple of -e_y and whose moment is -gamma*m.

## 3. A useful actual two-boundary-center cap

The leaf direction cannot satisfy (e_L)_y>=sqrt(3)/2. Indeed then

    |(c_L)_x|<91/120, (c_L)_y>1299/1000,

using sqrt(3)>433/250. Equations (4) and the center-radius bound
put the differences of c_L,c_U in a rectangle with coordinate
magnitudes less than 109/120 and 653/3000. Its squared diagonal is

    (109/120)^2+(653/3000)^2
        =3926017/4500000<1.                          (7)

The y bound covers both signs of that difference. This contradicts
the distance at least one between distinct unit centers. Hence

    (e_L)_y<sqrt(3)/2.                               (8)

This is only a geometric comparison of the two actual boundary units.

## 4. The complete X-frame reduction

Use the full degree-free genuine-leaf concurrence and feature lemma
in ROOTED_C3_334_PRIVATE_ADJACENT_LEAF_TWO_LOAD_C4_EXCLUSION.md
Section 1. It retains arbitrary degrees at both other neighbors.

For a tilted X choose own axes u,v so

    X=[delta,1+delta]u+[-beta,1-beta]v,
    e_L=A u-B v, A>=B>0,
    1+delta=d A, beta=d B,
    0<delta<epsilon, 0<beta<11/60.                   (9)

For an aligned X use the same rectangle with delta=epsilon,
0<=beta<=1, e_L=u. In that aligned case the sign of v is freely
reversible, replacing beta by 1-beta.

First u_y must be positive. If u_y<=0, the maximum global height
of the rectangle is at most one: its u-coordinate maximizing
height is the positive near coordinate; its other coordinate
contributes at most 1-beta or beta. It could not touch U at
height at least h>1.

Suppose u has negative horizontal component, and write
u=(-c,s), c,s>0, c^2+s^2=1.

For tilted X, if v=(s,c), its leftmost vertex is the actual
leaf corner d e_L. That corner lies in the relative interior of
L's inner side and cannot be shared with V. If v=(-s,-c),
the actual leftmost coordinate is

    a=-(1+delta)c-(1-beta)s.

Equations (5),(9) give c+(49/60)s<5/6. Concavity of
c+(49/60)sqrt(1-c^2) on [1/10,1] excludes that whole interval:
its endpoint values are greater than 5/6, with reserve at the
first endpoint at least 451/6000. Thus c<1/10 and s>99/100.
But (e_L)_y=A s+B c>s/d>297/305>sqrt(3)/2, contrary to (8).

For aligned X choose v=(-s,-c), and put t=1-beta in [0,1].
Then a=-d c-t s. If c<=1/2, (8) is again contradicted.
If c>1/2, (5) gives c<5/(6d)<5/6. Compare the actual centers
of V and L directly:

    |(c_V-c_L)_x|=(1-c)/2+t s
                   <4/3-(d+1/2)c,
    |(c_V-c_L)_y|=(d+1/2)s-alpha-1/2
                   <(d+1/2)s-1/2.                  (10)

The y expression is positive since s>1/2, d+1/2>3/2 and
alpha<1/60. Put rho=d+1/2<91/60. Their squared distance is
therefore less than

    rho^2+73/36-rho[(8/3)c+s]
       <=rho^2+73/36-rho[4/3+sqrt(3)/2]
       <2481/2500<1.                                (11)

The middle inequality follows because (8/3)c+sqrt(1-c^2)
is increasing on [1/2,5/6]. The last upper bound is increasing
in rho on [3/2,91/60], and uses sqrt(3)/2>433/500.
This is another contradiction between two actual unit centers.

The case u_x=0 has (e_L)_y>60/61 in the tilted case and equals
one in the aligned case, also excluded by (8).
We have proved u_x,u_y>0.

For tilted X the clockwise choice v=(s,-c) would make the actual
leaf vertex its highest vertex. Touching U would give
d(e_L)_y>=h>1 and contradict (8). For aligned X choose the
counterclockwise v. Thus the complete surviving actual chart is

    u=(c,s), v=(-s,c), c,s>0, c^2+s^2=1,
    X=[delta,1+delta]u+[-beta,1-beta]v.                (12)

Its leftmost vertex is

    N=delta*u+(1-beta)*v=(a,z),
    alpha<=z<=h.                                    (13)

In the tilted case (8) implies s<19/20: otherwise c<1/3 and

    (e_L)_y >= (s-beta c)/d
             >160/183>sqrt(3)/2.

In the aligned case s=(e_L)_y<sqrt(3)/2 already. Uniformly,

    s<19/20, c>3/10.                                (14)

All signs, axes and the aligned slider endpoints were covered
before choosing this chart.

## 5. Parallel X and exterior aligned concurrence are impossible

If X's two original cycle directions are parallel, the genuine-leaf
lemma says both are -e_L and their two actual applications lie on
the same unit inner side. Their vertical separation is at least
h-alpha=1. The side length is one, so both comparisons are equality:
the side is vertical and the applications are its two endpoints at
heights alpha,h. Thus e_L is horizontal. But the actual radial
leaf application d e_L has height zero and belongs to X's parallel
far side, whose entire vertical interval is [alpha,h]. This is
impossible because alpha>0. Hence the X pair is nonparallel.

The full genuine-leaf lemma gives positive proper q_X. In the tilted
case it lies in X. For aligned X it is tau*u, tau>=epsilon.
Suppose tau>d. Its only two nonleaf applications are the two near
vertices S=epsilon*u-beta*v and N=S+v. The upper one N must be
the U application, and the lower one S the H application, by
their vertical separation. Thus N belongs to U and V and z=h.

Consider first a nonparallel U pair. Its full conditional loaded
degree-two concurrence theorem, with no boundary-neighbor premise,
gives

    q_U=(m,h)+ell*e_y, ell>=0,
    q_U=r G_U, r>0.                                 (15)

The full U equation makes the X->U normal have negative horizontal
component, since G_U has x-coordinate m/r<0.

If m<a, the two distinct points (m,h),N=(a,h) lie in U's minimum-y
face, so U is axis-aligned. Its actual minimum for a vector with
negative horizontal component must have x equal to its right endpoint.
Thus N is that endpoint and (c_U)_x=a-1/2<epsilon-1/2<-3/20,
contrary to (4).

If m=a, the two original U applications coincide at N. Their
nonparallel concurrence is N, a noncircle vertex because N belongs
to the physically clear X. The complete coincident-vertex fact in
ROOTED_ORIGIN_ROOT_PARALLEL_LEAF_SIDE_CHANNEL_EXCLUSION.md Section 3
then makes its radius R-sqrt(2)<7/10. This contradicts N_y=h>1.
If that point were in a side interior, the two normals would instead
be parallel, so this does not miss a side-mean endpoint.

The U-parallel alternative has both outward directions -e_y:
opposite directions are impossible because its two neighbors X,V
physically touch. Its X->U normal is then e_y. But the positive
proper direction from q_X to N has horizontal coordinate

    -(tau-epsilon)c-(1-beta)s<0,

and cannot equal e_y. Thus this alternative also excludes tau>d.

We have proved q_X belongs to X in every surviving case.

## 6. The actual X ports and the uniform small slider

If U's pair is parallel, its opposite alternative is excluded by
the touching neighbors X,V. Its same-sign alternative is radial S
or D with minimum height h. The D height R-sqrt(2)<7/10 is impossible.
Thus this case already has the theorem's physical radial-S conclusion.
For the remaining proof assume the U pair is nonparallel and retain
(15). Put n for the original X->U normal. The full U equation is

    G_U=gamma*e_y+nu*n, gamma,nu>0.

By (6),(15), n_x<0.

For aligned X, the full transverse X equation says its two original
normal v-components have opposite strict signs. If the H normal
had positive v-component, the U normal would have negative
v-component. Every available U application would then lie on the
bottom own face (the far leaf corner is forbidden), with global
height at most d*s<d*sqrt(3)/2<1. It cannot touch U. A zero
v-component would make both directions parallel. Hence the H
normal has negative v-component. Its negative actual support,
because H contains O openly, places the H application at S.
If the proper length there is positive, write q_X=(epsilon+A)u.
Then

    beta^2<epsilon*A<=epsilon, 0<=A<=1.

If that length vanishes, q_X=S and beta=0. Thus this entire
coincident endpoint is included, and in all aligned cases
beta<2/15<11/60.

In the tilted case beta<11/60 is already part of (9).
The near-upper vertex has height

    N_y>= (1-beta)c>49/200>alpha.

It and the far-upper vertex cannot be H applications. The far
own side and bottom own side have nonnegative support; the leaf
corner is forbidden. Therefore H uses the near own side or S.
Its own v-component is nonpositive. The full genuine X equation
then makes n.v strictly positive in the tilted case too.

The only remaining U features are N, the top own side, or the
far-upper vertex

    W=(1+delta)u+(1-beta)v=N+u.                       (16)

N itself is impossible by exactly the minimum-face/coincident
argument in Section 5; that argument uses only (15), n_x<0 and
the actual point N in the V side. Therefore U uses the top own
side or W. In particular n_y>0 and

    n_y/(-n_x)>=c/s.                                 (17)

For W this follows by writing n=a0*u+b0*v with a0>=0,b0>0
and expanding the difference of the two ratios. For the top side
n=v and equality holds. Every U application R now has R_x>a>=m.

## 7. The complete U minimum-feature cover

If U is axis-aligned, n_x<0,n_y>0 makes R its bottom-right corner,
denoted E. Its minimum-y application (m,h) is its original arbitrary
side mean; it is not assigned to the left endpoint.

Otherwise its unique bottom vertex is P=(m,h). There are two
tilt signs. In the sign with inward edges (-C,S),(S,C), both
have strictly positive dot product with n: (17),(14) give

    n_y/(-n_x)>6/19>10/99>S/C.

Then its minimum-n feature is P itself, contradicting R_x>m.
Consequently the only surviving tilted frame has inward edges

    w=(C,S), zeta=(-S,C), S>0,
    R=P+t*w, 0<t<=1.                                (18)

The actual normal has positive dot product with zeta. Thus (18)
includes the full side mean when n.w=0 and the endpoint P+w
when n.w<0. No other U feature remains.

### 7.1. If X uses its top side, R is the bottom-right U vertex

Write R=N+r*u, 0<r<=1, n=v. If n.w=0 in (18), then w=u.
The relations P=R-t*w, P_y=h>=N_y and P_x=m<=N_x imply
r=t and P=N. But then

    (c_U)_x=N_x+(c-s)/2>-s+(c-s)/2
               >-1/10+(99/100-1/10)/2
               =69/200>3/20,

because s=S<1/10 and N_x=delta*c-(1-beta)s>-s.
This contradicts (4). Therefore n.w<0 and t=1.
In the axial case R is already the bottom-right corner.

In either case

    R_x>69/200.                                      (19)

If s>=3/5, the maximum X coordinate on its top side is at W and

    W_x<(61/60)c-(49/60)s
        <=(61/60)(4/5)-(49/60)(3/5)
        =97/300<69/200.

This contradicts (19). Hence s<3/5 in the entire top-side case.

### 7.2. If X uses W, again s<3/5

Equation (18), or the axial case, gives

    W_y<=h+S<d+1/10<67/60.

But W_y>s+(49/60)c. On 3/5<=s<=19/20 this latter concave
function has minimum at an endpoint. At s=3/5 its excess above
67/60 is 41/300. At s=19/20, c>3/10 gives excess greater than
47/600. The whole interval is impossible. Thus also here

    s<3/5, c>4/5.                                   (20)

No circle weight or proper length at U has been discarded.

## 8. Every unique-circle mask of U is impossible

For the tilted frame (18), write its two own coordinates at P.
The zeta coordinate is

    P.zeta=-m*S+h*C>0.

Thus each farthest corner contains its full zeta increment.
There are exactly three physical possibilities: the unique corner
P+zeta, the unique corner P+w+zeta, or equality of those two
corners. The last equality is precisely physical radial S.

The unique P+w+zeta corner has positive x-coordinate. Indeed (4)
and the center formula imply m>-13/20, while C-S>89/100, so
that corner's x-coordinate exceeds 6/25. Its positive circle
resultant cannot have the negative x-coordinate required by (15).

For the unique P+zeta corner, positive radial concurrence and m<0
give

    q_U = [m/(m-S)]*(P+zeta),
    0<m/(m-S)<1,
    (q_U)_y<h+C<h+1.                                (21)

In the axial case, positive-circle x-coordinate would likewise
contradict m<0. A unique upper-left circle corner has x-coordinate
at most m<0, since m remains in the actual bottom side. Its
positive radial multiple therefore also satisfies

    (q_U)_y<=h+1.                                    (22)

These comparisons concern physically unique circle masks. A physical
two-corner mask with one zero individual weight remains in the
two-corner alternative and is not silently reassigned here.

If X uses W, then R_x-m>=W_x-N_x=c, R_y>=h and (17),(20) give

    (q_U)_y=R_y+(R_x-m)*n_y/(-n_x)
             >=h+c^2/s>h+16/15>h+1.                 (23)

This contradicts (21) or (22).

If X uses its top side and U is tilted, Section 7.1 gives R=P+w.
Therefore

    (q_U)_y=h+S+C*c/s
             >h+(99/100)(4/3)>h+1.                 (24)

If U is axial, its actual bottom-right corner E has E_x>7/20,
while

    m<=a=N_x=delta*c-(1-beta)s
              <(1/60)c-(49/60)s.

Using (20), the actual uncentered channel mean satisfies

    (E_x-m)*c/s
       >c[49/60+(7/20-c/60)/s]
       >(4/5)[49/60+5/9]
       =247/225>1.

Again (15) gives (q_U)_y>h+1, contrary to (22).

These cover every possible unique-circle U. Thus U necessarily
has the two adjacent far-side circle corners. This proves the
physical radial-S conclusion with its full original circle weights
and actual lower-edge means retained.

## 9. Exact surviving original scope

The surviving U may have parallel or nonparallel original pair
forces. In the tilted case its actual bottom vertex is

    P=d*zeta-(1/2)*w,
    h=d*C-S/2=1+alpha>1,
    m=-d*S-C/2.

In the axial physical-S case h=d, but m is still an arbitrary
actual bottom-side mean in [-1/2,1/2], constrained by m<0 and
m<=a. It is not replaced by -1/2.

The X concurrence remains inside its own square, all original
X/U/V equations remain, and H keeps its entire other positive star.
The real X leaf and the physical radial-S U are distinct actual
units. No force on XV is asserted.

For the intended genuine-terminal-Q0 plus decorated-C4 caller,
the already established full origin theorem supplies H open and
the same canonical pose. The present source reduces its entire
U-loaded/V-unloaded row exactly as stated; it does not close the
remaining physical radial-S U masks, does not assert any pressure
sign for that branch, and does not alter the whole C2.44.b1 or
C2.44.b2 status.

