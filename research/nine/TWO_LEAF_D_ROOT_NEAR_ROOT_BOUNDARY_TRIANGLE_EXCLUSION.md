# A D-leaf root and a near-origin neighbor have no boundary common neighbor

Date: October 27, 2026.

**Status: accepted complete hand proof at its stated original scope; full root and separate independent source/scope reviews passed.**

Accepted reviews: REVIEW_D_ROOT_NEAR_ROOT_BOUNDARY_TRIANGLE_TRIANGLE_BRIDGES_2026_10_27.md and
REVIEW_NEAR_ORIGIN_AND_ATTACHMENT_CLOSURES_ROOT_2026_10_27.md.
Their mathematical-source pins precede this acceptance-only header update. No central ledger
or original checkbox is changed here.

Keep the original nine physical unit squares, the common compatible
selected certificate, and the full radius window

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),             s=1-r.

Let H have a genuine positive D leaf L. Let K be a distinct actual
unit meeting the closed disk D_epsilon, with an actual positive H-K
contact. Suppose a third unit T, different from H,K,L, physically
touches the containing circle and has an actual positive H-T contact
and a physical K-T contact.

**Theorem.** This configuration is impossible.

H and K keep arbitrary true positive degrees and all their other
forces; T also has arbitrary true degree. The conclusion uses no
force equation at these three bodies. The actual H-K and H-T normals
and common application means are retained. The K-T contact may have
zero stress. All masks, individual zero circle weights, other physical
units and additional contacts remain.

This strengthens TWO_LEAF_D_ROOT_NEAR_ROOT_COMMON_BOUNDARY_EXCLUSION.md:
its complete root-neighbor-list premise is unnecessary here. That
earlier reviewed two-gate proof remains valid. The new extension also
excludes the original DH_SB hub/tip sibling with its previously
uncontrolled extra hub force still present.

## 1. Exact D-root chart and the shallow supporting normal

Use the genuine D chart and near-origin reduction in Sections 1--2
of TWO_LEAF_D_ROOT_NEAR_ROOT_COMMON_BOUNDARY_EXCLUSION.md. Every
required physical input is recalled here.

The actual D leaf points east, its inner vertex is (r,0), and

    H=[-s,r] times [a-1,a],           0<a<1,
    O belongs to int H.

If epsilon=0, the distinct K contains O and already overlaps H.
Otherwise, after a vertical reflection if necessary,

    R>sqrt(17)/2>2,
    129/200<r<2/3,
    1/3<s<71/200<3/8,
    0<a<=epsilon<1/60.                                 (1)

The real near-origin point of K is horizontally strictly inside H
and must lie beyond one of its horizontal sides. Reflection chooses
that side to be the top and leaves the D radial axis east.

The actual H-to-K unit normal n satisfies

    0<h_H(n)<=epsilon,
    n_y>4/5,              |n_x|<1/20.                  (2)

If n_y<=0 its support would exceed 1/3. Once n_y>0, the support
is r n_x+a n_y for n_x>=0, or s|n_x|+a n_y for n_x<0. These
exact formulas give (2), without normal reselection. The occupied
D leaf is

    L={ (x,y): |x-r-1/sqrt(2)|+|y|<=1/sqrt(2) }.       (3)

The upper-left H vertex cannot belong to a physical boundary unit:

    |(-s,a)|^2<(3/8)^2+(1/8)^2=5/32<1/4<r^2.         (4)

Every point of a unit with a circle corner has norm at least r.

We also retain the two degree-free physical-triangle facts proved
in Section 2 of the earlier source: an H-owned side normal has
nonnegative scalar product with the other H normal, and two strictly
exposed opposite H vertices cannot be the contacts when their
neighbors physically touch. These facts retain actual support
features and every common side mean.

## 2. No other boundary unit touches the shallow top or upper right strip

**Lemma.** No physical boundary unit E distinct from H and L can
contain a point Q of either set

    [-s,r] times {a},       {r} times [0,a].             (5)

Since E is boundary, |Q|>=r. For Q=(x,a) on the top, (4) rules
out x<=0, so x>0. Then

    0<=r-x=(r^2-x^2)/(r+x)<=a^2/(r+x)<2a^2.

On the second set in (5), the displacement from (r,0) is at most a.
Thus in both cases

    |Q-(r,0)|<a+2a^2<31/1800<1/30.                   (6)

Let z be any actual circle corner of E. Its unit diameter gives
|z-Q|<=sqrt(2). If theta is the smaller angle from e_x to z, then
(R-r)^2=2 and (6) give

    2Rr(1-cos(theta))
       =|z-(r,0)|^2-2
       <(sqrt(2)+1/30)^2-2
       <91/900.

Since R>2 and r>3/5,

    1-cos(theta)<91/2160<1/20,
    cos(theta)>19/20,
    theta<pi/9.                                       (7)

The last comparison is exact: beta=arccos(19/20) has
cos(3beta)=1159/2000>1/2 and 0<3beta<pi, so beta<pi/9.

We record an elementary actual circle-corner/center bound. Let phi in
[0,pi/4] be the angle of a boundary unit center from its first own
axis, after reflection. Every actual farthest circle corner has acute
angular deviation eta from the center satisfying

    tan(eta)^2
      =(1-sin(2phi))/(4R^2-1+sin(2phi))
      <=1/(4R^2-1)<1/16.

This follows by writing z=c+(u+v)/2 and using the original circle
equation. When c is on an own axis, either of its two actual circle
corners has the same absolute deviation. Thus both physical masks
and every force-weight endpoint are included. Since
tan(pi/12)=2-sqrt(3)>1/4, the deviation is less than pi/12.

The actual D-leaf center direction is e_x. Consequently the E and L
center directions have minor separation strictly below

    pi/9+pi/12=7pi/36<pi/5.

This contradicts the complete physical boundary-center separation
in CIRCLE_CONTACT_ANGULAR_ORDER.md, Lemma 2.1, independently of their
circle weights. The lemma is proved.

## 3. A left-side return to the near-root half-plane cannot reach the circle

Suppose n=(-t,k), with 0<=t<1/20, k>4/5 and t^2+k^2=1. Then

    K subset {-t x+k y>=ts+ka}.                        (8)

We prove that no boundary common neighbor T can have outward H
normal -e_x. Its actual rightmost support is x=-s, with a genuine
H contact at a height in [a-1,a]. Its full physical square has form

    T=(-s,b)+[0,1]w+[0,1]z,
    w=(-alpha,beta), z=(-beta,-alpha),
    alpha>=0, beta>0, alpha^2+beta^2=1,
    b<=a.                                              (9)

For a tilted T, (-s,b) is its actual rightmost vertex. For a vertically
sided T take alpha=0,beta=1 and b the actual lower endpoint of its
right side. That endpoint need not be the selected H mean: the real
mean remains on the whole original shared segment, and b<=a follows
only from existence of that genuine contact.

As T touches K, (8)--(9) imply

    k b+t alpha+k beta+max(t beta-k alpha,0)>=ka.

Hence

    a-beta-eta<=b<=a,
    eta=(t/k)alpha+max((t/k)beta-alpha,0),
    0<=eta<3/32,                                      (10)

where eta<=(t/k)(alpha+beta)<(1/20)(5/4)(3/2)=3/32.
The full actual side position b is retained.

Put w_0=alpha+beta<=sqrt(2)<3/2. The exact identity

    13/8-alpha^2-2alpha beta
       =(5/8)(alpha-8beta/5)^2+beta^2/40>0

and its exchanged version give

    w_0^2+alpha^2<21/8,       w_0^2+beta^2<21/8.        (11)

At both reference positions b=a and b=a-beta, every vertex of (9)
has squared norm at most

    B_0=s^2+a^2+2s w_0+21/8
        <249/64+1/3600.                                (12)

Here is the complete check. At b=a-beta the four ordinates are
a-beta, a, a-alpha-beta, a-alpha. The first two squared norms are
bounded by s^2+a^2+1+2s w_0. For the last two use (11), dropping
the nonpositive terms -2a w_0 or -2a alpha. At b=a the first three
squared norms are bounded by s^2+a^2+1+2s w_0+2a. The last equals
s^2+a^2+2+2s w_0+2a(beta-alpha), bounded by B_0 since 2+2a<21/8.
Thus every corner and orientation is covered.

Each squared vertex norm is convex in b. The only additional endpoint
in (10) is b=a-beta-eta, a downward displacement eta<3/32 of the
lower reference square. Every reference ordinate has absolute value
less than 3/2. Such a displacement increases squared norm by less
than 3 eta+eta^2<297/1024. Therefore every point of the actual T
has squared norm strictly less than

    249/64+1/3600+297/1024
       =17/4-15911/230400
       <17/4<R^2.                                     (13)

We used convexity in b and the fact that squared norm on an actual
square is maximized at a vertex. This excludes physical boundary
status throughout the whole left-side return, including t=0 and
every original side mean or slider.

## 4. A right-side return crosses the original D leaf

Suppose n=(t,k), with 0<=t<1/20, k>4/5 and t^2+k^2=1. The actual
K lies in

    t x+k y>=tr+ka.                                    (14)

Let a distinct original unit T contain P=(r,y), a-1<=y<0, and
touch K at an actual point Y. We show that T overlaps H or L.
This statement does not need a boundary premise.

Put X=Y_x-r and eta=t/k<1/8. Equation (14) gives

    Y_y>=a-eta X.                                      (15)

If X<0, the segment P-Y immediately enters int H: it moves left
and strictly upward, since Y_y>a>y. This includes the lower-right
endpoint y=a-1 and contradicts interior disjointness.

If X=0, the vertical segment P-Y contains (r,0) in its relative
interior. This point is in the relative interior of H's right side.
Another square containing that whole local vertical segment must
have the point in a side interior and lie locally to its right,
or it already overlaps H. The right local half-plane overlaps the
open D-leaf sector at (r,0), also a contradiction.

Suppose X>0. Put b=-y, so 0<b<=1-a. Along P-Y the linear function
(x-r)+y changes from -b<0 to X+Y_y>=a+(1-eta)X>0. It crosses
the line of the D leaf's lower-left side at

    (r+v,-v),          v=bX/(b+X+Y_y)>0.

Using (15), monotonicity in b and b<=1-a gives

    v<=bX/[a+b+(1-eta)X]
      <=(1-a)X/[1+(1-eta)X]
      <sqrt(2)/[1+(1-eta)sqrt(2)]
      <1/sqrt(2).                                     (16)

The penultimate bound uses X<=|Y-P|<=sqrt(2), since P,Y are in
the same actual T. The last uses
(1-eta)sqrt(2)>(7/8)(8/7)=1.

Thus the crossing is in the relative interior of the exact diamond's
lower-left side and occurs strictly before Y. Immediately afterwards
the same segment enters int L. The closed T contains those points,
and its interior points approach them, giving forbidden interior
overlap. This excludes every negative-height right-side return.

For a potential boundary T with a right-side contact at 0<=y<=a,
Section 2 applies instead. Thus a physical boundary common neighbor
cannot have any contact on the entire right side under (14).

## 5. Complete actual H-contact feature cover

Let m be the actual outward H-to-T normal of a contrary boundary
common neighbor. Use the physical triangle H,K,T and its complete
side-normal and opposite-vertex facts from Section 1.

### 5.1. n_x>0

The H-K contact is the upper-right vertex. If m_x<0, then m_y>0
uses the forbidden short upper-left vertex (4), m_y=0 is the left
H axis with n.m<0, and m_y<0 uses the strictly opposite lower-left
vertex. Every such feature is excluded.

If m_x=0, the downward axis has n.m<0; the upward axis uses the
shallow top excluded by Section 2. If m_x>0, a positive m_y uses
the upper-right vertex, also excluded by Section 2. Zero m_y is
the right side, and negative m_y uses the lower-right vertex on
that same side. Section 4 excludes both complete possibilities.

### 5.2. n_x=0

Now n=e_y is an actual H side axis, so the triangle fact gives
m_y>=0. If m_y>0, its H contact lies on the shallow top, including
both upper vertices, and Section 2 excludes it. If m_y=0, the
contact is on the left or right side. Sections 3--4 with t=0
exclude both whole possibilities.

### 5.3. n_x<0

The H-K contact is the upper-left vertex. If m_y>0, its H contact
lies on the shallow top and Section 2 excludes it. If m_y=0,
the right H axis has n.m<0, and the left H axis is excluded by
Section 3.

If m_y<0, positive m_x gives the strictly opposite lower-right
vertex, and zero m_x gives the bottom H axis with n.m<0. Negative
m_x is the strict southwest lower-left contact. This is exactly
the whole geometric cap of Section 4 in
TWO_LEAF_D_ROOT_NEAR_ROOT_COMMON_BOUNDARY_EXCLUSION.md: the real
T must span n-height k from (-s,a-1) to its actual K point; its
complete vertex/side feature and original slider place it in
|x|<3/2, |y|<5/4. Hence every point has squared norm less than
61/16<4<R^2, contradicting physical boundary status. That cap
uses no H force equation or complete H-neighbor-list premise.

Every actual n and m, support feature and original side mean is
covered. This proves the geometric theorem with arbitrary true
degrees and all other original forces retained.

## 6. The remaining D-hub/S-tip diamond gate

Use the original diamond hubs H,K and tips B,C, with all five positive
edges HK,HB,HC,KB,KC, in the exact unchanged family

    M6.B4L2.DIAMOND.HUB_TIP.LKC.DH_SB.

H has a genuine D leaf and B a genuine S leaf. The actual S root B
meets D_epsilon. The other actual hub K has true positive degree
three and is loaded by NO_UNLOADED_DIAMOND_HUB.md, with its actual
neighbor contacts HB and HC retained. Equivalently its load is part
of the original complete LKC cover. Thus K is physically boundary
and is a common original positive neighbor of H and B.

Apply the theorem with its near-origin unit equal to B and its
boundary common neighbor equal to K. H keeps true degree four,
including its actual force to the additional private tip C; no
H equation is used. K keeps true degree three and all its original
forces. The other genuine leaf, private tip and all three arbitrary
completion squares remain occupied.

This excludes the whole DH_SB family, including every physical mask,
individual zero-weight endpoint, common mean, genuine D side-interior
slider, root orientation and force ratio. It is one new original
child closure after independent review, not a new replacement gate.

The same geometric theorem strengthens the SD two-hub and SH_DB
hub/tip exits already supplied by the earlier full-force source.
They must not be counted twice. Together with the earlier distinct-D
root exit, these sources exclude every distinct-root diamond family
having a genuine D leaf. Their SS siblings, the distinct-root C4
families, remaining S/side arms and complete C1.4.b2 parent remain
separate obligations.

No physical motion, smaller degree, omitted force, new normal selection,
artificial circle atom, numerical pose, coefficient packet, secondary
minimizer, Lean compilation, CI or remote action is used.

