# Adjacent mixed leaves in the two-load four-cycle are impossible

Date: October 27, 2026.

**Status: complete hand original-family proof, submitted for full root
and separate independent review.** No coarse or fine status is changed
here. The compatible finite owner selection in Section 4 is stated at
its actual local scope, before extraction of the necessary certificate.

Keep all nine original physical unit squares and the common compatible
radius/Phi-minimizer and minimum-positive-original-scalar-atom certificate,
with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,       r=R-sqrt(2).

The exact positive component is A--B--C--D--A, with a genuine D leaf
L at A and a genuine S leaf M at B. C and D have positive total circle
loads. The genuine degrees are A3,B3,C2,D2,L1,M1. All original normals,
force magnitudes, real application means, physical circle masks and
individual zero weights remain, as do the other three arbitrary units.

**Theorem.** The entire original fine family

    M6.B4L2.C4.ADJACENT.LCD.SD

is impossible. The reflection interchanging A,B and C,D identifies
the two mixed orders for this double-load representative. No such
identification is made for a single-load representative.

## 1. The genuine D root and the nonzero cycle moment

If d<=1, the actual D root A contains O openly and the actual S root B
contains O closed. The two physical interiors would overlap. Hence
assume d>1 and put epsilon=d-1. The exact bounds used below are

    0<epsilon<1/60,       d<61/60,
    1/2<r<2/3,           37/110<s=1-r<1/2.

For the sharper lower bound on s, use
R<187/90 and sqrt(2)>140/99, giving
s>1+140/99-187/90=37/110. These comparisons follow by squaring
positive rationals against R^2<=1105/256 and 2 respectively.

Orient the unchanged actual D leaf east. Its root and real leaf are

    A=[-s,r] times [-b,h],       b+h=1, b,h>0,
    p_AL=(r,0),                n_AL=e_x,
    L has vertices (r,0), (r+sigma,sigma), (R,0),
                   (r+sigma,-sigma),       sigma=1/sqrt(2).

The genuine S root B contains its real point epsilon e_M. Both horizontal
origin margins of A exceed epsilon. Since B cannot meet int(A), one
vertical margin is at most epsilon. Reflect vertically to obtain

    0<h<=epsilon,       b>=1-epsilon>59/60.              (1)

Let n be the actual A-to-B unit normal and m the actual A-to-D one.
The genuine B point gives the actual support inequality

    h_A(n)<=n.(epsilon e_M)<=epsilon.                  (2)

Thus |n_x|<epsilon/s<1/20. Its y component is positive: otherwise
the bottom margin b>59/60 and |n_y|>19/20 would contradict (2).
The force-free D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md applies to
the actual physical boundary D and gives m_y<=0. The full A3 vertical
equation makes this strict:

    n_y>0,       m_y<0.                                (3)

The actual cycle has a nonzero, correctly oriented origin moment.
Here are the complete routing and torque details. Use the compatible
occupied center/contact embedding, keep the actual A--L access, and
add physical circle access strands through C and D. The A--L strand
and the C,D strands leave the Jordan cycle on its exterior side. An
occupied strand cannot cross the cycle later, and its circle endpoint
cannot be in the bounded face of a loop contained in the disk. Cutting
at the genuine leaf access preserves the order of these strands on
the circle, including the compatible small-junction limits.

At A the upward B port precedes the downward D port counterclockwise,
cut at the unshareable actual leaf point (r,0). Consequently C to D
has the counterclockwise minor boundary-pair order. The genuine L
lies on the opposite arc, and a boundary pair's minor arc cannot skip
it, by CIRCLE_CONTACT_ANGULAR_ORDER.md. This is precisely the occupied
cycle order argument in D_LEAF_BOUNDARY_ROOTS_CYCLE_EDGE_EXCLUSION.md,
Sections 2--3; it uses no boundary status at B. B's additional real
leaf also remains an exterior strand and cannot reverse the order.

Orient the actual cycle A to B to C to D to A. At every vertex its
two directed edge moments agree. The original circle forces at C,D
are radial, and the additional genuine leaf forces at A,B have zero
origin moment. Thus the four actual positive-magnitude directed edge
moments have one common value. The unchanged physical boundary edge
C--D makes this value strictly positive, by
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1. In particular

    det(p_AB,n)>0,       det(p_AD,m)<0.                 (4)

All application means are the actual ones. No true B3 equation has
been replaced by a transmitter equation.

## 2. A positive intercept greater than one quarter

Define the actual radial-line intercept

    kappa=det(p_AB,n)/n_y>0.                           (5)

If n were northwest, its A application would be (-s,h), giving

    kappa=-s+h |n_x|/n_y
          <-1/3+1/1140<0.

This contradicts (5). Thus n is north or strictly northeast. In the
north case p_AB=(kappa,h), with its unchanged actual side mean; in
the northeast case p_AB=(r,h) and kappa=r-h n_x/n_y. Hence

    0<kappa<=r.                                        (6)

The complete A3 horizontal equation, including the positive east leaf,
now forces m_x<0. Its actual A point is (-s,-b). The vertical equation
and the zero origin torque together say that the two actual pair lines
have the same x-axis intercept kappa. Write m=(-c_D,-t_D). Then

    c_D,t_D>0,
    c_D/t_D=(kappa+s)/b,
    g_D=p_AD.m=(s(kappa+s)+b^2)/sqrt((kappa+s)^2+b^2).

The actual contained unit D lies beyond its minimum-m support g_D.
Every unit's directional width is at least one, while its center norm
is at most d+1/2. Therefore g_D<=d; this is a physical support bound,
not a changed equation at D.

Put

    G(s,b,k)=(s(k+s)+b^2)/sqrt((k+s)^2+b^2).

For positive s,b,k, G increases strictly in s and b and decreases
strictly in k. Differentiation gives positive numerators
(k+s)^3+s b^2 and b(2(k+s)^2-s(k+s)+b^2) for the first two
derivatives, and numerator -k b^2 for the third.

Using (1), if kappa<=1/4 we would have

    g_D>G(37/110,59/60,1/4)>61/60>d.

The middle exact squared comparison is

    [s_0(k_0+s_0)+b_0^2]^2
      -(61/60)^2[(k_0+s_0)^2+b_0^2]
       =6101297/12649824000>0,
    (s_0,b_0,k_0)=(37/110,59/60,1/4).

We have proved the uniform strict bound

    1/4<kappa<=r<2/3.                                 (7)

One further consequence will be needed only in the final tilted case:

    kappa<29/100  implies  h>1/110.                    (8)

Otherwise b>=109/110 and monotonicity would give
g_D>G(37/110,109/110,29/100)>61/60. Its exact positive squared
reserve is 970619263/527076000000. Both (7) and (8) therefore follow
from the actual boundary-side support, with no numerical certificate.

## 3. A small upper support cannot belong to a boundary unit

We record a purely physical estimate. Let a unit T lie below y=z,
where 0<=z<=1/60, and contain the actual supporting point P=(x,z)
with |x|<4/5. Then every corner of T has squared norm below

    106/25<17/4.                                      (9)

If its maximum-y support is a side, T is aligned. Its corner horizontal
coordinates have absolute value less than 9/5 and its vertical ones
have absolute value at most one, proving (9). This includes side means
and endpoint applications.

If that support is a vertex P, both inward orthogonal sides point
downwards. Adjacent corners have norm at most |P|+1<19/10. The opposite
corner is P+(Delta,-Sigma), where |Delta|<=1,
Sigma=sqrt(2-Delta^2)>=1. Its squared norm is at most

    x^2+z^2+2+2|x|-2z
      <=x^2+2+2|x|<106/25.

Thus no such T physically reaches the circle in the present high
radius interval R^2>17/4. This estimate is rotation-invariant.

## 4. Every strict northeast A-to-B contact is impossible

We first state exactly the compatible owner selection used here.
At a genuine radial-leaf root with precisely two other positive forces,
distinct singleton applications P,Q, and leaf direction e, the original
force and torque equations imply

    det(e,n)det(Q,m)-det(e,m)det(P,n)=0.                (10)

If n is a free point normal, m is nonparallel to e, and P is not on
the radial line through e, the expression is det(W,n), with
W=det(Q,m)e-det(e,m)P nonzero. Thus it excludes finitely many directions
in that actual open strict normal interval. If both contacts are free,
their distinct physical junction parameters are independent, and the
same expression is not identically zero on their product. Include all
these finitely many physical assignments before extraction, together
with the existing strict/nonradial/matched-junction requirements, as
in RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md, Section 3.
Uncrossing preserves surviving point normals and adds only shared-side
forces; thinning only deletes atoms. No selected force or mean is
subsequently changed. This local argument requires no degree or load
condition at the other endpoints; its full statement also appears in
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md, Section 4.

Here, when n is strictly northeast, the actual A points are (r,h) and
(-s,-b), at nonzero distinct heights. Both nonleaf normals have nonzero
y components. Hence (10) excludes a free AB normal. The compatible
strict convention excludes an owned-axis endpoint at a vertex/vertex
contact as well. The actual AB point is therefore in a relative side
interior of B, and n is an actual B side axis.

Write n=(u,v), k=(-v,u), and P=(r,h). Its actual B frame is

    B=P+[0,1]n+[-rho,1-rho]k,       0<rho<1.

The support (2) gives

    0<u<1/30,       v>29/30,
    g=P.n=r u+h v<=epsilon,
    t=P.k=-r v+h u<-2/5.                              (11)

The real D leaf supplies a second physical restriction. The actual
segment P-lambda k enters that leaf after crossing its inner upper
edge at lambda=h/(u+v), at positive height below sigma. Consequently

    rho<=h/(u+v)<1/60.                                (12)

The two k coordinates of B's near and far n sides are t-rho and
t+1-rho. The first is strictly between -7/10 and -2/5; the second
is strictly between 3/10 and 3/5. The n coordinate on its near side
is 0<g<=epsilon. Thus both near vertices have norm less than one,
whereas both far vertices have squared norm greater than
1+(3/10)^2>d^2. None can be B's genuine S application d e_M.

The supports in the two k-axis directions have magnitude below 7/10,
and the support in -n is negative. The only possible genuine S direction
is therefore n itself, with

    e_M=n,       g=epsilon.                            (13)

Keep the full B3 equation. Its BA force points -n and its genuine
leaf force points n, so BC is parallel to n. If BC pointed n, the
actual C would lie beyond support d and the sharp contained-unit
equality theorem would identify it with the genuine S square M.
Those are distinct original units, so BC points -n.

The radial leaf has zero origin moment. Since the original BA point
has k coordinate t<0, the unchanged BC mean has k coordinate t_C>0.
It is on B's near n side and satisfies

    0<t_C<=t+1-rho<3/5.

The actual C lies below n.z=epsilon and contains
epsilon n+t_C k. Section 3 excludes its physical circle contact.
This handles every strict northeast case.

## 5. A north contact with an aligned B is impossible

It remains n=e_y and P=p_AB=(kappa,h). First let B's minimum-y support
be a side, including either application endpoint. Write

    B=[x,x+1] times [h,h+1].

Its genuine near point gives x<=epsilon, while P in B and (7) give
x>=kappa-1>-3/4 and x+1>=kappa>1/4. Disjointness from the actual
D leaf forces x+1<=r+h: otherwise a height just above h produces
an open overlap with that leaf's upper inner interval. Therefore

    -3/4<x<-3/10,       1/4<x+1<7/10.                 (14)

Its bottom vertices have norm below one. Both top vertices have
squared norm greater than 1+1/16>d^2. Its horizontal supports have
magnitude below 3/4, and its south support is negative. The genuine
S leaf is therefore north, and h+1=d, so h=epsilon.

Exactly as in Section 4, the complete B3 force equation makes BC
south: the north alternative would duplicate its actual leaf M.
If x_C is the unchanged BC mean's x coordinate, the real B torque is

    mu kappa+nu x_C=0,       mu,nu>0.

Hence -3/4<x_C<0. The actual C lies below y=epsilon and contains
(x_C,epsilon). Section 3 again contradicts its circle contact.

## 6. A north contact with a tilted B forces one exact remaining star

Now B's minimum-y support is the actual vertex P=(kappa,h). Its
unchanged inward frame has the form

    B=P+[0,1]u+[0,1]v,
    u=(-c,t),       v=(t,c),
    c,t>0,          c^2+t^2=1.                         (15)

Every zero-angle endpoint was included in Section 5. Because B meets
D_epsilon, some actual point P+lambda u+eta v has both coordinates
at most epsilon. Its x coordinate gives lambda c>=kappa-epsilon,
and its y coordinate gives h+lambda t<=epsilon. Consequently

    t/c<1/14,       c>99/100.                          (16)

The four genuine S-application vertices are all impossible. P has
norm below one. The other lower vertex

    Q=P+u=(kappa-c,h+t)

also has norm below one, since |kappa-c|<3/4 and
h+t<1/60+1/14. The upper-right vertex P+v has x>1/4 and y>99/100.
The upper-left vertex P+u+v has x<-1/4, because

    kappa-c+t<2/3-99/100+1/14=-529/2100<-1/4,

and it too has y>99/100. Both upper vertices therefore have squared
norm greater than 5213/5000>(61/60)^2>d^2.

Put tau=kappa c-h t. Equations (7),(16) give

    1/5<tau<2/3,       tau>t/c.                         (17)

The two u-axis supports of B are 1-tau<1 and tau<1, and its -v
support is negative. Thus the only possible genuine S direction is
the actual own axis v. The actual leaf support and point are

    kappa t+h c=epsilon,
    e_M=v,       p_BM=d v=P+tau u+v.                   (18)

In particular t<epsilon/kappa<1/15. Nothing about C's circle mask
has been used in this complete B feature cover.

Let mu>0 be the original BA magnitude and alpha>0 the genuine leaf
magnitude at B. The full force toward C is

    mu e_y-alpha v=mu t u+(mu c-alpha)v.               (19)

Its u component is strictly positive. Its v component cannot be
nonnegative. If it were positive, the actual B port would be P+u+v;
the original moment about P would give

    alpha/mu=(c-t)/(1-tau)<=c,

which implies tau<=t/c, contrary to (17). If that component were
zero, the actual port would be P+u+lambda v with its unchanged
lambda in [0,1]. The same moment equation would give
lambda=c tau/t>1. This also excludes both side-mean endpoints.

Hence the actual BC port is exactly Q=P+u. Moment about P now gives

    alpha/mu=c/(1-tau).

Write the unchanged unit normal from B into C as (-a,-b_C).
Both components are strictly negative in (19), and their exact ratio is

    a/b_C=c t/(tau-t^2),       a,b_C>0,
    a^2+b_C^2=1.                                       (20)

These are the full B3 equations with its actual leaf force retained.

## 7. Every possible C frame at that port stays inside the circle

Write Q=(-X,Y), with

    X=c-kappa,       Y=h+t.

In all remaining cases X>97/300>Y>0. We bound the actual normal (20)
in two intervals, using (8) precisely where necessary.

If kappa>=29/100, then

    X<71/100,       t<5/87,       Y<3/40,
    tau-t^2>2871/10000-1/900-1/225=25339/90000.

Thus a/b_C<150000/734831<21/100, and a+b_C<6/5.
The last comparison follows exactly by squaring
(1+21/100)/sqrt(1+(21/100)^2)<6/5.

If kappa<29/100, (8) gives h>1/110. Together with (18) and c>99/100,
this gives

    t<4(1/60-99/11000)=23/750,
    X<3/4,       Y<1/20,
    tau-t^2>99/400-23/45000-529/562500
              =553609/2250000>8(23/750).

Consequently a/b_C<1/8, and
a+b_C<9/sqrt(65)<28/25. All these inequalities have strict rational
reserves; in particular the denominator reserve above is
1609/2250000.

We finish with a physical all-frame estimate, so no generic owner or
private circle-resultant restriction is needed at C. Let

    n_C=(-a,-b_C),       k_C=(-b_C,a).

Here a<b_C and X>Y>0, so

    Q.k_C=X b_C+Y a>|Q.n_C|.

If Q is a vertex of C, its inward opposite-vertex diagonal has length
sqrt(2) and angle at most pi/4 from n_C. The last displayed strict
inequality makes its scalar product with Q largest at the endpoint
diagonal n_C+k_C. Every adjacent corner has norm at most |Q|+1<19/10.
If instead the minimum-n_C support is a side, every near-side corner
has that same bound. The far-side corners are Q+n_C+lambda k_C,
with -1<=lambda<=1. Convexity in lambda and Q.k_C>0 make their
squared norm no larger than the value at lambda=1. This also includes
all side endpoints and every original shared mean.

In both physical owner cases the only possible farthest corner thus
has squared norm at most

    E=X^2+Y^2+2+2X(a+b_C)+2Y(a-b_C)
       <X^2+Y^2+2+2X(a+b_C).                          (21)

For kappa>=29/100, the first set of bounds yields

    E<(71/100)^2+(3/40)^2+2+2(71/100)(6/5)
       =168549/40000<17/4.

For kappa<29/100, the second set yields

    E<9/16+1/400+2+(3/2)(28/25)
       =849/200<17/4.

The strict reserves from 17/4 are respectively 1451/40000 and 1/200.
Every actual C corner therefore has norm strictly below R. This
contradicts the original physical boundary C, completing Section 6
and the proof.

## 8. Exact original-family scope

The low and critical intervals were excluded by the two genuine roots'
physical overlap. At high radius, Sections 1--2 retain the actual cycle
and its real radial leaf moments to establish the positive intercept.
Sections 4--7 exhaust the northeast and north contacts, the aligned and
tilted B frames, every actual leaf support, and every owner or shared
mean at C. Thus the whole double-load mixed family is excluded.

The true C2/D2 positive circle loads were used only as their original
physical boundary facts and to transport the original radial moments.
The genuine A3/B3 equations retain both actual leaf forces. The common
selection is imposed before extraction, never by altering a surviving
normal. All six component units and all three arbitrary original extras
remain throughout, including every physical circle mask and individual
zero weight. The separate high S/S family is not claimed closed here.

No numerical pose, altered force, replacement mean, Lean compilation,
CI, remote mutation or shared-ledger edit is used.
