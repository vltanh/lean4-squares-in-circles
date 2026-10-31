# The adjacent mixed S/D C4 with both private loads is excluded

Date: October 27, 2026.

**Status: accepted complete whole original-family proof after full
root and separate independent source-and-scope reviews.** See
REVIEW_MIXED_D_ADJACENT_TWO_LOAD_ROOT_2026_10_27.md and
REVIEW_MIXED_D_ADJACENT_TWO_LOAD_MIXED_BLOCKS_2026_10_27.md.
Both pin the complete mathematical source before this acceptance-only
header. The entire original LCD.SD child is covered; no whole layout
or coarse cell closes from this source alone.

Keep the same nine actual interior-disjoint closed unit squares and
the common compatible selected certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, epsilon=max(d-1,0),
    r=R-sqrt(2), s=1-r.

The actual positive cycle is H-K-U-T-H. H has a genuine D leaf L,
K has a genuine S leaf N, and the actual private U and T are loaded.
The true degrees are H3,K3,U2,T2,L1,N1. All three other physical
squares remain occupied and arbitrary. Every physical circle mask,
individual zero corner weight, original normal and shared-side mean,
positive force and zero-stress physical contact remains.

**Theorem.** This entire original configuration is impossible in the
same compatible selection used for the accepted one-private-load
mixed S/D theorem.

The proof uses the original full H3 and K3 equations. It actually
needs only the physical boundary status of U, not a circle equation
or a reduced equation at either U or T. The actual U-T edge and all
its forces remain present throughout. No boundary-neighbor theorem
is applied to a fictitious physical triangle H-K-U or H-K-T.

## 1. The original shallow D root and its full three-force concurrence

Use the genuine D chart and near-root reduction already proved in
D_LEAF_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md and
TWO_LEAF_D_ROOT_NEAR_NEIGHBORS_AND_CHANNELS_EXCLUSION.md. H contains
O openly. K contains O when d<=1, so that entire radius range is
impossible by physical nonoverlap. Reflect vertically if needed. Then

    d=1+epsilon>1, 0<epsilon<1/60,
    H=[-s,r] times [-l,a], l=1-a,
    0<a<=epsilon, 129/200<r<2/3,
    1/3<s<71/200<3/8, 59/60<l<1.                    (1)

The actual D leaf is the unchanged diamond

    L={ (x,y): |x-r-1/sqrt(2)|+|y|<=1/sqrt(2) }.     (2)

Let n be the original H-to-K unit normal, P its actual application,
and m the original H-to-T normal. For their positive magnitudes,
the complete original H equation is

    lambda e_x+mu n+nu m=0, lambda,mu,nu>0.          (3)

Its genuine leaf application is (r,0) and has zero origin moment.
The actual near point of K and O in int H give

    0<h_H(n)<=epsilon, n_y>4/5, |n_x|<1/20.         (4)

In particular P is on the shallow top side or one of its endpoints.
Every possible P has

    |P|^2<=r^2+epsilon^2<4/9+1/3600<(27/40)^2.      (5)

The last difference is 157/14400. Both H and K are physically clear:
their actual points near O have norm below r, the minimum possible
point norm of a physical boundary unit. Also O is outside closed K.

The n and m lines are nonparallel. Otherwise their sum would be
parallel to n, whose vertical component is nonzero, and could not
balance the positive horizontal force in (3). The original H moment
therefore puts their concurrence at q_H=(q,0), where

    n_x>0: q=r-a*n_x/n_y in (r-1/960,r),
    n_x<0: q=-s+a*|n_x|/n_y in (-s,-s+1/960),
    n_x=0: P=(q,a), -s<=q<=r.                       (6)

Thus q_H belongs to the actual closed H. Every H port is proper
from it. In particular m_y<0 by (3). If n_x=0, the same full
equation gives m_x<0, so its actual application is (-s,-l) and

    m=(-s-q,-l)/sqrt((s+q)^2+l^2).                   (7)

No application mean is fixed in deriving (6)--(7).

Every actual contained neighbor of any actual unit X has, along
their original separating normal v,

    h_X(v)<=d.                                      (8)

Indeed every contained unit center has norm at most d+1/2, and
its directional half-width is at least 1/2. The neighbor center
projection is at least h_X(v)+1/2. This proves (8) without a force
or circle-load assumption on that neighbor.

We use precisely the finite D-star selection of Section 1 of the
accepted TWO_LEAF_MIXED_D_ADJACENT_ONE_LOAD_EXCLUSION.md. In a true
D-root H3 star whose two other normals are nonaxis at H, have
opposite nonzero vertical signs, and apply at its two distinct fixed
vertices of heights a and a-1, a point-only vertex/vertex H edge
is excluded. Its avoided determinant is

    n_y det(Q,m)-m_y det(P,n)=0.

The full compatible preselection and distinct-junction argument in
that accepted source require no contact between K and T. The same
prelisted condition already applies here; no new condition or
post-extraction normal change is introduced.

## 2. Two exact support consequences at a vertical H-K contact

Assume n=e_y. Write

    h(q)=[s(s+q)+l^2]/sqrt((s+q)^2+l^2).             (9)

By (7)--(8), h(q)<=d is necessary.

### 2.1. The entire small-concurrence interval is impossible

The exact identity

    h(q)^2=s^2+l^2-q^2*l^2/((s+q)^2+l^2)
            >=s^2+l^2-q^2                          (10)

shows that |q|<=11/60 is impossible. Indeed

    (1/3)^2+(59/60)^2-(11/60)^2-(61/60)^2
       =13/1200>0.                                 (11)

The actual strict bounds in (1) give h(q)>d. This includes q=0
and every zero-length concurrence possibility at the other root.

### 2.2. A positive concurrence must exceed one quarter

For q>=0, h(q) decreases with q, increases with s and increases
with l. Direct differentiation gives, with A=s+q and denominator
(A^2+l^2)^(3/2), the respective numerators

    -q*l^2, A^3+s*l^2, l*(2*A^2-s*A+l^2).           (12)

We have the useful strict bound s>269/800. To check it with exact
window constants, R<8311/4000 since

    (8311/4000)^2-1105/256=10221/16000000>0,

and sqrt(2)>140/99. Consequently

    s>133211/396000=269/800+7/49500.                 (13)

Put s_0=269/800 and l_0=59/60. The exact comparison is

    [s_0*(s_0+1/4)+l_0^2]^2
      -(61/60)^2*[(s_0+1/4)^2+l_0^2]
       =4157748667/11059200000000>0.                (14)

Thus if 0<q<=1/4, (12)--(14) would give h(q)>61/60>d.
Every surviving vertical-H-K case with q>0 therefore has

    q>1/4.                                         (15)

## 3. Two elementary physical support facts, with all side endpoints

### 3.1. An actual inward normal contains a full unit segment

If Q is any minimum-v support point of an actual unit square X,
where v is a unit vector, then

    Q+[0,1]v is contained in X.                     (16)

At a vertex, the two inward own components of v are nonnegative
and at most one, so this entire segment fits within the actual
unit side intervals. At a side-interior point, v is its own inward
axis and there is exactly one unit of room in that direction.
Side endpoints are covered by the same closed statement. A point
of this segment may lie on an actual side; if it lies in the open
interior of another unit, interior approximation still gives open
overlap of the two original squares.

### 3.2. A complete corner cap for a nearly horizontal minimum normal

Use any orthonormal coordinates. Suppose an actual unit X contains
Q=(epsilon,j) as a minimum-w support point, where

    0<epsilon<j<1,
    w=(-c,z), c^2+z^2=1, 0<=z<c.                    (17)

Then every point of X has squared norm at most

    B(epsilon,j,z/c)
      =epsilon^2+j^2+2
         +2[(j-epsilon)c+(j+epsilon)z].             (18)

Here is the full vertex/side proof. Put v=-Jw=(z,c), and write
A=Q dot w=-epsilon*c+j*z, D=Q dot v=epsilon*z+j*c.
Then D>|A| and A>-epsilon. If Q is a vertex, the vector to its
opposite vertex has length sqrt(2) and angle at most pi/4 from w.
Its scalar product with Q increases toward v throughout this
interval, since D>|A|. Its maximum is Q dot(w+v)=A+D, giving
(18). Either adjacent vertex has squared norm at most (|Q|+1)^2.
Since A+D=epsilon*(z-c)+j*(z+c)>=j-epsilon and |Q|<=j+epsilon,
the bound in (18) exceeds this by at least 1-4*epsilon>0.
Q itself is also below that bound.

If Q is on a minimum side, w is an actual own axis and the unit
is Q+[0,1]w+[-theta,1-theta]v, 0<=theta<=1. Convexity in the
second coordinate bounds its corner norms by the choices -1,1.
D>0 selects +1. Adding w increases the squared norm by
1+2A>0, so Q+w+v gives (18) again. This includes a genuine mean
at either side endpoint. No orientation, physical circle mask or
individual corner multiplier is assumed in this cap.

We will use the following exact complete parameter consequence:

    j<751/1000, b=1-j>249/1000,
    k>b^2/epsilon, k>1,
    c=k/sqrt(k^2+j^2), z=j/sqrt(k^2+j^2)
       imply B(epsilon,j,j/k)<R^2.                  (19)

To prove it, set j_0=751/1000, b_0=249/1000 and

    chi=j_0/b_0^2=751000/62001,
    x_0=chi*epsilon<37550/186003<2/9.

In the form (18) with c=1/sqrt(1+x^2), z=x*c, the bound is
strictly increasing with j and with x for 0<=x<1: its x derivative
has the positive numerator (j+epsilon)-(j-epsilon)x.
The hypotheses in (19) therefore bound it strictly above by
the same expression at j_0,x_0.

For 0<=x<=2/9, the Taylor upper bound gives

    (1+x^2)^(-1/2)<=1-x^2/2+3*x^4/8
                       <=1-(12/25)x^2.             (20)

For example 1/2-(3/8)(2/9)^2=13/27>12/25 proves the last step.
Since R^2=17/4+4*epsilon+epsilon^2, the resulting difference is
at most the following quadratic after its negative cubic and
quartic terms are dropped:

    C+A*epsilon+D_2*epsilon^2,
    C=-183999/1000000,
    A=755996/62001,
    D_2=-104498886320/1281374667.                    (21)

Those dropped terms are nonpositive because j_0*chi-1>0. The
quadratic is increasing throughout 0<=epsilon<=1/60; its derivative
at the right endpoint is

    A+D_2/30=36422619364/3844124001>0.

Its value there is exactly

    -39566732179997/11532372003000000<0.             (22)

Equations (20)--(22) prove (19) over the entire parameter interval,
with no sampling or subdivision. In particular a physically boundary
unit cannot have the data in (19).

## 4. Every tilted genuine S root K is excluded at its original degree

Suppose K is not aligned with its genuine leaf direction e. In its
own axes toward that actual support vertex write

    e=(A/d,B/d), A>=B>0, A^2+B^2=d^2,
    K=[A-1,A] times [B-1,B].                        (23)

Because O is outside closed K,

    1<A<=d, 0<B<sqrt(d^2-1)<11/60.                 (24)

By (5), the actual H-K point P cannot lie on K's right or bottom
side: those have point norm at least A>1 or 1-B>49/60. The only
possible features are its left side, top side and their common
near vertex. A pure top outward K normal would give the H-to-K
support -B<0, contrary to O in int H. Thus in these own axes

    n_1>0, n_2<=0, P_1=A-1.                        (25)

If K's two nonleaf normals were parallel, its original full force
equation would make them parallel to e. Its H port would then be
the leaf vertex or the opposite vertex. Both have norm above the
bound (5). Hence they are nonparallel. Its genuine full moment
puts their concurrence at q_K=t e for a real t.

Set t_0=d(A-1)/A. Then 0<t_0<=epsilon. If t<t_0, the H port is
improper, because P=q_K-eta*n and (25) give eta<0. A normal port
with negative proper length is the unique metric projection of
q_K onto K. That projection cannot be on the bottom side by (5),
so it is on the left side with unchanged normal n=e_1 and
P=(A-1,tB/d).

The full K equation now makes the other K-to-U normal w have
w_2<0. It must have w_1>0. If w_1<0, its port would also be
improper and hence the same unique projection, with normal -e_1,
contrary to w_2<0. If w_1=0 its force line would have first
coordinate (q_K)_1<A-1 and could not meet K. Therefore its actual
port is Q=(A,B-1), and it is proper.

For 0<=t<t_0, |q_K|<=epsilon and |Q|>5/4. Hence its original
support satisfies

    h_K(w)=Q dot (Q-q_K)/|Q-q_K|
              >=|Q|-2|q_K|>73/60>d,                (26)

contradicting (8).

For t<=0, put z=-tB/d>=0. Equation (5) gives z<27/40. Write

    rho=B*(1-B-z)/(A*(B+z)),
    w=(1,-rho)/sqrt(1+rho^2).

Here 1-B-z>17/120, and

    B/8< (1020/6283)*B < rho <= (1-B)/A.             (27)

The first strict comparison uses 1020/6283>1/8. The support

    h_K(w)=[A+(1-B)*rho]/sqrt(1+rho^2)

is nondecreasing up to rho=(1-B)/A. At rho=B/8 its squared
numerator minus d^2 times the squared denominator is

    B*[A*(1-B)/4-B*(1+(A^2+2*B-1)/64)]>0.           (28)

Indeed the bracket is strictly above

    49/240-(11/60)*(1+1441/230400)
       =272149/13824000>0.

Thus h_K(w)>d again. This excludes the entire improper H-port
range, including t=0.

At t=t_0 the actual q_K is in the relative interior of K's left
side and P=q_K, of norm at most epsilon. H then owns its vertical
normal and has |q|<=epsilon, contrary to Section 2.1. This explicitly
covers the zero-length endpoint without imposing a sign on a zero
normal ray.

It remains t>t_0. If t>d, an improper H port would be the leaf
vertex d*e, contradicting (5). A proper H port would instead have
both own coordinates of P-q_K negative, contrary to the nonnegative
second coordinate of its actual outward K normal -n in (25).
Thus t<=d, q_K belongs to K, and its H port is proper.

On a left-side normal the unchanged port has second coordinate
tB/d in (0,B]; on the near vertex it has second coordinate B.
In either case

    |P|^2 <= (A-1)^2+B^2=d^2-2*A+1
                         <d^2-1<(11/60)^2.          (29)

It cannot be an H vertex, whose norm is at least s>1/3. Hence
the actual H normal is vertical, and |q|<11/60. Section 2.1
contradicts this. Every tilted K is excluded, with all original
means and both zero-length possibilities retained.

## 5. Complete aligned-root equations and their zero-length endpoint

Write the actual remaining K as

    K=[epsilon,d]e+[alpha,alpha+1]Je,
    alpha<=0<=alpha+1.                              (30)

Its actual near point epsilon*e cannot enter int H. Its horizontal
coordinate is strictly inside [-s,r], so

    epsilon*e_y>=a>0.                               (31)

Also n dot(epsilon*e)>=h_H(n)>0, giving n dot e>0.
The actual H port is therefore always on K's inner radial side:

    P=epsilon*e+y*Je.                               (32)

### 5.1. Every parallel alternative retains both actual means

If the two original nonleaf normals at K are parallel, the full
leaf force makes them parallel to e. Since n dot e>0, n=e.
The other K-to-U normal cannot be +e: a contained unit beyond the
actual support d in that direction is uniquely the genuine radial
S square N. Indeed its center has e-projection at least d+1/2 and
norm at most d+1/2, forcing center (d+1/2)e and directional
half-width 1/2, hence that exact aligned unit. U and N are distinct
actual units.

Thus the other normal is -e. Its unchanged port is

    Q=epsilon*e+z*Je,
    mu*y+gamma*z=0, mu,gamma>0,
    q*n_y=det(P,n)=-y.                              (33)

If y=0, then z=0 and P=epsilon*e has norm epsilon. H owns a
vertical normal, so n=e=e_y and q=0, excluded by Section 2.1.
Otherwise y,z have strictly opposite signs and

    |y|+|z|<=1.                                    (34)

These are original weighted means anywhere on the actual inner
side, including each closed endpoint.

### 5.2. Nonparallel root forces have genuine proper radial intersection

Suppose K's two nonleaf normals are nonparallel. Their full actual
force and moment give q_K=t e. Put k=t-epsilon. The H port obeys

    P=q_K-eta*n, eta=k/(n dot e).                    (35)

If t<epsilon, its negative length makes P the unique projection
epsilon*e, and n=e, forcing the other original normal parallel as
well. This is impossible in the present case. If t=epsilon, then
P=q_K=epsilon*e. That small actual H port is on its top-side
interior, with n=e_y and |q|<=epsilon. Section 2.1 excludes this
entire zero-length case. Thus

    t>epsilon, k>0, eta>0.                          (36)

The H port is a strict inner vertex of K: otherwise its normal
would be -e and the full K force would again be parallel. Its
transverse coordinate y is an endpoint of [alpha,alpha+1].
The determinant of (32),(35) gives the exact sign relation

    q*n_y=det(P,n)=-t*y/eta.                         (37)

If k>1, q_K is beyond the genuine leaf support. An improper K-U
port would then be its unique projection d*e, with outward K
normal +e, again making n parallel to e by the full K equation.
Thus the K-U port is proper. Its radial component is negative,
and its transverse component has the same sign as n dot Je,
by the actual transverse force equation at K. It is consequently
the other inner vertex, with transverse coordinate of opposite
strict sign to y. No zero length is possible when k>1.

## 6. Every negative H concurrence crosses the actual D leaf

Assume q<0. By (6), n_x<=0.

### 6.1. The full nonparallel K alternative

Equation (37) gives y>0. Write e=(-f,c), c>0. Equations (31)--(32)
give a=epsilon*c-y*f, so f>=0. The actual normal from (35) is

    n=(k*e-y*Je)/sqrt(k^2+y^2),
    n_x=(-k*f+y*c)/sqrt(k^2+y^2)<=0.                 (38)

Hence f>0 and k*f>=y*c. With a>0 this implies

    f<epsilon*c/y, k>y^2/epsilon.                   (39)

If n_x<0, P=(-s,a), so y^2=s^2+a^2-epsilon^2>1/30.
If n_x=0, Section 2.1 gives |q|>11/60, and
y^2=q^2+a^2-epsilon^2>1/30 as well. Therefore

    y>1/6, k>2, 0<f<1/10, c>99/100.                (40)

Section 5.2 now gives 0<y<1 and the actual opposite inner port

    Q=P-Je=(P_x+c,a+f),
    w=(-k*e-j*Je)/sqrt(k^2+j^2)=(u,-v),
    j=1-y in (0,1).                                 (41)

The exact simple bounds from (40) are

    0<u<3/5, v>4/5, u/v>f/c.                       (42)

For the second, v>(99/100-1/20)/sqrt(5/4)
>(47/50)/(9/8)>4/5. The last follows by cross multiplication
from j(c^2+f^2)>0.

The original unit U contains Q+[0,1]w by (16). At

    eta_0=(a+f)/v in (0,7/48)

this actual segment reaches y=0. Write its first coordinate as X.
Because -s<=P_x<=0, (41)--(42) give

    X-r>=-(1-c)+(u/v)*(a+f)
          >-(1-c)+f^2/c=1/c-1>0,

    X-r<s+(3/5)*(7/48)<37/80<sqrt(2).               (43)

Thus (X,0) is strictly inside the actual D diamond (2), while
belonging to the closed original U. Interior approximation gives
open overlap, including an inward segment lying on a side of U.
This excludes the entire nonparallel negative-q alternative.

### 6.2. Both original parallel means and the coincident-side limit

Now use (33). Since q=-y/e_y<0, y>0 and z<0. Put
t_1=y+|z|, so 0<t_1<=1. Write n=e=(-f,c), with f>=0,
c>99/100 and f<1/20 by (4). The actual U support and its
inward normal segment are

    Q=P-t_1*Je, Q+[0,1](-e) subset U.               (44)

If f>0 then P=(-s,a), and the segment in (44) crosses the
horizontal line y=a at first coordinate -s+t_1/c. This occurs
at parameter t_1*f/c<1. A value strictly between -s and r would
make the segment immediately enter int H. Therefore t_1>=c.
At y=0 the same segment has parameter (a+t_1*f)/c<1 and

    0<a*f/c<=X-r=-1+t_1/c+a*f/c
                    <1/99+1/1188<sqrt(2).          (45)

It therefore enters int L, as in (43).

If f=0, then a=epsilon, P=(q,a), and Q=(q+t_1,a).
Here q+t_1>-s. The vertical actual inward segment would enter
int H unless q+t_1>=r. Also q+t_1<1. A strict inequality
q+t_1>r puts its y=0 point in int L immediately.

At the exact endpoint q+t_1=r, U contains the vertical segment
from (r,a) to (r,a-1). Along 0<y<a this is in the relative
interior of H's right side. Disjoint interiors force it to be
an actual vertical side of U with U lying to its right: a tilted
U would instead have these inward-normal points in its interior,
and a left-side placement would overlap H. Since y=0 is strictly
between a-1 and a, the rightward interior of U there enters the
open D diamond. This excludes the exact endpoint too. All actual
parallel application means have been retained.

## 7. Every positive H concurrence excludes the boundary unit U

Assume q>0. By (6), n_x>=0. The full H equation makes m_x<0
and m_y<0. Its H application is the lower-left fixed vertex.

### 7.1. A nonvertical H-K normal

If n_x>0 and K were nonparallel, its H application would be
the strict K inner vertex from Section 5.2. It is simultaneously
H's strict upper-right vertex. The other original H normal is
strict southwest at the lower-left vertex. These are precisely
the two fixed nonaxis vertices of the accepted finite D-star
selection in Section 1. Its point-only H-K edge is impossible.

Hence K is parallel and (33)--(34) hold, with n=e. At the upper-
right H vertex, |y|^2=r^2+a^2-epsilon^2>=r^2-epsilon^2 and y<0.
Put rho=sqrt(r^2-epsilon^2)>1/2. Then z>0 and z<=1-rho<rho.
Its actual K-U point has

    |Q|^2=epsilon^2+z^2<epsilon^2+rho^2=r^2,         (46)

impossible for the physical boundary unit U. This covers all its
original side means and their endpoints.

### 7.2. A vertical H-K normal and parallel K forces

Now n=e_y. Section 2.2 gives q>1/4. In the parallel case e=e_y,
a=epsilon, y=-q and 0<z<=1-q<3/4. Its original boundary point
gives z>epsilon, since otherwise |Q|<=sqrt(2)*epsilon<r.
Apply the full cap (18) with j=z, c=1 and the normal into U equal
to -e. Every squared corner norm is less than

    epsilon^2+(3/4)^2+2+2*(3/4)
                  <65/16+1/3600<17/4<R^2.           (47)

The exact middle reserve is 337/1800. Thus U cannot be boundary.

### 7.3. A vertical H-K normal and nonparallel K forces

Put y=-b<0. The exact vertical-normal identities from (35) are

    L_0=sqrt(k^2+b^2),
    e=(b/L_0,k/L_0),
    q=b*(epsilon+k)/L_0,
    a=(epsilon*k-b^2)/L_0>0.                         (48)

Equations (15),(32),(48) give

    b^2=q^2+a^2-epsilon^2>1/16-1/3600
                                      >(249/1000)^2,
    k>b^2/epsilon>1.                                (49)

The exact reserve in the first strict comparison to (249/1000)^2
is 1991/9000000. Section 5.2 now gives the other original inner
vertex with j=1-b in (0,751/1000), and

    Q=epsilon*e+j*Je,
    w=(-k*e+j*Je)/sqrt(k^2+j^2).                    (50)

Since Q belongs to physical boundary U, its norm is at least r;
in particular j>epsilon. In the actual (e,Je) frame, (50) is
exactly the minimum-normal chart (17), with all inequalities of
(19). The complete cap (19)--(22) puts every actual U corner
strictly inside the circle. This contradicts its physical boundary
status, independently of its circle-weight split or contact owner.

The vertical parallel and nonparallel cases exhaust every positive q.
The case q=0 was already excluded by Section 2.1. Together with
Sections 4 and 6, this completes the entire original configuration.

## 8. Exact original gate and retained scope

Return to the original C4 A-B-C-D-A with genuine leaves at A,B
and both private C,D loaded. For S at A and D at B, the exact
renaming is

    H=B, K=A, U=D, T=C.

The other mixed assignment is its original graph reflection, so
the full symmetry-identified original domain is covered. The sole
new whole fine gate supplied after full acceptance is

    M6.B4L2.C4.ADJACENT.LCD.SD.

The proof preserves true H3/K3 and U2/T2, both original leaf
equations, all six component bodies and all three arbitrary other
physical squares. It uses neither a false H-K-U triangle nor the
unloaded-channel conclusion for either positively loaded private
unit. Every original circle mask, individual zero corner coefficient,
normal owner, application mean and zero-stress physical contact is
included. Its full proof even keeps the U/T force equations unused
rather than replacing them by smaller equations; they remain genuine
equations of the original unchanged certificate.

The S/S sibling, opposite-root S/S C4, and remaining S/S hub-tip
diamond are not included or declared closed. No parent layout or
whole coarse cell is changed by this source. No physical motion,
new certificate selection, numerical pose, parameter subdivision,
Lean compilation, CI, remote mutation or shared-ledger edit was used.
