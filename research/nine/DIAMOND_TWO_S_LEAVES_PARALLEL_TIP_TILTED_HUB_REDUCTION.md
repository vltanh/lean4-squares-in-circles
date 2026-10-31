# A parallel S tip forces two tilted units and one specific owned hub contact

Date: October 27, 2026.

**Status: complete hand exclusion of the stated interfaces and exact
remaining-frame reduction, submitted for full root and independent
review.** The remaining tilted K frame is explicitly retained; this
source does not claim the whole high S/S fine gate closed.

Keep all nine actual physical units, the common compatible selected
certificate, and the exact original positive edges

    HK, HB, HC, KB, KC, HL, BM.

H and B are genuine S-leaf roots with actual leaves L and M. The true
degrees are H4,K3,B3,C2,L1,M1; K,C have positive circle loads. Every
original force, application mean, selected normal, physical circle mask,
individual zero weight and completion unit remains. Assume

    d=1+epsilon,       0<epsilon<1/60,
    R^2=(2+epsilon)^2+1/4<=1105/256,
    |c_T|<M_0=91/60.

Suppose B's two nonleaf forces are parallel. The complete original
parallel-tip cover in Section 1 of
DIAMOND_TWO_S_LEAVES_PARALLEL_TIP_OWNED_HUB_EXCLUSION.md gives, after
one common rotation and reflection,

    M=S(e_x),
    B=[epsilon,d] times [a-1,a],
    P=p_BH=(epsilon,y),       Q=p_BK=(epsilon,z),
    z<-16/25<0<y<9/25,       -1<z,
    Delta=y-z<=1.                                      (1)

The original positive means obey mu_H*y+mu_K*z=0. No mean is reset.
That complete earlier source excludes an H-owned east HB normal.
Consequently H has its unique rightmost vertex at P, with actual
inward own axes

    u=(-c,-t),       v=(-t,c),
    c,t>0,       c^2+t^2=1,
    H=P+[0,1]u+[0,1]v.                                 (2)

**Theorem.** In this entire parallel-tip domain:

1. The actual HK normal must be owned by K and strictly expose
   U=P+u on H.
2. K cannot own the east KB normal; in particular K cannot be aligned.
3. The complete remaining K chart is

       K=Q+[0,1]w+[0,1]j,
       w=(-a_0,b_0),       j=(-b_0,-a_0),
       a_0,b_0>0,       a_0^2+b_0^2=1,
       U=Q+sigma w,       0<sigma<1,
       c=sigma a_0,
       Delta=t+c b_0/a_0<=1,
       b_0/a_0<=c/(1+t),       a_0>c,       b_0<t.     (3)

Thus both the whole non-K-owned HK interface and the whole aligned-K
interface are excluded. The proof retains the real HK force and K3.

## 1. Complete genuine-leaf and actual HK feature covers

Put

    tau=epsilon c+yt>0,
    kappa=yc-epsilon t,
    V=P+v,       W=P+u+v.

In H's own coordinates about the unchanged origin, H is

    [-tau,1-tau] times [kappa,1+kappa].                 (4)

Its positive-u support is 1-tau<1<d. Its negative-u support tau is
at most |P|<1/2. Its negative-v support is -kappa<epsilon<d.
Therefore its only possible owned genuine S-leaf direction is +v,
in which case

    kappa=epsilon,       y=epsilon(1+t)/c.              (5)

For strict vertex supports, P has norm below r and cannot have norm d.
At U=P+u the radial outward normal would have negative world y
component, hence y<t. But then

    |U|^2=1+epsilon^2+y^2-2epsilon c-2yt
           <1+epsilon^2<d^2.

At W the exact difference is

    |W|^2-d^2
      =1+y^2+2y(c-t)-2epsilon(1+c+t)>0.

For example y<9/25, c-t>=-1 and c+t<3/2 give the lower bound
1-369/625-1/12>0. The only possible strict leaf vertex is therefore
V. In the latter case

    |V|=d,       e_L=V/d=(-tau u+(1+kappa)v)/d.          (6)

The two coefficients in the outward V cone are strictly positive.
This is the full owned/vertex cover of H's genuine S leaf.

The boundary unit K contains Q and lies in x<=epsilon. It cannot
contain the small P. An HK application on the -u, +u or +v face
would require respectively

    (Q-P).(-u)=-t Delta>=0,
    (Q-U).u=-1+t Delta>=0,
    (Q-V).v=-1-c Delta>=0,

all impossible. At W the last two strict failures exclude every
normal in its strict outward cone.

The vertex V is also unavailable to a boundary neighbor. In the strict
leaf case, H's right-angle cone lies strictly inside the half-plane
opposite the actual leaf, leaving two gaps each shorter than a right
angle. No third unit fits there. In the owned +v case, the real leaf
port is V+tau u and 0<tau<1/2, so V is in the relative interior of
the real leaf's inner face. A third unit through V must fill the one
remaining right-angle sector. It then has the H frame and shares
the full side V--P with H, hence contains the small P and is physically
clear. This includes a possible shared-side endpoint mean; it is not
discarded by calling that contact point-only.

It follows that K can contact H only on the owned -v face P--U,
or at U with a strict normal in the cone spanned by u,-v. In both
cases the actual normal from K to H has positive world y component.

## 2. Every HK contact not owned by K makes K physically clear

First suppose the actual H-to-K normal is the H-owned -v direction.
At K the normals toward B and H are e_x and v, whose dot product
is -t<0. The complete physical triangle side-normal obstruction for
the actual triangle BHK forbids either normal being K-owned. Thus
both actual K applications are strict K vertices.

More generally, suppose HK is not K-owned and has its strict H
application U. If K owned e_x, its frame would be aligned and its
vertices' x coordinates would be epsilon or epsilon-1. U has x
coordinate epsilon-c strictly between them, so it could not be a
strict K vertex. Therefore here too both K applications are strict
vertices. They are distinct. The complete physical triangle fact in
RADIAL_TRIANGLE_CONCURRENCE.md, Section 1, excludes opposite vertices,
so they are adjacent.

Treat both situations together. Write the actual HK point as

    R=P+lambda u,       0<lambda<=1.

The second situation has lambda=1. Its difference from Q is

    R-Q=(-lambda c,A_0),       A_0=Delta-lambda t,
    (lambda c)^2+A_0^2=1.                             (7)

R is K's upper adjacent vertex: its outward normal toward H has
positive y component, whereas all strict normals at the lower adjacent
vertex have negative y component. Thus the actual K frame at Q is

    R-Q=(-lambda c,A_0),
    j_0=(-A_0,-lambda c),       A_0>0.

Solving (7), its only positive root is

    lambda=t Delta+sqrt(1-c^2 Delta^2).

The other root is nonpositive because Delta<=1. Since lambda<=1,
squaring gives Delta>=2t, so t<=1/2. Consequently

    A_0>=Delta-t>16/25-1/2=7/50>epsilon.                (8)

All four actual K corners are strictly inside radius two. Q has norm
less than sqrt(1+epsilon^2), and R has norm at most |P|+1<3/2.
The other two have coordinates

    Q+j_0=(epsilon-A_0, y-Delta-lambda c),
    R+j_0=(epsilon-lambda c-A_0, y-lambda(t+c)).

For the first, both coordinates are negative and removing epsilon,y
strictly increases their squared magnitudes. Hence

    |Q+j_0|^2
       <A_0^2+(Delta+lambda c)^2
       =1+Delta^2+2Delta lambda c<4.                   (9)

For the second, if its y coordinate is nonpositive, the same comparison
and (7) give

    |R+j_0|^2
       <(lambda c+A_0)^2+lambda^2(t+c)^2
       =1+lambda^2+2lambda c Delta<4.                 (10)

If its y coordinate is positive, its square is instead less than
2+(9/25)^2<4, since (lambda c+A_0)^2<=2 by (7).
Thus K is physically clear, contradicting its actual boundary load.
This proves that HK is K-owned and strictly exposes U on H.

## 3. The entire aligned K geometry

Suppose now K owns e_x. By the theorem just proved it also owns the
HK direction. Since U_x=epsilon-c is strictly inside its horizontal
interval and the K-to-H normal has positive y component, that contact
is on K's north side. Therefore

    K=[epsilon-1,epsilon] times [-k-1,-k],
    k=t-y.                                             (11)

K is boundary. Because its right support contains Q with -1<z<0,
its lower-left corner has strictly greater norm than either right
corner. Its upper-left corner has norm below sqrt(2): its x magnitude
is below one, and -k=y-t lies in (-1,9/25). Thus its only possible
circle corner is the lower-left one. This proves

    k>0,
    (1-epsilon)^2+(k+1)^2=R^2,
    k=sqrt(13/4+6epsilon)-1,
    401/500<k<5/6,       t>k>4/5,       c<3/5.          (12)

For the lower bound, (901/500)^2<13/4; for the upper bound,
13/4+6epsilon<67/20<(11/6)^2. In particular U is in the relative
interior of K's top side. The actual B side contains the full vertical
segment from P down to (epsilon,-k), since z<=-k<y.

The parameters in (4) now satisfy the useful uniform bounds

    0<tau<1/5,       kappa>-1/60,
    A=1-tau>4/5,       D=1+kappa>59/60.                (13)

Indeed y=t-k, so

    tau=epsilon c+t(t-k)
       =1-k-c^2+k(1-t)
          +epsilon c
       <1-k-c^2/2+epsilon c
       <=1-k+epsilon^2/2<1/5.

Here k<t<1 gives k/(1+t)<1/2, and (12) leaves a strict reserve
against epsilon^2/2<1/7200. The lower bound for kappa is immediate.

## 4. The actual exterior page has only two possible center caps

C cannot contain P: B has a relative side-interior contact there,
and H's vertex cone is strictly inside B's complementary half-plane,
leaving no right-angle gap for a third unit. Likewise C cannot contain
U, where K's relative side interior and H's strict upper vertex cone
leave two gaps shorter than a right angle.

C cannot contact a relative interior point of P--U either. The three
segments joining P, U and (epsilon,-k) form a real closed triangular
barrier: they are respectively in H's side, K's top side and B's left
side. A unit on the outward side of the H segment enters the bounded
triangular pocket. Its connected interior cannot exit through the three
occupied sides or through their weak endpoints. That pocket is strictly
inside the containing circle, so a physical boundary C cannot occupy it.

The vertex V is unavailable to boundary C by the complete argument in
Section 1. Thus C touches H on its far-u face, far-v face, or W.
In the own coordinates of (4), put its actual center at (X,Y).
It must satisfy one of the two caps

    X>=A+1/2,       or       Y>=D+1/2.                 (14)

For a relative side contact this follows from the true supporting
half-plane and the center halfwidth at least 1/2. Here is the full
corner case. If C contains W=(A,D), its center is within sqrt(2)/2
of W, so neither coordinate can fall below H's corresponding near
side. If both center coordinates exceed A,D, its incircle must have
distance at least 1/2 from H. Thus

    |c_C|^2>=A^2+D^2+1/4+min(A,D)
             >(4/5)^2+(59/60)^2+1/4+4/5>M_0^2,

impossible. If both coordinates are below A,D, the center lies in H,
also impossible. In either remaining case the coordinate on the far
side is at distance at least 1/2 from that H face, proving (14).
Equalities and all corner/side owners are included.

The second cap is impossible immediately. Its center direction is
within pi/12 of v, since

    (D+1/2)/M_0>89/91>cos(pi/12).

The actual genuine H-leaf direction is v or, by (6), within pi/12
of v, since tau/D<12/59<tan(pi/12). Thus the distinct physical
boundary centers C,L would be less than pi/6 apart. The accepted
CENTERED_INNER_ARC.md requires their separation to exceed 2*pi/9.

## 5. The exterior circular order in the first cap

We retain the straight drawing of every original positive edge supplied
by TWO_NEAR_HUBS_BOUNDARY_DIAMOND_EXCLUSION.md, Sections 1--2. Every
physical boundary center is strictly exposed by its own radial direction.
The original M center and edge BM make B exterior to the diamond;
C is boundary and exterior. Consequently H-B-K-C-H is its outer face,
with HK retained as its real interior chord. The genuine leaf edges
HL,BM lie in the exterior, since their boundary endpoints are exposed.

The boundary-center cyclic order along that exterior face is therefore
L,M,K,C, up to reversal. It agrees with their radial order: the same
strict exposure places them in their convex-hull order, whose supporting
radial directions have that order. This is a planar statement about
the unchanged selected graph and its real exposed endpoints; no root
load has been reassigned.

Here L is in the second quadrant, K's center in the third, and M is
on the positive x ray. Hence C's center direction is strictly between
L and K along the counterclockwise arc not containing M.

The actual K center has own coordinates

    A_K=c(1/2-epsilon)+t(k+1/2)>0,
    B_K=t(1/2-epsilon)-c(k+1/2).                       (15)

Its norm is greater than 4/3, since R>41/20 and sqrt(2)/2<43/60.
The first cap in (14) gives X>=A+1/2>13/10, and therefore its
center direction differs from u by an angle delta with

    cos(delta)>(A+1/2)/M_0>6/7.                        (16)

If B_K>=0, both relevant center directions are on the clockwise side
of u, and the just-proved circular order puts C farther clockwise.
Their gap is at most |delta|, already smaller than 2*pi/9.
It remains to cover B_K<0. Write alpha for K's counterclockwise
angle from u; then

    sin(alpha)=|B_K|/|c_K|,
    gap(C,K)<=|delta|+alpha.                           (17)

The following short rational bounds prove this gap too small in its
whole actual c range. The intervals are analytic estimates of one
formula, with no change to any physical frame or force.

### 5.1. 0<c<=2/5

Here t>9/10, so (12),(15) give

    B_K>(9/10)(29/60)-(2/5)(4/3)>-1/10.

Thus sin(alpha)<3/40 and cos(alpha)>99/100. Equation (16) gives
sin(|delta|)<13/25. The angle addition formula yields

    cos(gap)> (99/100)(6/7)-(3/40)(13/25)
              =5667/7000>4/5.                         (18)

### 5.2. 2/5<=c<=1/2

Now 173/200<t<11/12. Since x^2-(4/5)x is increasing in this
range, the original tau formula gives

    tau<t^2-(4/5)t+1/120<83/720.

Consequently cos(delta)>997/1092>91/100 and sin(|delta|)<21/50.
Also

    B_K>(173/200)(29/60)-(1/2)(4/3)>-1/4,

so sin(alpha)<3/16<19/100 and cos(alpha)>49/50. Hence

    cos(gap)>(91/100)(49/50)-(21/50)(19/100)
              =203/250>4/5.                           (19)

### 5.3. 1/2<=c<3/5

Here 4/5<t<13/15 and epsilon c<1/100, giving

    tau<t^2-(4/5)t+1/100<61/900.

Thus cos(delta)>1289/1365>47/50 and sin(|delta|)<7/20. Moreover

    B_K>(4/5)(29/60)-(3/5)(4/3)=-31/75,

so sin(alpha)<31/100 and cos(alpha)>19/20. Therefore

    cos(gap)>(47/50)(19/20)-(7/20)(31/100)
              =1569/2000>77/100.                      (20)

All three estimates contradict the required gap greater than 2*pi/9.
For an exact common trigonometric comparison, cos(2*pi/9)<77/100:
the cubic 4x^3-3x is increasing for x>1/2, has value -1/2 at
cos(2*pi/9), and has value greater than -1/2 at 77/100.

Thus both caps (14) are impossible. This excludes the entire aligned
K interface with its full K3 force and all original side means.

## 6. Exact surviving tilted K frame and retained scope

K does not own the east normal, so Q is its unique rightmost vertex.
Use its actual axes w=(-a_0,b_0), j=(-b_0,-a_0), with both components
positive. Its actual HK normal is K-owned by Section 2 and has positive
y component. Its negative-x owned alternative has negative dot product
with the K-to-B east normal and is forbidden by the physical triangle
side-normal lemma. Thus the K-to-H normal is exactly -j=(b_0,a_0),
and U lies on the side Q--(Q+w).

Write U=Q+sigma w. The x difference gives c=sigma a_0>0. The endpoint
sigma=1 would be an actual point-only vertex/vertex HK contact with a
K-owned side normal, contrary to the original strict point convention;
sigma=0 would give c=0. Hence 0<sigma<1. Its y difference gives

    Delta=t+sigma b_0=t+c b_0/a_0<=1.

Using c^2=1-t^2 gives the remaining inequalities in (3). These are
the actual remaining variables, not a selected replacement contact.

The entire original parallel B domain is now reduced to (3), together
with the full original force and torque equations and H's two genuine
leaf alternatives (5),(6). The proof does not close that final tilted
frame or any nonparallel B frame. No sampled pose, new normal selection,
deleted force, Lean compilation, CI, or shared-ledger edit is used.
