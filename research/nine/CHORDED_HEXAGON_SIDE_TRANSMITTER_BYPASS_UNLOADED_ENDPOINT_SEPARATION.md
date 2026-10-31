# A side transmitter and its bypass separate the external neighbors of two unloaded endpoints

Date: October 27, 2026.

**Status: complete proposed radius-free local theorem and whole original
H2_D0.L134 exclusion, pending root and separate independent review.**
No original gate or shared ledger is changed.

All units below are actual closed unit squares with pairwise disjoint
open interiors. Every stated force is an original positive pair force
with its actual common application and outward common normal. Variable
shared-side means, point-only contacts and coincident applications are
retained. No normal is reselected in this proof.

## 1. A one-endpoint theorem at the complete original force scope

Use a rigid-motion chart in which the actual side transmitter S is

    S=[0,1] x [k-1,k], 0<=k<=1.

Its two endpoint bodies A,D have unchanged common applications

    P=(0,0) in A intersect S,
    Q=(1,0) in D intersect S,
    A subset {x<=0}, D subset {x>=1}.

Let T be an actual unit bypass touching both A and D. Suppose it is
on the upper transverse side of S:

    T subset {y>=k}, hence T subset {y>=0}.            (1)

No force, degree or circle-load premise at T or D is imposed. In
particular the TD contact need not have positive multiplier.

Assume A is unloaded and has exactly three positive neighbors S,T,B.
Write the complete unchanged force equation at A as

    alpha e_x+beta n+gamma m=0,
    alpha,beta,gamma>0,                              (2)

where n points A to T and m points A to B. The S application is
the actual P=(0,0), so its torque vanishes in this chart. The full
original torque equation at A is also retained.

**One-endpoint theorem.** Every point of the actual external unit B
has x<0.

This is stronger than a statement about a center or a contact point.
It will be applied at both real endpoints of the same transmitter.

## 2. Two elementary unit-support reach bounds

Let K be any actual unit, p a minimum support point for a unit normal
n, so K lies in n.(x-p)>=0. The point p may be anywhere on the
actual closed support face, including a variable mean or an endpoint.

First, p+t*n belongs to K for all sufficiently small t>=0. In K's
own coordinate intervals, every nonzero component of n points from
the appropriate minimizing endpoint toward the interval interior;
zero components remain fixed. This proves the assertion for both
vertex and side support, including an endpoint-valued side point.

### 2.1. Backward reach

If n_x<0, then

    max_(z in K) (z_x-p_x) <= |n_y| <1.               (3)

For a vertex support, the two unit edges r,s issuing into K satisfy
n.r,n.s>=0. At most one can have positive x-component: if both did,
their perpendicular directions would lie on opposite sides of the
x axis, and one would have negative dot product with n. If an inward
edge w has positive x-component, n.w>=0 implies

    |n_x|*w_x <= |n_y|*sqrt(1-w_x^2),

and hence w_x<=|n_y|. The other edge contributes no positive x
displacement. For a side support, n is an own axis. The inward normal
edge has negative x-component; the transverse interval has length
one and x-component magnitude |n_y|. The same bound follows for
every actual p on that side. This proves (3).

If n_x=0 the same argument gives the weak bound max(z_x-p_x)<=1.

### 2.2. Forward reach for an upward-steep normal

If n=(c,d), 0<c<d, c^2+d^2=1, then

    max_(z in K) (z_x-p_x) <= c+d.                    (4)

For a vertex support with at most one positive-x inward edge, the
reach is at most one, which is below c+d. If both inward edges have
positive x-components, write them as

    r=(cos(theta),-sin(theta)),
    s=(sin(theta),cos(theta)), 0<=theta<=pi/2.

The support inequality n.r>=0 gives tan(theta)<=c/d<1.
The function cos(theta)+sin(theta) is increasing on this interval,
so its value is at most c+d. For a side support the inward edge
contributes at most c, and the length-one transverse interval at
most d. This proves (4) with every original support-face mean kept.

Neither reach bound assumes that p is a selected side midpoint or
that K has any circle load.

## 3. The bypass normal and the complete A feature cover

Let p_T be A's actual T application. Since T touches the unchanged D,

    max_(t in T) t_x>=1.                              (5)

But (p_T)_x<=0. If n_x<0, the backward-reach bound would make
max_T x<(p_T)_x+1<=1, a contradiction. Therefore

    n_x>=0, m_x<0,                                  (6)

where the second strict sign follows from the full equation (2).

If A has e_x as an own side axis, then its full x interval is
[-1,0]. Every original m support lies on its left face, with
(p_B)_x=-1. Equation (3) gives max_B x<-1+1=0. This proves
the entire aligned A case, with no restriction on either actual mean.

Now suppose A is oblique to e_x. The actual S application P is its
unique rightmost vertex. Write its two inward unit edges as

    u=(-a,b), v=(-b,-a),
    a,b>0, a^2+b^2=1,
    A=P+[0,1]u+[0,1]v.                              (7)

Write U=u, V=v, W=u+v for its upper, lower and opposite vertices.
Every outward normal at P has strictly positive x-component.
Consequently n_x=0 in (6) cannot occur at P. If n_x=0 anywhere
else, the weak reach bound and (5) force (p_T)_x=0, which again
means p_T=P. Thus in this entire oblique case n_x>0.

Condition (1), the actual unit diameter and this sign leave exactly
the following T features:

* p_T=P;
* n=-v and p_T=lambda*u, with 0<lambda<=1;
* p_T=U, with n=(c,d), c,d>0, including any remaining upper-vertex
  normal not covered by the preceding own-axis case.

Here is the full cover check. The lower edge P--V and V itself have
negative y, so cannot meet T except at P. The opposite vertex W
has x=-a-b<-1; a unit through W cannot reach x>=1, since its
diameter is sqrt(2)<2. The opposite two sides have outward axes
u,v with negative x-components and are excluded by (6). The sole
remaining side is P--U, whose axis is -v. At U every remaining
normal with positive x-component also has positive y-component.
This exhausts all side, endpoint and strict-vertex features.

In each of these oblique cases n_y>=0. For p_T=P this follows
from the inward-normal-segment fact and T subset {y>=0}. In the
other two cases n_y>0 directly. Equation (2) therefore gives

    m_x<0, m_y<=0.                                   (8)

For the last two cases the vertical sign is strict. Since the v
projection of such a southwest normal is strictly positive, its
actual support on A is one of:

    W; V; or V+[0,1]u with m=v.                      (9)

If the support is W, (3) already gives

    max_B x <= -a-b+|m_y| < -a-b+1 <0.               (10)

Only the other features in (9) need further work.

## 4. The coincident bypass application p_T=P

Both the S and T forces are applied at P. The complete A torque
equation therefore gives det(p_B,m)=0. Because P belongs to the
actual A and p_B is its m support, this says p_B=lambda*m with
lambda>=0. The value lambda=0 is incompatible with m_x<0, since
all outward normals at P have positive x-component. Thus lambda>0.

In the own u,v coordinates of (7), every nonzero component of m is
positive, and its corresponding support coordinate must equal one.
Thus p_B is one of U,V,W. If p_B=U, then m=u. Projecting (2) on
v gives beta*(n.v)=alpha*b>0, whereas n is an outward normal at P
and must have n.v<=0. This is impossible. If p_B=V, then m=v;
projecting (2) on u similarly gives beta*(n.u)=alpha*a>0, impossible
for the same P normal cone.

Therefore the only possible external support is W, and (10) proves
the claimed strict half-plane separation. This includes every
coincident-port and horizontal-normal endpoint at P.

## 5. The complete A-owned upper-side feature

Suppose n=-v=(b,a) and p_T=lambda*u, 0<lambda<=1. If the external
normal were m=v, projection of (2) on u would give -alpha*a=0,
impossible. Thus the entire variable-mean face V+[0,1]u in (9)
is excluded in this case.

If p_B=V, use the full force equation to compute its actual torque:

    gamma*det(v,m)=det(v,-alpha*e_x+beta*v)=-alpha*a<0.

The T torque is beta*det(lambda*u,-v)=-beta*lambda<0.
The S torque at P is zero. Their sum cannot vanish. Hence V is
also impossible. Only W remains, and (10) proves max_B x<0.

Both lambda=1 and every original side mean strictly between zero
and one have been retained; lambda=0 was the complete previous case.

## 6. The complete upper-vertex feature

Suppose p_T=U=u and n=(c,d), c,d>0. Since the same unit T contains
u and a point of D with x>=1, its diameter gives

    1+a<=sqrt(2), hence a<1/2 and b>a.                (11)

If m=v and p_B=v+rho*u, 0<=rho<=1, the backward-reach bound gives

    max_B x <= -b-rho*a+|v_y|
             = -b-rho*a+a <0.                        (12)

This handles the entire genuine shared-side-mean alternative at B,
including both endpoint values, without replacing its mean by V.

It remains p_B=V with its other southwest normal. Put

    K=a*d+b*c>0, L=b*d-a*c.

The complete torque equation and (2) give

    0=beta*det(u,n)+det(v,-alpha*e_x-beta*n)
      =-beta*K-alpha*a+beta*L,
    alpha*a=beta*(L-K)>0.                            (13)

Consequently

    t=c/d < (b-a)/(a+b) <1.                          (14)

The forward-reach bound (4) now applies to the actual T. Its point
u has x=-a, while T reaches x>=1. Since (1+t)/sqrt(1+t^2) is
strictly increasing for 0<=t<1, (14) gives

    1+a <= c+d < sqrt(2)*b.

Squaring the positive quantities yields

    (3a-1)(a+1)<0, hence 0<a<1/3.                    (15)

The actual force ratio at the external normal is equally exact.
Set D0=b-a-b*t>0. Equations (2),(13) imply

    |m_x|/|m_y|=D0/a,
    |m_y|=a/sqrt(D0^2+a^2).

By (14),

    D0 > a*(b-a)/(a+b) > a^2/b.                     (16)

The last strict inequality is justified on the entire range (15):

    b^2-a^2-2ab=1-2a^2-2ab
       >1-2/9-2/3=1/9>0.

Thus |m_y|<b. Applying (3) at the actual p_B=V gives

    max_B x <= -b+|m_y|<0.                           (17)

Together (10),(12),(17) cover every actual external normal and every
mean in the upper-vertex case. Sections 3--6 prove the entire
one-endpoint theorem.

## 7. Both unloaded endpoints have disjoint actual external neighbors

Suppose now S is a genuine unloaded degree-two transmitter between
A,D and T is any actual physical unit bypass touching both endpoints.
The complete unit-bypass theorem gives reserve exactly one. Its
Section 4 supplies full transverse separation of T from S. Choose
the transverse sign so T is above S, and translate the actual common
channel height to zero. This gives exactly the chart in Section 1,
with 0<=k<=1 and both genuine endpoint means retained.

Suppose A,D are both unloaded and have their exact positive neighbors

    A: S,T,B;       D: S,T,C.

All three original magnitudes at each endpoint are strictly positive.
Their other physical contacts and the full degrees/loads at T,B,C
are unrestricted. The one-endpoint theorem gives B subset {x<0}.
Reflect the whole chart by x -> 1-x and apply it at the unchanged D.
It gives C subset {x>1}. Therefore

    B and C are distinct and have empty closed intersection.

If the same physical body had been proposed for both roles, the two
strict half-plane inclusions would already be impossible. Thus this
is a full physical external-neighbor separation theorem, not merely
the absence of a positive BC edge.

The proof needs neither circle containment nor a selected free-normal
perturbation. It retains the original full unloaded three-force stars
and every actual side mean. A higher-degree endpoint cannot be used
by dropping a force, and an unloaded transmitter cannot be replaced
by an arbitrary unbalanced square.

## 8. Exact whole original H2_D0.L134 exclusion

The original exterior-pentagon graph H2_D0 has rim 0,1,2,3,4 and
the two actual positive spokes H0,H2, with no outer chord. In its
complete positive-load orbit 134, the actual H,0,2 are unloaded.
Their true positive degrees are

    H: 2 with neighbors 0,2;
    0: 3 with neighbors H,1,4;
    2: 3 with neighbors H,1,3.

The physical unit 1 touches both endpoints 0,2 and is the genuine
unit bypass for H. The complete theorem of Section 7 therefore
applies with

    S=H, A=0, D=2, T=1, B=4, C=3.

It says the actual closed units 4 and 3 are disjoint. Their original
rim edge 34 says they physically touch. This is the contradiction.

Every original physical circle mask, zero individual corner weight,
positive edge magnitude, actual side mean and all three additional
physical squares remain. No force equation at loaded 1,3,4 is
needed, so their true equations and degrees are not altered. The
reflection preserving the two-spoke graph is included automatically.

Consequently this is a whole exclusion of exactly the original gate

    M6.B6.PENTAGON.H2_D0.L134.

Together with the separate double-channel three-load theta theorem,
it excludes both of those complete original H2_D0 three-load orbits.
The different 013 orbit and the original four-load domains remain
separate. No whole H2_D0 graph or coarse C1.6.b0 closure is inferred.

No numerical pose, artificial force, altered mean, physical motion,
post-extraction normal selection, Lean compilation, CI, remote action
or shared-ledger mutation is used.
