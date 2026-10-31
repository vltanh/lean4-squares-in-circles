# Two actual near neighbors force every unloaded triangle hub near the origin

Date: October 30, 2026 UTC. Author: branch_budget continuation.

**Status: complete reconstructed hand theorem, submitted for a fresh full
independent review.** The earlier unpublished copy was lost when the
execution environment restarted. The proof below is newly written and
uses a shorter actual-point argument in its strict-external cases. No
old source or review hash is asserted to pin these new bytes.

The theorem covers every original external normal and every return
owner. It retains the full original unloaded three-force equation,
all actual side means and their endpoints, all neighboring degrees,
all physical masks and every original square.

## 1. Exact theorem and full original equations

Let U,Q,V,W be four distinct actual closed unit squares with disjoint
open interiors in the unchanged disk about O. Assume

    R^2 <= 1105/256,       0 <= delta <= 1/60.

The entire positive pair neighborhood of U is exactly Q,V,W, and its
total circle load is zero. Write its unchanged full equations as

    lambda*n + mu*g + nu*k = 0,
    lambda*det(p0,n) + mu*det(pV,g) + nu*det(pW,k) = 0,
    lambda,mu,nu > 0.                                      (1.1)

Every normal is a unit vector outward from U. Every application is
the actual common point or the original aggregate mean on the actual
shared segment. In particular p0 is an actual maximum-n support point
of U and a minimum-n support point of Q. Assume that

    Q and V meet the closed disk D_delta;
    V and W physically touch.                             (1.2)

The latter contact need not have positive force. The degrees, loads,
physical circle masks, individual corner coefficients and further
equations at Q,V,W are arbitrary. Other zero-weight physical contacts
at U are allowed. There is no normal-selection hypothesis.

**Theorem 1.** The same actual U meets the closed disk D_delta.

**Theorem 2.** In an original nine-unit packing, the motif above is
impossible if one further actual unit Z, distinct from U,Q,V, meets
D_(1/60). The unit Z may be W if W has this physical nearness.

Theorem 1 extends the published external-own-axis theorem to every
strict external vertex normal. The full original Type II six-body
three-genuine-leaf family is excluded in Section 8.

## 2. Actual support tools, exact reserves and the owned external case

### 2.1. A unit step along a genuine support normal

If p is any actual minimum-e support point of a unit square K and e
is a unit vector, then

    p+e belongs to K.                                    (2.1)

At a vertex p, write K=p+[0,1]a+[0,1]b using its inward orthonormal
own axes. The minimum-support condition gives e.a,e.b >= 0. Both
components are at most one, so p+e is in the actual coordinate box.
At a relative side-interior point, e is the inward side axis and the
unit step reaches the opposite actual side. The vertex argument
includes a side endpoint. Thus (2.1) does not require ownership by K,
a singleton intersection or a midpoint mean.

We also use the complete strict reach lemma from [S]: if p is a
minimum-e point and e.f<0 for a unit vector f, then

    max_(z in K) f.(z-p) < 1.                            (2.2)

Its vertex proof uses the two inward own axes: at most one can have
a positive f component, and that component is strictly below one.
Its side proof uses the unchanged tangent interval of length one.
Consequently, for U=[x,x+1] times [Y-1,Y], an actual neighbor at
the upper-right vertex with a strict Northeast normal lies wholly in

    {z_x>x, z_y>Y-1};                                   (2.3)

an actual neighbor at the lower-right vertex with a strict Southeast
normal lies wholly in

    {z_x>x, z_y<Y}.                                     (2.4)

These are statements about each whole closed neighboring square.

Two further physical facts from the complete proof [S] are used.
If one return normal is an own axis of U, its dot product with the
other return normal is nonnegative because the returned units touch.
Also, opposite strict U vertices cannot support touching returns.
Indeed their actual common point would lie in int U by (2.2).
Opposite own axes cannot support touching returns either, since their
outward half-planes are separated by the unit width of U.

### 2.2. The external support is close to the original origin

Put H=h_U(n)=n.p0. The actual Q point in D_delta and its original
support half-plane give H<=delta. The complete full-star separation
theorem [S] puts every actual point of V and W strictly on U's side
of that line. Applying it to a point of V in D_delta gives

    -delta < H <= delta.                                (2.5)

If delta=0, (2.5) is already impossible. Hence delta>0 below.

If n is an own side axis of U, the complete published theorem [O]
applies directly to (1.1)--(1.2). It proves Theorem 1, including
every unchanged external mean. We therefore assume that n strictly
exposes an actual vertex of U. No owner is inferred at Q.

### 2.3. Fixed exact containment reserves

The following rational inequalities will close all far-side cases:

    (5-3delta)^2/5 >= 9801/2000 > 1105/256,
    2(19/20)^2 + 1 + 2(19/20) = 941/200 > 1105/256,
    (53/20)^2 > 1105/256.                               (2.6)

The three strict reserves are respectively 18691/32000,
2487/6400 and 17319/6400. In the first comparison use delta<=1/60.
Thus an actual point z with e.z>5-3delta for a vector |e|=sqrt(5)
cannot belong to the containing disk. Likewise a point p with both
coordinates greater than 19/20, followed by a unit Northeast step,
has squared norm greater than the second bound in (2.6).

All subsequent coordinate frames are rotations or reflections about
the unchanged O. The displayed x,y,Y are the actual square's global
coordinate levels, not a translation of O into U.

## 3. Both return normals are own axes of U

Opposite axes are impossible by physical contact. Equal axes make
the external normal their opposite own axis, already covered by [O].
It remains to consider perpendicular axes. Interchange the return
names if necessary so that the near one is the East return V, and
choose the orientation so that W is North. Write

    U=[x,x+1] times [y,y+1],
    pV=(x+1,y+a), pW=(x+b,y+1), 0<=a,b<=1,
    F_V=(mu,0), F_W=(0,nu), kappa=nu/mu>0.

The strict external normal is Southwest, at p0=(x,y), and full
torque about p0 gives

    nu*b=mu*a,       b=a/kappa,
    n=(-1,-kappa)/L, L=sqrt(1+kappa^2),
    H=-(x+kappa*y)/L.                                 (3.1)

The actual near point of V lies in x-coordinate at least x+1.
Therefore A=-x>=1-delta. The unchanged W application followed by
its inward unit North step is an actual W point by (2.1):

    z=(-A+a/kappa, 2+(A-LH)/kappa).

Its projection in direction (-1,2) is

    (-1,2).z=4+A+(2A-a-2LH)/kappa
       >=4+A-2delta+(2A-a-2delta)/kappa
       >5-3delta.                                    (3.2)

For the second line use H<=delta and L<=1+kappa. For strictness,
2A-a-2delta>=1-4delta>0, and A>=1-delta. This contradicts (2.6).
The argument includes every value of both original means a,b,
including zero or one whenever compatible with (3.1).

## 4. Exactly one return normal is an own axis of U

Call the owned return V for this section; the near return can be
either V or W, and both possibilities are treated separately.
The physical nonobtuse-normal fact permits the normalization

    U=[x,x+1] times [Y-1,Y],
    pV=(x+1,Y-1+p), 0<=p<=1,
    pW=(x+1,Y-1),
    F_V=(m,0), F_W=(s,-w), m,s,w>0.

The nonaxis return is strict Southeast. The external normal is
strict Northwest at p0=(x,Y). Full torque and force, with no term
removed, give

    w=s+m(1-p), E=m+s,
    b=s/E in (0,1), kappa=w/E=1-(1-b)p,
    b<=kappa<=1,
    n=(-1,kappa)/L, L=sqrt(1+kappa^2),
    H=(-x+kappa*Y)/L, x=kappa*Y-LH.                  (4.1)

### 4.1. The owned return V is near

Its actual East support gives x+1<=delta. Consequently

    Y=(x+LH)/kappa
       <=(-1+2delta)/kappa+delta
       <=-1+3delta<=-19/20.                           (4.2)

Here L<=1+kappa and kappa<=1. Put D=sqrt(b^2+kappa^2).
The actual W point obtained from (2.1) is

    z=(x+1,Y-1)+(b,-kappa)/D.

Since kappa>=b>0, kappa/D>=1/sqrt(2)>7/10. Thus z_y<-53/20,
contradicting (2.6). This covers the entire owned-near alternative.

### 4.2. The strict return W is near

Choose an actual z0 in W with |z0|<=delta. Equation (2.4) gives

    x<(z0)_x<=delta,       Y>(z0)_y>=-delta.

By (4.1), H<=delta and L<3/2,

    x>-(kappa+L)delta>-3delta.                        (4.3)

If Y<=1, the actual point

    q=(max(x,0), min(Y,0))

belongs to U. Indeed x+1>0 by (4.3), while Y-1<=0. If x>0,
(z0)_x>x; if Y<0, (z0)_y<Y. In either coordinate the absolute
value of q is at most the absolute value of the corresponding
coordinate of z0. Hence |q|<=|z0|<=delta, proving nearness.

If Y>1, use the actual V point

    z=pV+East=(x+2,Y-1+p).

Its projection on (2,1), using (4.1), satisfies

    (2,1).z=3+(1+2kappa)Y+p-2LH
       >4+2kappa+p-2Ldelta
       >=5-2Ldelta>5-3delta.                          (4.4)

The middle inequality is 2kappa+p=2-p+2bp>=1 for 0<=p<=1.
Equation (2.6) contradicts containment. This finishes every original
one-owned-return feature, including p=0, p=1 and kappa=b.

## 5. Neither return normal is an own axis: the same vertex

Opposite U vertices are already physically impossible. First suppose
the two actual applications coincide. Normalize them to the upper-right
vertex of

    U=[x,x+1] times [y,y+1].

Both return forces are strict Northeast. Their positive sum is
strict Northeast, so the external application is p0=(x,y).
Full torque about p0 gives equality of the two coordinates of that
sum. Thus

    n=(-1,-1)/sqrt(2),       H=-(x+y)/sqrt(2).          (5.1)

Let z0 be an actual near point of whichever returned unit is near.
The strict reach lemma gives (z0)_x>x and (z0)_y>y. In particular
x,y<delta. Equation (5.1) and H<=delta then imply

    x,y>-(1+sqrt(2))delta>-3delta.

The point q=(max(x,0),max(y,0)) is consequently in U and satisfies
|q|<=|z0|<=delta coordinate by coordinate. This proves nearness.
No distinct-application selection is used; coincident applications
are retained exactly.

## 6. Neither return normal is an own axis: adjacent vertices

The two remaining applications are adjacent. Normalize them as

    U=[x,x+1] times [Y-1,Y],
    pV=(x+1,Y), F_V=(f,t), f,t>0,
    pW=(x+1,Y-1), F_W=(s,-w), s,w>0.

If w=t, the external normal is West and [O] applies. If w<t,
reflect the actual chart vertically and exchange the return names.
Both near-return possibilities will be proved, so this exchange
does not assume which physical unit is near. We may assume w>t.

The external normal is Northwest, at p0=(x,Y). Full torque gives
t+s-w=0. With E=f+s, set

    kappa=s/E in (0,1), omega=w/E>kappa,
    F_V/E=(1-kappa,omega-kappa),
    F_W/E=(kappa,-omega),
    n=(-1,kappa)/L, L=sqrt(1+kappa^2),
    H=(-x+kappa*Y)/L, x=kappa*Y-LH.                  (6.1)

All displayed vectors are the original forces divided by one
positive scalar. No normal at a returned square is required to be
owned, and its actual application can be a relative side-interior
mean or a vertex.

### 6.1. The upper return V is near

Choose z0 in V with |z0|<=delta. Equation (2.3) gives

    (z0)_x>x,       (z0)_y>Y-1.

If Y>=0, (6.1) gives x>=-Ldelta>-3delta. The actual point

    q=(max(x,0), max(Y-1,0))

belongs to U: x+1>0, Y>=0, and each displayed lower coordinate
does not exceed its corresponding upper face. As before, each
coordinate's absolute value is no greater than the corresponding
absolute coordinate of z0. Hence |q|<=delta.

If Y<0, put D=sqrt(kappa^2+omega^2) and take the actual W point

    z=pW+(kappa,-omega)/D.

Its fixed projection is

    (1,-2).z=3+(kappa-2)Y-LH+(kappa+2omega)/D
       >5-Ldelta>5-3delta.                            (6.2)

Indeed (kappa-2)Y>0. Also

    (kappa+2omega)^2-4D^2
       =kappa(4omega-3kappa)>0,

so the last quotient is strictly greater than two. The external
bound H<=delta finishes (6.2), and (2.6) contradicts containment.

### 6.2. The lower return W is near

Now choose z0 in W with |z0|<=delta. Equation (2.4) gives

    x<(z0)_x<=delta,       Y>(z0)_y>=-delta.

Equation (6.1) consequently gives x>-3delta. If Y<=1, exactly
the point q=(max(x,0),min(Y,0)) from Section 4.2 belongs to U
and has norm at most |z0|. Thus U is near.

If Y>1, the actual upper application pV=(x+1,Y) has both
coordinates strictly greater than 19/20: its first coordinate
is greater than 1-Ldelta>39/40, and its second is greater than
one. Let g=F_V/|F_V|, the original strict Northeast unit normal.
The actual point pV+g belongs to V by (2.1). Since g_x+g_y>1,

    |pV+g|^2>2(19/20)^2+1+2(19/20)=941/200,

contradicting (2.6). This completes both near-return alternatives
for the entire adjacent-vertex feature.

## 7. Complete all-normal union and two broad nine-unit consequences

Every original U support is either an own side axis, carrying its
unchanged actual mean, or a strict vertex cone. The external-own-axis
case is the complete input [O]. For a strict external normal the two
return features have been exhausted: both own axes, one own axis, or
neither own axis; the last has same, adjacent or opposite vertices.
All force-equality endpoints were either included explicitly or sent
to the original owned-normal theorem. This proves Theorem 1.

Theorem 2 now follows from [F4]: the four distinct actual units
U,Q,V,Z meet D_(1/60), so the containing disk has total unit capacity
at most eight. All nine physical units enter this count. None is
discarded because it is absent from the local positive star.

There is also a useful two-hub form requiring only two named near
units. Suppose A,B,U1,U2 are distinct actual units, A and B meet
D_delta, and each Ui is unloaded with entire positive neighborhood

    {A,B,Wi},       i=1,2.

Require Wi to physically touch at least one of A,B. Every Wi is an
actual third neighbor, distinct from its own Ui,A,B; W1 and W2 may
coincide if the complete original stars permit it. Theorem 1 applies
to each Ui, naming the touching near root as the returned near unit
and the other near root as the external unit. Hence A,B,U1,U2 are
four distinct actual near units, and [F4] excludes all nine-square
configurations with this full motif. No degree or load at A,B,Wi is
reduced. This is a conditional whole physical motif, not a newly
invented ledger identifier or a claim that a remaining parent must
contain it.

## 8. Exact entire six-body three-root Type II caller

Use the complete original graph cover [G]. The positive component
consists of a six-body biconnected block with vertices A,B,C,P,Q,N
and precisely the three genuine leaves at distinct roots A,B,C.
In Type II the required block edges are

    AP, PQ, QA, QB, BN, NC, CA.

The original root edge BC may be present or absent. The possible
AB edge is excluded by the complete graph/load result [G], rather
than deleted from any equation. That same source proves that Q
is physically circle-clear, hence genuinely unloaded, and has true
positive degree exactly three with neighbors A,B,P. The private P
is a true degree-two triangle tip and is positively loaded. N is
also genuinely loaded. Every original zero-weight contact remains.

The complete high-S entry used in [G] excludes all original low,
critical and D-leaf alternatives. Thus in every possible remaining
case d=1+epsilon>1, 0<epsilon<1/60, and the actual roots A,B,C each
meet D_epsilon at their real genuine radial near points. Their full
degrees remain unchanged; in particular A retains its genuine leaf
and all three block neighbors C,P,Q.

Apply Theorem 1 with the literal substitution

    local U = original Q,
    local external Q = original B,
    local near return V = original A,
    local other return W = original P,
    delta = epsilon.

The actual AP edge supplies the required return contact. Both
actual A and B are near. The original Q3 equations are exactly
the full equations required in (1.1); no A4 or loaded P2 equation
is shortened. Therefore the same original Q meets D_epsilon.

The four distinct original units A,B,C,Q now meet D_(1/60). The
full nine-unit capacity theorem [F4] contradicts all nine actual
units. This excludes the entire original Type II family, both BC
choices and every physical mask, original owner and complete mean.
It does not by itself close the entire coarse cell C1.6.b3.

## 9. Complete operative inputs and fresh review boundary

| Label | Complete source | SHA256 | Exact consumed scope |
| --- | --- | --- | --- |
| S | UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full original U3 separation and complete physical support/triangle facts; no generic normal selection |
| O | UNLOADED_TRIANGLE_HUB_OWNED_EXTERNAL_SUPPORT_TWO_NEAR_NEIGHBORS_FORCE_NEARNESS_2026_10_29.md | 6233da37b69080a854a61d3905a5249a1f5f14577f3dc236a934ff5e80212263 | Entire original external-own-axis theorem at closed delta endpoints |
| F4 | FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md | 63560c355c1b4c385618f412f6b6c01946f664684e843aa4fef85d78cba07190 | Total physical capacity eight for four distinct actual units meeting closed D_(1/60) |
| G | THREE_GENUINE_ROOTS_ARBITRARY_PRIVATE_NETWORK_LOAD_AND_UNIQUE_PAIR_CLASS_2026_10_29.md | be54ef6e20015c3841606d0b7779ba17fe319d2aa886ad9adfd376e985995a20 | Complete original Type II graph/load/high-S caller, genuine degrees and both optional BC choices |

All four complete direct sources were restored from the published
49a5537a6cc7a28db36e7d7ad74b9c7582da9ae3 tree, read in full and
checked against the displayed exact SHA256 values. Sections 3--6
are the reconstructed all-normal proof. The support-step projections
in this version replace the longer lost strict-external estimates.
They require a fresh complete nonauthor review; the earlier review
of different bytes is historical evidence only.

Root identified the wider two-hub consequence after the earlier
version's completion. Its exact full-star proof is printed in
Section 7, and no independent self-review of that contribution is
claimed. The main all-normal proof and Type II mapping are authored
here. All new checks are exact rational identities or continuous
unit-support arguments.

No numerical pose search, angle grid, new packing certificate,
normal reselection, degree suppression, physical motion, Lean build,
CI run, metadata edit, remote write or merge is used.
