# The parallel inward-face S interface forces a boundary-owned return

Date: October 28, 2026 UTC. Author: thin_d continuation.

**Status: complete proposed necessary-domain reduction, frozen for full
root and independent review. This is not closure of the high S domain
or of the lower-house TDC S family.**

In the high aligned-root interface where the root and its unloaded
neighbor share a parallel inward face, the complete original forces
fix which triangle return is below the unloaded hub. They also force
the other return to own its contact with that hub. The proof retains
the loaded degree-three middle body and both original loaded
degree-two endpoints. It uses no substitute transmitter or A--C edge.

## 1. Original graph, actual means and exact interface

Retain all nine actual unit squares, their pairwise disjoint open
interiors, the unchanged circle, and the complete compatible selected
physical certificate. The original positive graph and loads are

    AT, TD, AD, AB, BC, CD, BL;
    B3 and A3 unloaded; T2, D3 and C2 loaded; L1 a genuine S leaf.

The three other packing squares and any additional physical contacts
remain arbitrary. In particular D has all three original positive
pair forces and its complete original circle load. Every actual
circle mask, individual zero circle weight, original normal, contact
application, shared-side mean and mean endpoint is retained.

Work only in the remaining high range

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+a,
    0<a<1/60, F=1-a>59/60.

The already established full third-support theorem excludes the
entire d<=1 range. Here the genuine leaf is East and the actual root
is aligned:

    L=[d,d+1] x [-1/2,1/2],
    B=[a,a+1] x [t_B-1,t_B], 0<=t_B<=1.

Assume the original B-to-A normal is West and the actual A frame is
parallel to B. This is the entire interface treated below; no other
high aligned or tilted interface is declared excluded.

The full B vertical force makes B-to-C horizontal. It cannot be
East. Any contained square beyond x>=d has center x coordinate at
least d+1/2 and center norm at most d+1/2. Its center is therefore
(d+1/2,0), its x halfwidth is exactly 1/2, and its frame is aligned.
The unique possible unit is the already occupied genuine L. Thus
both original B returns point West.

Write their unchanged applications and positive magnitudes as

    p_BA=(a,y_A), p_BC=(a,y_C), gamma>0, beta>0.

The full B torque gives gamma*y_A+beta*y_C=0. Both means are
nonzero: CD joins actual boundary units and has nonzero original
moment; full C2 torque makes BC nonzero, and full B3 torque with
the zero-moment genuine leaf makes BA nonzero. These are the complete
global facts of Section 2 of the closed-origin S source, valid without
an origin assumption at B. After one whole vertical reflection, retain

    y_C>0>y_A, 0<y_C<=1.                              (1)

Since A is parallel and its right support is x=a, write its actual
full rectangle as

    A=[-F,a] x [c-1,c], y_A in [c-1,c].               (2)

The original AB contact is a genuine shared vertical side; a
point-only aligned vertex/vertex contact could not have the selected
axis normal. Neither its overlap nor its mean is modified.

**Theorem.** In this exact original interface the following are
necessary:

* 1/60<c<1, so O belongs to int(A).
* The original A-to-T normal is strict Southwest at (-F,c-1), and
  the original A-to-D normal is strict Northwest at (-F,c).
* The actual point (-F,c) lies in the relative interior of a D side.
  Thus D owns the original AD normal, and the contact is a singleton
  at the strict A vertex.

The full C frame and its remaining original CD features are also
recorded in Section 5. The D-owned AD residue is not excluded here.

## 2. Two uniform physical estimates and the complete A feature cover

Every contained unit center satisfies |z|<91/60; every contained unit
has width at least one in every direction. Distinct actual unit centers
are at distance at least one, because their open inscribed disks of
radius 1/2 are disjoint. Every point of an actual boundary unit has
norm at least r=R-sqrt(2)>11/20.

### 2.1. A support-contact cap

Suppose an actual contained unit E has a minimum support point P in
a unit direction n, with h=n.P>=F. Its width w in this direction
satisfies

    1<=w<=R-h<25/12-59/60=11/10.

Its center projection is h+w/2>89/60. Since its center norm is
less than 91/60, its perpendicular center coordinate has magnitude
strictly less than

    sqrt((91/60)^2-(89/60)^2)=sqrt(1/10)<1/3.

A square has equal widths in perpendicular directions. Thus every
point of E has perpendicular coordinate of magnitude less than

    1/3+(11/10)/2=53/60.

The contained-neighbor support bound also gives h<=d<61/60.
At the actual support point P this proves the uniform estimate

    |P|^2<(61/60)^2+(53/60)^2=6530/3600.            (3)

This statement is force-free and includes every vertex or side mean.

### 2.2. The entire actual A return cover

The third A force, toward B, is East. If either of its two returns
were an A-owned North or South axis, the physical triangle ATD would
make the other return's vertical component have that same weak sign.
The full A vertical force would then be nonzero. Thus neither vertical
axis is possible.

If one return is horizontal, full vertical balance makes the other
horizontal too. East and West together violate the owned-axis triangle
inequality. Both East cannot balance the positive East AB force.
Both West would put two distinct actual units beyond x<=-F. Their
centers would lie in the one rectangle

    -91/60<x<-89/60, |y|<sqrt(1/10),

whose squared diameter is

    (2/60)^2+4/10=1444/3600<1.

This contradicts their center separation. Every horizontal return
mean and endpoint is included in that estimate.

Therefore both returns strictly expose actual A vertices, and their
vertical components have opposite signs. If their horizontal signs
were opposite, they would occupy opposite strict A corners, which
cannot have physically touching outer neighbors. If both horizontal
signs were positive, all three A forces would have positive horizontal
component. Hence both signs are negative. Exactly one return is
strict Northwest at

    P_+=(-F,c),

and the other is strict Southwest at

    P_-=(-F,c-1).                                      (4)

This feature cover has not yet assigned the labels T and D.

## 3. The upper A corner has height strictly greater than 1/60

First suppose c<=0. At P_+, any strict Northwest normal (-u,v),
u,v>0, has strictly negative origin moment

    det(P_+,(-u,v))=-F*v+c*u<0.                       (5)

If the lower return moment were positive, full true T2 torque would
make the original triangle A,T,D a directed positive-moment cycle,
in whichever labeling of (4) occurs. At A, the contact chord from
P_+ to P_- has strictly positive angular advance: it is a downward
vertical segment at x=-F<0, and

    det(P_+,P_-)=F>0.

The center-to-port strands are homotopic to this chord within x<0,
since c_A,x=a-1/2<0. At T and D the complete physical far-body port
theorem gives nonnegative angular advances; that theorem imposes no
degree-two equation or neighbor-clearance premise at D. The sum is
strictly positive, so the actual triangle loop has positive winding.

On the other hand, the general full A3 touching-return separation
puts the whole actual T and D in x<a. Their physical boundary
clearance r>a prevents either from meeting the nonnegative x-axis.
The two A strands have x<0 as just observed. Thus the whole actual
center/contact loop avoids that ray and has winding zero. This is
a contradiction. No embedding of a fictitious A--C edge or a private
positive component was used.

Consequently the lower moment is nonpositive. Write its strict
Southwest normal as (-s,-v), s,v>0, s^2+v^2=1. At P_- this says

    F*v<=(1-c)*s.

The actual support of that return is therefore

    h=F*s+(1-c)*v>=F/s>=F.

Apply (3) to its actual neighboring unit. But

    |P_-|^2=F^2+(1-c)^2>7081/3600>6530/3600,

an impossibility. This proves c>0. From y_A<0 and (2) we also
have c<1, so O belongs to int(A).

If c<=1/60, the actual upper-right A vertex (a,c) has norm less
than sqrt(2)/60<1/40. The complete small-origin-corner contact
kernel says that two distinct physical boundary neighbors of an
origin-containing square with such a vertex cannot touch one another.
Apply it to the actual A,T,D. Their genuine TD contact contradicts
that kernel. Therefore

    1/60<c<1.                                         (6)

All zero return-moment endpoints were retained in the first argument;
in particular a nonpositive moment was never deleted as a force.

## 4. The actual boundary path fixes the return labels

Let F_L,F_T,F_D,F_C be the complete nonzero circle-resultant vectors,
with their actual nonnegative corner weights. The true loaded-two
proper-concurrence lemma applies to C because its actual neighbor D
is physically boundary. With its original C-to-B normal East and
application (a,y_C), the concurrence q_C satisfies

    q_C=(a,y_C)-ell_C*East, ell_C>=0,
    q_C is a positive multiple of F_C.

Thus F_C,y>0 by (1), regardless of C's physical circle mask.

The actual three-boundary path T--D--C has

    F_D=u*F_T+v*F_C, u,v>0.

This is the full boundary-path resultant-cone theorem: no force or
degree-two equation is imposed on D, and all physical zero-weight
corners remain. Sum all original forces in this actual positive
component. The genuine leaf resultant is a positive East multiple,
so the vertical coordinate of the exact component equation is

    (1+u)*F_T,y+(1+v)*F_C,y=0.

Consequently

    F_T,y<0.                                          (7)

If T were the upper return in (4), its own true loaded-two
concurrence, using its actual boundary neighbor D, would obey

    q_T=P_++ell_T*n_AT, ell_T>=0.

Both c and the vertical component of n_AT would be positive, hence
q_T,y>0. Its positive proportionality to F_T contradicts (7).
Therefore the labels are fixed:

    A-to-T strict Southwest at P_-,
    A-to-D strict Northwest at P_+.                   (8)

At T the strict minimum-support span in the North direction now
gives the whole-unit bound

    max_T y<c.                                        (9)

This proof is about the actual circle resultants, not center-angle
proxies or a chosen positive corner of D.

## 5. Complete physical C frame and original return features

Write y=y_C. Then C lies in x<=a and contains its actual right
support point or mean

    P_C=(a,y), 0<y<=1.

Its norm is less than d, since a^2+y^2<=a^2+1<d^2. A physical
two-circle unit is radial S and every point of it has norm at least
d. Thus C has exactly one physical circle corner Z. Its full
concurrence is in the actual C, is a positive multiple of Z, and has
height y. In particular Z_y>0.

The full original C2 vertical force has its East BC term equal to
zero and its circle term positive. Therefore the actual C-to-D normal
has strictly negative vertical component. The whole D lies in x<a,
by full A3 separation, so no actual CD point can have x=a.

### 5.1. The parallel C frame

If C is parallel to B, write

    C=[-F,a] x [g-1,g].

Since F>a, its unique circle corner with positive height is necessarily

    Z=(-F,g), F^2+g^2=R^2.

Thus

    g>sqrt(13)/2>9/5, g-1>4/5,
    q_C=(-F*y/g,y), -F<q_C,x<0.                       (10)

A and C have the same horizontal interval. Since C is above the
origin-containing A, physical interior disjointness forces

    g-1>=c.

The full negative-vertical CD normal and proper concurrence leave
only the following actual CD possibilities:

* the owned South bottom side, with original mean
  R=((q_C)_x,g-1);
* the strict Southwest bottom-left vertex R=(-F,g-1).

The strict Southeast bottom-right vertex has x=a and is already
excluded by whole-D separation. All remaining features have zero or
positive vertical normal component. In the owned South row the
original mean is determined by concurrence, rather than arbitrarily
moved along the side; its zero normal-line length is allowed.

### 5.2. The tilted C frame

Otherwise P_C is the unique actual rightmost C vertex. Its complete
inward frame has the form

    u_C=(-k,l), v_C=(-l,-k),
    k,l>0, k^2+l^2=1,
    C=P_C+[0,1]u_C+[0,1]v_C.                         (11)

Neither P_C nor either adjacent corner can be a circle point:
|P_C|<61/60, and an adjacent corner has norm less than
121/60<sqrt(17)/2. Therefore its unique physical circle corner is

    Z=P_C+u_C+v_C=(a-k-l,y+l-k).

In particular

    R^2=a^2+y^2+2-2a(k+l)+2y(l-k).

If l<=k the right side would be at most 3+a^2<17/4, which is
impossible. Hence

    l>k.                                              (12)

Write q_C=P_C-ell*East. Its positive radial proportionality to Z,
whose x coordinate is negative, gives ell>0. In the actual C frame

    q_C-P_C=ell*k*u_C+ell*l*v_C,
    0<ell*k<=1, 0<ell*l<=1.                          (13)

We retain these weak endpoints; no unnecessary strict-interior premise
is imposed on q_C.

Physical A--C disjointness first gives y>=c. Otherwise the inward
horizontal direction at the rightmost C vertex enters int(A), since
y>0>c-1. The lower C vertex P_C+v_C has x=a-l strictly between
-F and a, and has height y-k>c-1. If it had height below c, it
would belong to int(A). Consequently

    min_C y=y-k>=c.                                   (14)

Here A--C is only a disjointness constraint between actual units;
no physical or positive A--C contact has been assumed.

The exact negative-vertical CD cover, using (13) and proper
concurrence, is now

    (i)  C-owned -u_C: R=P_C+ell*l*v_C;
    (ii) strict lower vertex: R=P_C+v_C;
    (iii) C-owned +v_C: R=P_C+ell*k*u_C+v_C.          (15)

The first two points have x>-F. In row (iii),

    c<R_y=y-k+ell*k*l<=y<=1.                          (16)

For completeness, the other owned axes have positive vertical
component; the upper adjacent vertex has only positive-vertical
support normals; the rightmost vertex is excluded by x=a; and the
opposite vertex is the physical circle point Z, which no other
actual unit can contain. This exhausts all original owned, free,
shared and endpoint possibilities. The strict lower-vertex row does
not assign its normal an owner.

## 6. Every vertex alternative at the actual AD point is impossible

Put P=P_+=(-F,c). By (8), its original A-to-D normal is strict
Northwest. Suppose P is an actual D vertex.

The open tangent quadrant of A at P is Southeast. The two actual
orthogonal inward D edges cannot have a sector meeting that quadrant.
The full right-angle sector cover therefore puts D either entirely
in x<=-F or entirely in y>=c. This includes edge-on-axis endpoints.
The latter alternative contradicts the actual TD contact and (9).
Thus

    D lies in x<=-F.                                  (17)

If D were parallel to A, its actual minimum for a strict Northwest
normal at P would be its bottom-right vertex. It would again lie in
y>=c, already impossible. Hence D is tilted and P is its unique
rightmost vertex. Write its actual inward edges as

    r_D=(-q,p), s_D=(-p,-q),
    p,q>0, p^2+q^2=1.

Containment and (17) give p+q<=R-F<11/10. Therefore

    min(p,q)<1/8, max(p,q)>sqrt(63)/8>59/60.          (18)

Indeed sqrt(1-t^2)+t is increasing on [0,1/sqrt(2)], and at
t=1/8 it is (sqrt(63)+1)/8>11/10. The last comparison in (18)
follows by squaring positive quantities.

### 6.1. The parallel C frame is impossible

The owned South CD mean in (10) has x>-F and cannot belong to D.
The remaining strict Southwest point is (-F,g-1). Since P is D's
unique rightmost vertex, it would equal P, giving c=g-1>4/5.

But (17) puts the whole D beyond the wall x<=-F<-39/40. The
complete force-free wall estimate gives |c_D,y|<3/20. Its y width
equals its x width p+q<11/10. Thus

    max_D y<3/20+11/20=7/10,

contradicting its actual point P of height c>4/5. This uses the
wall estimate for the whole contained D, not a selected circle corner.

### 6.2. The tilted C frame is impossible

Rows (i) and (ii) of (15) have x>-F, so they cannot meet D.
Thus the actual CD normal is C-owned +v_C, and its actual point
has the heights (16). The outward normal from D to C is

    g=-v_C=(l,k).

Its dot product with s_D is strictly negative. Its dot product with
r_D is

    g.r_D=-l*q+k*p.

If this is negative, D's unique g support is P, of height c,
contrary to (16). If it is positive, that support is P+r_D, of
height c+p. By l>k it then follows that p>q; hence (18) and (6)
give c+p>1, again contradicting (16).

Finally suppose g.r_D=0. The actual unit frames satisfy

    (l,k)=(p,q), u_C=r_D, v_C=s_D.

The actual CD contact may now use any point or mean of that full
D side; it is not assigned a corner. Equality of the two genuine
support lines requires

    v_C.P=v_C.P_C+1,
    l+k*(y-c)=1.                                     (19)

But (14) gives y-c>=k. Thus the left side of (19) is at least

    l+k^2=1+l*(1-l)>1,

another contradiction. This last row includes a shared CD segment
and both of its original endpoint means.

The entire D-vertex alternative has therefore been excluded. Since P
is an actual support point of D, it lies instead in the relative
interior of a D side. Its original strict Northwest normal is that
side's actual inward axis. This proves the theorem.

## 7. Exact operative inputs and the remaining obligation

| Source | SHA256 | Exact use |
| --- | --- | --- |
| LOWER_HOUSE_TDC_S_CLOSED_ORIGIN_SUPPORT_AND_SHALLOW_REDUCTION.md | 53a1f33837c353088f83b5226c2e37dfef6434037cd149755af4f24758cbfad6 | Only its global original CD/BC/BA nonzero-moment fact and literal full graph scope |
| UNLOADED_BOUNDARY_TRIANGLE_HUB_THIRD_SUPPORT_AND_CRITICAL_EXCLUSION.md | d8661132bd2d97911116373d22968bbde2ff3c4c4a63c962c72d722ec3d5b089 | Previously complete d<=1 join; no high-row exclusion borrowed |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Whole actual T/D lie in x<a at the full unloaded A3 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete owned-axis triangle implication and strict whole-unit support span |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 | Only its Section 2 degree-free opposite-strict-corner physical obstruction |
| D_LEAF_ROOT_BELONGS_TO_EVERY_CYCLIC_BLOCK.md | 9dd28b72bf8a837747c39c50c1d30f3f6d405f4442e39eda47d38d4485acb743 | Only its degree-free physical far-body port order; no D leaf or degree premise at D |
| GENERAL_SMALL_ORIGIN_CORNER_CONTACT_KERNELS.md | b977be65217728c0363e8bab030bdb3d11b1b8ef75cc32d295a8337c4ea01477 | Actual origin-containing A with a small vertex cannot have touching boundary neighbors T/D |
| ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md | 6ebda6299f692af6380ad36b98420aeb3155cf95a6b586e1df3848807d4cf467 | Uniform center bounds and the complete force-free wall estimate in Section 3 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Only Lemma 2.1 at the true original loaded T2/C2, each with actual boundary neighbor D |
| THREE_BOUNDARY_PATH_RESULTANT_CONE.md | 9789d4cf5dc456512fd2713e78b722c94325c51f93ac973c535f4249a1a68d9e | Full actual T-D-C resultant cone, retaining the loaded degree-three middle star |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Only the physical two-circle radial-S classification used to identify C's unique corner |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | The actual genuine aligned S root/leaf rectangles |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Exact original graph, all true degrees, load mask and all-nine contract |

The surviving interface retains a D-owned strict-Northwest AD contact
at P=(-F,c), with P in that D side's relative interior, and the
actual strict-Southwest T return at (-F,c-1). Sections 5.1--5.2
retain all remaining physical C frames and full CD contacts. No
conclusion about their final incompatibility is asserted here.

No normal was reselected after extraction, no side mean was changed,
no positive force was omitted, and no degree-three loaded equation was
replaced by a two-force one. This source does not use a sampled pose,
mesh, numerical certificate, Lean compilation or CI, and does not
change any original ledger or whole-family flag.
