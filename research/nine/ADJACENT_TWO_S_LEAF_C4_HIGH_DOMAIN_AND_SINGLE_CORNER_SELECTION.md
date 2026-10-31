# The high adjacent-S-leaf C4: full original domain and a single-corner owner reduction

Date: October 27, 2026.

**Status: complete hand necessary-domain theorem and compatible
single-corner selection theorem, submitted for full root and separate
independent review.** This is not a whole high-family exclusion.
In particular the complete two-physical-circle-corner masks remain;
the owner conclusion in Section 5 is confined to the stated unique /
unique physical mask. No fine or coarse gate is counted here.

Keep all nine actual contained, interior-disjoint unit squares and the
common compatible selected certificate. The exact positive component is

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

L and M are the genuine S leaves at the adjacent cycle roots A,B.
C,D have positive total circle load and physically touch. A,B are
physically clear. All three other original units remain arbitrary and
present, as do every actual force, contact owner, application mean,
physical circle mask and individual zero circle weight.

Work in the remaining strict-high domain of
M6.B4L2.C4.ADJACENT.LCD.SS:

    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<epsilon<1/60,       R^2<=1105/256.

Let e_L,e_M be the unit directions of the actual two radial leaves.
Their applications at their real roots are d*e_L and d*e_M,
and their original positive resultant magnitudes are alpha,beta.
Their root forces have zero origin moments. Each real root contains
its particular inward-segment point epsilon*e_L or epsilon*e_M.

The new finite selection in Section 5 is made on the fixed physical
pose before multiplier extraction, simultaneously with the earlier
strict, nonradial and matched-junction choices. It changes no normal
or application in an obtained certificate. Its only use of a physical
circle mask is an actual unique corner at each of C,D, not an
assumption that one of two physical corner weights happens to vanish.

## 1. A touching boundary pair excludes every other radial-S center from its resultant cone

Let S,T be any two physically touching boundary units in the declared
radius window, with arbitrary nonnegative physical-circle-corner
weights of positive total. Write their full nonzero resultants as
F_S,F_T. Let U be a third physical radial S unit, with center
direction e_U. Then

    e_U is not a positive multiple of a*F_S+b*F_T
    for any a,b>0.                                      (1)

This statement requires no force equation, degree or contact owner.
It keeps both physical masks and all individual zero corner weights.

To prove it, use the complete geometric facts in
CIRCLE_CONTACT_ANGULAR_ORDER.md and CENTERED_INNER_ARC.md. After
reflection choose lifts of the two actual center angles as

    theta_S=0,       theta_T=delta,
    2*pi/9<delta<2*pi/5.

The minor center arc between them contains no other boundary center.
Section 1 of FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md puts every
physical circle corner, and every nonzero nonnegative circle
resultant, strictly within pi/12 of its own center direction.
Consequently the resultant lifts satisfy

    -pi/12<phi_S<pi/12,
    delta-pi/12<phi_T<delta+pi/12,
    0<phi_T-phi_S<2*pi/5+pi/6<pi.

Every positive sum in (1) has its direction strictly between phi_S
and phi_T. If the distinct radial-S center direction e_U were in
that interval, its lift would belong to
(-pi/12,delta+pi/12). It cannot be in [0,delta], by the physical
angular-neighbor rule and distinctness of center directions. In the
remaining two intervals it is less than pi/12 from one endpoint
center, contradicting the strict 2*pi/9 center separation.

This proves (1). The actual radial S center is (d+1/2)e_U, so its
direction is exactly the real leaf direction when this is applied
to L or M. No circle-force direction is identified with a general
boundary square's center direction.

## 2. The two genuine leaf directions are not parallel

Equal leaf directions would give the same physical radial S unit,
whereas L and M are distinct original squares. Opposite directions
are also impossible.

Indeed the unchanged component force equations sum to

    alpha*e_L+beta*e_M+F_C+F_D=0.                       (2)

The actual C,D boundary pair has strictly acute physical corner
pairs, by ACUTE_LOADED_CONTACT_GRAPH.md. Its positive-total
resultants satisfy F_C.F_D>0, so F_C+F_D is nonzero. If
e_M=-e_L, equation (2) makes that nonzero sum a positive multiple
of e_L or e_M. Both are actual distinct radial-S center directions.
This contradicts Section 1. Hence

    det(e_L,e_M)!=0.                                   (3)

This is a complete exclusion of the parallel genuine-leaf directions
for every physical C,D mask. It does not assume any side orientation
or contact mean at A,B.

## 3. Both real roots are near, and every tilted root is shallow

Let n be the original unit AB normal directed A to B, and let h
be its actual support value. The two real inward-segment points give

    epsilon*(n.e_L)<=h<=epsilon*(n.e_M),
    -epsilon<=h<=epsilon.                              (4)

The original AB application P satisfies n.P=h. Equation (4)
controls the support line, not the tangential position of P; no
point norm or midpoint claim is inferred from it.

There is also a useful uniform physical description of either root
when it is tilted relative to its own genuine leaf. Reflect and
exchange its own axes to write that real root as

    [U-1,U] times [V-1,V],
    U>=V>0,       U^2+V^2=d^2.

The other actual root has a real point in the closed disk D_epsilon.
That point cannot belong to this root's open interior. We claim

    U>=1-epsilon,
    |U-1|<=epsilon,
    0<V<=2*sqrt(epsilon)<13/50.                         (5)

If U<1-epsilon, then U>=d/sqrt(2)>epsilon and
V<=d/sqrt(2)<1-epsilon. If V<=epsilon, the identity
U^2=d^2-V^2>=d^2-epsilon^2=1+2epsilon>1 contradicts
U<1-epsilon. Thus V>epsilon as well. All four actual side
margins would exceed epsilon, putting the whole closed D_epsilon
inside this root's open interior. That contradicts the other
root's actual near point. Therefore U>=1-epsilon, and the other
two assertions follow from U<d and

    V^2=d^2-U^2<=d^2-(1-epsilon)^2=4*epsilon.

This is precisely the purely physical argument used in Section 1
of DIAMOND_TWO_S_LEAVES_TILTED_TIP_FULL_DEGREE_DOMAIN.md; it has
no triangle, neighbor-degree or force premise. In the present graph
it applies separately at A and B.

Accordingly the complete arbitrary-degree theorem
SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md applies to
each actual tilted root. In its own coordinates, every physical
circle corner of every boundary neighbor lies on the strict negative
side of the transverse vector (-V,U). In particular it applies to
D at A, and C at B, with every actual physical mask retained.
It does not assign boundary status to the other genuine root.

## 4. The unchanged four-body force and moment identities

Orient the original cycle A to B to C to D to A. Write its actual
unit normals, positive magnitudes and applications as

    n_1,n_2,n_3,n_4,
    mu_1,mu_2,mu_3,mu_4>0,
    P_1,P_2,P_3,P_4.

The exact full force equations are

    mu_1*n_1-mu_4*n_4+alpha*e_L=0,
    mu_2*n_2-mu_1*n_1+beta*e_M=0,
    mu_3*n_3-mu_2*n_2+F_C=0,
    mu_4*n_4-mu_3*n_3+F_D=0.                         (6)

Every circle term and genuine leaf has zero moment about the actual
circle origin. The four true body moment equations therefore give
one unchanged directed cycle moment

    mu_i*det(P_i,n_i)=tau       for i=1,2,3,4.          (7)

The actual CD edge joins two physical boundary units, so its moment
is nonzero by CIRCLE_CONTACT_ANGULAR_ORDER.md, Lemma 6.1 (or the
stronger oriented statement in FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md,
Lemma 1.1). Thus tau!=0. In particular P_1!=O, and the actual
AB application has not been replaced by a radial or central point.

The true C2 and D2 pairs are nonparallel by Lemma 2.1 of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, since their actual
neighbor across CD is physical boundary. Their genuine proper
concurrences are positive multiples of F_C and F_D. That theorem
retains the physical two-corner masks and all actual means; only
its single-physical-corner clause puts a concurrence in its unit.
No analogous concurrence or nonparallel conclusion is assigned to
the true A3/B3 root pairs by this paragraph.

## 5. With unique physical corners at both C,D, AB has an actual side-axis owner

Assume now that C and D each have exactly one physical circle
corner, say z_C,z_D. Put

    e_C=z_C/R,       e_D=z_D/R,
    F_C=lambda_C*e_C,       F_D=lambda_D*e_D,
    lambda_C,lambda_D>0.

These four external directions e_L,e_M,e_C,e_D are fixed by the
physical pose. Application means on AD,BC,CD may still vary over
their complete physical segments. The conclusion is:

**There is a compatible necessary certificate, with all preceding
properties retained, in which the original AB normal is a side axis
of A or B.** A free point-only vertex/vertex AB contact cannot occur
in this complete unique/unique physical mask.

The proof uses the full translational equations alone. Thus it does
not falsely fix an original AD or BC shared-side application in
order to apply the earlier singleton-star selection theorem.

### 5.1. The exact force-cycle determinant

Taking the determinant of each equation (6) with its own external
unit direction and multiplying the four resulting equalities gives
the necessary identity

    K*det(n_1,e_L)-L*det(n_1,e_M)=0,                    (8)

where

    K=det(n_2,e_M)*det(n_3,e_C)*det(n_4,e_D),
    L=det(n_4,e_L)*det(n_2,e_C)*det(n_3,e_D).          (9)

Equivalently (8) is det(n_1,K*e_L-L*e_M)=0.
Every original positive magnitude cancels in this necessary
identity; no force was discarded from (6). No application point
or moment has entered (8).

### 5.2. The finite choices are made before extraction

At the fixed physical pose, prelist every ordered assignment of
the six distinct component bodies and its two candidate genuine
radial-S leaves, for which C,D have the unique physical corners
above and e_L,e_M are nonparallel. These are finitely many pose
data. Use the original finite product of open permissible point-
normal intervals, with the prescribed matched coefficients at
four-square junctions.

First choose every free point normal to avoid the finitely many
candidate radial-S leaf directions and their opposites. This is
compatible with strict exposure and the previous finite nonradial
avoidances. It does not restrict any fixed side-axis normal.

For each prelisted cycle with AB free, retain only the cases that
do not use both opposite body pairs of a four-square junction.
Those omitted cases are already impossible in the final uncrossed
certificate. In each retained case the free AB parameter can vary
over an open interval while the other three cycle normals remain
fixed. At a four-square junction only its other opposite pair is
linked to that parameter; the other contacts are fixed own-axis
side contacts. At other junctions there is no matched-parameter
constraint. Thus the stated independent variation is valid in the
original compatible normal domain.

Add to the finite prelist the avoidance of (8) for every such tuple
for which its left side is not identically zero on that parameter
domain. These are ordinary finite open dense avoidances. For fixed
other normals, a nonzero expression det(n_1,W) has only finitely
many zeros on the free open interval. More generally the complete
expression is a real analytic polynomial in the normal components;
after local slope coordinates and multiplication by positive
normalizing factors it is an ordinary polynomial. A nonzero such
polynomial cannot vanish on a nonempty open parameter set. The
intersection of the finitely many dense open complements is nonempty.

Perform this choice simultaneously with the earlier ones before
applying the physical multiplier theorem. Original uncrossing
retains each surviving point normal and adds only the already
available shared-side endpoint forces. Conic thinning only deletes
atoms. The prelist includes all these fixed physical side axes,
so any surviving tuple still satisfies the selected avoidances.
The subsequent minimum-positive-atom choice may be taken within
the same nonempty admissible class.

### 5.3. An identically zero tuple cannot evade the conclusion

Suppose a positive original unique/unique component survived with
AB free. The first finite avoidance gives

    det(n_1,e_L)!=0,       det(n_1,e_M)!=0.

The first two actual equations (6) then force
det(n_4,e_L)!=0 and det(n_2,e_M)!=0. The C2 pair n_2,n_3
is nonparallel. Its positive equation in (6) consequently makes
det(n_2,e_C) and det(n_3,e_C) nonzero. The same argument at
true D2 makes det(n_3,e_D) and det(n_4,e_D) nonzero. Thus
both actual K and L in (9) are nonzero.

By (3), the actual vector K*e_L-L*e_M is nonzero. Holding the
other three normals at these actual values and varying the free
AB parameter therefore makes the left side of (8) a nonzero
sinusoidal linear form. It is not identically zero on the allowed
open interval. Hence this tuple was included in the finite avoidance
list of Section 5.2. Its necessary equation (8) contradicts that
original selection.

This excludes every free AB in the unique/unique physical mask.
The original physical contact classification then leaves a normal
owned by at least one actual square side. This includes vertex/side
contacts, side/side contacts and their actual mean endpoints. It
does not assert that both roots are parallel, that a mean is in a
relative side interior, or that a specified one of the two roots
owns the normal. Since both C,D are loaded, the actual attachment
reflection may exchange A,B and C,D when a later caller chooses
which root to name as the owner.

## 6. Exact retained frontier

Sections 1--4 apply to the whole original high LCD.SS family, at
all physical C/D masks and every original contact mean. Section 5
adds one complete necessary owner restriction only when each of
C,D has a unique physical circle corner.

If C or D has two physical circle corners, it is an actual radial
S square. Both original corner weights, including an individual
zero, stay in its full C2/D2 equation. No owner restriction from
Section 5 is claimed in that mask. This entire mask and the complete
unique/unique owner-domain still require their respective whole
exclusions or the three-extra completion theorem.

The exact balanced six-body example in
ADJACENT_TWO_S_LEAF_C4_HIGH_CORE_WITNESS.md is not contradicted:
its C,D have unique physical corners and its actual AB is already
owned by both roots. The exact-grid capacity theorem is a separate
physical completion input; the present source does not claim that
every surviving root frame is that grid.

All nine units and true A3/B3/C2/D2 equations remain. No false
triangle-neighbor concurrence, fixed shared mean, normal reselection
after extraction, force deletion, numerical pose, compilation, CI,
remote action or shared-metadata edit is used.
