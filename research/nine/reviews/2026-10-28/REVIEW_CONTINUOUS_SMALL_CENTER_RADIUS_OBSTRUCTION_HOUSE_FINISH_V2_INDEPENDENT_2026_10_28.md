# Independent full review of the continuous small-center radius obstruction

Date: October 28, 2026 UTC. Reviewer: house_finish_v2.
Author of the reviewed target: root continuation.

**Verdict: PASS at the exact frozen target pin below.** The continuous
two-parameter theorem is valid for

    1/sqrt(2)<b<1, 0<=a<=1/b-b.

One actual unit center of norm at most a permits at most two other
actual centers in the closed radius-b disk. The proof includes the
entire equality curve, every allowed closed radius endpoint, arbitrary
actual square orientations and both exceptional open b endpoints.
The stated 19/25 center-count consequence is valid throughout the
whole existing aligned-house chart. It neither supplies an angular
location nor closes the original house family.

## 1. Exact complete read set and independent method

I read the complete target and all four direct sources, including
their original graph scope and physical endpoint statements. The
exact bytes read are:

| File | SHA256 | Bytes | Lines |
| --- | --- | ---: | ---: |
| CONTINUOUS_SMALL_CENTER_THREE_NEIGHBOR_RADIUS_OBSTRUCTION.md | 5dc6820cdc19844cbf6472d8913bbef83a43397bc6324e3b1e46427b4c13b63c | 11954 | 271 |
| SMALL_CENTRAL_UNIT_EXCLUDES_THREE_OTHER_THREE_QUARTER_CENTERS.md | 5ec9509ff5e2e79c25a4bd9d59d3ee2a53dd2fcf5c0ddd039c93add3552e2a14 | 9098 | 215 |
| ALIGNED_S_ROOT_SHALLOW_BOUNDARY_PAGE_EMPTY_CENTER_GAP.md | 5681926e8705af07ab4cde28d16e859c42ed8bab71f69e01641844efab47ae0a | 20709 | 462 |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | 17789 | 376 |
| THIRTY_SEVEN_FIFTIETHS_CENTER_UNIT_CENTERED_FORTY_DEGREE_ARC.md | aef1a6c7a6ac6631c5b236f50301b31db2f87441b1f9e22883686d8f70032282 | 10415 | 280 |

The complete read set has 1604 lines. All four direct pins match
their current source bytes. I independently derived the monotonic
cosine-law interval, every equality implication, the exact critical
center coordinates and the physical distance-one axis obstruction.
Exact rational arithmetic checked the displayed house reserves.
No source was edited and no prior review verdict was substituted
for reading the target's proof.

Sections 1--5 of the target are self-contained. Its predecessor
identifies the old fixed parameter pair and its chart; the actual
physical equality lemma is proved again in the new source. The
graph and arc inputs only supply the stated original-family and
threshold consequences. No numerical pose, angle mesh, orientation
enumeration or computational exclusion certificate is involved.

## 2. Full physical center separation, including distance one

Every actual unit contains its open radius-1/2 incircle, so centers
of two distinct interior-disjoint units have distance at least one.
This remains true for arbitrary relative orientation and physical
contacts; no positive edge or circle load is needed.

The target's equality rigidity is valid. A closed separating line
exists for two convex squares with disjoint open interiors. With
its unit normal n directed from the first square to the second,
center displacement w=d-c and actual directional halfwidths give

    1=|w|>=n.w>=h_c(n)+h_d(n)>=1.

At |w|=1 every comparison is equality. Equality in the first
comparison gives n=w. Both actual halfwidths equal 1/2. In
either square's actual orthonormal side frame, this means

    |n.u|+|n.v|=1, (n.u)^2+(n.v)^2=1.

The two nonnegative components therefore have zero product, so
one is one and the other zero. Thus w is a signed side-axis
direction of each square. This auxiliary geometric separating
line does not change any selected original contact normal.

This is the precise square-specific fact needed to exclude the
equality configuration. A conclusion from center separation alone
would leave that configuration unexcluded.

## 3. The entire parameter domain and all zero-radius cases

For 1/sqrt(2)<b<1, put a_*=1/b-b. Then

    0<a_*<b<1,
    gamma=1-1/(2b^2) belongs to (0,1/2),
    theta=acos(gamma) belongs to (pi/3,pi/2).

The supplied r=|c_A| satisfies 0<=r<=a<=a_*.
If r=0, no further center of norm at most b can exist at all,
because its distance to c_A would be below one. In particular
the theorem includes a=0. If a proposed further center were O,
its distance from c_A would be r<1, also impossible. All angular
directions used in the nontrivial proof are consequently defined.

For 0<x,y<1, independent differentiation gives

    F(x,y)=(x^2+y^2-1)/(2xy),
    partial_x F=(x^2-y^2+1)/(2x^2 y)>0,
    partial_y F=(y^2-x^2+1)/(2x y^2)>0.

Both signs hold on the whole displayed open domain. The exact
critical substitution simplifies to

    F(a_*,b)=(1-2b^2)/(2b^2)=-gamma,
    F(b,b)=gamma.

All actual radii in the proof lie in this strict monotonicity
domain, including when their upper bounds are attained.

## 4. One complete angular interval forces the critical equality

The cosine law and actual center distance at least one imply

    cos(angle(c_A,c_E))<=F(r,|c_E|)<=-gamma.

Since acos(-gamma)=pi-theta, this is exactly the single closed
interval of halfwidth theta about the direction opposite c_A.
Its full length is 2theta<pi. This statement concerns actual
center directions only and makes no assertion about a square's
whole occupied region.

For two proposed further centers the same argument gives minor
angular separation at least theta. Their directions are distinct:
two nonzero centers on the same ray with radii at most b<1
would have distance below one.

Order three such directions in the containing interval. Because
its length is below pi, each successive difference is its minor
angle. Each is at least theta, so their total span is at least
2theta, while the containing interval gives at most 2theta.
Thus the outside directions are exactly its endpoints, the middle
is exactly its midpoint and both successive differences equal theta.

For either outside direction, the entire cosine-law chain is now
an equality. Strict monotonicity forces r=a_* and that outside
radius equal to b. An adjacent-pair equality similarly forces
the middle radius to be b. The other outside radius is handled
in the same way. Since r<=a<=a_*, this also forces a=a_*.
Therefore every strict parameter inequality is already impossible;
the only possible remaining case is the full exact critical curve.

No equality was discarded by a generic-position assumption. In
particular |c_A|=a, |c_E|=b and b(a+b)=1 remain until this
explicit reduction, where their geometry is evaluated exactly.

## 5. Exact critical coordinates exclude the whole equality curve

Rotate only about the unchanged O to put c_A=(a_*,0).
The middle center is (-b,0), and the endpoint centers are

    c_+=(1/(2b)-b, sqrt(1-1/(4b^2))),
    c_-=(1/(2b)-b,-sqrt(1-1/(4b^2))).

These expressions follow from -b gamma=1/(2b)-b and
b^2(1-gamma^2)=1-1/(4b^2). Their displacements from the
same actual A are

    v_+=(-1/(2b), sqrt(1-1/(4b^2))),
    v_-=(-1/(2b),-sqrt(1-1/(4b^2))).

Both have norm exactly one, and their scalar product is

    v_+.v_-=1/(2b^2)-1 in (-1/2,0).

The physical equality lemma makes both signed vectors side axes
of the same actual square A. Such scalar products can only be
-1, 0 or 1. The displayed whole open interval contains none
of these values. This contradiction is strict for every allowed
b, and excludes every configuration on the critical curve.

## 6. Individual-center formulation and both excluded b endpoints

For 0<r<1/sqrt(2), the expression

    B(r)=(sqrt(r^2+4)-r)/2

is the positive root of B^2+rB=1. It lies strictly between
1/sqrt(2) and one. Taking a=r,b=B(r) therefore gives the
stated closed-radius conclusion directly, including its equality
curve. Conversely, r<=1/b-b implies b<=B(r), so this individual
formulation also recovers the corresponding nonzero-r cases of
the parameter theorem. The third-smallest center radius must be
strictly greater than B(r) whenever at least three other units
exist; a weak greater-than conclusion would lose the proved endpoint.

The separate r=0 assertion is accurate: center separation gives
every other center radius at least one, with equality possible.
It does not extend the strict B(r) conclusion to that endpoint.

Both physical counterexamples in Section 5 check. At
b=1/sqrt(2), four axis-aligned unit squares with centers at
(+/-1/2,+/-1/2) are interior-disjoint and all have that radius.
The critical displacement scalar product becomes zero, allowing
their common square axes. At b=1,a_*=0, a square at O and
the three stated axis-aligned side neighbors have disjoint interiors
and attain radius one. These examples justify both strict b
endpoints. The source correctly makes no additional global
sharpness claim from them.

## 7. Entire aligned-house threshold and exact numerical reserves

The physical chart used by the corollary is

    2<=R<=sqrt(1105)/16,
    A=[d-1,d] times [-beta,1-beta],
    L=[d,d+1] times [-1/2,1/2],
    1/3<=beta<=1/2.

I checked the full shallow-page source's original-family entry.
Its same-nine lower-radius input gives R>2. Its low aligned
argument, including the centered strict-SE endpoint, supplies
1/3<beta<=1/2. Its critical/high house-valid reduction supplies
353/1000<=beta<=1/2. Both are contained in the corollary's
closed interval. The real B--C--D branch and full A4/D3 are
retained; the fan-only second triangle is not used for this house.

The exact geometric bounds are

    14/15<d<61/60,
    c_A=(d-1/2,1/2-beta),
    |c_A|^2<(31/60)^2+(1/6)^2=1061/3600.

I verified the lower and upper d reserves, respectively 11/900
and 31/57600. Taking b=19/25 gives exactly

    a_*=25/19-19/25=264/475,
    b^2-1/2=97/1250>0,
    (264/475)^2-1061/3600=460699/32490000>0.

Thus the entire physical chart has |c_A|<a_*, and every premise
of the continuous theorem is supplied. The previous pair
a=7/12,b=3/4 is itself exactly another point on the same curve,
since 1/(3/4)-3/4=7/12.

Among any three further actual units at least one must therefore
have center radius greater than 19/25. Among any four, at least
two must. If a retained D is one of these four and has radius at
most 19/25, it consumes one of the at most two allowed small
centers, so at least two of the other three are strictly larger.
All equality cases at radius 19/25 have been counted as small.

In the literal original HOUSE.HUB.LTCB.S graph, these four units
can be taken to be the actual unloaded D and the three actual
completion units. Their original contacts and loads are unchanged:

    AT,DT,AD,AB,BC,CD,AL;
    true A4,D3,T2,B2,C2,L1;
    positive circle loads at T,B,C,L.

Every qualifying center is strictly above the accepted centered-arc
threshold because 19/25-37/50=1/50>0. The old threshold is
improved by 19/25-3/4=1/100. The complete arc source retains
all actual orientations and puts its closed forty-degree arc in
the actual unit interior; no physical boundary or positive load
premise has been added to make that relation hold.

## 8. Exact acceptance and remaining scope

I accept the exact
5dc6820cdc19844cbf6472d8913bbef83a43397bc6324e3b1e46427b4c13b63c
target at its complete printed parameter and original-chart scope.
No repair or source edit is needed. The result proves one uniform
continuous restriction and a stronger necessary house center count.

It does not locate those large centers in an angular gap, assert
that their whole units occupy a pocket, identify their boundary
status or declare any original whole-family flag closed. All nine
actual units, true degrees, full forces and torques, original normals
and applications, physical masks and individual zero coefficients
remain available to the later house proof. No BD contact is inferred.

No computational certificate is introduced or retired by this review.
No Lean/Lake, CI/workflow, metadata/count edit, staging, commit,
publication or remote action was performed. The target and all four
direct sources remain at their frozen pins, pending root's exact
adoption of this separate independent review.
