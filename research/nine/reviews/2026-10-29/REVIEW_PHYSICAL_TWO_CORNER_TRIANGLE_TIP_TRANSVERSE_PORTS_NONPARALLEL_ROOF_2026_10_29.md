# Independent full review: transverse ports of a physical-two triangle tip

Date: October 29, 2026 UTC. Reviewer: nonparallel_roof.

## 1. Decision and exact reviewed object

**PASS unchanged** for the complete local transverse-port exclusion,
the exhaustive necessary inner-face domain, and both literal D02
caller transfers. The source does not exclude the two remaining
inner-face features or either whole original D02 row.

The complete reviewed source is

    PHYSICAL_TWO_CORNER_LOADED_TRIANGLE_TIP_TRANSVERSE_PORT_EXCLUSION_AND_INNER_FACE_DOMAIN_2026_10_29.md
    SHA256 317de21d86ca2559dd225911ced5358f1049329d7c2a8a3892d193749a188d1c
    476 LF lines; 21179 bytes.

I read all 476 source lines and reconstructed the complete support
cover, all force/moment signs, the AD parallel/nonparallel alternatives,
the two residual parameter domains and the original graph substitutions.
I did not supply the new proof steps or edit the reviewed source. An
earlier author progress message was not used as proof or as a substitute
for the full source reconstruction below.

The result is selection-free inside the accepted actual separating
normal construction: it imposes no new generic parameter restriction.
It retains every original positive force and full aggregate mean.

## 2. Scope and radius audit

The local hypotheses are exactly three actual pairwise-touching units
A,V,D, with V truly loaded of positive pair degree two and the two
triangle hubs unloaded of true positive pair degree three. Their
neighborhoods are V:{A,D}, A:{V,D,B}, D:{V,A,C}. The actual B,C
are distinct from the triangle and each other. The proof never gives
them a degree-two equation or requires them to be boundary units.

The broad analytic hypotheses are

    R>sqrt(2), d=sqrt(R^2-1/4)-1<3/2.

They imply d>0. The entire original closed radius window satisfies
them, including its lower endpoint 79/40. No use of an R>2-only
exit or a high-radius premise is hidden in the proof.

In fact the transverse-port contradiction uses only the full
unloaded three-force equation of the hub at the transverse port.
At the opposite hub it uses only the two actual triangle contacts
and pure square geometry. The source correctly states this broader
one-hub local implication without replacing the main two-hub
setting or adding a third-neighbor premise at the opposite hub.

The condition d<3/2 is used precisely in the final strict support
reserve. At d=3/2 that displayed proof would lose its reserve for
some directions; the source does not silently include that endpoint.

## 3. Complete physical mask and support budget

The two physical circle corners are adjacent. In farthest-corner own
coordinates the adjacent comparisons give a,b>=1/2. An opposite
equal-radius corner forces a+b=1 and therefore a=b=1/2, outside
the actual radius domain. Exactly one coordinate is tied at 1/2.
Thus the actual, circle-centered radial-S chart is forced:

    a=sqrt(R^2-1/4)=d+1,
    V=[d,a] x [-1/2,1/2],
    Z_+=(a,1/2), Z_-=(a,-1/2).

The full physical force is

    F=k*(a,eta), k=2*(lambda_++lambda_-)>0,
    eta=(lambda_+-lambda_-)/(2*(lambda_++lambda_-)).

I checked both endpoint interpretations: eta=-1/2 means lambda_+=0,
and eta=1/2 means lambda_-=0. Both are still physical-two masks.
The source neither normalizes away an individual zero coefficient
nor substitutes a unique-corner force argument.

The unshareable-circle-point argument is complete. At a contained
corner Z, each unit inward edge u satisfies Z.u<=-1/2. Hence -Z
is strictly interior to its inward quadrant. A short common radial
inward segment would lie in the open interiors of any two actual
units containing Z, which is impossible. A point of the containing
circle cannot be side-interior in a contained square, by strict
convexity of that circle. Thus every physical circle point is
excluded as a pair application, regardless of its circle coefficient.

The support budget for an arbitrary actual unit K follows directly
from its full corner-radius bound:

    max_corner |z|^2
      =|c|^2+1/2+|c.u|+|c.v|
      >=|c|^2+|c|+1/2.

Therefore |c|<=d+1/2. A unit square has directional halfwidth at
least 1/2, so lying beyond support n.z>=h forces h<=d. No boundary
status, selected circle coefficient or additional force premise
is used here.

I also checked the actual point-membership lemma Q+[0,1]n subset K
at a minimum-n support Q. At a vertex the two inward own components
of the unit vector n lie in [0,1]. At side-interior n is the inward
own axis. Side endpoints belong to the vertex case. This lemma
includes every original shared-side mean and does not move Q.

## 4. Pure physical triangle inputs are used at their actual scopes

I read the complete proper-port proof in Section 2 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md. For a nonparallel pair
of actual outward normal lines at any physical triangle vertex,
it proves P=q+alpha*n, Q=q+beta*m with alpha,beta>=0.

The proof covers both own axes with arbitrary means, one own
axis and a strict vertex, identical strict vertices, and distinct
adjacent strict vertices. Opposite strict vertices are eliminated
by the radius-free unit support-span estimate and the actual
contact of the other two units. No circle-load equation or true
degree-two condition is needed for this Section 2 statement.

The reviewed source uses only that pure statement at A and D.
It does not import the end-triangle source's later radial-resultant
or boundary-tip arguments into either unloaded hub.

The separate side-normal obstruction was read in full. It gives
n.m>=0 when n is an own side axis at a triangle vertex. The zero
dot-product case is retained, and all original side means remain.
The reviewed proof does not strengthen this to a strict inequality.

Two parallel outward normals at a triangle vertex cannot have
opposite signs: their actual neighboring units would lie beyond
opposite supports separated by the positive width of that vertex
unit. The required physical neighbor-neighbor contact would fail.
This also has no load or degree premise.

Throughout these arguments, the normal lines are the lines through
the actual applications parallel to their actual normals. They are
not the supporting lines perpendicular to those normals.

## 5. Full V support cover and transverse reduction

The outer vertices are unshareable physical circle points. East
would require its real neighbor beyond a=d+1>d and contradict the
actual-unit support budget. The remaining exact support features
are West, North, South, strict Northwest at the upper inner corner,
and strict Southwest at the lower inner corner.

The complete North feature has actual x in [d,a), retaining x=d
and every allowed shared mean; x=a is the forbidden circle point.
At a North port the side-normal triangle obstruction removes
every other feature with negative vertical component, including
South and strict Southwest. Another North has positive origin
moment x>=d>0. A strict Northwest (-c,s) at (d,1/2) has moment
d*s+c/2>0. Thus these same-sign possibilities contradict the
unchanged full V2 moment equation.

The only possible companion is West at (d,-t). Its moment is -t.
With the actual positive magnitudes mu for West and nu for North,
the exact equations are

    mu*t=nu*x,
    mu=k*a, nu=-k*eta,
    0<t<=1/2, d<=x<a, eta<0.

The strict t>0 is derived from positivity, not omitted from an
endpoint audit. The endpoint t=1/2 and eta=-1/2 remain. The
South case follows by reflecting all actual geometry and forces.
This covers every transverse side port before the support argument.

## 6. Every original AD endpoint and sign in the support contradiction

Name the West neighbor A and the North neighbor D. At A its
triangle normals are East and g, while at D they are South and
-g. Here g is the unchanged A-to-D normal, with actual magnitude
gamma>0 and original application W.

If A's pair is parallel, the opposite-sign physical obstruction
forces g=East. If D's pair is parallel, it forces g=North. These
are the complete cases in which one of the hub concurrences is
undefined. Neither is lost by dividing by a determinant.

Otherwise the pure proper-port theorem supplies

    q_A=(d-alpha,-t), alpha>=0,
    q_D=(x,1/2+beta), beta>=0,
    W=q_A+s*g=q_D-u*g, s,u>=0.

The same actual AD mean occurs in both expressions. Thus

    q_D-q_A=(s+u)*g
      =(x-d+alpha,1/2+t+beta).

Its horizontal component is nonnegative and its vertical component
is strictly positive. Therefore s+u>0 and g has both components
nonnegative. The two parallel cases also have this property.
Zero individual proper lengths, x=d and either endpoint of an
original positive shared AD interval are all retained.

The complete unloaded D3 force equation is now essential:

    F_DC=nu*North+gamma*g.

Its actual unit direction n has n_x>=0 and n_y>0. No exterior
term has been dropped to obtain this equation. Since Q=(x,1/2)
is the actual minimum-North support of D, the physical segment
lemma places Q+North=(x,3/2) in D. Hence its actual external
support obeys

    h_D(n)>=x*n_x+(3/2)*n_y
      >=d*(n_x+n_y)+(3/2-d)*n_y>d.

The strict inequality uses n_x+n_y>=1, d>0, n_y>0 and d<3/2.
It includes n=North and all parallel-AD endpoints. The real
neighbor C lies beyond this exact support, contradicting its
budget h<=d. This is a uniform contradiction, not a sampled
normal or a relaxed fictitious-neighbor argument.

## 7. Complete surviving cover and distinctness

After the transverse exclusion only West and the two strict
inner-corner supports remain. Two West normals are parallel.
Two strict normals at the same upper corner have positive
moments; two at the lower corner have negative moments.
The same-sign corner possibilities cannot balance.

With one West and an upper strict corner, full torque puts
the West mean strictly below height zero. With two strict
corners, they must be different inner corners. This proves
actual application distinctness over the whole remaining
physical-two domain, including all West mean endpoints.

The source correctly permits a strict corner normal to be
owned by its actual hub or to be genuinely free. No unique-
corner selector is applied to either physical-two row, and
there is no unproved owner restriction on AD or the exterior
contacts.

## 8. Independent reconstruction of both residual full V2 domains

For the West/upper-corner row write p=s/c>0. The actual V2
equations give

    mu/nu=c*(d*p+1/2)/t,
    eta=-a*t*p/(d*p+1/2+t).

The entire physical interval eta>=-1/2 is exactly

    (2*a*t-d)*p<=1/2+t.

The factor 2*a*t-d is never divided out. Its sign need not
be fixed. Equality retains the zero upper-corner coefficient;
reflection retains the opposite zero coefficient. The actual
intersection of the original two normal lines is

    q_V=(d+(1/2+t)/p,-t).

Direct substitution gives q_V,y/q_V,x=eta/a. Its x-coordinate
is positive and strictly above d, but may exceed a. Thus its
positive radial proportionality does not imply membership in V.

For the two-strict-corner row put u=mu*c, v=nu*C, p=s/c,
q=S/C. The complete torque gives

    v/u=(d*p+1/2)/(d*q+1/2).

Combining both force components then gives exactly

    eta=a*(q-p)/(2*(1+d*(p+q))).

The full closed physical-weight interval is equivalent to

    q-(2*d+1)*p<=1,
    p-(2*d+1)*q<=1.

The first equality is eta=1/2 and the second eta=-1/2.
Neither is lost. Equal weights p=q are allowed and do
not make the two actual normals parallel.

The actual intersection is

    q_V=(d+1/(p+q),(q-p)/(2*(p+q))).

Both port distances along their actual outward normals
are strictly positive. Its height is strictly between
-1/2 and 1/2, and direct substitution again gives the
same positive radial line through the full F_V. There
is no proof or use of q_V,x<=a. Both formulas are valid
necessary domains; the manuscript does not claim every
parameter point is physically realizable with the hubs.

## 9. Literal original-domain transfer and retained limitations

The original chord-02 hexagon map is A=0,V=1,D=2,C=3,N=4,B=5.
Its rim is 01,12,23,34,45,50 and its positive chord is 02.
In both L135 and L1345, A,D are unloaded true3, while V,B,C
are loaded true2. N is unloaded true2 in L135 and loaded
true2 in L1345. The graph reflection exchanges A,D and
B,C together, fixing V,N; it preserves these actual degrees.

Every local hypothesis is literal in both original callers.
All three actual completing units remain. No whole packing
is replaced by a subconfiguration, no hub is made degree
two, and no N force is deleted in L1345. The local theorem
works for both rows without using an exterior equation.

The source's final limitation is correct and substantive:
the surviving two charts are not excluded. This theorem
does not close the physical-two nonparallel feature,
the unique-mask feature, either original row or any
coarse parent. No count or flag change is justified by
this reduction alone.

## 10. Exact checked inputs and verification boundary

All five directly cited input pins were recomputed and match:

| Input | LF / bytes | SHA256 | Operative scope reviewed |
| --- | --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | 399 / 17993 | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original force/moment and mean conventions, read in full in this continuation and unchanged |
| LOADED_PARALLEL_FULL_STAR_WITH_DISTINCT_NEIGHBORS_FORCES_RADIAL_S_2026_10_29.md | 271 / 12041 | f0e7b44a8d7e0eff5654384bf20bb5a99c3809d57a92bbb16afba6ee7ac1c96c | Complete Section 2 physical-mask, circle-point and inward-segment facts; no parallel-star conclusion imported |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | 132 / 4431 | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete radius-free triangle theorem and zero-dot endpoint, read in full |
| END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md | 226 / 8686 | 20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf | Complete Section 2 proper-port theorem; the full file was read to verify later narrower scopes were not imported |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | 244 / 11952 | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original rim/chord, load labels, unchanged nine-unit contract and exact chord-02 graph degrees |

This is a full independent review of the new theorem and
its complete operative joins. It does not pretend to replace
every historical recursive proof behind the accepted physical
certificate construction. No new selection compatibility is
required by this selection-free reduction.

No numerical pose sample, finite angular mesh, computational
packing certificate, Lean/Lake, CI/workflow, remote mutation,
source repair, metadata or original flag edit was used.
