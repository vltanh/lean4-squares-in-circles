# A sole triangle cannot carry two pendant paths at one root

Date: October 26, 2026.

**Status: accepted complete theorem after full-source root review in REVIEW_BRIDGE_MATCHING_TRIANGLE_FORESTS_ROOT_2026_10_26.md and separate review in REVIEW_TRIANGLE_TWO_PATH_ROOT_GLOBAL_2026_10_26.md.** All nine physical squares, the common canonical pose, and the
original equations of the selected minimum-support stress are retained.
No shared ledger or original gate is changed by this source.

## 1. Full component scope

Work in 79/40<=R<=sqrt(1105)/16 with

    d=sqrt(R^2-1/4)-1, epsilon=max(d-1,0), r=R-sqrt(2).

Keep the common physical normals, all actual shared-side means, complete
circle masks, zero individual weights and all zero-stress physical contacts.
Choose minimum positive scalar support on the unchanged radius/Phi-minimizer
pose by `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md`.

**Theorem.** A selected positive component with exactly one cyclic block,
a triangle A--B--C--A, cannot have two distinct pendant paths attached to
the same triangle vertex A. Other bridge trees may be attached at B or C;
they and their full forces are included in this theorem.

Use the complete theorem
`ROOTED_TRIANGLE_FOREST_OUTSIDE_FORK_EXCLUSION.md` first. There are no
branching vertices outside the triangle. Every bridge branch is thus a
simple pendant path, with genuinely unloaded degree-two internal bodies
and a genuine radial S/D leaf. The articulation selection permits at most
two such branches at a triangle vertex, because the intact triangle is one
other branch of that articulation.

If every bridge branch is attached to A, the accepted whole theorem
`GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md` already excludes
the component. Accordingly suppose another triangle vertex has a bridge
branch. It ends in a third genuine leaf, distinct from the two terminals
of A's paths. Its root is different from A and from any internal
degree-two body already supporting one of those two terminals.

## 2. Both original paths have length one or two

All internal bodies have already been proved unloaded. Their original
radial channel equations give, for an arm in its actual leaf direction e,

    p_A=(r_L-W)e, r_L in {r,d},

where W is the sum of its intermediate widths, each in {1,sqrt(2)}.

An arm of at least four edges has W>=3. Since r_L<=d<61/60, its actual
support puts c_A dot e<-149/60, contrary to |c_A|<91/60. Thus no such arm
occurs, regardless of any original circle load or additional force at A.

If one arm has length three, its signed support x=r_L-W satisfies
x<-59/60. Since A is in e dot x<=x and contains x e, that application is
its unique nearest point to the origin, of norm greater than 59/60.
The second arm cannot be a direct leaf: a direct S root meets D_epsilon
along the unit inward segment from d e, and a direct D root contains zero.

For a second arm of length at least two, its signed application is either
negative or the sole nonnegative S/width-one alternative epsilon. A
nonnegative application is too near zero. If it is negative, uniqueness of
the nearest point forces the two actual leaf directions to agree. Two S
leaves on that ray coincide, two D leaves coincide, and an S/D pair on the
same ray overlaps in an open set. Each alternative is physically
impossible. This argument uses no equilibrium equation at A.

Consequently A's two path lengths are (1,1), (1,2), or (2,2). Their full
force-free root geometries are the two-arm classifications in
`GLOBAL_CLOSURE_ONE_ROOT_TRIANGLE_FORESTS_EXCLUDED.md`, Section 3. In
particular D_epsilon subset A, with zero in its interior when d!=1.

## 3. Every noncritical radius is excluded by the actual third leaf

If d<1, only the two-direct-leaf case survives and zero is interior to A.
Every other genuine leaf root contains zero, so the third leaf cannot
occur.

Suppose d>1. Two direct leaves put the closed D_epsilon strictly inside A.
Every other genuine leaf root meets that disk: a D root contains zero and
an S root contains its actual inward-segment endpoint epsilon e. Hence a
third leaf is impossible in this case too.

In a mixed (1,2) root the only point of boundary(A) in D_epsilon is
epsilon e in the direction of the existing S length-two arm. In a (2,2)
root the only such points are epsilon e_1 and epsilon e_2 in the two actual
orthogonal S arm directions. All other points of the closed disk are in
the open interior of A. A third D root is therefore impossible; the third
S root must have its inward endpoint at one of those displayed tangent
points. Its actual leaf would repeat the corresponding already present
radial S square. This is impossible for a distinct genuine leaf.

Thus all d!=1 alternatives are excluded. This is a statement about the
original physical third leaf, not about a stress with a force deleted.

## 4. Physical tools at d=1

Now R^2=17/4 and d=1. Every outside unloaded positive-degree all-bridge
body contains zero by
`GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md`. Every genuine leaf root
also contains zero. A D leaf puts zero in the open interior of its root;
an S root contains its original unit inward segment from e to zero.

We use three accepted physical completion theorems with their full domains:

* `P_ALL_COMPLETION.md` excludes every four-square P skeleton consisting
  of S(e), S(-e) and two side-aligned unit squares occupying the radial
  intervals [-1,0] and [0,1], with arbitrary transverse intervals of length
  one containing zero. Every endpoint slider is included, and every other
  physical square is retained in the completion problem.
* `Y_ALL_COMPLETION.md` excludes the entire nonaligned five-square Y:
  a vertex-origin root [0,1]u+[0,1]v with S(u),S(v), a side-origin unit
  aligned to e with e dot u<0 and e dot v<0, and S(e). The side-origin
  point is relative interior; all open angle and slider parameters remain.
* `THREE_VERTEX_ORIGIN_CAPACITY.md` excludes nine physical squares whenever
  three of them have zero as a vertex. It assumes no stress or positive
  contact graph for those three units.

We shall use these only after identifying their actual original bodies.

### 4.1. A vertex root with two orthogonal S terminals has no other boundary neighbor

**Physical lemma.** Suppose

    H=[0,1]u+[0,1]v, S(u), S(v)

are three actual interior-disjoint units at R^2=17/4. No other physical
circle-touching unit can touch H.

Here u,v are orthonormal and S(w) is the actual radial unit of (2) in
`ROOTED_TRIANGLE_FOREST_OUTSIDE_FORK_EXCLUSION.md`. This lemma has no
force, degree or positive-circle-weight premise.

Every center has norm at most 3/2. If a distinct center lies in the closed
quadrant of H, the inscribed radius-1/2 disk and the bound |c|<=3/2 force
it to be 3u/2 or 3v/2. For completeness, in own coordinates a point
(x,y)>=0 must have distance at least 1/2 from [0,1]^2. If just x>1,
y<=1, this forces x>=3/2 and hence (x,y)=(3/2,0). The exchanged case is
identical. If both x,y>1, then

    dist(c,H)^2=x^2+y^2+2-2(x+y)<9/4+2-4=1/4,

impossible. The remaining region is inside H. This is the full
single-quadrant lemma of `THREE_VERTEX_ORIGIN_CAPACITY.md`.

The two exceptional centers are already occupied by S(u),S(v). Thus an
additional boundary center c lies outside the closed quadrant. Write
r_c=|c|. Circle contact gives

    r_c>=sqrt(17)/2-1/sqrt(2)>4/3,   r_c<=3/2.             (1)

The strict lower comparison follows from 71>48sqrt(2), whose squared
reserve is 5041-4608>0. Center separation from S(u) gives

    cos(angle(c,u)) <= (r_c^2+5/4)/(3r_c) <= 7/9.          (2)

The last function is increasing on [4/3,3/2]. The same bound holds for v.
Put gamma=arccos(7/9). Since c is outside the quadrant and separated from
both boundary directions by at least gamma, its minor angle theta from
the bisector (u+v)/sqrt(2) satisfies theta>=pi/4+gamma. Hence

    cos(theta) <= (7-4sqrt(2))/(9sqrt(2)).                 (3)

If the boundary unit touched H, their center distance would be at most
sqrt(2), and c_H=(u+v)/2 would give

    cos(theta) >= (r_c^2-3/2)/(sqrt(2) r_c)
               > 5/(24sqrt(2)).                         (4)

The expression is strictly increasing with r_c>0. Finally

    (7-4sqrt(2))/9 < 5/24

is equivalent to sqrt(2)>41/32, an exact strict comparison. Equations
(3)--(4) contradict each other and prove the full physical lemma.

### 4.2. Two vertex-origin units and an additional origin body

Two vertex-origin unit squares either share one full side or meet only
at zero. In the latter case their two complementary angular gaps are
positive and sum to pi; each is less than pi. A third square containing
zero cannot have a side-interior or interior origin, since its tangent cone
would have angle at least pi. It would be a third vertex-origin unit,
excluded at nine squares by the preceding physical capacity theorem.

If a vertex-origin unit and a side-origin unit have a strict nonaligned
separator at zero, the two remaining angular gaps are each less than
pi/2. No further square containing zero fits. These elementary cone
observations refer to all physical squares, including zero-stress extras.

## 5. The critical (1,1) root

The complete two-direct-leaf geometry says either zero is interior to A,
or

    A=[0,1]u+[0,1]v

with its two actual leaves S(u),S(v). In the interior case the third
genuine leaf root is impossible immediately.

In the vertex case choose the original third leaf and let K be its actual
root. K contains zero, is distinct from A, and cannot have zero in its
interior. The third leaf is therefore S. If zero is in a relative side
interior of K, let f be that leaf direction. It is K's sole norm-one
radial support direction, on the opposite side. Tangent-cone disjointness
gives f dot u<=0 and f dot v<=0. If both are strict, the five actual
units A,K,S(u),S(v),S(f) are the complete physical Y skeleton. If one
vanishes, f=-u or f=-v, and A,K together with the corresponding opposite
S pair form a physical P skeleton. Both completions are impossible.

It remains that zero is a vertex of K. If K and A share a side, their
cones are adjacent coordinate quadrants. The two possible unit radial
directions of K are the shared side ray and the opposite of A's other
side ray. The third leaf cannot use the shared ray: that would repeat an
existing S leaf of A. Thus it uses the opposite ray, and A,K with that
opposite pair of actual S units form a P skeleton. This is impossible.

Consequently A and K meet only at zero. Section 4.2 says they are the
only physical squares containing zero in the hypothetical nine-packing.

If K is outside the triangle, it is an original unloaded degree-two
transmitter. Its S leaf direction is one of its side axes and its
width is one. Its other actual bridge application is zero. The next body
on the path toward the triangle therefore contains zero too. That body
cannot be A: A's two allowed bridge branches are already its two genuine
direct leaves. It is a third origin-containing unit, a contradiction.

If K is a triangle vertex, call it B. The third triangle vertex C cannot
have degree two. Such an unloaded degree-two tip would separate its two
physically touching neighbors, so it would have to be circle-loaded and
physically touch the boundary. But Section 4.1 excludes every such
boundary neighbor of A other than its two actual S leaves.

Thus C has an attached bridge path. Its terminal's actual leaf root is
distinct from A and B: the bridge forest cannot return to another
triangle vertex or to either rooted bridge tree without another cycle.
That root contains zero. Again it is a forbidden third origin-containing
unit. This covers every attachment and extra force at B and C, including
a second path at either one.

The entire critical (1,1) root is excluded.

## 6. The critical (1,2) root

The complete mixed-arm classification at d=1 forces a direct S leaf and
a width-one S arm. Let e be the arm direction, U its true unloaded
intermediate body, and S(e) its original terminal. The actual A--U
application is zero. Thus A and U both contain zero on their boundaries,
U is side-aligned to e, and A lies in e dot x<=0.

Choose the original third leaf root K. It is distinct from A and U,
because A already has its two allowed branches and U has its exact
degree two. It contains zero. Its leaf is S, since a D root would put
zero in its open interior and overlap A or U.

If zero lies in a relative side interior of A, the direct S leaf can
only point along -e. The two actual radial terminals S(e),S(-e) and
the two actual inner units A,U form a P skeleton, including both
possible endpoint positions on U. Hence zero must be a vertex of A.

### 6.1. Zero is also a vertex of U

The original channel normal is a side axis of U. A point-only
vertex/vertex contact with this normal would violate the selected
strict point-normal convention. Therefore A and U have a positive-length
shared side. Their frames are the same and, for some perpendicular v,

    A=[0,1](-e)+[0,1]v,
    U=[0,1]e+[0,1]v.                                    (5)

The third origin body K cannot be a vertex-origin unit, by the physical
three-vertex capacity theorem. It must have zero in a relative side
interior; the tangent cones in (5) already fill the v-positive half-plane,
so K occupies the v-negative half-plane. Its actual S leaf is S(-v).

The direct leaf of A is either S(-e) or S(v). In the first case A,U
and S(e),S(-e) form P. In the second case A,K and S(v),S(-v) form P.
Both are the full physical P family with retained endpoint sliders.

### 6.2. Zero is in a relative side interior of U

Its tangent cone is e dot x>=0. Both inward side rays of A have
nonpositive dot product with e. If both are strictly negative, the two
remaining angular gaps are each less than pi/2, leaving no room for K.

Otherwise A has the form in (5), while U is the side-origin unit in
the e-positive half-plane. The only possible remaining cone for K is
the quadrant generated by -e and -v. Thus

    K=[0,1](-e)+[0,1](-v).

The direct S leaf of A points along -e or v. If it is S(-e), A,U
and S(-e),S(e) form P. Otherwise it is S(v), and K's actual S leaf
is either S(-e) or S(-v). In the former case K,U and S(-e),S(e)
form P; in the latter A,K and S(v),S(-v) form P. Each alternative
uses four unchanged original units in the complete physical P theorem.

These cases exhaust every side slider and endpoint of the critical mixed
root. They use no triangle force equation at A, whose actual positive
degree remains four throughout.

## 7. The critical (2,2) root

The exact force-free classification gives A=[-1,0]^2 in the two actual
orthogonal arm directions. Both genuine intermediate transmitters U_1,U_2
contain zero, their original A applications. The original third leaf root
K also contains zero and is distinct from A,U_1,U_2.

If both U_i have zero as a vertex, A,U_1,U_2 violate the physical
three-vertex capacity theorem. Otherwise one has a side-interior origin,
whose tangent cone has angle pi. Together with A's right-angle cone and
the other U_i's cone of angle at least pi/2, these already occupy the full
angle 2pi. No additional K with cone angle at least pi/2 can fit.

This excludes the entire (2,2) root whenever another attachment root is
present. The all-at-A case was already excluded by the one-root theorem.

## 8. Whole-family conclusion and next remaining class

The original two-arm root admits only lengths (1,1), (1,2), (2,2).
Section 3 covers all noncritical radii. Sections 4--7 cover every
critical physical feature, side slider, normal endpoint, leaf type and
attachment at the other triangle vertices. No original graph force was
dropped or reassigned to a physical S body used in a capacity theorem.

Thus no selected sole-triangle component has two pendant paths at one
triangle vertex. Combined with the complete outside-fork exclusion,
every remaining bridge branch is a single pendant path and at most
one path is attached at each of the three triangle vertices.

The exact canonical-pose and minimum-support premises remain attached.
The theorem alone does not exclude all length-three paths at distinct
roots, does not close C1.3.b4, C1.3.b5 or C1.3.b6, and gives no unrestricted
sharp-radius or equality claim. No numerical pose sampling, Lean
compilation, CI or remote action is used.
