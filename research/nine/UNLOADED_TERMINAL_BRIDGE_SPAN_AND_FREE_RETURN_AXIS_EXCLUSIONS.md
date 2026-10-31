# A real one-unit bridge excludes two complete free-return axis configurations

Date: October 29, 2026 UTC. Author: roof continuation, with the actual bridge-span observation contributed by root continuation.

**Status: complete proposed radius-free geometric and full-stress hand theorems, submitted for a separate full independent audit.** The original bridge body is retained. The first exclusion covers the entire sole-terminal-axis configuration with a free return to that bridge endpoint, regardless of the other return's owner. The second excludes every nonzero parallel incoming shift when the bridge-end return is free. Both give literal features of the original D02.L014 and D02.L0145 families, with every actual unit and its original positive degree retained. Neither original family is asserted closed in full.

## 1. Actual data and the two statements

All units below are actual closed unit squares with pairwise disjoint open interiors. No containing radius or physical circle contact is required for the local results. In any circle-stress caller, every original circle corner and its coefficient remain present; a body called unloaded has zero total original circle load, rather than an asserted absence of physical circle contacts.

For a unit direction `r`, write

    h_K(r)=max_{z in K} r.z,
    l_K(r)=min_{z in K} r.z,
    w_K(r)=h_K(r)-l_K(r).

An original positive contact `IJ` has its actual unit separating normal `n_IJ` from `I` to `J`, its positive magnitude, and its unchanged application point in the actual intersection. A positive shared segment retains its entire original weighted mean, including its endpoints. Thus its support identity is

    h_I(n_IJ)=n_IJ.P_IJ=l_J(n_IJ).                 (1)

Use the same compatible strict point-normal certificate selected before extraction. An isolated vertex/vertex contact has a normal strictly exposing the two actual vertices. A **free** contact means that its original normal is a side axis of neither incident square. There is no selection or perturbation after extraction in this manuscript.

Retain distinct actual units

    U,V,W,T_1,...,T_m,C,B, with m>=1,              (2)

with the following common hypotheses.

* `U` is unloaded true positive degree three, with exactly the positive neighbors `V,W,T_1`.
* `UV`, `UW`, and `VW` are actual positive edges. In particular the real units `V` and `W` physically touch.
* `U--T_1--...--T_m--C` is an actual positive path. Each `T_i` is unloaded true positive degree two, with exactly its displayed predecessor and successor.
* The single actual unit `B` physically touches both `C` and `W`. These two physical contacts need not have positive force. No direct `C--W` or `U--C` edge is inferred.

Every body's complete original force and torque equations are retained. The proof uses only the complete unloaded equations at `U,T_1,...,T_m`; it does not suppress a force at `V,W,C,B`. Their degrees, loads, physical masks, means and additional positive edges are arbitrary. In particular this theorem does not make either endpoint of the bridge a transmitter.

**Theorem A, entire sole-terminal-axis/free-return exclusion.** Under (2), suppose `n_UT_1` is an own side axis of `U`, both `n_UV,n_UW` are not own axes of `U`, and the original `UW` contact is free. Then the configuration is impossible. There is no restriction on the owner of `UV` or `VW`.

**Theorem B, entire nonzero parallel-shift/free-return exclusion.** Under (2), suppose `n_UV` is an own side axis of `U`, the actual frames of `V` and `U` are parallel modulo quarter turns, `n_UW` is not an own axis of `U`, and the original `UW` contact is free. Rotate and, if necessary, reflect the entire configuration into the parallel chart of Section 6. The tangential displacement of `V` relative to `U` must be zero. Every strictly positive or strictly negative displacement is impossible. The zero-displacement case is explicitly retained.

Both statements allow every side-normal or diagonal transmitter on the actual path, every actual `UT_1` owner, and every original path mean. In particular Theorem A does not require a preliminary radius reduction making `T_1` a side transmitter.

## 2. A sharp backward-reach bound for an actual unit

Let `K` be any actual unit, `Q` any point on its minimum-`m` support feature, and `m,r` unit vectors with

    m.r<0.

Then

    h_K(r)-r.Q <= sqrt(1-(m.r)^2) < 1.             (3)

The left inequality includes every closed support-side mean and endpoint, and includes `r=-m`, when its right side is zero.

First suppose `Q` is a vertex. Write

    K=Q+[0,1]e+[0,1]f,

where `e,f` are its perpendicular inward unit axes. The minimum support condition gives `m.e,m.f>=0`. If both `r.e,r.f` were nonnegative, then

    m.r=(m.e)(r.e)+(m.f)(r.f)>=0,

contrary to the hypothesis. Thus at most one inward edge contributes a positive `r` projection. For either inward unit edge `e` with `m.e>=0`, set `a=-m.r>0`. Resolve `r` and `e` into their components parallel and perpendicular to `m`. Cauchy's inequality gives

    r.e <= -a*(m.e)+sqrt(1-a^2)*sqrt(1-(m.e)^2)
         <= sqrt(1-a^2).

Taking the nonnegative part and then the sum over the at most one positive edge proves (3) at a vertex. If neither edge contributes positively, the maximum relative projection is zero and the same bound holds.

If `Q` lies in the relative interior of a minimum-support side, its inward perpendicular own axis is exactly `m`. This edge has negative `r` projection. The remaining tangential interval has total length one and contains `Q`; its possible positive projection from `Q` is at most

    |r.Jm|=sqrt(1-(m.r)^2).

This proves (3) for every possible actual support feature. In particular no contact mean has been replaced by an extreme point.

The strict `<1` in (3) follows solely from `m.r<0`; there is no angle compactness or quantitative separation premise. The sharp bound will be used to keep an entire return unit strictly on one side of a hub vertex.

## 3. The complete side-normal triangle fact

For completeness, the radius-free triangle fact needed in Theorem B follows immediately from (3). If actual units `U,V,W` all physically touch, `n` is an own side normal of `U` separating `U` from `V`, and `m` is any actual separating normal from `U` to `W`, then

    n.m>=0.                                          (4)

Indeed, if `n.m<0`, every maximum-`m` support point `Q` of `U` lies on the minimum-`n` side of `U`. The own-axis width of `U` in direction `n` is one, so

    n.Q=h_U(n)-1.

The same actual `Q` is a minimum-`m` point of `W`. Equation (3) gives `h_W(n)<h_U(n)`. Every point of `V` has `n` projection at least `h_U(n)` by its actual separation from `U`. Thus `V,W` are closed-disjoint, contrary to their physical contact. This proves (4), including its permissible perpendicular equality case.

This is the complete geometric statement of the pinned side-normal triangle source; no containing disk or force equation is used here.

## 4. Exact forward widths and the actual bridge constraint

Put `n=n_UT_1` and `h=h_U(n)`. At a genuinely unloaded true-degree-two body, the two complete positive forces are opposite and have equal magnitude. Consequently all original forward normals along the actual path in (2) equal `n`, with the same positive magnitude.

At each `T_i`, retain its original incoming and outgoing application means `P_i^-` and `P_i^+`. Complete torque balance gives

    n.J(P_i^+-P_i^-)=0.

These points lie on the two opposite support features of the same actual unit. Hence

    P_i^+-P_i^-=w_T_i(n)*n,
    w_T_i(n) in {1,sqrt(2)}.                         (5)

The two alternatives in (5) follow directly: an own-axis normal gives two opposite sides and width one; any nonaxis normal exposes opposite vertices, and their collinearity with `n` makes it a square diagonal, of width `sqrt(2)`. All side means and the two matching endpoints are included. Even the weaker general unit-width inequality `w_T_i(n)>=1` would suffice for the forthcoming contradiction.

Every actual contact joins the maximum support of its predecessor to the minimum support of its successor in the propagated normal. Iterating these equalities, without removing or contracting any physical square, gives

    l_C(n)=h+sum_{i=1}^m w_T_i(n) >= h+m.             (6)

Now choose actual physical points `c in C cap B` and `w in W cap B`. They exist by the two literal bridge contacts. Since they belong to the same unit `B`,

    l_C(n)-h_W(n)
      <= n.c-n.w
      <= |c-w|
      <= sqrt(2).                                    (7)

Equation (7) is valid regardless of the sign of its left side. It uses the diameter of the real body `B`, not a fictitious edge from `C` to `W`. It needs neither a boundary load nor any equation at `B,C,W`. Combining (6) and (7) yields the necessary condition

    h-h_W(n)+sum_{i=1}^m w_T_i(n) <= sqrt(2).          (8)

In particular a chart with `h_W(n)<=h-1` is impossible as soon as there is at least one actual unloaded true-two transmitter: its left side is at least `m+1>=2>sqrt(2)`. This entire bridge implication is radius-free.

## 5. Proof of Theorem A: the entire sole-terminal-axis case

Rotate so `n_UT_1=West=(-1,0)` and write the actual hub as

    U=[x-1,x] x [p-1,p].                              (9)

Let `n=n_UV`, `m=n_UW`, and let the unchanged positive magnitudes at `U` be `mu,omega,lambda`. Its complete unloaded force equation is

    mu*n+omega*m+lambda*West=0.                       (10)

Both `n,m` are nonaxes of `U`, so both components of each are nonzero, and their actual applications are uniquely exposed vertices of `U`. The vertical component of (10) says their vertical signs are opposite.

### 5.1. Opposite return vertices are impossible, at all owners

Suppose the actual `UV` and `UW` vertices `P,Q` were opposite vertices of `U`. Their outward support quadrants would be strictly opposite, so `n.m<0`. Since `P` maximizes `n` on `U` and `Q` is its opposite vertex,

    n.(P-Q)=|n_x|+|n_y|>1.                            (11)

But `Q` is an actual minimum-`m` point of `W`. Equation (3), with `r=n`, gives

    h_W(n)-n.Q <= sqrt(1-(m.n)^2)<1.

By (11), this implies `h_W(n)<n.P=l_V(n)`, contradicting the real `VW` contact. This argument uses no force, load, mask or owner at `V` or `W`.

The two return vertices therefore lie on the same vertical side of `U`. They cannot both lie on its left side, because then the horizontal component of every term in (10) would be strictly negative. Thus they lie on its right side. Reflect vertically if necessary, preserving all body labels, to obtain

    P=P_UV=(x,p),       Q=P_UW=(x,p-1),
    n=(a,b),           m=(c,-d),
    a,b,c,d>0,         a^2+b^2=c^2+d^2=1.             (12)

The reflection only makes the actual `V` return upper and `W` return lower; it does not exchange `V` with the bridge endpoint `W`.

### 5.2. All of V is strictly above the free return vertex

Apply (3) to the actual unit `V`, its actual minimum-`n` point `P`, and the direction South. Here `n.South=-b<0`, so

    h_V(South)-South.P <= a.

Equivalently,

    l_V(North)>=p-a>p-1=Q_y.                         (13)

This is the point at which an assumption that `UV` is V-owned could have been used, but (13) proves the stronger statement for every original owner and every physical `V` frame. In particular a free `UV` is included without any new normal selection.

### 5.3. A free UW then puts the entire W to the right

Because `UW` is free, `Q` is a strict minimum-`m` vertex of `W`. Let its inward own axes be `e,f`. They satisfy

    m.e>0, m.f>0.                                    (14)

Since `W` physically touches `V`, equation (13) gives an actual point of `W` with height strictly greater than `Q_y`. At least one inward edge therefore has positive vertical component. For that edge, (14) with `m=(c,-d)` forces its horizontal component to be positive too. It is strictly Northeast. The perpendicular inward edge cannot be Northwest, whose dot product with `(c,-d)` would be negative. It is strictly Southeast.

There are thus `C_0,S_0>0`, `C_0^2+S_0^2=1`, with the complete actual frame

    W=Q+[0,1](C_0,S_0)+[0,1](S_0,-C_0).              (15)

In particular every point of `W` has horizontal coordinate at least `x`, and its West support is exactly

    h_W(West)=-x.                                    (16)

No `VW` feature was selected in obtaining (15); its actual contact may have any owner and any allowed original mean.

### 5.4. The real bridge contradiction

From (9), `h_U(West)=1-x`. Equations (6) and (16) give

    l_C(West)-h_W(West)
       =1+sum_{i=1}^m w_T_i(West)
       >=m+1>=2>sqrt(2),                             (17)

contrary to (7) for the actual bridge `B`. This proves Theorem A, including all original terminal-side means, all transmitter alternatives and all owners on `UV,VW`.

## 6. Proof of Theorem B: every nonzero parallel incoming shift

By (4), the actual `UW` normal has nonnegative projection onto the own-axis `UV` normal. Rotate so `n_UV=North`. Since `n_UW` is not a U axis, both its components are nonzero; its North component must be strictly positive. Reflect horizontally if needed. Write

    U=[L-1,L] x [H-1,H],
    m=n_UW=(b_0,a_0), a_0,b_0>0,
    a_0^2+b_0^2=1,
    Q=P_UW=(L,H).                                    (18)

Actual parallel `V` lies immediately above `U`, with

    V=[L-1+s,L+s] x [H,H+1], -1<s<1.                (19)

The strict interval in (19) retains the chosen original convention. At `s=1` or `s=-1` the contact would be isolated at two vertices, while its original normal North would be a side axis, contrary to strict exposure at an isolated point. The full actual `UV` shared mean remains `(q,H)` with

    L-1+max(s,0)<=q<=L+min(s,0).                      (20)

Let the complete positive magnitudes at `U` be `mu,omega,lambda`. Its force is

    mu*North+omega*m+lambda*n_T=0.                    (21)

Consequently

    n_T=(-alpha,-beta),
    alpha,beta>0, alpha^2+beta^2=1,
    S=P_UT_1=(L-1,H-1).                              (22)

The entire original torque about `S` is, without changing the mean in (20),

    mu*(q-L+1)+omega*(a_0-b_0)=0.                    (23)

Equation (23) is retained and in particular gives `a_0<=b_0`; the span proof below already follows from the complete force (21) and physical geometry. No equality case of (23), or endpoint in (20), is discarded.

### 6.1. The positive-shift tangent-cone exit

Suppose `s>0`. The actual point `Q=(L,H)` lies in the relative interior of the bottom side of `V`. Near `Q`, the interior of `V` occupies the open upper half-plane. The interior of `U` occupies the open Southwest quadrant.

The inward tangent cone of `W` at the same point must avoid both of these open sets. Since it is the closure of its interior directions, it is contained in the closed Southeast quadrant. A square's side-interior cone is a half-plane, which cannot fit there. Its vertex cone has angle `pi/2`, so its two actual inward axes would have to be East and South.

However South has strictly negative dot product with `m=(b_0,a_0)`. This contradicts minimum-`m` support of `W` at `Q`. Thus every `s>0` is impossible, even without using the free-owner premise, the transmitter path, or the bridge.

### 6.2. The negative-shift free return has Q as its bottom vertex

Suppose `s<0`, and put `delta=-s>0`. Then every point of `V` has horizontal coordinate at most `L-delta<L`.

By the free `UW` premise, `Q` is a strict minimum-`m` vertex of `W`. Both inward own edges have strictly positive `m` projection. If the `W` frame were parallel to `U`, the only possible inward axes would be East and North. That would put all of `W` in `x>=L`, preventing its physical contact with `V`.

Otherwise both coordinates of both inward edges are nonzero. Neither edge can point Southwest, since both components of `m` are positive. Orthogonality then forces one edge to be Northeast and the other to be either Northwest or Southeast. If the other edge were Southeast, both inward horizontal components would be positive and again all of `W` would lie in `x>=L`, disjoint from `V`. The other edge must therefore be Northwest.

Thus `Q` is the actual unique bottom vertex of `W`, and

    z_y>=H for every z in W,
    m.(z-Q)>0 for every z in W distinct from Q.       (24)

All axis endpoints have already been included in the parallel-frame branch, so this is the complete free-return frame cover. No property of the actual `VW` owner or mean was required.

### 6.3. Full U3 makes Q the maximum-n_T vertex of W

Dot (21) with `z-Q`. For every `z in W` distinct from `Q`, (24) yields

    lambda*n_T.(z-Q)
       =-mu*(z_y-H)-omega*m.(z-Q)<0.

Therefore

    h_W(n_T)=n_T.Q.                                  (25)

The actual hub support in direction `n_T` is the opposite vertex `S` in (22). Hence

    h_U(n_T)-h_W(n_T)
       =n_T.(S-Q)=alpha+beta>1.                      (26)

Equations (6), (25) and (26) give

    l_C(n_T)-h_W(n_T)
       =alpha+beta+sum_{i=1}^m w_T_i(n_T)
       >1+m>=2>sqrt(2),                              (27)

contrary to the actual bridge constraint (7). This excludes every negative shift.

Together Sections 6.1--6.3 prove Theorem B: only `s=0` can remain. The argument does not assert (24) at zero shift. There, nonparallel `W` can instead have `Q` as its leftmost vertex, and a parallel `W` can share a vertical side with `V`; all such zero-shift possibilities and their original means remain outside the exclusion.

## 7. Literal original D02 low-load callers, including reflection

Retain the complete original graph

    01,12,23,34,45,50,02,
    degrees (3,2,3,2,2,2),                            (28)

and all three actual completing units. For both original rows use the exact roles

    U=2, V=1, W=0, T_1=3, C=4, B=5, m=1.            (29)

The full load and degree map is:

| Original row | Positive loads | Unloaded true-three hub | Unloaded true-two transmitter | Actual bridge | Unchanged endpoint data |
| --- | --- | --- | --- | --- | --- |
| D02.L014 | `{0,1,4}` | `U=2` | `T_1=3` | `B=5`, unloaded true two | `V=1` loaded true two; `W=0` loaded true three; `C=4` loaded true two |
| D02.L0145 | `{0,1,4,5}` | `U=2` | `T_1=3` | `B=5`, loaded true two | `V=1` loaded true two; `W=0` loaded true three; `C=4` loaded true two |

The bridge contacts in (7) are literally `45` and `50`. The proof keeps the full equations at true `W3` and true `C2` as original equations; it uses none of their individual forces to form a smaller star. It does not turn `45,50` into an edge `40`, and does not turn `23,34` into an actual `24` contact. In the first row, zero load at body `5` does not erase it or its two actual contacts. In the second row, its positive circle load is unrestricted and remains in its full original equation.

Theorem A excludes in each row the entire original feature

    n_23 a U2 own axis,
    n_21,n_20 not U2 own axes,
    original 20 free.                                (30)

This includes every original owner of `21,10`, every physical mask at `1,0,4,5`, every original mean on `23,34,45,50`, and both transmitter alternatives. If the caller has separately reduced an own-axis `23` to a positive shared segment, that whole segment case is included as well; such a reduction is not needed for (30).

Theorem B excludes, in each row, every nonzero tangential shift in the original feature

    n_21 a U2 own axis,
    V1 parallel to U2,
    n_20 not a U2 own axis,
    original 20 free.                                (31)

The entire actual incoming mean in (20) is retained. Neither (31) nor the earlier positive-shift tangent-cone exit is misreported as a zero-shift exclusion.

For the graph reflection `phi(i)=2-i` modulo six, the same literal roles become

    U=0,V=1,W=2,T_1=5,C=4,B=3.

The reflected load sets are respectively `{1,2,4}` and `{1,2,3,4}`. The actual bridge is now `4--3--2`; the proof is unchanged under this simultaneous reflection. Rotations of the whole original embedding are equally legitimate.

No completing unit is allocated to a pocket, a cap, or a central region anywhere in this argument. All nine actual units remain, and the contradiction already occurs among the displayed actual bodies. This permits the feature exits without a completion-capacity hypothesis.

## 8. Exact remaining scope and provenance boundaries

Theorem A is deliberately asymmetric in `V,W`: the real bridge touches `W`. The original caller cannot exchange them while leaving the bridge attached to the old label. Thus an `UV`-free/`UW`-owned sole-terminal-axis configuration is not excluded merely by relabeling (30).

Theorem B keeps the zero incoming shift. It does not exclude a nonfree `UW` return at negative shift. Neither theorem supplies a complete no-own-axis exclusion, a perpendicular-axis union, a full high-radius family, or an original accounting change.

The general bridge bound (7) was proposed by root continuation using the real `C4--5--W0` path. Roof continuation derived the sharp reach (3), the all-owner sole-terminal normal form, and the complete two-feature bridge applications. Root is therefore a discovery contributor; the requested separate independent reviewer has not contributed to these deductions.

The older e551 free-vertex source and ae4 parallel-incoming source below provided useful geometric context. Their respective frame arguments have been reproduced here with all hypotheses needed in this radius-free proof. In particular the full theorem of ae4 requires physical boundary `T`, whereas Sections 6.1--6.3 above do not. No false boundary-free import of that older whole theorem is made. Likewise no containing-circle mask, old loaded-terminal capacity, or old four-load allocation is imported from either context source.

There is no numerical pose, sampled angle cover, numerical optimizer, Lean compilation, Lake build or CI claim in these proofs.

## 9. Exact immutable input and context identities

The first three entries supply the physical convention/equations, the already established radius-free triangle fact, and the literal graph/load identification. All operative geometric and stress deductions are proved in full above. The final four entries are preserved source/review context, with the scope boundary in Section 8; they are not additional hypotheses or unproved capacity inputs.

| File | Bytes | SHA-256 | Role |
| --- | ---: | --- | --- |
| `PHYSICAL_CONTACT_STRESS.md` | 17993 | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` | Actual support applications, complete equations, strict point convention, and full transmitter alternatives |
| `UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md` | 4431 | `b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207` | Side-axis triangle fact, rederived in Section 3 |
| `SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md` | 11952 | `cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1` | Full original graph, load representatives and reflection |
| `FREE_BOUNDARY_VERTEX_ADJACENT_HUB_PORTS_ALL_RETURN_NEAR_ORIGIN.md` | 35739 | `e5515892f7b1f12ef6884c293eb668069ef1b7dd32582ca996eea00471e4188f` | Earlier adjacent free-return geometric context only |
| `REVIEW_FREE_BOUNDARY_VERTEX_ALL_RETURN_NEAR_ORIGIN_ROOF_RESUME_2026_10_29.md` | 23650 | `7312346a1ab4a926c23bd8bf3c734fef394593069f975874c8af139f727551d4` | Separate complete audit of that earlier context source |
| `PARALLEL_INCOMING_HUB_AXIS_CHAIN_POCKET_NEAR_ORIGIN_AND_FOUR_LOAD_FEATURES.md` | 42756 | `ae4e518534c911e778d81db0a6a3a644e186066e29edd1b1ba2a60819c1371da` | Earlier complete parallel-placement context, with its stronger whole-theorem boundary premises preserved |
| `REVIEW_PARALLEL_INCOMING_HUB_AXIS_CHAIN_FOUR_LOAD_ROOF_RESUME_2026_10_28.md` | 33456 | `5f2049d2078ca83d6a24a477169799eb1dc8f01e4f0dae5ab64c16fab0d8c9d3` | Separate complete audit of that earlier context source |
