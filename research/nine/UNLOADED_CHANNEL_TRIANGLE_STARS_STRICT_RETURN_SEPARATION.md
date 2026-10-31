# Two unloaded touching-return stars remain strictly separated across every genuine unloaded channel

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed radius-free theorem, full-window one-star exclusion of every channel with at least two internal transmitters, and complete seven-, eight- and nine-body subdivision-family corollaries, submitted for root and separate independent review.** The radius-free statement uses the entire original force and torque equations at both end stars and every internal transmitter. Its full-window long-channel consequence requires only one such end star. It changes no existing fine or coarse checkbox.

## 1. Complete physical setting

Keep actual closed unit squares with pairwise disjoint open interiors and their original physical contact certificate. Let

    U, X_1, ..., X_k, V,       k>=0,

be an actual positive path with distinct vertices. At k=0 this is the actual positive edge UV. For k>=1 every X_i has zero total circle load and exactly its two displayed positive path neighbors. The endpoints U,V are unloaded and have the complete positive neighborhoods

    N(U)={X_1,A,B}, N(V)={X_k,C,D}       when k>=1,
    N(U)={V,A,B},   N(V)={U,C,D}         when k=0.

Every displayed neighborhood consists of three distinct actual units. The four return labels lie outside the displayed path. The two return sets may initially share a label. Assume the actual physical contacts AB and CD exist. They need not carry positive force.

All original positive magnitudes, separating unit normals, common applications and shared-side means are retained. The return units A,B,C,D have arbitrary actual degrees, circle loads, physical circle masks, individual zero circle weights, other forces and extra physical contacts. Every other physical packing unit stays present. There is no containing-circle or radius premise.

Orient the first path normal from U into the path and denote it by n. Let p_0 be that original edge's common application or side mean, and put h=n.p_0.

**Theorem.** All path edges have this same forward unit normal n and the same positive magnitude. If p_k is the original application on the last path edge at V, then

    p_k=p_0+w*n,
    w=sum_(i=1,...,k) width_(X_i)(n)>=k.               (1)

For k=0 use p_k=p_0 and w=0. The entire closed return groups satisfy

    n.x<h       for every x in A union B,
    n.y>h+w     for every y in C union D.             (2)

Consequently the two return groups are closed-disjoint and cannot share a unit label. Any physical contact from either of A,B to either of C,D makes this whole configuration impossible. For k>=1 the actual groups have a strict separation gap larger than the full original channel width w, and in particular larger than k.

No claim is made about an arbitrary path with loaded or higher-degree internal units.

## 2. The original channel transmits its exact normal and full width

Suppose k>=1. At X_1 the complete force equation has precisely its two original positive pair forces and zero total circle force. The two outward normals are therefore opposite and their magnitudes equal. Since the outward normal from X_1 back to U is -n, its forward normal is exactly n. Iterate this argument at every actual X_i. This proves the unchanged common normal and positive magnitude along the entire original path.

Let p_(i-1),p_i be the original incoming and outgoing application means of X_i. They are actual minimum-n and maximum-n support points of that same unit, so

    n.(p_i-p_(i-1))=width_(X_i)(n).

The full X_i torque equation gives

    det(p_i-p_(i-1),n)=0.

Because n is unit, the two component identities imply

    p_i-p_(i-1)=width_(X_i)(n)*n.                     (3)

For any own orthonormal side frame f_i,g_i,

    width_(X_i)(n)=|n.f_i|+|n.g_i|>=1.

Summing (3) proves (1), with every actual side mean unchanged. No axis/diagonal classification or generic normal convention is needed. All widths from one through sqrt(2), and every original mean endpoint, are included.

A zero total circle load means all nonnegative circle coefficients at that unit vanish. It does not imply that the unit is physically circle-clear. Thus a zero-weight physical circle contact at an internal unit does not affect its exact two-force equations.

At k=0 the actual UV edge has one common original application, and its two directed normals are n and -n. Formula (1) is then immediate with w=0.

## 3. Strict separation at both full end stars

Apply the complete all-normal touching-return support theorem

    UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md

to the true unloaded U3, with its actual first path neighbor as the third neighbor and actual physically touching returns A,B. It gives

    n.x<n.p_0=h

for every point of both whole closed returned units.

At the actual V3, the third normal points backward along the unchanged path and is exactly -n. Its unchanged application is p_k. Apply the same complete theorem with physically touching returns C,D. For every point of these two whole returned units it gives

    (-n).y<(-n).p_k=-(h+w).

This is precisely n.y>h+w, completing (2). A common point of the two groups would simultaneously satisfy n.z<h and n.z>h+w with w>=0, which is impossible.

If a return label were shared by the two groups, any point of that actual nonempty square would give the same contradiction. Since the groups are finite unions of compact units, their strict extreme inequalities also give

    min_(C union D) n.y - max_(A union B) n.x > w.

The Euclidean distance between any point of the first group and any point of the second is at least their positive projection difference. This proves the claimed strict geometric gap as well as the no-contact conclusion.

The endpoint theorem is used at genuine full degree-three stars. No force or moment is deleted from an endpoint, no channel unit is contracted away, no normal is reselected and no aggregate supporting neighbor is invented. The imported support theorem covers own-side, externally owned and free normals, parallel and nonparallel returns, all actual side means and both endpoints.

## 4. One touching-return star already forbids every width-two channel in the full radius window

Now assume every actual unit is contained in a circle with

    R^2<=Q=1105/256.

For any contained unit center z, its farthest corner has squared
norm at least |z|^2+|z|+1/2: in an orthonormal own frame the exact
formula is |z|^2+1/2+|z.f|+|z.g|, and the last two terms have sum
at least |z|. Therefore

    |z|<M=91/60,
    M^2+M+1/2-Q=31/57600>0.                         (4)

For this section keep only the first unloaded star U3 and its
actual touching returns A,B. Let its third edge start the genuine
unloaded channel of Section 2, ending at an arbitrary actual unit
Q. Impose no degree, load, triangle or equilibrium restriction on
Q. Retain all of its original forces. The channel still gives its
unchanged supporting half-plane

    Q subset {z:n.z>=h+w}.

Its center has n projection at least h+w+1/2, because every unit
has halfwidth at least 1/2. Equation (4) therefore gives

    h<M-w-1/2.

The complete strict touching-return theorem at U gives max n.x<h
on both A and B. Their actual centers consequently satisfy

    n.z_A, n.z_B < h-1/2 < M-w-1.

If the total original channel width w>=2, this implies

    -91/60 < n.z_A,n.z_B < -89/60.

Their absolute tangent coordinates are strictly less than

    sqrt((91/60)^2-(89/60)^2)=sqrt(1/10).

Both centers therefore lie in one rectangle of squared diameter

    (1/30)^2+4/10=361/900<1.                        (5)

But A and B are distinct actual unit squares. Their open inscribed
disks of radius 1/2 are disjoint, so their centers must have distance
at least one. Equation (5) is a contradiction.

**Full-window one-star corollary.** A true unloaded U3 with two
physically touching returns cannot have its third edge feed a
genuine unloaded positive-degree-two channel of total width w>=2,
ending at any actual unit Q. In particular every channel with
k>=2 internal unloaded units is excluded. The far endpoint's true
degree and complete circle/force system are arbitrary; no second
star, return cross-contact or external bypass is required.

This includes the two-star setting of Section 1, and remains true
regardless of any additional paths between the displayed units.
It needs only the containing upper-radius cap. No radius lower
bound, positive circle load or equation at A,B,Q is used. A single
internal unit of width less than two is not excluded by this cap
argument alone.

## 5. Uniform complete opposite-ear subdivision families on seven through nine bodies

Begin with the six-body opposite-ear positive graph

    0--1--2--3--4--5--0,       chords 02 and 35,

and replace only its original 23 edge by the actual positive path

    2--X_1--...--X_k--3.

For k in {1,2,3}, keep exactly the four positive block circle loads

    {0,1,4,5}.

Every inserted X_i is a genuine unloaded positive-degree-two unit. The true endpoint neighborhoods are

    N(2)={X_1,0,1}, N(3)={X_k,4,5}.

The original positive contacts 01 and 45 are the two return contacts, and the unchanged positive edge 05 is a physical cross-contact between their return groups. Sections 1--3 apply with

    U=2, V=3, A=0, B=1, C=4, D=5.

They contradict that actual 05 contact. This excludes every physical realization of each entire displayed graph/load family, with all independent square frames, every original mask and side mean, all individual zero circle weights and every permitted additional zero-weight physical contact.

The complete graph remains one biconnected block: its outer cycle is the original six-cycle with the actual 23 path inserted, and both original chords remain. The literal size and retained-nine bookkeeping are:

| Internal path units k | Actual component bodies | Original coarse cell containing this family | Arbitrary remaining squares of the same nine packing |
| --- | --- | --- | --- |
| 1 | 7 | C1.7.b0 | 2 |
| 2 | 8 | C1.8.b0 | 1 |
| 3 | 9 | C1.9.b0 | 0 |

The original loaded degrees at 0 and 5 remain three and at 1 and 4 remain two. No equation at any of those loaded bodies is used by the theorem. In the broader local form of Sections 1--3 they may also have additional forces, provided the two end stars and the internal path units retain their stated complete degrees. The physical contradiction is independent of all completion units.

The k=0 specialization recovers the already accepted entire six-body family M6.B6.HEXAGON.D0235.L0145. That gate is already closed and is not counted again.

The three positive-path subdivision families are complete continuous geometric families within their respective original coarse cells. No pre-existing fine ID is assigned to them here. None of C1.7.b0, C1.8.b0 or C1.9.b0 is closed, because their other biconnected graphs and load domains have not been covered.

For k=2,3 the stronger corollary in Section 4 already excludes
the same complete family without needing its original 05 edge.
That edge is nevertheless retained in the literal original
subdivision graph and in every full equation at 0 and 5.

## 6. Exact dependencies and proof limits

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| `UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md` | `406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87` | Complete radius-free whole-return strict support theorem, once at each actual full U3 endpoint |
| `ADJACENT_UNLOADED_TRIANGLE_STARS_NO_RETURN_CROSS_CONTACT.md` | `0789ef5bd9a293a2b7a929be0a4bad8b64f82096ce4053070230214b347484db` | Provenance and literal k=0 original opposite-ear graph/load family |
| `SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md` | `cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1` | Original opposite-ear labels, both chords and complete load orbit for the unmodified six-body graph |

The channel identities are proved in full in Section 2. They are the same physical identities printed in Section 4 of `UNLOADED_TRIANGLE_HUB_CHANNEL_BYPASS_EXCLUSION.md`; that source is not an additional premise here.

The theorem requires genuine unloaded degree-two units on the entire path. An arbitrary longer path between the return groups is not excluded. It also does not license a three-force reduction at an endpoint with an extra positive force. The full higher-degree equations at the return units are harmless because no equation there is used.

This manuscript is a broad geometric exclusion and a complete family substitution, not a new case-counting device. It changes no gate, ledger or historical source. No sampled pose, numerical interval certificate, Lean compilation, CI, workflow dispatch, merge or remote write is used.

