# Full cut size controls every unloaded tree module

Date: October 31, 2026. Status: complete hand theorem; separate root reconstruction passed in REVIEW_GLOBAL_UNLOADED_TREE_CUT_BUDGET_ROOT_2026_10_31.md. No original fine or coarse flag is changed.

This source gives two results valid across all original component sizes. First, an entirely unloaded connected **tree** with exactly `p>=3` positive edges leaving it has at most `2p-3` actual square members. In particular a three-edge cut cannot hide four or more unloaded tree members. Second, every group of unloaded branching bodies has a quantitative lower bound on the force carried by its direct exits. The latter retains its internal support work and applies when the group has cycles and chords.

Neither statement is a general eight-body packing theorem. In particular, an unloaded cyclic module is not silently replaced by a tree. The exact eight-body cross example remains outside the tree theorem and satisfies the force budget. All nine actual squares remain in every nine-square caller.

## 1. One physical certificate and two geometric inputs

Let actual closed unit squares with pairwise disjoint open interiors lie in the disk `D_R`, where

    R^2 <= Q = 1105/256.

Retain a single physical nonnegative contact/circle certificate. For every positive body pair retain its original positive magnitude, common unit supporting normal and actual application or shared-side mean. A body is **unloaded** when every selected circle coefficient on it is zero. Physical circle contact with zero coefficient is allowed and does not change this definition.

Write `c_i` for the center of square `i` and `h_i(n)` for its support halfwidth in unit direction `n`. The complete translational equations on unloaded bodies and the actual support equalities are

    sum_j mu_ij n_ij = 0,
    n_ij . (c_j-c_i) = h_i(n_ij)+h_j(n_ij),
    h_i(n) >= 1/2.                                      (1)

The first sum includes **all** original positive neighbors. On reversal of a positive pair, its normal changes sign and its magnitude is unchanged.

Every actual center satisfies

    |c_i| < M = 91/60 < 2.                              (2)

Indeed the farthest-corner squared norm is at least `|c_i|^2+|c_i|+1/2`, and

    M^2+M+1/2-Q = 31/57600 > 0.

We also use the complete positive-long-endpoint theorem in

`UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md`, Section 5:

> If two successive internal bodies of a positive path are unloaded of true full positive degree two, both path endpoints are positively circle-loaded, even at arbitrary endpoint degrees.

That source proves its conclusion from actual containment and the full translational equations. It does not require torque, a compatible plane embedding, or a changed selection. Its proof uses the universal actual-contact-radius bound `|p|<29/15`, then shows that a channel with two internal units leaves each endpoint's entire outward own side contact-free. The inward channel force makes zero endpoint circle load impossible. These exact hypotheses are checked at every use below.

Consequently, every maximal channel incident to an unloaded body of true degree at least three contains at most **one** unloaded true-degree-two internal body. If it contained two or more, the first two give a four-body subpath whose unloaded branching endpoint contradicts that theorem. A channel returning to its starting body is also impossible: propagating one signed normal through its true-degree-two internal bodies would telescope positive support gaps to zero displacement.

## 2. The full reduced graph of an unloaded module

Let `K` be a nonempty connected set of unloaded bodies. Let `p` count its **entire** positive cut in the original body-pair graph. Repeated contacts to one external body are counted separately when they are different original body pairs. No positive cut edge may be omitted because its external endpoint is absent from a displayed subgraph.

Every body of `K` has true degree at least two. A degree-one body would have one nonzero force and zero circle force in (1), which is impossible. Let

    B = {i in K : true degree(i) >= 3},
    b = |B|,
    k = |K|-b.

The remaining `k` bodies have true full degree two. Suppress them only for the following algebraic bookkeeping. Every positive cut edge is terminated at its actual external square; for counting, label these external occurrences separately as `p` terminal stubs, even when several stubs belong to one actual external square. No geometric copy of an external square is made.

Assume `b>0`. In the resulting reduced graph every channel has an endpoint in `B`. A channel joining two terminal stubs without a branching endpoint would itself be an entire connected component of `K`, contrary to the connectedness of `K` and `b>0`. The preceding long-endpoint input therefore shows that every reduced channel has either zero or one suppressed internal body.

For a channel `e` from actual endpoint `i` to actual endpoint `j`, let its signed direction and magnitude be `n_e,mu_e`. The true degree-two equations propagate these unchanged values along the original path. If its internal count is `k_e` in `{0,1}`, its exact endpoint projection gap is

    g_e = n_e . (c_j-c_i)
        = h_i(n_e)+h_j(n_e)
            + sum_(internal U on e) 2 h_U(n_e)
        >= 1+k_e.                                      (3)

All actual endpoint halfwidths and internal orientations remain. The original complete equation at every `i in B` is exactly the sum of its reduced incident channel forces. This is a telescoping identity on the original system, not a replacement certificate.

## 3. Quantitative direct-exit force budget

Form the graph on `B` whose edges are the **direct** original positive contacts between its members, namely channels with `k_e=0`. Let `S` be one connected component of this graph. Include all reduced channels with both endpoints in `S` in the internal work

    I_S = sum_(internal channels e) mu_e g_e >= 0.

In particular, a channel with one suppressed internal body whose endpoints both belong to `S` remains in this sum. Let

    C_S = sum_(channels leaving S) mu_e,
    Z_S = sum_(direct channels leaving S) mu_e.

A direct channel leaving `S` must end at an original cut stub of `K`: otherwise it would join `S` to another member of the same direct-contact component. All nondirect outgoing channels have their original one internal body and `g_e>=2`.

**Theorem 1 (direct exits carry nearly half the cut force).** Every such `S` has `C_S>0` and

    Z_S > (2-M) C_S + I_S
        = (29/60) C_S + I_S.                            (4)

**Proof.** Dot the full reduced equation at each member `i in S` with its unchanged actual center `c_i`, and sum. Internal channel forces combine to `-mu_e g_e`; hence their sum is `-I_S`. Orient each outgoing channel from `i in S` to its actual endpoint `j` outside. Equation (3) gives the exact identity

    I_S + sum_(outgoing e) mu_e g_e
       = sum_(outgoing e) mu_e n_e . c_j.              (5)

If no outgoing channel existed, (5) would give `I_S=0`. A component containing an internal positive channel would have `I_S>0`. A singleton with no outgoing or internal channel would have degree zero, contrary to its membership in `B`. Thus `C_S>0`.

By (2), the right side of (5) is strictly below `M C_S`. For its outgoing gap sum, (3) gives

    sum_(outgoing e) mu_e g_e
       >= Z_S + 2(C_S-Z_S)
        = 2 C_S-Z_S.

Substitution in (5) proves (4). Every strict inequality comes from the actual center bound, with all original channels included. QED.

In particular, every direct-contact component of unloaded branching bodies has at least one direct exit through the module's original full cut. This is stronger than merely knowing that some direct edge occurs somewhere in `K`.

One may retain the stronger exact version

    Z_S > (2-M)C_S + I_S
          + sum_(direct outgoing e) mu_e(g_e-1)
          + sum_(nondirect outgoing e) mu_e(g_e-2),     (6)

where all added terms are nonnegative actual width reserves.

The theorem does not say that the direct exit endpoint is itself loaded. That endpoint may be an unloaded external branching body, and its full outside force system remains. It is only the channel into that endpoint that must be direct.

## 4. Complete size bound for a tree module

Suppose now that the induced positive graph on `K` is a tree and `p>=3`.

**Theorem 2 (full-cut tree size).**

    |K| <= 2p-3.                                      (7)

In particular:

| Full positive cut size | Maximum unloaded tree size |
| ---: | ---: |
| 3 | 3 |
| 4 | 5 |
| 5 | 7 |
| 6 | 9 |

**Proof.** Put `m=|K|`. Since the internal graph is a tree, the sum of the true full degrees over its members is `2(m-1)+p`. Consequently

    sum_(i in K) (degree(i)-2) = p-2.                 (8)

Each summand is nonnegative. Each of the `b` branching bodies contributes at least one, whereas the true degree-two bodies contribute zero. Thus

    1 <= b <= p-2.                                    (9)

For the left inequality, `p>=3` makes the sum in (8) positive.

The reduced graph with `b` branching vertices and `p` terminal stubs is a tree, because suppressing degree-two vertices in the original tree with its separate terminal stubs preserves connectedness and acyclicity. It therefore has exactly

    e = b+p-1                                         (10)

channels. Each channel has zero or one internal body, by Section 2; hence `k` is exactly its number of nondirect channels.

Let the direct-contact graph on the `b` branching vertices have `q` components. It is a forest and has `b-q` edges. By Theorem 1, each of its `q` components has at least one direct exit to an original cut stub. These exits are distinct reduced channels, and are distinct from the `b-q` internal direct edges. Thus the total number `e_0` of direct reduced channels satisfies

    e_0 >= (b-q)+q = b.                               (11)

Equations (10)--(11) now give

    k=e-e_0 <= p-1,
    m=b+k <= (p-2)+(p-1)=2p-3.

This proves (7). QED.

All attachments were counted in the **full** original cut. The proof allows the external stubs to represent repeated actual terminal bodies and does not assume any terminal degree, positive circle load, planar order, or mutual separation. It does not assume that the module's own ends are genuine leaves of the whole positive graph.

## 5. Exact three-port topology and the remaining physical question

For `p=3`, (8) forces exactly one branching body `H`, of true degree three. Every other member is a true-degree-two transmitter on one of its three arms. Let `a_1,a_2,a_3` be the internal transmitter counts on the arms from `H` to the three original external cut endpoints. The entire cover is

    a_i in {0,1},     at least one a_i=0.              (12)

The possible unordered arm multisets are therefore exactly

    (0,0,0),  (1,0,0),  (1,1,0).                     (13)

This is a complete necessary topology statement for unloaded tree modules behind a three-edge cut. There is no omitted long arm, fork hidden in a suppressed vertex, or branch whose other positive force has been discarded. A repeated external square may further exclude some rows, but is not needed for this theorem.

In the last row the single direct exit has magnitude `z`, while the two subdivided arms have magnitudes `a,b`. The complete degree-three equation gives `z<=a+b`. With `I_S=0` for the singleton branching component, (4) gives the additional uniform force constraint

    (29/60)(z+a+b) < z <= a+b,

or equivalently

    29/31 < z/(a+b) <= 1.                             (14)

The exact retained width reserves in (6) can strengthen its lower bound. This is a constraint on the entire arm feature; it does **not** assert that the two nonparallel arm directions are close when one of their magnitudes is arbitrarily small. Nor does it exclude the whole `(1,1,0)` feature. Such an exclusion would require an additional geometric or joint-completion argument.

The complete two-port source
`EVERY_UNLOADED_TWO_PORT_MODULE_IS_A_ONE_OR_TWO_SQUARE_CHANNEL_2026_10_30.md`
already handles `p=2` without a tree premise. The new theorem does not replace its sharper result.

## 6. A cycle-rank extension, with its exact limitation

For any connected unloaded `K` with `b>0`, let `beta` be the internal graph's cycle rank, namely `E(K)-|K|+1`. Let

    eta = sum_(i in B) (degree(i)-3) >= 0,

and let `beta_0` be the cycle rank of the direct-contact graph on `B`, with the ranks of its components added. The same degree sum yields

    b = p-2+2 beta-eta.                               (15)

Suppression preserves `beta` when the cut stubs are separate, so there are `b+p-1+beta` reduced channels. The internal direct graph has `b-q+beta_0` edges. Theorem 1 adds at least `q` distinct direct exits. Therefore

    k <= p-1+beta-beta_0,
    |K| <= 2p-3+3 beta-eta-beta_0.                    (16)

This extension uses no planarity. It retains every chord and exposes the precise topological deficit in the tree argument. It cannot be read as `|K|<=2p-3` when `beta>0`.

## 7. Physical controls and original scope

1. **Five-square cross.** Its central unloaded body has four cut contacts and no internal edge. The tree bound allows its one body; the quantitative force bound allows its four direct exits. It does not assign one unit of boundary set gap to a turning branch.

2. **Exact eight-body outer-face counterexample.** In
   `EXACT_EIGHT_BODY_OUTER_FACE_CYCLE_WITH_UNLOADED_BRANCHING_VERTICES_2026_10_30.md`, the four central unloaded squares induce a four-cycle, so `beta=1`; their cut has eight positive edges. The tree theorem is inapplicable. Their full internal work is `I=2` and total direct cut magnitude `C=4`, so the direct-force inequality reads `4>(29/60)4+2=59/15`, with reserve `1/15`. Thus the new inequality is consistent with the exact physical stress, including its positive chords.

3. **D02 six-body rim.** In the original L135 mask, the unloaded connected hub pair `{A,D}` has one internal direct edge and four outgoing direct edges. The theorem imposes its complete internal-work bound through (4), but does not assert a contradiction and does not close L135. The isolated unloaded `N` has its existing two-port classification. The root pair cannot be relabelled as a three-port module by dropping either roof force.

4. **Maximal one-block profiles.** The same theorem excludes any original eight- or nine-body graph/load feature containing an entirely unloaded tree of at least four members behind exactly three full cut edges, and any unloaded tree of at least six members behind exactly four full cut edges. These callers permit arbitrary outer degrees, loads, means, orientations, and positive chords outside the module. A proposed caller with an additional positive contact into the module has a different `p` and must be tested with that full cut.

The theorem therefore supplies a uniform structural exclusion and an exact force budget, not a complete classification of all 11 open one-block coarse parents. A genuine unloaded cyclic module, or the surviving three-port star rows in (13), remains an additional obligation. No original fine/coarse denominator is changed and no entire parent is marked closed.

## 8. Verification boundary

Everything above is a hand proof using the displayed degree identities, support telescoping and full force sums. There is no mathematical exclusion script, numerical optimization, angle mesh, pose certificate, Lean run, or CI invocation. No normal, application point, individual circle coefficient or physical square was changed. The long-endpoint theorem is used only with its exact true-degree and positive-force premises. The separate root review reconstructs the inherited long-endpoint entry, exact virial signs, full-cut counting and cycle-rank limitation. No formal verification is claimed.
