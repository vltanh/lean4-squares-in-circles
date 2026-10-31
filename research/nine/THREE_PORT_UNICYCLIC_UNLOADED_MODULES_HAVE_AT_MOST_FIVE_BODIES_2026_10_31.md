# Every three-port unicyclic unloaded module has at most five bodies

October 31, 2026. Input commit: 8e8413d6abbb29663f70cf5511da45905b678763.

**Status: complete new hand derivation, self-checked; not independently reviewed or formally verified.** This replaces the previous uncommitted suggestion of a three-hub reduction by a proved reduction and a stronger size bound. It treats an entire full-cut cyclic module, not a selected cycle with its chords removed. No original fine/coarse flag is changed.

## 1. Exact scope and statement

Keep any one physical force-and-torque certificate on actual interior-disjoint unit squares in D_R, with

    R^2<=Q=1105/256,     |c_i|<M=91/60.

Every positive pair has its unchanged unit supporting normal, magnitude and actual application or shared-side mean. A body is unloaded when all its selected circle coefficients vanish; physical circle contact with zero coefficient is allowed.

Let K be a nonempty connected set of unloaded bodies. Assume:

- its **full original positive cut** consists of exactly three body-pair edges;
- its induced positive graph has cycle rank exactly one, E(K)-|K|+1=1.

External endpoints may repeat and have arbitrary degrees, loads and physical masks. All original squares outside K remain. Then:

**Theorem.** K has exactly three true-degree-three hubs. Suppressing only its genuine unloaded true-degree-two runs gives a triangle on these hubs and one exit arm from each hub. Every triangle edge and exit arm has zero or one internal transmitter. If t is the number of subdivided triangle edges and s the number of subdivided exit arms, the complete necessary cover is

| t | s | Actual body count | Additional distinction |
| ---: | ---: | ---: | --- |
| 0 | 0 | 3 | No transmitter |
| 0 | 1 | 4 | Any one exit arm, up to relabeling |
| 1 | 0 | 4 | One subdivided cycle edge |
| 1 | 1 | 5 | Exit at an endpoint of that cycle edge, or at its opposite hub |
| 2 | 0 | 5 | No subdivided exit arm |

In particular **|K|<=5**. Every three-port unloaded unicyclic module of six or more actual bodies is impossible. Rows retained by this table are necessary forms, not asserted realizable configurations or completed nine-square exclusions.

## 2. Channel facts at their original full-degree scope

At a genuinely unloaded vertex of true full positive degree two, force balance propagates one magnitude and one signed normal. Its full torque equation keeps consecutive actual applications collinear. In a square, the resulting width is 1 for a side-normal transmitter or sqrt(2) for a diagonal transmitter. This follows by considering either opposite support sides or the two unique opposite support vertices; in the latter case their displacement is parallel to the normal only on the square diagonal.

The long-endpoint theorem in UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md, Sections 3--5, proves that two consecutive such internal bodies force both endpoints positively loaded, at arbitrary endpoint degrees. Its geometric premise is a support gap at least two and a positive inward force. The companion SHARP_CONTACT_RADIUS_AND_NEAR_LONG_ENDPOINT_LOAD_2026_10_31.md independently proves the stronger gap threshold 39/20.

It follows that every reduced channel incident to an unloaded branching vertex has at most one true-degree-two internal body. Otherwise the first two internal bodies and their adjacent actual endpoint contradict that loaded-endpoint theorem. A returning channel is impossible: its propagated signed support gaps are strictly positive but would telescope to zero center displacement.

For a reduced channel from i to j, with k_e in {0,1} internal bodies, its actual projection gap is

    g_e=n_e.(c_j-c_i)
       =h_i(n_e)+h_j(n_e)+sum_internal 2h_U(n_e)
       >=1+k_e.                                        (1)

All endpoint halfwidths and original means are retained. This is bookkeeping on the same equations, not deletion of a force or replacement by a physical edge.

## 3. Two channels between the same endpoints have the same signed direction

Consider two internally disjoint true unloaded degree-two transmission paths from actual A to B, each with at least one internal body. For one path, full torque propagation gives original applications p_A in A and p_B in B with

    p_B-p_A=L n,

where L>0 is the sum of its actual transmitter widths. The supporting halfplanes of A and B are separated in n by exactly L. Thus every displacement b-a, a in A and b in B, has n projection at least L, while the displayed displacement attains length L. Hence dist(A,B)=L.

The displacement vector realizing minimum distance between two disjoint compact convex sets is unique. Indeed two distinct minimizing displacement vectors would have a midpoint in the convex difference B-A, whose squared norm is strictly smaller by the parallelogram identity. Therefore the other channel has the same L and the same signed unit n. This argument does not require uniqueness of either individual application point.

A direct A--B contact cannot coexist with a channel having an internal body, since it would give dist(A,B)=0. Two direct channels are not distinct edges in the simple original body-pair graph. These observations cover every multiple-edge possibility after suppression.

### Degree-three endpoint obstruction

Suppose an unloaded endpoint A of two such channels has true degree three. The two forces from A into the channels are positive multiples of n. Its only other positive force is therefore a positive multiple of -n. Let X be that immediate actual third neighbor, and let U be the first internal body of one channel from A towards B. Section 2 makes this channel A--U--B.

The actual contacts X--A, A--U, U--B have one signed normal n in that order. Support equalities give

    g_n(X,B)=2h_A(n)+2h_U(n)>=2.                         (2)

The four bodies X,A,U,B are distinct: in particular X cannot be B, since dist(A,B)>0, and it is neither first internal channel neighbor. B has its positive actual inward normal -n. The loaded-endpoint theorem applied to (2) forces B loaded, a contradiction.

Thus **parallel reduced channels cannot have an unloaded true-degree-three endpoint**. The other endpoint's degree is arbitrary. No normals are reselected, no limiting force is set to zero, and A was never relabeled as true degree two.

## 4. The whole unicyclic topology reduces to a triangle

Every member of K has true degree at least two, since one positive force cannot balance at an unloaded body. Summing full degrees, including all three cut edges, gives

    sum_(i in K)(degree(i)-2)=2E(K)+3-2|K|=3.           (3)

Let B be its set of true-degree-at-least-three bodies and b=|B|. Then 1<=b<=3. Suppress the other true-degree-two bodies, and terminate each cut edge at a separately labeled external occurrence. Repeated occurrences of one actual external square remain distinct counting stubs; no geometric copies are made.

The reduced internal graph on B is connected and unicyclic. Suppression preserves the cycle rank. Every channel has an endpoint in B: a channel joining two cut stubs with no branching member would form a separate entire connected component of K, contradicting b>0. Section 2 bounds every channel by one internal body and excludes loops.

If b=1, the internal cycle would be a loop, impossible. If b=2, a loop-free unicyclic connected graph has two parallel channels. Equation (3) gives the two full degrees 3 and 4, so Section 3 excludes this case. If b=3, (3) makes all three full degrees exactly three. A loop is impossible, and any parallel pair is excluded by Section 3. A simple connected unicyclic graph on three vertices is the triangle. Each hub therefore has its two triangle channels and exactly one exit arm. This proves the complete reduction without assuming the module initially had a simple rim.

## 5. A stronger work inequality for an arbitrary reduced module

The following argument is not confined to a triangle. Retain a connected reduced set of unloaded branching bodies B, with all its true-degree-two channels retained algebraically, and suppose **each branching body has at most one outgoing reduced exit channel**. Any cycles or chords inside B are allowed. Every channel has zero or one internal body as above. Assume its exit set is nonempty.

Let

    D=sum of magnitudes of direct internal channels,
    N=sum of magnitudes of internal channels with one transmitter,
    C=sum of magnitudes of all exit channels,
    A=sum of magnitudes of exit channels with one transmitter.

All four are force magnitudes, not counts. Write

    W=D+N,
    I=sum_internal mu_e*g_e,
    Delta=2W-C.

At a branching body with one exit, its exit magnitude is at most the sum of all incident internal magnitudes, by its full force balance. At a body with no exit the corresponding inequality has left side zero. Summing yields

    C<=2W,       Delta>=0.                               (4)

Dot the complete reduced equation at each body with its unchanged center and sum. Each internal channel contributes -mu_e*g_e. For an outgoing channel from i to its actual external endpoint j, use g_e=n_e.(c_j-c_i). This gives the exact work identity

    I+sum_exit mu_e*g_e
       =sum_exit mu_e*n_e.c_j < M C.                    (5)

The strict inequality uses |c_j|<M. This includes repeated external squares and every actual internal width. Since I>=D+2N and the outgoing gap sum is at least C+A, (5) implies

    I+A < (31/60)C,
    D >29N+30A+(31/2)Delta.                             (6)

For the second expression substitute C=2(D+N)-Delta into the first and multiply by 30. No selected force or width reserve was discarded before deriving (5); weakening to the integer-width lower bounds only gives the displayed necessary inequality.

Also I>=W>=(1/2)C, so

    A<C/60.                                            (7)

More exactly, (5) gives

    N+A+Delta/2 < C/60.                                (8)

Consequently D>0: the whole reduced interior must contain a direct channel. These bounds are uniform in the number of bodies, cut edges, cycles, chords and actual normal slopes, at the stated one-exit-per-branch hypothesis. They do not apply to a branch with multiple reduced exits simply by omitting some exits.

## 6. Complete removal of the six-body unicyclic alternative

Return to the three-hub triangle. Its three outgoing forces sum to zero by summing all full reduced hub equations. If their magnitudes are z_1,z_2,z_3 and C=z_1+z_2+z_3, each z_i<=C/2. Any two magnitudes therefore sum to at least C/2. Equation (7) makes two subdivided exit arms impossible. Thus s<=1.

If all three triangle edges were subdivided, D=0 and N>0, contradicting (6). Thus t<=2.

Suppose t=2. Label the sole direct internal edge H_1--H_2, with magnitude d, and the two subdivided edges to H_3 with magnitudes a,b. Then D=d, N=a+b, and (6) gives

    d>29(a+b).                                         (9)

The exit arm at H_3 cannot be subdivided. If it were, every reduced channel incident to H_3 would have g_e>=2. Dot its complete force equation with c_H3 and rewrite each term using its actual other endpoint center. This would give

    sum_incident mu_e*g_e
       =sum_incident mu_e*n_e.c_other
       <M sum_incident mu_e,

contrary to g_e>=2>M on every incident channel.

Nor can an exit at H_1 or H_2 be subdivided. If the exit at H_1 were, its magnitude z satisfies, by the reverse triangle inequality on the full H_1 equation,

    z>=d-a>=d-(a+b)>0.

Since this force contributes to A, (6) also gives d>30z. Thus

    d>30[d-(a+b)],
    d<(30/29)(a+b),

contrary to (9), because 29>30/29. The same reasoning applies at H_2. Hence t=2 forces s=0.

Together, t=0 or 1 with s<=1, and t=2 with s=0, give exactly the necessary table in Section 1. Since |K|=3+t+s, the bound |K|<=5 follows.

## 7. Literal transfer and limitations

The theorem excludes every full three-edge-cut unloaded module with exactly one independent cycle and at least six actual members. It does not depend on how the rest of the positive graph is attached, whether its external endpoints carry load, or whether those endpoints are distinct. All actual completion units remain. Together with the previously proved three-port tree bound, any connected unloaded module behind three full cut edges and having at most one independent cycle has at most five bodies (and at most three in the tree case).

The new work theorem (6)--(8) also applies to cyclic or chorded reduced interiors of higher cycle rank whenever each retained branching body has at most one reduced exit. It is a force restriction, not a higher-cycle-rank size theorem.

The remaining three-port unicyclic geometries are the five rows of the table, including the two inequivalent exit positions in its (t,s)=(1,1) row. Their actual orientations, transmitter type, means, weights, external terminals and nine-square completion capacity are not settled here. No original C1 or C2 parent is closed solely by this theorem, and the original ledgers remain 37/58 coarse, 2373/2513 fine, 18/38 exterior.

## 8. Verification boundary

The proof uses the unchanged true-degree-two torque classification, the fully stated loaded-endpoint theorem, a strict-convexity nearest-displacement argument, the exact degree sum, and complete reduced force work. It neither assumes equal circle weights nor chooses new contact means. The force bounds include arbitrarily small positive coefficients. No numerical search, mathematical script, generated case table, Lean, Lake, CI, or independent review is claimed.
