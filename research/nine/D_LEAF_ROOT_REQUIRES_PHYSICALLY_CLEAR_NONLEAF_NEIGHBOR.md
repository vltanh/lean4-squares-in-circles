# Every genuine D-leaf root has a physically clear nonleaf positive neighbor

Date: October 28, 2026.

**Status: complete proposed uniform hand theorem and two whole original
house-family joins, frozen for full root and separate independent review.**
This source changes no original checkbox, fine label, coarse cell or remote
state. All nine actual squares and all original forces remain.

Work with the common selected physical certificate and the original
nine-square packing in

    79/40 <= R <= sqrt(1105)/16.

## 1. Uniform statement at the full actual degree

Let L be a genuine positive degree-one D leaf and H its actual neighbor.
There is no restriction on H's true positive degree, on the graph induced
by its other neighbors, or on those neighbors' true degrees. Keep every
original positive H edge and every actual contact normal and application,
including each shared-side mean and its endpoints. Keep physical circle
contacts with zero total multiplier and every zero individual corner weight.

**Theorem.** At least one positive neighbor of H other than L is physically
circle-clear. Equivalently, it is impossible that every such actual neighbor
physically touches the containing circle.

This is a statement about physical circle contact, stronger than the
existence of a zero-loaded neighbor. It imposes no endpoint concurrence,
no boundary-path connectivity and no terminal or genuine-block condition
on the other neighbors. It permits additional genuine leaves among them;
they remain physical boundary units and actual positive forces.

The same-nine lower bound NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md supplies
R>2. Its current accepted five-charge proof and all of its declared
analytic/arithmetic dependencies are retained. No charge is rerun, removed
or replaced here. The new cap lemma below is entirely analytic and holds
on the whole stated radius window even before that lower-bound join.

## 2. The radial D leaf occupies the entire available outward cap

Here is the force-free geometric input. Put

    r=R-sqrt(2), sigma=1/sqrt(2).

An actual radial D square has center

    c_L=(r+sigma)e,             |e|=1,

and inward radial vertex r e. We claim that there is no distinct actual
unit T, interior-disjoint from L and contained in the same circle, with

    T subset {x:e.x>=r}.                                      (1)

There is no boundary-contact, force or degree premise on T.

### 2.1. Every actual contained center satisfies one sharp bound

Let c be the center of any contained unit and u,v its orthonormal own
axes. The exact maximum of its four squared corner norms is

    |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Consequently

    |c| <= M:=sqrt(R^2-1/4)-1/2.                              (2)

Its projection halfwidth in the unit direction e is

    (|u.e|+|v.e|)/2 >= 1/2.

Thus (1) gives c_T.e>=r+1/2. Using (2) and the actual c_L,

    |c_T-c_L|^2
      =|c_T|^2-2(r+sigma)c_T.e+(r+sigma)^2
      <=M^2-2(r+sigma)(r+1/2)+(r+sigma)^2
      =M^2-r^2-r+1/2-sigma
      =(2sqrt(2)-1)R-sqrt(R^2-1/4)-3/2+1/sqrt(2).             (3)

The coefficient r+sigma is positive throughout the stated window,
so the direction of the projection substitution is correct. This
calculation includes all orientations and all weak support endpoints.

### 2.2. One rational margin excludes the whole cap

Throughout R>=79/40,

    sqrt(R^2-1/4)>R-1/15.                                    (4)

Both sides are positive. Squaring reduces (4) to

    2R/15-229/900>0,

whose lower bound at R=79/40 is 2/225>0. Also

    R<133/64,                sqrt(2)<99/70,                  (5)

with positive squared reserves respectively 9/4096 and 1/4900.
The right side of (3) is therefore strictly less than

    (2R+1/2)(sqrt(2)-1)-14/15
      <(149/32)(29/70)-14/15
       =6691/6720
       =1-29/6720.                                         (6)

Distinct interior-disjoint unit squares have center separation at
least one, since their open radius-one-half incircles are disjoint.
Equations (3)--(6) contradict this for the actual pair T,L. This
proves the claim.

**Outward-cap corollary.** At the actual D root, no positive edge to a
body different from L can have its normal equal to the outward radial
leaf direction e. That original edge would put its unchanged neighbor
wholly in (1). No normal is reselected, and no neighbor is required
to have positive circle load.

## 3. The complete original root chart and every force

The genuine radial-leaf theorem, including its selected off-origin
point-contact convention, gives an actual aligned root and its real
leaf. Rotate the entire packing to make e=e_x and write

    H=[-s,r] times [-b,a],
    r=R-sqrt(2), s=1-r,
    a,b>0, a+b=1,
    p_HL=(r,0), n_HL=e_x.                                   (7)

The D leaf meets a relative interior point of H's east side. The
actual H contains O openly and is physically circle-clear. No
assumption on H's other true forces entered this chart.

For 2<R<=sqrt(1105)/16 the elementary margins recorded in
D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md and its full D-root input are

    r>1/2,           1/3<s<r,
    r^2-s^2=2r-1>1/16.                                     (8)

For clarity, r<2/3 follows from R<133/64 and sqrt(2)>140/99,
since 133/64-140/99<2/3. The strict lower comparison in (8)
follows from r>2-sqrt(2) and sqrt(2)<47/32.

Let X_i, 1<=i<=m, be all positive H neighbors other than L, with
unchanged magnitudes mu_i>0, outward unit normals n_i and actual
common applications p_i. If m=0, H's full force equation already
fails. Otherwise its complete force and origin-moment equations are

    alpha e_x + sum_i mu_i n_i = 0,       alpha>0,
    sum_i mu_i det(p_i,n_i) = 0.                             (9)

The displayed omission of the real leaf in the second sum is exactly
its zero moment det((r,0),e_x)=0. H has no physical circle force.
No other term is omitted or replaced.

For contradiction suppose every actual X_i physically touches the
circle. Every point x in such a unit then satisfies

    |x| >= R-sqrt(2)=r,                                     (10)

by comparing it with any one actual physical circle corner of that
same unit. The chosen corner need not carry a positive multiplier.

## 4. Deep root margins use all eight other original squares

First suppose a>1/4 and b>1/4. By (8), all four original own margins
r,s,a,b exceed 1/4. Choose a number eta strictly between 1/4 and
their minimum. Then the closed disk D_eta lies in int H.

Every other original closed unit E is disjoint from int H. Indeed,
a point of a closed full-dimensional convex square inside another
square's open interior would, by a small inward displacement in the
first square, give overlap of their open interiors. Therefore

    dist(O,E)>=eta>1/4

for every one of the other eight actual units, irrespective of its
positive-component membership or circle status.

Let z be the nearest point of E to O. The elementary nearest-point
inequality gives

    (z/|z|).x >= |z|>1/4       for every x in E.

The force-free whole-orientation cap theorem in
GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md Section 1 now assigns each of
these eight actual E one connected open-interior arc on the same
circle of radius 5/4, of angular length strictly greater than pi/4.
Their open arcs are pairwise disjoint because the eight original
square interiors are disjoint. Their total length would exceed 2pi.
This contradiction excludes the whole deep-margin domain.

The exact boundaries a=1/4 or b=1/4 are retained in the next domain.
No square is removed to obtain this nine-square capacity bound.

## 5. A shallow root has a strict full torque sign

Reflect the entire chart vertically if necessary. The remaining
complete domain is

    0<a<=1/4,             b>=3/4.                            (11)

Apply the force-free theorem D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md
to each actual physical triple H,L,X_i, with the unchanged n_i,p_i.
Its scope permits arbitrary neighbor degrees, zero circle weights,
strict vertices, owned sides, side interiors and all mean endpoints.
It gives

    (n_i)_y<=0             for every i.                       (12)

The y component of H's full force equation (9), with all positive
mu_i retained, implies (n_i)_y=0 for every i. Each original unit
normal is consequently east or west. The outward-cap corollary
of Section 2 excludes east for every X_i. Hence

    n_i=-e_x,              p_i=(-s,y_i),
    -b<=y_i<=a.                                               (13)

This is a statement about the original applications, including
any original weighted mean on the full H west side. By (10),

    s^2+y_i^2>=r^2,
    |y_i|>=sqrt(r^2-s^2)>1/4.                                 (14)

But y_i<=a<=1/4. Therefore y_i<-1/4 for every actual nonleaf
positive force. Its unchanged origin moment is

    det(p_i,-e_x)=y_i<-1/4.

The second complete equation in (9) becomes a strictly negative
sum of positive multiples of these y_i. It cannot be zero. This
excludes the whole shallow domain, including a=1/4, every actual
side mean and every physical zero-weight circle corner.

Sections 4--5 exhaust (7) and prove the theorem in Section 1.
The proof did not use a force equation at any X_i, an X_i--X_j
contact, a cyclic port order, an endpoint degree or a concurrence.

## 6. Two entire original C1.5.b1 D families

Use the exact original house labels and positive block edges from
FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md:

    roof T; hubs A,D; lower vertices B,C;
    AT,DT,AD,AB,BC,CD.

Add the one original genuine leaf L at the displayed root, and
retain all three arbitrary physical completion squares. No block
edge or force is deleted.

| Entire original D family | True root star, including L | Physical boundary premises used | All true block degrees |
| --- | --- | --- | --- |
| M6.B5L.HOUSE.HUB.LTDB.D | A has exactly T,D,B,L | T,D,B are positively loaded and hence physically boundary | A4,D3,T2,B2,C2 |
| M6.B5L.HOUSE.LOWER.LTAC.D | B has exactly A,C,L | A,C are positively loaded and hence physically boundary | B3,A3,D3,T2,C2 |

In the first row take H=A. Its three nonleaf positive neighbors are
precisely T,D,B. The actual C remains its true unloaded degree-two
body with both original edges BC,CD and both original means. No
transmitter equation is needed in this proof.

In the second row take H=B. Its two nonleaf positive neighbors are
precisely A,C. The actual D remains its true unloaded degree-three
body with every force AD,DT,DC. The loaded roof T and all of its
original circle data remain. No degree-two equation is assigned
to A or D, and no extra force at a hub is discarded.

Both rows meet Section 1 literally throughout their entire original
positive-load orbits. The theorem uses physical boundary status only,
so every single-/double-circle-corner mask, individual zero corner
weight, zero-total physical boundary status at another block body,
selected contact owner, original shared-side mean, D-root slider,
root-preserving image and completion placement is retained. The
inherited same-nine R>2 theorem covers the rest of the original
radius window, including R=2. The upper radius endpoint is included
by the strict margins in (5)--(6) and the stated accepted inputs.

At comparison head 703cfc0e079b93fc860a4f32cbb5ce5f70458b4b, these are
exactly two existing unchecked fine IDs. They are prospective whole
family exits after full root and independent review, not new feature
labels. Their corresponding S families remain separate obligations.
The thirteen still-open original house/fan load orbits therefore
remain thirteen until their other full alternatives are handled;
this result would reduce their twenty-six full S/D obligations to
twenty-four. It closes neither of the five whole remaining rooted
types nor the coarse C1.5.b1 cell by itself.

## 7. Reusable scope, provenance and dependencies

The local outward-cap exclusion of Section 2 is force-free on the full
79/40<=R<=sqrt(1105)/16 window. It can be reused even when a candidate
unit T is physically circle-clear or has arbitrary degree. Its new
uniform rational center-distance reserve is 29/6720. It is not a pose
grid or a finite family of computational sign obligations.

The root theorem is a uniform necessary condition for every genuine
D leaf in the original nine-square problem: its true root must have
another positive neighbor which is physically clear. This may be
joined to further whole original graph/load families only after all
of their actual root neighbors are audited. In particular an unloaded
neighbor is not assumed physically clear or physically boundary merely
from its zero multiplier.

The exact active source copies below were fetched read-only at the
comparison head and are locally cached in current_703_base/research/nine.
Hashes are SHA256 of the complete UTF-8 source bytes.

| Active input | Exact SHA256 | Use |
| --- | --- | --- |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Actual D leaf/root, physical clearance, radial application and full degree-independent chart |
| D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md | 79ddc3bc94613ba34b30ea3b1e4176a14d644b08887020cbc38f9ef9d785d8a8 | Every actual boundary neighbor has weakly downward normal in the entire shallow domain |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Section 1 only: each actual far unit has a longer-than-quarter-turn open inner arc |
| NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | 46220c8a3eb3f539c682bf6a6fa932edf003e37484e0f6004d321e7cb14d7957 | Original same-nine R>2 with its current five-charge replacement and declared prerequisite chain retained |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original graph, two load sets, root stars and complete S/D family contract |

The sharp contained-center inequality was reproved in Section 2;
no end-triangle force or tip-degree theorem was imported for it.
The handoff and original roadmap supply only the stated comparison
frontier and existing fine identifiers; no bookkeeping file is edited.

No scalar force certificate, new angular subdivision, post-extraction
normal choice, force deletion, arm contraction, lower-degree replacement,
Lean compilation, CI, workflow dispatch or remote write is a premise or
action of this source. The new cap inequality and full-root moment proof
are analytic; the existing same-nine radius-two certificate remains an
explicit inherited dependency.
