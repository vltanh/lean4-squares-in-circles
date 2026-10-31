# A triangle hub has weak third-support control without boundary returns

Date: October 28, 2026 UTC. Author: broad_load_channels continuation.
Comparison head: `234b4f0d03d772031dfc90a739fbe5b45351a3b8`.

**Status: complete proposed uniform weak-support theorem, complete general
channel/boundary-bypass exclusion, and complete original D02.L134 join;
frozen for full root and separate independent mathematical review.**
No original identifier or authoritative flag is edited. No computational
exclusion certificate is introduced.

The existing boundary-triangle proof contains a strict negative-support
argument whose operative hypotheses do not require boundary returns.
This source proves that weaker conclusion directly, with the actual
moment and winding inputs stated in full at their correct scopes.
It does not extend the old strict zero-support endpoint. A separate
physical spanning theorem handles the critical radius exactly.

Root checked the proposed boundary-free scope and its critical-radius
join during development and contributed to the separately frozen physical
spanning input. Root is not the sole independent reviewer of this source.
All original squares, true degrees, forces, torques, selected normals,
physical masks, actual applications and full mean intervals remain.

## 1. Exact actual setting and elementary support facts

Retain the same nine actual interior-disjoint closed unit squares, their
unchanged containing circle centered at O, and their common compatible
selected physical certificate. Work in the inherited interval

\[
79/40\le R\le\sqrt{1105}/16,\qquad
d=\sqrt{R^2-1/4}-1,\qquad
\epsilon=\max(d-1,0)<1/60.
\tag{1}
\]

Translate coordinates so the same actual O is zero. Every circle atom
is individually radial about O, including an atom whose coefficient is
zero. The full origin-moment equation at each body is therefore the sum
of all its actual positive pair moments equal to zero.

For any contained unit with center c and orthonormal own axes u,v, its
farthest-corner squared norm is

\[
|c|^2+1/2+|c\cdot u|+|c\cdot v|
\ge |c|^2+|c|+1/2.
\]

Consequently

\[
                              |c|\le d+1/2.
\tag{2}
\]

If an actual contained unit lies beyond an actual unit-normal support
`e.z>=b`, its e half-width is at least 1/2, so

\[
                         b+1/2\le c\cdot e\le|c|,
\qquad b\le d.
\tag{3}
\]

These full physical facts require no degree, force or circle-contact
premise and include every actual side and vertex support.

### 1.1. Every contact between two units outside the small disk has nonzero moment

Suppose two actual units both avoid the closed disk `D_epsilon`, and
their original common contact has application p and unit normal n.
Then

\[
                              \det(p,n)\ne0.
\tag{4}
\]

If p=0, either actual unit already meets that disk. Otherwise zero
determinant means that the original support line is radial. Write
`p=t e`, with t=|p|>0, and choose the names inner/outer so the inner
unit lies in `e.z<=t` and the outer unit in `e.z>=t`. The actual
outer unit and (3) give t<=d.

The inner unit avoids O, so at least one own interval misses zero.
Reflect such an own coordinate to write that interval as `[a,a+1]`,
a>0. Because e=p/t, the e-component along that positive own interval
is positive. Radial maximality at p therefore forces its corresponding
coordinate to be exactly a+1. Hence

\[
                      t>1,\qquad a\le t-1\le d-1.
\tag{5}
\]

If both own intervals miss zero, reflect both positively. Both coordinates
of p exceed one, giving `t>sqrt(2)>d`, impossible. Thus the other own
interval contains zero and the actual point `(a,0)` belongs to the inner
unit. If d<1, (5) is already impossible. Otherwise `a<=d-1=epsilon`,
so that actual point lies in the forbidden closed disk. This proves (4).

The argument preserves every original mean. Its two-body avoidance
premise ensures that whichever body is the radial inner one has the
needed avoidance. No unit is declared circle-clear from a zero load.

## 2. Boundary-free weak third-support theorem

Let U,V,W,Z be distinct actual units. Keep the original positive edges
UV,UW,VW,UZ, with

* U unloaded and its entire positive neighborhood exactly V,W,Z;
* V of true positive degree two, with entire neighborhood exactly U,W;
* W and Z of arbitrary original degrees, loads and other forces.

There is no physical boundary premise at U,V,W or Z. In particular the
second triangle hub W may be physically circle-clear, physically boundary
with zero load, or positively loaded. All its equations remain untouched.

Let n be the original U-to-Z unit normal and P its original application
or shared-side mean. Write

\[
                             h=n\cdot P=h_U(n).
\]

**Weak third-support theorem.** The complete original data imply

\[
                               h\ge-\epsilon.
\tag{6}
\]

This theorem does not claim `h>0` at d<=1. Its critical equality is
intentionally retained.

### 2.1. Every actual return lies behind the third support

The exact complete theorem
`UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md`
applies to the full unloaded U3 and the actual V-W contact. It has no
circle, radius, load or degree premise at the three neighbors. It gives

\[
                   n\cdot z<h\quad\text{for every actual }z\in V\cup W.
\tag{7}
\]

Every actual point of U has `n.z<=h` by the original support. These are
whole closed-unit statements. No center-only estimate is substituted.

Assume for contradiction that `h<-epsilon`. The three actual triangle
units then all avoid `D_epsilon`, and the whole actual center/contact
triangle loop lies in a strict half-plane disjoint from O. Its winding
about O is therefore zero. Every original triangle edge moment is nonzero
by Section 1.1.

### 2.2. The exact original moment equations give a complete sign dichotomy

For an oriented original positive edge I-J, use

\[
                 M_{IJ}=\mu_{IJ}\det(p_{IJ},n_{IJ}),
\qquad M_{JI}=-M_{IJ}.
\]

Both bodies use the same original physical application, opposite normals
and the same positive magnitude. Put

\[
                         x=M_{UV},\qquad y=M_{UW}.
\]

Both x and y are nonzero. The complete true-V2 origin torque, including
all its radial circle atoms, is

\[
                       -M_{UV}+M_{VW}=0,
\qquad M_{VW}=x.
\tag{8}
\]

If x and y have opposite signs, the actual positive triangle becomes
a directed cycle with every directed original moment positive: use
`U->V->W->U` when x>0,y<0, and the reverse when x<0,y>0.

Sections 2--3 of
`GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md`
prove the complete directed-cycle theorem at precisely these hypotheses:
all actual cycle units avoid closed `D_epsilon`, every directed original
moment is positive, and the original compatible physical embedding is
retained. It allows arbitrary true degrees and extra forces, coincident
ports and every original mean. The actual center/contact cycle must have
strictly positive winding about O.

This contradicts its strict negative half-plane. If a compatible local
routing is used, choose its finite neighborhoods within that half-plane;
positive clearance from O preserves the actual zero winding. There is
no assumption that the three physical contact points were distinct or
enclosed an artificial triangular face.

Thus x,y have the same strict sign. The full unloaded U3 origin torque
now gives

\[
                              M_{UZ}=-(x+y),
\tag{9}
\]

which has the opposite strict sign. Reflect the whole coordinates if
needed so the exceptional UZ moment is positive and both return moments
negative. No selected normal or extracted magnitude is changed relative
to the transformed physical configuration.

### 2.3. The full opposed-star theorem excludes the remaining sign domain

The exact Section 1 theorem of
`UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md`
assumes an actual unloaded body's entire positive force equation, an
exceptional original support below `-epsilon` with positive moment, and
strictly negative original moments at every other positive force.
It allows arbitrary true degree, needs no distance premise, no boundary
neighbor and no origin premise at the exceptional neighbor.

Here those hypotheses are literal at U: its entire equation has exactly
the original UZ,UV,UW forces; (9) and the preceding reflection give the
stated strict signs; and the alleged original support is `h<-epsilon`.
That theorem contradicts U's full force equation. No equation at W or Z
is used or shortened.

The two sign alternatives exhaust all original nonzero moments, proving
(6). The argument has not applied the older boundary-return critical
endpoint theorem with a missing boundary premise. Its zero-support case
remains within the weak conclusion, as required.

## 3. An actual unloaded channel forces the entire narrow wall domain

Replace the role Z by the first body T_1 on an actual positive path

\[
                     U--T_1--\cdots--T_k--Q,\qquad k\ge1,
\tag{10}
\]

where every T_i is genuinely unloaded with true positive degree two and
exactly its two path neighbors. All named units are distinct. Q has
arbitrary actual degree, load, normal owners and other forces. The
triangle U,V,W and its true U3/V2 hypotheses from Section 2 are unchanged.

### 3.1. Exact force, moment and width transmission

At each actual T_i the full unloaded two-force equation makes its two
original magnitudes equal and its forward normal the same n. The full
origin torque makes the difference of its outgoing and incoming
applications parallel to n. Since they are on its actual maximum and
minimum n-supports, this difference is

\[
                             w_i n,
\]

where w_i is the actual positive width of that original square in n.

If n is an own axis, w_i=1, and the original two transverse means are
equal. If n is not an own axis, its two support points are opposite
actual vertices. Their displacement has length sqrt(2); the torque
parallelism therefore forces n to be that actual diagonal direction and
w_i=sqrt(2). These alternatives include every original side mean and
endpoint, and do not reselect the transmitter frame or force.

Thus with P the original U/T_1 application,

\[
P_{T_kQ}=P+w n,\qquad
w=\sum_{i=1}^k w_i,\qquad w_i\in\{1,\sqrt2\}.
\tag{11}
\]

The actual Q lies beyond `n.z>=h+w`. Its full physical support bound
(3), together with (6), gives

\[
                        h+w\le d,\qquad h\ge-\epsilon,
\qquad w\le d+\epsilon.
\tag{12}
\]

No body in (10) is contracted, deleted or treated as an abstract force.
Equation (11) is an algebraic identity among the unchanged actual means.

### 3.2. Low, critical and high radius endpoints

If d<1, epsilon=0, so (12) and w>=1 would imply
`d>=h+w>=1`, a contradiction. Thus every survivor has

\[
                     d\ge1,\qquad R^2\ge17/4.
\tag{13}
\]

When d=1, (12) forces exactly `h=0,w=1,k=1`. No unsupported strict
zero-support conclusion is asserted.

When d>1, epsilon=d-1<1/60, and

\[
                        w\le1+2\epsilon<31/30<\sqrt2.
\]

Since every actual width in (11) is 1 or sqrt(2), the only possibility
again is `k=1,w=1`. In either radius case the complete original survivor
therefore satisfies

\[
                   k=1,\quad w_{T_1}=1,\quad
-\epsilon\le h\le\epsilon,\quad |h|<1/60,
\tag{14}
\]

\[
Q\subseteq\{n\cdot z\ge h+1\},\qquad
n\cdot z<h\quad\text{on the whole actual }V\cup W.
\tag{15}
\]

Every longer actual path and every diagonal transmitter was excluded by
its real width, rather than removed from the graph.

## 4. Complete channel/boundary-bypass theorem with no boundary return premise

In addition to the exact hypotheses of Sections 2--3, suppose an actual
physical boundary unit Y, distinct from all the displayed units, touches
Q and at least one of V,W. Y's entire actual degree, total load, other
forces and physical masks are arbitrary. The two contacts need only be
physical; in a positive original graph the given selected normals and
actual means are retained.

**Uniform theorem.** These full original data are impossible.

The entire low radius, multiple-transmitter and diagonal-width domains
were covered in Section 3. In the only remaining domain, choose n as
the horizontal direction. The actual Y has a point with x<h by its
contact with V or W and (15), and it touches the actual Q wholly beyond
x>=h+1. The complete physical theorem in Sections 1--4 of

`FAR_WALL_BOUNDARY_NEIGHBOR_SPAN_EXCLUSION_AND_D02_L0145.md`

therefore places every actual Y point strictly inside
`D_(sqrt(17)/2)`. This source allows arbitrary Q/Y degrees and all
original support owners and means. Its proof covers both tilt signs
of the actual Q, all four corners of Y, and all physical masks.

By (13), this contradicts Y's actual containing-circle contact at every
remaining radius, including the exact critical endpoint `R^2=17/4`.
Thus the absence of a strict h>0 conclusion at d=1 leaves no gap.

This theorem assumes no boundary status at V,W or Q. It uses no Q or Y
force equation and never shortens one. Its operative star equations
are exactly the full U3, the full V2 moment, and the true unloaded T_i2
equations. It retains all other original stars and all nine units.

## 5. Literal complete original D02.L134 application

The exact positive graph is the original six-body outer hexagon with
rim `01,12,23,34,45,50` and chord `02`. Its entire positive circle-load
set is `{1,3,4}`. Keep all three arbitrary original completing units.
The correct roles are

\[
                    U=0,\quad V=1,\quad W=2,
\quad T_1=5,\quad Q=4,\quad Y=3.
\tag{16}
\]

The entire actual stars and loads are:

| Body | Entire positive neighbors | True degree | Original total circle load |
| --- | --- | ---: | --- |
| 0=U | 1,2,5 | 3 | Zero |
| 1=V | 0,2 | 2 | Positive |
| 2=W | 0,1,3 | 3 | Zero |
| 3=Y | 2,4 | 2 | Positive |
| 4=Q | 3,5 | 2 | Positive |
| 5=T_1 | 0,4 | 2 | Zero |

The actual positive triangle is `0--1--2--0`. The genuine unloaded
channel is `0--5--4`. The actual loaded body 3 physically touches
W=2 and Q=4 through the original edges 23 and 34, and its positive
total circle load guarantees physical boundary contact.

All hypotheses of Section 4 are literal. In particular W=2 is not
assumed physically boundary. Its zero total load gives no such fact,
and the proof does not need one. It retains W's true degree three and
all three positive forces. The loaded Q=4 and Y=3 retain their entire
true-degree-two systems; neither is treated as a transmitter.

The graph reflection `i -> 2-i mod 6` preserves the D02 graph and sends
the original load set 134 to 145. It sends the role tuple in (16) to

`U=2,V=1,W=0,T_1=3,Q=4,Y=5`.

The same theorem applies with those literal labels and the reflected
full original loads. Hence the entire original load orbit is excluded,
with all force ratios, physical masks, original owners and means,
zero individual corner coefficients and completing units included.

The accepted same-nine lower-window theorem handles earlier R<=2
before entry into (1). Section 3 covers all remaining d<1, d=1 and
d>1 alternatives. No radius endpoint or physically clear W branch
is omitted.

## 6. Exact direct inputs and inherited boundaries

| Complete source | Bytes | SHA256 | Exact operative scope |
| --- | ---: | --- | --- |
| `UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md` | 16935 | `406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87` | Whole radius-free original U3 separation with arbitrary neighbor degrees and loads |
| `GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md` | 16597 | `8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49` | Only Sections 2--3: full disk-avoiding port order and directed-cycle winding, not its intact-root caller |
| `UNLOADED_OPPOSED_MOMENT_STAR_AND_LOWER_HOUSE_TDC_D_SMALL_SUPPORT_REDUCTION.md` | 14907 | `008acc8485e591b34604bf3e0b0cdcb03b7220aa249fc8e49552a065770ca129` | Only complete Section 1 strict opposed full-star theorem, with no boundary or distance premise |
| `FAR_WALL_BOUNDARY_NEIGHBOR_SPAN_EXCLUSION_AND_D02_L0145.md` | 20190 | `5a0e6118982b812bf27c831b68334052607920cfdf9a01bffbe85e1c4fc3eb3d` | Only complete physical Sections 1--4, including strict containment at R^2=17/4; not its boundary-return triangle caller |
| `SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md` | 11952 | `cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1` | Exact original D02.L134 load orbit, graph, true degrees and all-nine completion contract |
| `LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md` | 13069 | `3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90` | Same-nine radius entry with its accepted analytic prerequisites |

All five published inputs match the exact current234 tree blobs. The
new spanning source is a separate frozen local source undergoing its
own full root and independent review. Its acceptance and the complete
independent review of this source are required before authoritative
closure credit is granted.

The proof was motivated by the strict negative-support portion of
`UNLOADED_BOUNDARY_TRIANGLE_HUB_THIRD_SUPPORT_AND_CRITICAL_EXCLUSION.md`,
20568 bytes, SHA256
`d8661132bd2d97911116373d22968bbde2ff3c4c4a63c962c72d722ec3d5b089`.
That source's boundary-premised strict zero-support theorem is not an
operative input. The weaker generalization is proved above from the
exact full moment/winding and opposed-star theorems, without altering
the old manuscript or silently deleting one of its hypotheses.

The original selected-certificate and compatible physical embedding
foundations remain accepted inputs at their original domains. No new
complete transitive audit of those foundations is claimed here.

## 7. Exact prospective credit and further scope

After full root and separate independent acceptance, the new whole
original fine closure supplied here is exactly

`M6.B6.HEXAGON.D02.L134: false -> true`.

No new identifier, denominator change or whole D02 coarse closure is
claimed. The broad theorem also applies to the already separately
proposed L0145 caller, but gives no duplicate credit for that row.
The earlier L014 result remains a distinct theorem with a distinct
second-unloaded-channel hypothesis. No load subset or superset is
declared closed by monotonicity.

The generic result treats one through four actual internal channel
units, arbitrary degrees and full loads at both end neighbors and at
the physical boundary bypass, and every physical mask at the two
triangle returns. Further original callers require literal full-star
and graph/load joins. In particular L135, L0134, L0135 and L1345 are
not declared closed by this source.

No numerical pose, sign grid, optimization result, generated coefficient
packet or computational exclusion certificate is an operative premise.
No Lean compilation, CI, workflow, remote mutation, merge or authoritative
ledger edit was performed. The global sharp theorem and its complete
equality classification are not declared closed.
