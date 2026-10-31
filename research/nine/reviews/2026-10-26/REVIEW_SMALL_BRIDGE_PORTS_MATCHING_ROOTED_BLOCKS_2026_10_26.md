# Independent full review: small bridge ports and unloaded matching

Date: October 26, 2026.
Reviewer: rooted-blocks independent agent.

**Verdict: ACCEPT the complete small-port theorem and matching corollary.**
The full reviewed source is
`GLOBAL_CLOSURE_SMALL_BRIDGE_PORTS_AND_MATCHING.md`, SHA-256
`69b2a3abc3a4d0f52c49abb99bfedc642e4251221f079a72b179fe8ca1f09d18`.

The off-origin direct prerequisite has been clarified to state explicitly
that U has positive pair degree. Its revised SHA-256 is
`ef623b16310b6b253f71771c6c3c339be905d9555fa06228aa92f25868d945a8`.
My earlier full review in
`REVIEW_OFF_ORIGIN_BRIDGE_TRANSMITTERS_ROOTED_BLOCKS_2026_10_26.md` applies
to this clarification: all reviewed nontrivial bodies belonged to a
positive component. The new wording excludes vacuous unstressed extras,
which may of course avoid the origin. The small-port source now explicitly
handles those degree-zero extras as trivial isolated vertices. No intended
application or proof has changed.

## 1. Actual degree and radial equations

For a positive-component unloaded all-bridge body the degree is at least
two. Every incident bridge is a separate branch, so the proved
minimum-support articulation argument bounds the degree by three. At
degree three, collinear branch forces would put the three vectors
(f_j,a_j) in dimension at most two. Positive private branch masses and the
exact nonnegative scaling give a complete smaller-support normalized
stress, a contradiction. Thus the three directions are pairwise
nonparallel. This conclusion uses the full original equation at the body.

The accepted off-origin theorem puts a degree-three body H through the
origin. Every original bridge port then satisfies p=rho n with
rho=h_H(n)>=0. Its contained physical neighbor gives rho<=d. These
statements include zero applications and endpoint means; no port is
replaced by a midpoint.

At degree two the two actual supports are opposite. Their projected
separation, and hence their Euclidean distance, is at least one. Two
ports of norm at most 1/4 would be at distance at most 1/2. This directly
excludes the degree-two alternative, including bodies avoiding zero.

## 2. Complete two-small-port feature cover

For degree three, coincident small ports and nonparallel normals force the
common port to be zero. It cannot be a side-interior point, whose normal
cone has only one ray. At an origin vertex choose H=[-1,0]^2. The two
nonparallel outward normals lie in its closed northeast normal cone.
Their positive weighted sum has both coordinates strictly positive.

For distinct small ports, their distance is at most 1/2, so they cannot
both be distinct square vertices. Relabel a side-interior port as
p_1=(x,0), with normal e_x and 0<=x<=1/4. In the actual own frame
H=[x-1,x] times [b,b+1], containing zero. The opposite left face is too
far from zero. Another right-face interior would repeat the first normal.
The second port must therefore lie on a horizontal face or its right
endpoint. Reflection gives the actual form

    H=[x-1,x] times [y-1,y], 0<=x,y<=1/4.

The second normal has nonnegative first component and positive second
component. This follows from the original radial relation and its support
feature, and includes a top-axis endpoint. The two positive weighted
normals consequently have two strictly positive components. This is the
same conclusion as in the coincident case. No missing side/vertex
transition or zero-application alternative remains.

The third actual normal is strictly southwest by the genuine three-force
equilibrium. It exposes p_3=(x-1,y-1). Radiality forces its support height
to equal |p_3|, and the exact comparison is

    |p_3|>=3sqrt(2)/4>61/60>d,
    9/8-(61/60)^2=329/3600>0.

This contradicts the actual contained-neighbor support bound. The
small-port theorem is complete.

## 3. Whole induced-graph conclusion

For an edge between two truly unloaded all-bridge bodies containing zero,
the separating line passes through zero and radiality forces the actual
application to be zero. If one body avoids zero, its accepted off-origin
form has applications rho e and (rho+1)e with 0<rho<=epsilon. The second
body cannot be its outward neighbor: it would lie beyond radius one,
whereas every positive-degree unloaded all-bridge body meets D_delta,
delta<1/12. It is the actual incoming neighbor, and the port has norm at
most epsilon<1/60. The same theorem excludes two adjacent off-origin
bodies, so this is an exhaustive edge cover.

Every edge in the induced graph is therefore small. The full small-port
theorem bounds every induced degree by one, and the graph is a matching
plus isolated vertices. All surviving applications, positive magnitudes
and means are their original ones. This conclusion is valid with arbitrary
cyclic blocks elsewhere; no degree-specific equation is imposed on a
cyclic interface body.

The common canonical-pose and minimum-support scope remains attached to
the forest application. The result does not exclude a biconnected block or
prove the sharp radius by itself. No Lean compilation, CI, numerical
sampling or remote action was performed.
