# A full-angle stress leaf has a circle-unloaded neighbor

Use an extracted full-angle stationary stress from
`SPARSE_MINIMIZER_STRESS.md`, with its positive pair graph and actual physical
contacts. Assume `q>9/2`, as now established for every eleven-square packing.

**Theorem.** If a vertex of the positive pair graph has degree one, its sole
neighbor is strictly inside the containing disk: every point of that
neighbor square has squared norm strictly less than q. In particular the
neighbor has zero circle weight in any active-constraint stress.

The theorem uses angular stationarity. It does not apply to a general stress
obtained only after freezing the frames.

## 1. The leaf's local frame and position

Let L be the leaf and N its neighbor. Direct their selected normal n from L
to N and write beta>0 for the aggregate edge weight. An unloaded leaf is
impossible by force balance, so L has total circle weight A>0. Its force
equation is

    2 sum_w alpha_w (p_L+w) = -beta*n.              (1)

The leaf analysis in `FOUR_PATH_ANGULAR_CLASSIFICATION.md` is local: it uses
only (1), this one incident edge, and angular stationarity at L. It does not
use the unloaded status of any other vertex. For clarity, its consequences
and reasons are summarized here.

If L's frame is nonparallel to n, it cannot own the selected axis. Its
supporting corner in direction n is unique. With one loaded farthest corner,
(1) places that corner at `-sqrt(q)*n`, and the farthest-corner sign condition
makes its centered offset the negative of the support corner. The disk and
pair angle derivatives are both `beta*h_L'`; hence the support width is
stationary. This forces the diagonal, 45-degree frame.

If two farthest corners are positively loaded, the center lies on a frame
axis. Writing `p_L=-rho*u`, `n=c*u+s*v` with c,s>0, the difference of their
weights is `-beta*s`. The total angular derivative equals
`beta*((1/2-rho)*s-c/2)<0`, since rho>1/2; choosing the other center axis
instead gives the strictly positive counterpart. Thus this case is
impossible for a nonparallel frame.

Consequently L has one of two forms:

* **Parallel:** `p_L=-C*n`, where `C=sqrt(q-1/4)-1/2`. Its two farthest
  corners have equal positive weights. Their combined angle derivative is
  zero. The transverse center coordinate is zero, since otherwise every
  farthest corner has the same strictly signed transverse absolute coordinate
  and cannot satisfy (1).
* **Diagonal:** the unique farthest corner is `-sqrt(q)*n`. The opposite
  support corner, pointing toward N, has absolute position
  `P=-(sqrt(q)-sqrt(2))*n`.

All these statements are unchanged by swapping the labels of the pair and
reversing its signed normal.

## 2. A radial contact point prevents a neighbor circle contact

Suppose a shared point has the form `P=-r*n` with r>0, and the neighbor lies
in the inward half-plane `n dot x>=-r`. For any neighbor point x with
`||x||^2=q`,

    ||x-P||^2 = q+r^2+2r*(n dot x) >= q-r^2.

But P and x belong to one unit square, whose squared diameter is two.
Therefore if `q-r^2>2`, N cannot have any point on the containing circle.
Since N is compact and already lies in the closed containing disk, it is
then strictly inside the disk.

For a diagonal leaf, its support corner P is unique. Actual physical contact
forces P to belong to N as well. It is radial with
`r=sqrt(q)-sqrt(2)>0`, and

    q-r^2 = 2sqrt(2q)-2 > 4 > 2.

The preceding argument proves the theorem in this case.

## 3. Parallel leaf owning the selected axis

Suppose L is parallel and owns n. Set

    r=C-1/2=sqrt(q-1/4)-1 > 0.

Its inward face lies on the line `n dot x=-r`, with radial midpoint `-r*n`.
For each positive support-vertex atom, let w be the neighbor's centered
support corner in direction n. Their normalized convex combination is
`w_bar`. The point `p_N-w_bar` belongs to N's near support face, because
every such support corner is active and the face is convex.

The leaf's circle angle derivative is zero. For an owner-L pair atom, the
angular derivative is

    (Jn) dot (w-(p_N-p_L)).

After summing the positive atom weights, angular stationarity gives
`(Jn) dot (p_N-w_bar)=0`, since p_L is parallel to n. The selected separator
is tight, so this same point lies on `n dot x=-r`. Thus

    p_N-w_bar = -r*n.

It belongs to N and to the middle of L's inward face, and is therefore an
actual shared point. This argument does not assume that an arbitrary
individual support atom is a physical contact point.

Finally,

    q-r^2 = 2sqrt(q-1/4)-3/4 > 13/4 > 2,

where q>9/2 implies `sqrt(q-1/4)>2`. Section 2 applies again.

## 4. Parallel leaf with the neighbor owning the axis

If N owns n, then N is parallel too. Tightness puts its center at

    p_N=(1-C)*n+t*(Jn).

Actual contact of the two parallel squares requires `|t|<=1`. The use of
physical contact is essential here: angular atoms alone need not place the
radial face midpoint inside N.

Since C>1, the largest possible squared norm of a neighbor corner is

    (C-1/2)^2+(|t|+1/2)^2 <= r^2+9/4.

The previous strict estimate `q-r^2>13/4` shows this is strictly below q.
Every point of N is a convex combination of its corners, so the entire
neighbor square is strictly inside the disk. This covers the final owner
case and proves the theorem.

## 5. Consequence for the retained core size

A four-vertex path has two leaves, and each of its internal vertices is
adjacent to one of them. The theorem makes both internal vertices
circle-unloaded. The angular path classification then forces `q=17/4`
under `q<=49013/10000`, contradicting `q>9/2`.

Together with the spanning-star and four-cycle exclusions in
`CLOSED_STRESS_GRAPH_FAMILIES.md`, and the earlier exclusion of smaller
cores, this proves:

    Every retained connected full-angle stress core has 5<=k<=11.

It may be thinned and reconnected with the at-most-`3k` full-angle atom
bound. The smaller fixed-frame certificate must retain its separate scope:
thinning after discarding angle equations need not preserve this new
five-body conclusion.
