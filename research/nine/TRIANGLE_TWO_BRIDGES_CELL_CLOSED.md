# The entire triangle-with-two-bridges cell C1.3.b2 is closed

**Status: complete whole-cell hand assembly; root and separate independent full hand audits passed.**
In the explicit working window
\[
                   \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\tag{1}
\]
the necessary planar physical certificate of a nine-unit-square radius
minimizer can be selected so that its unique positive component is not
a triangle with two bridges. Every graph attachment, radial leaf type,
physical circle mask, contact owner, actual application mean and all
four further physical squares are included.

This closes the entire coarse cell **C1.3.b2 / G3.M5.T2**. Together
with C1.3.b0, C1.4.b0 and C1.3.b1, there are now four closed coarse
cells and 54 open cells. Other five-body components remain possible
in the unresolved inventory, so the selected component still has
5--9 bodies and 3--7 noncollinear loaded resultants. This is not the
unrestricted sharp theorem or the equality classification.

## 1. The attachment cover is exhaustive

The connected five-body graph has one triangle block and exactly
two bridge edges. Its bridge forest has precisely three possibilities,
up to relabeling:

1. A two-edge pendant chain A--U--L attached to a triangle vertex A.
2. Two pendant leaves attached to the same triangle vertex A.
3. One pendant leaf attached to A and one to a distinct triangle
   vertex B.

Indeed, two bridge edges either belong to one path outside the
triangle, or are two single edges with their endpoints on the
triangle. In the second situation their attachment vertices are
equal or distinct. No other cyclic block or bridge is available.

The radial bridge/leaf theorem retains the complete physical S/D
leaf cover. A leaf cannot be unloaded. Its precise radial inner
application and all genuine supporting-side intervals are the ones
in RADIAL_BRIDGE_AND_LEAF_REDUCTION.md; no condition is imposed on
an extra square's orientation or circle weight.

## 2. The chain and same-articulation layouts are excluded

| Full layout | Complete source | Exact scope |
| --- | --- | --- |
| Two-edge chain | TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | Both radial leaf types, both transmitter widths, every articulation frame, physical circle mask and pair-contact owner. The entire selected core is impossible. |
| Two leaves at one articulation | TRIANGLE_TWO_LEAVES_SAME_ARTICULATION_CLOSED.md | Exhaustive S/S, D/S and D/D assembly. Every support feature, parallel or oblique frame, actual side mean, positive weight and radius endpoint is retained. The whole selected core is impossible. |

Both complete implications have root and separate independent hand
audits. Their conclusions account for all four remaining squares
without placing them in hypothetical independent pockets.

## 3. The distinct-articulation domain is completely reduced

Use TRIANGLE_DISTINCT_LEAVES_DOMAIN.md. The only loaded bodies
in this component are the two pendant leaves and C, the third
triangle vertex. Both articulations A,B are physically circle-clear.
The source excludes every D/D leaf pair, every zero common triangle
moment, and the entire range R<=sqrt(17)/2, including its shared-side
endpoint. All remaining cases have
\[
 R>\frac{\sqrt{17}}2,\quad H\ne0,\quad
 d=\sqrt{R^2-1/4}-1=1+\delta,\quad 0<\delta<1/60,
\tag{2}
\]
with each articulation meeting the closed delta-disk about zero.

TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md retains all actual
ports, including shared means and the physical two-corner mask at C.
It excludes articulation port coincidences and proves the common
moment sign and positive radial concurrence at every nonparallel
articulation. Parallel articulation forces are not removed by this
statement.

TRIANGLE_DISTINCT_MIXED_LEAVES_EXCLUSION.md excludes the entire
remaining D/S family. Its directional support-span contradiction
does not assume an owner for the final triangle edge or a particular
circle mask at C. Thus only the whole S/S family remains.

## 4. Every remaining S/S core belongs to one complete exact family

The reduction and classification use these audited implications in order:

| Source | Whole implication |
| --- | --- |
| DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md | C has exactly one physical circle corner and nonparallel cycle forces. The exact positive core also shows why core exclusion alone would be false. |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | A side-owned normal in any physical unit-square contact triangle has nonnegative dot product with the other normal. This is a radius-free geometric theorem. |
| DISTINCT_S_LEAVES_PARALLEL_ARTICULATION_REDUCTION.md | The entire tilted-articulation and shared-AB domain is excluded unless at least one articulation has parallel cycle forces. Its leaf is then aligned with that articulation. All variable means and four extras remain. |
| DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md | Every wall frame pair and every contact owner is exhausted. All three central frames align, one exact radius is forced, and the complete position/force/mean intervals are determined with their valid endpoints. |

Explicitly, after rotation, reflection and relabeling, put
\[
 x=\frac{\sqrt{70}-8}{4},\quad \delta=x^2,\quad
 d=1+x^2,\quad u=1-x^2,
 \qquad R^2=(2+x^2)^2+\frac14.
\tag{3}
\]
The entire necessary family is
\[
 \begin{split}
 A&=[\delta,d]\times[t-1,t],\\
 B&=[-u,\delta]\times[2x-1,2x],\\
 C&=[-u,\delta]\times[2x-2,2x-1],\\
 L_A&=[d,d+1]\times[-1/2,1/2],\\
 L_B&=p+[0,1]e+[-1/2,1/2]Je,
          \qquad p=(-u,2x),\quad e=p/d,
 \end{split}
\tag{4}
\]
where the full slider domain is
\[
                       \frac{x(1-2x)}{1-x}\le t<2x.
\tag{5}
\]
The classification also supplies all positive force magnitudes and
every actual shared-side mean. The lower endpoint in (5) is valid;
some force means there are endpoints of genuine positive-length
sides. The upper endpoint is excluded by the strict selected
point-normal convention. Every t in (5) gives a physical positive
five-body core. This assembly does not contradict or discard that
positive control.

## 5. Whole-square routing and the completed universal capacity

DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md proves that the two actual
radial leaf rays screen every extra square into one of two sectors.
The origin-to-leaf segments lie in B or A, the next segments lie in
the leaves, and the actual outer-face screen excludes crossing
beyond the circle chord. Connected open interiors therefore cannot
cross a screened ray. This is a whole-square routing argument.

The upper sector has aperture pi-2 arctan(x)<170 degrees. Any upper
extra with center norm at most2/3 contains (0,2/11) strictly, by an
all-orientation side-coordinate bound; that point lies inside B.
Every remaining center therefore has radius in (2/3,151/100).
Inscribed-disk clearance from the two physical radial leaves excludes
forty degrees at each end of the sector. Two extra centers at angular
separation at most thirty degrees would be closer than one, contrary
to their disjoint inscribed disks. The remaining angular interval
has length less than ninety degrees, so it holds at most three
centers. This proves **upper capacity at most three**, uniformly
over the whole slider.

DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md proves **lower capacity zero**.
Its complete route is:

* Center-disk clearance from the full B/C column, together with the
  fixed B-leaf center, excludes every lower-sector center to the
  left of the column's right support.
* The actual screened horizontal ray then puts the entire square
  below y=0. Clearance from the fixed smaller rectangle contained
  in A union B, and from L_A, gives the complete center bounds.
* The two possible signs of an oblique frame are handled separately.
  A square extending around the right end of the central rectangle
  or below the bottom of C has an explicit corner outside the disk.
* Every remaining square lies in the complete quadrant
  x>=delta, y<=2x-1. Its orientation-uniform far-corner bound is
  at least R^2+4delta, strictly beyond the circle.

All boundary contacts, side endpoints and independent extra frames
are retained. In particular no separate capacity is added before
proving the routing of an entire square. The two complete theorems
yield
\[
             \#\{\text{additional unit squares}}\le3+0=3
\tag{6}
\]
for every core (4)--(5). A nine-square packing would need four,
which is impossible.

## 6. One compatible necessary certificate

The geometric and capacity arguments impose no new choices on the
four completion squares. The finite normal exclusions used by the
chain, same-articulation and distinct-articulation proofs are made
before the physical multiplier theorem.

For a fixed physical packing, prelist the finitely many relevant
body assignments, circle corners, radial leaves, side-axis owners
and genuine point-contact variables. Each new determinant or finite
direction exclusion is proved nontrivial on its permitted open
normal interval or product of independent intervals in its source.
The special coincident, radial, parallel and variable-mean cases
are either separately excluded or explicitly retained there.
Intersect the finitely many open dense choices with the preceding
strict, nonradial and matched-junction choices. The intersection is
nonempty. No selected force direction depends on an unknown
multiplier or on an arbitrarily fixed shared mean.

Apply the physical certificate theorem, then planar uncrossing and
thinning. Surviving point contacts retain their chosen normals;
uncrossing can add only actual shared-side forces, whose complete
intervals have been retained. Thinning deletes atoms. The unique
positive component and the at-most27-atom bound are unchanged.
If its graph were C1.3.b2, the exhaustive three-layout cover and
Sections2--5 would give a contradiction.

No secondary minimization assumption is needed for this cell. The
canonical secondary choice used in the separate opposite-load C4
work is not a premise of this assembly.

## 7. Scope of the closure

The entire C1.3.b2 cell is excluded throughout (1), with all four
completion squares accounted for. The positive S/S control and its
whole slider family remain valid five-body packings; their capacity
is at most eight units in total.

The remaining five-body cells are C1.4.b1, C1.5.b0 and C2.33.b0.
The boundary-only C7 lower-bound problem, all larger mixed cells,
the unrestricted sharp theorem and all equality cases remain
separate gates. Independent local audits and this assembly do not
claim a completed audit of the entire earlier prerequisite chain.
No Lean compilation or CI was run. Subsequent formalization remains
a separate stage, and PR #11 stays draft until the unrestricted
goal is finished.
