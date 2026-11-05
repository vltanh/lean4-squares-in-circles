# Fresh strict 011/00 root and exact affine adapter, version 2

## Status and caller

This is a new implementation of the full strict `011/00` caller. It is
prepared for independent physical review. It proves no cell or mask
excluded, starts no numerical search, and installs no conditional terminal.
The previously reviewed prepared specification remains unchanged. The only
strengthening of its initial box is the separately reviewed universal center
bound `91/60`; it has no chain, sign or ordering premise.

There are nine physical unit squares, with fixed labels A through I. Every
one of their 36 corners has squared distance **strictly less** than
`Q = 1105/256` from the fixed disk center. All 36 original pairs have
disjoint open interiors; contacts remain allowed. There are five directed
center-cone links AB, BC, CD, EF and FG. Each has `dx >= |dy|`. AB, EF and
FG have `dx >= h_i+h_j`; BC and CD have **strict** `dx < h_i+h_j`.

A common rotation puts the supplied witness basis on the x/y axes, without
translating the disk. Each square's own quarter-turn symmetries choose its
canonical parameterization

\[
 u_i=(\alpha_i,\beta_i),\quad v_i=(-\beta_i,\alpha_i),\quad
 \alpha_i^2+\beta_i^2=1,\quad \alpha_i\geq |\beta_i|.
\]

This is a parameterization of the same physical square. In particular,
`alpha_i` is positive. Put `z_i=|beta_i|`,
`h_i=(alpha_i+z_i)/2`, `g_i=1/(2(alpha_i+z_i))`, and
`t_i=beta_i/alpha_i` in the complete closed interval `[-1,1]`.

Columns 0–17 are the interleaved center coordinates; columns 18–26, 27–35,
36–44 and 45–53 are respectively alpha, beta, z and g. The root has empty
path, empty selected-pair list and empty inherited difference and diagonal
maps. It assumes no large gap, no actual BC, no endpoint sign, no DG
vertical or horizontal guard, and no H/I ordering. No registered 001 cell
or its geometry stack is imported.

The exact nonlinear target is also the already published generic emitter
called with `mask='011/00', radius='strict', n=9`. This implementation does
not call a solver. Its affine rows are necessary consequences of this
target, so a feasible relaxation point is not a physical witness.

## 1. Universal initial bounds

For a center c and its orthonormal side frame u,v, let `r=||c||`. The
largest squared corner norm is exactly

\[
 r^2+\tfrac12+|c\cdot u|+|c\cdot v|
 \ \geq\ r^2+r+\tfrac12.
\]

The last inequality follows by squaring the two nonnegative absolute
projections. At `rho=91/60`,

\[
 \rho^2+\rho+\tfrac12-Q=\frac{31}{57600}>0.
\]

Since `r^2+r+1/2` increases for nonnegative r, even closed containment
would imply `r<rho`. Thus every coordinate lies in `[-rho,rho]`. The
additional center-support rows below use this same norm bound, not merely
the coordinate box.

Canonical unit frames give `alpha^2 >= 1/2`, `beta^2 <= 1/2`, and
`1 <= alpha+z <= sqrt(2)`. Therefore the initial closed scalar boxes are

| Quantity | Initial interval |
|---|---|
| alpha | `[7/10,1]` |
| beta | `[-3/4,3/4]` |
| z | `[0,3/4]` |
| g | `[1/3,1/2]` |

The exact comparisons are `49/100 < 1/2 < 9/16` and `1/9 < 1/8`.
These intervals include both diagonal canonical endpoints and zero slope.

## 2. Outward frame intervals and propagation

All square roots are enclosed by two consecutive points of the grid
`2^-48`. Integer square comparisons verify the lower and upper endpoints;
no floating point enters this operation. For a slope interval `[l,u]`, let
`m` be the smallest absolute slope in that interval, with `m=0` when it
contains zero, and let `M=max(|l|,|u|)`.

The following exact functions supply interval endpoints before outward
rounding:

\[
 \alpha(t)=\frac1{\sqrt{1+t^2}},\quad
 \beta(t)=\frac{t}{\sqrt{1+t^2}},\quad
 z(t)=\frac{|t|}{\sqrt{1+t^2}},\quad
 g(t)=\frac{\sqrt{1+t^2}}{2(1+|t|)}.
\]

Alpha decreases with absolute slope; beta increases with signed slope;
z increases with absolute slope; and g decreases with absolute slope on
`[0,1]`. The width sum `s=alpha+z=(1+|t|)/sqrt(1+t^2)` increases there.
These monotonicities follow either by differentiation or squaring positive
quantities. The producer and checker independently compute the same grid
enclosures and verify their squared endpoint inequalities.

Propagation intersects each already proved scalar interval with these
analytic intervals. Every original difference interval is recomputed as
the Cartesian difference of the current center intervals, then intersected
with any previously proved interval for that same pair and direction.
There is no special CD or DG propagation. An empty intersection is an
explicit exact interval terminal; the independent checker reconstructs its
specific lower and upper endpoints.

Version 2 deliberately makes no scalar-to-angle contraction. Its
`infer_angles` interface returns the unchanged angles and no inference
identities. This is a weaker but valid interface for the accepted generic
replay core. Closed angle splitting is available. Unsupported old path
kinds and nonempty diagonal maps are rejected rather than interpreted.

## 3. Necessary rows for one original frame

Every interval endpoint yields its ordinary upper or lower bound row.
The canonical and absolute-value consequences are

\[
 z\leq\alpha,\qquad \beta\leq z,\qquad -\beta\leq z,
 \qquad \alpha+z\geq1.
\]

The last inequality uses `alpha^2+z^2=1` and nonnegative alpha,z. Slope
bounds give `l*alpha <= beta <= u*alpha`, because alpha is positive. The
outward width-sum interval supplies both bounds on `alpha+z`.

The absolute-value upper row is reconstructed from the **current proved
beta interval**, not just the angle interval. If its lower endpoint is
nonnegative, `z=beta`; if its upper endpoint is nonpositive, `z=-beta`.
If `b_l<0<b_u`, convexity of absolute value gives

\[
 z\leq\frac{b_u+b_l}{b_u-b_l}\beta
       -\frac{2b_ub_l}{b_u-b_l}.
\]

This distinction retains correctness when weighted bounds prove a beta
sign while the enclosing angle interval still crosses zero.

For `a in [a_l,a_u]`, `v in [v_l,v_u]`, and `a^2+v^2=1`, add

\[
 -(a_l+a_u)a-(v_l+v_u)v\leq -1-a_la_u-v_lv_u.
\]

Its slack is exactly `(a-a_l)(a_u-a)+(v-v_l)(v_u-v)`, nonnegative on the
rectangle. It is used once with `(a,v)=(alpha,beta)` and once with
`(alpha,z)`. Unit support rows `p*alpha+q*beta <= sqrt(p^2+q^2)` for the
eight small integer directions use Cauchy–Schwarz and an outward rational
square root on the right.

For `s=alpha+z>0` and any installed positive rational sigma,

\[
 -g-\frac{s}{2\sigma^2}\leq-\frac1\sigma.
\]

Its slack is `(s-sigma)^2/(2*s*sigma^2)`. For the positive proved width
interval `[s_l,s_u]`, the upper secant is

\[
 g+\frac{s}{2s_ls_u}\leq\frac{s_l+s_u}{2s_ls_u},
\]

whose slack is `(s-s_l)(s_u-s)/(2*s_l*s_u*s)`. Both use the exact physical
definition `g=1/(2s)`. The rectangular frame variables are never asserted
to be independent physical choices.

## 4. Center and all-corner containment rows

The center norm bound gives
`p*x+q*y <= rho*sqrt(p^2+q^2)` for the eight small integer directions.
For each of the 36 original corners, take all 32 integer directions
`(p,q)` satisfying `p^2+q^2=1105`. The row is

\[
 px+qy+\frac{\epsilon p+\tau q}{2}\alpha
      +\frac{\epsilon q-\tau p}{2}\beta\leq\frac{1105}{16}.
\]

Its left side is the dot product of `(p,q)` with the actual corner
`c+(epsilon*u+tau*v)/2`. Its right side has square
`Q*(p^2+q^2)`, so Cauchy–Schwarz and corner containment prove the row.
All four corners of all nine originals are retained. The weak supporting
rows are legitimate necessary consequences of the strict caller and also
hold for closed-Q control packings.

## 5. Five exact marked links

For each marked link i,j, the two cone rows are

\[
 x_i-x_j\pm(y_j-y_i)\leq0.
\]

For each bit zero, the row is
`x_i-x_j+(alpha_i+z_i+alpha_j+z_j)/2 <= 0`.
For each bit one, its negative is a necessary weak affine row. The source
predicate for BC and CD remains strict in the root document. In
particular, no actual-BC row or 001 equality blocker is available.

The axis-parallel closed square centered at c with halfside g is contained
in the physical square: for `|w_x|,|w_y|<=g`, both owned normal projections
have absolute value at most `g*(alpha+z)=1/2`. The interior of this inset
is inside the physical interior. Hence two originals' inset interiors are
disjoint. On a marked center cone, if `dx<g_i+g_j` then
`|dy|<=dx<g_i+g_j`, making the two inset interiors overlap. Thus all five
links also supply `dx>=g_i+g_j`. This argument uses their actual physical
pair condition, not an assumed axis separator.

## 6. All-pair rows and the four-way inset cover

Every physical unit square contains its centered open disk of radius
`1/2`. Disjoint physical interiors imply center distance at least one for
each of the 36 pairs. For proved difference intervals
`dx in [l_x,u_x]`, `dy in [l_y,u_y]`, ordinary quadratic secants give

\[
 -(l_x+u_x)dx-(l_y+u_y)dy
 \leq -1-l_xu_x-l_yu_y.
\]

Indeed `d^2 <= (l+u)d-lu` and `dx^2+dy^2>=1`. Bounds on both difference
coordinates are also printed explicitly. These rows are only necessary
conditions; they do not replace the full physical pair predicates.

For any selected original pair, disjoint inset interiors imply at least
one of `sign*(coordinate_j-coordinate_i)>=g_i+g_j`, for axis x or y and
sign positive or negative. The four closed alternatives form a complete
union. Each selected alternative yields that literal row, while the full
original caller remains in force. Every alternative, including boundary
contacts, must be retained in the enclosing proof tree.

## 7. Complete physical owned-axis SAT cover and six auxiliaries

The separating-axis theorem for two rectangles says that their open
interiors are disjoint exactly when one of their four owned side normals
separates the projections, allowing equality. Enumerating both signs gives
the eight `(owner,axis,sign)` alternatives used here. For canonical frames,
put

\[
 C=\alpha_i\alpha_j+\beta_i\beta_j,\qquad
 S=\alpha_i\beta_j-\beta_i\alpha_j.
\]

They satisfy `C^2+S^2=1`, `0<=C<=1`, and `|S|<=1`.
For the selected signed owned normal n, the support sum is
`(1+|C|+|S|)/2`, independently of the owner and chosen owned axis.

Each selected pair receives exactly six auxiliary columns, in its path
order:

| Offset | Physical value |
|---|---|
| 0 | `n_x*(x_j-x_i)` |
| 1 | `n_y*(y_j-y_i)` |
| 2 | `alpha_i*alpha_j` |
| 3 | `beta_i*beta_j` |
| 4 | `alpha_i*beta_j` |
| 5 | `beta_i*alpha_j` |

The i,j order is always the increasing original-label order, independent
of which original owns the separator. Four signed support rows impose
`2*(z0+z1) >= 1+c*(z2+z3)+s*(z4-z5)` for both c,s signs. Their conjunction
is exactly the chosen support inequality when auxiliaries have their
physical meanings. The independent frame identities also give the stated
cosine and sine bounds and `z0+z1>=1`, since `|C|+|S|>=1`.

Each product `Z=UV`, with `U in [l,u]` and `V in [a,b]`, has four
McCormick rows. Their nonnegative residuals, in printed order, are

\[
 (U-l)(V-a),\quad (U-u)(V-b),\quad
 (u-U)(V-a),\quad (U-l)(b-V).
\]

The normal's signed coordinate interval is reconstructed from the current
proved scalar box. Difference-product intervals use the current proved
original pair rectangle. Frame products use the same original alpha/beta
variables as every other row. The auxiliary absolute bounds are the
largest absolute corner product of these intervals. No old normal sign,
separation corridor or guessed numerical frame is used.

## 8. Exact replay and complete coverage

The producer and independent adapter are separate standard-library-only
modules. The adapter imports neither the producer nor any previous
geometry stack. It checks the entire strict root document, including all
labels, corners, pairs, alternatives, five literal bits, all initial boxes,
and the absence of extra assumptions. At each weighted use it reconstructs
every printed row from its family and current certified physical state,
and supplies a proved absolute bound for every original or auxiliary
column. Altered rows, unknown families and unsupported paths are rejected.

The unchanged generic exact replay core checks integer-weight rational
sums, residual payments and outward-rounded deductions. If a sum has
coefficient vector c, right side b and absolute bounds M, its strict
contradiction reserve is `-b-sum(M_k*|c_k|)`. Only a positive reserve
excludes a node. An interval terminal is accepted only after independent
reconstruction of the empty interval. No LP point or solver diagnostic is
a proof premise.

The separate complete-cover interfaces require exactly all four inset
alternatives, all eight owned physical alternatives, or both angle halves.
An angle cut at r uses `[l,r]` and `[r,u]`; the shared r face appears in
both. A proof of the whole root would additionally require an enclosing
complete-tree assembly starting at the verified initial state. No such
search or whole-tree exclusion is claimed by this implementation packet.

## 9. Controls and practical limits

The control script independently reconstructs every baseline literal,
every owned alternative on every original pair, every proxy alternative,
and many closed angle children. It checks physical rational frame and
corner examples, the exact inset and McCormick residual identities, and
the symbolic squared enclosures at both diagonal canonical endpoints.
It replays complete zero-round 4/8/2 covers as **OPEN**, preserving all
faces. A hand-constructed three-row weighted certificate proves a center
difference lower bound in one guarded proxy child and remains OPEN; no
numerical solver is involved.

Damaged controls change strict scope, marked bits, labels, initial signs,
old paths, physical pair inventories, row right sides,
owned choices, exact multipliers and cover completeness. They must fail.
The strict seven-original `011/00` packing below `17/4` remains a valid
seven-original control. Duplicating originals to supply H and I fails the
full 36-pair caller. The five known other-mask closed-Q witnesses are
retained as controls for universal rows; their equality radius prevents
any strict-radius counterexample claim.

The baseline intentionally omits optional Gram, four-product, owner-free,
sharp row and accepted conditional-terminal extensions. They may be added
only with their own source-bound reconstruction against this new caller.
Likewise, global vertical reflection and H/I relabeling could support a
separate symmetry layer after explicit whole-caller review; neither is
installed here. The implementation is a clean starting point for such
extensions, not a claim that these initial affine rows already close the
full mask.
