# A weighted occupied-arc budget: every compatible seven-cycle has at most one diagonal transmitter

Date: October 30, 2026 UTC.

**Status: complete proposed hand family theorem, awaiting independent
full review. This does not close all seven-body graph or load domains,
and no original proof gate is changed.**

The actual chord of each gap retains more information than its arc
length alone. This gives one uniform integer inequality for every
compatible marked cycle with true side or diagonal transmitters:

    2m+d<=15,

where m is the number of actual cycle bodies and d is the number of
diagonal singleton transmitters. In particular every compatible
seven-body cycle has at most one such diagonal, regardless of its
load count or the positions of its runs. The proof is a single
occupied-arc argument over all original orientations and means.

## 1. Actual occupied arcs and their directed gaps

Assume actual unit squares have disjoint open interiors and lie in a
centered disk of radius

    79/40<=R<=sqrt(Q), Q=1105/256.

The complete occupied-arc theorem
`OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md`,
SHA256369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403,
proves the following physical facts on the circle of radius rho=5/4.

Each actual square touching the outer circle has one connected full
intersection arc. One may choose a compact subarc in its open interior
whose angular length lambda is strictly greater than pi/4, retaining
both its center direction and any chosen actual outer-circle corner
direction. The selected compact arcs of distinct physical units are
disjoint. Their actual cyclic order is their center and outer-corner
order. For a compatible marked cycle, the original occupied routing
and retained outer-circle spokes give exactly this marked cycle order.
No torque or abstract-planarity substitution is used for that order.

Take t>=2 selected physical-boundary units in this cyclic order. Let
lambda_i>pi/4 be their actual compact arc lengths, and let delta_i
be the directed intervening angular gaps. Then

    sum_i (lambda_i+delta_i)=2pi.                       (1)

The two endpoints of the i-th gap are actual points of the two
consecutive original units. If their Euclidean set distance is at
least W_i, their chord length satisfies

    2rho*sin(delta_i/2)>=W_i.                           (2)

Since 0<=delta_i<=2pi, equation (2) implies

    delta_i>=2asin(W_i/(2rho))                         (3)

whenever W_i<=2rho; larger W_i is itself impossible. Formula (3)
does not replace a directed gap by a minor angle. In particular it
is still valid for delta_i>pi, because delta_i/2 remains in[0,pi]
and sin(delta_i/2)>=u implies delta_i/2>=asin(u).

## 2. Three exact gap costs, with no trigonometric approximation

At rho=5/4 the following implications are strict:

| Actual set-distance lower bound | Directed angular gap |
| --- | --- |
| W>=1 | delta>pi/4 |
| W>=sqrt(2) | delta>3pi/8 |
| W>=2 | delta>pi/2 |

For the first row, sin(pi/8)^2=(2-sqrt(2))/4<4/25,
because sqrt(2)>7/5>34/25. Thus2/5>sin(pi/8), and (3)
gives the asserted gap.

For the second row,

    sin(3pi/16)^2=(2-sqrt(2-sqrt(2)))/4<8/25.          (4)

Indeed sqrt(2)<71/50 gives

    2-sqrt(2)>29/50>(18/25)^2,

where the final difference is77/1250. Hence
sqrt(2-sqrt(2))>18/25, proving (4). Equation (3) then
gives delta>3pi/8. The comparison sqrt(2)<71/50 follows by
positive squaring, since5041>5000.

For the third row, (4/5)^2=16/25>1/2=sin(pi/4)^2.
Thus4/5>sin(pi/4), and (3) gives delta>pi/2.

These strict comparisons remain valid at the upper disk radius and
at every physical support or circle-weight endpoint.

## 3. The whole weighted budget

Suppose a compatible marked cycle has exactly the following run
types between its t physical-boundary marks:

* direct contact, with no internal body;
* a singleton side-normal transmitter, actual reserve1;
* a singleton diagonal transmitter, actual reserve sqrt(2);
* two side-normal transmitters, actual total reserve2.

Let s,d,l count the three nonempty types, respectively. All bodies
are actual and distinct as vertices of the original simple cycle,
and

    m=t+s+d+2l.                                       (5)

Actual support telescoping makes the endpoint set distances at
least the indicated reserves. Apply Section2 to the original gaps
and the occupied arc estimate to the marks. Equation (1) yields

    2pi > t*pi/4+s*pi/4+d*3pi/8+l*pi/2
         =(pi/8)*(2m+d).                              (6)

Consequently 2m+d<16. Since m,d are integers,

    boxed: 2m+d<=15.                                  (7)

For m=7 this gives d<=1. All positions of the diagonal runs, every
side-versus-shared-point application and all orientations of the
marked bodies are covered by this same inequality.

The purely geometric part needs only the actual arc order and the
three set-distance lower bounds. A caller may supply them without
stress if its actual paths already have those support properties.
The full physical-stress caller below explains exactly where moment
balance enters the discrete run classification.

## 4. Full actual force-and-moment caller

Let the unmarked cycle bodies have zero total circle load and full
true positive degree two in the original physical certificate. Retain
their original force normals, positive magnitudes and actual support
means. Full translational balance propagates equal opposite normals
and equal magnitudes along each unmarked run. Full angular balance
makes consecutive actual means differ parallel to that common normal.

For a unit square, opposite support means whose difference is
parallel to their normal have width exactly1 or sqrt(2). With a
zero own-frame component of the normal, the support features are
opposite sides and the width is1. With both components nonzero,
they are the uniquely exposed opposite vertices; parallelism forces
equal component magnitudes and width sqrt(2). This retains every
endpoint mean on a side and does not assume a generic contact.

Every actual center satisfies |c|<M=91/60. A run with internal
width sum W has endpoint center projection at least W+1. Thus
W+1<2M=91/30. Three internal bodies would give W+1>=4,
which is impossible. Two internal bodies including a diagonal would
give W+1>=2+sqrt(2)>91/30, also impossible. Therefore every
run has precisely one of the four types in Section3.

This proves (7) for every compatible marked cycle with this literal
full true-degree and zero-load condition. Marked bodies can have
arbitrary other positive edges, circle masks and actual means. They
need only be physical-boundary units; an individual circle weight
may vanish. No full equation is applied after deleting an unmarked
body's additional edge, and no purely translational certificate is
used to infer the side/diagonal classification.

For an entire simple positive component, the existing full force
argument supplies at least two positively loaded bodies. Mark all
such bodies. Every remaining body is a true unloaded degree-two
transmitter, so the preceding caller applies directly. Physical
circle contacts of zero-weight unmarked bodies are retained, not
declared absent.

## 5. Concrete simultaneous seven-cycle consequences

The inequality d<=1 removes every seven-cycle feature with at least
two diagonal singleton transmitters at once. In particular:

* Four loaded marks with run lengths (1,1,1,0) can have at most
  one diagonal among the three singleton transmitters. Both the
  two-diagonal and three-diagonal cases are excluded, at every
  cyclic placement and every physical corner mask.
* Five loaded marks with two singleton runs can have at most one
  diagonal. Both-diagonal features are excluded whether the two
  nonempty runs are adjacent or separated in the five-mark cycle.
* All compatible eight- and nine-body cycles are again excluded
  by (7), but their earlier complete occupied-arc theorem remains
  independently available and has the weaker force-only caller.

This does not replace the separate long-plus-diagonal angle theorem:
the latter already removes a single diagonal singleton when the same
seven-cycle also has a two-internal long run. Nor does it replace the
new sharp opposite-long/short theorem. The present inequality is a
uniform additional weighted occupation rule, not a relabeling of any
original fine obligation or a closure of the full seven-body parent.

## 6. Sources and verification boundary

| Source | SHA256 | Exact role |
| --- | --- | --- |
| `OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md` | `369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403` | Full actual inner-arc proof, compact interior arcs, compatible marked order, and the at-least-two-loaded caller |
| `SHARP_LONG_AND_DIAGONAL_RUN_ANGLE_BUDGET_2026_10_30.md` | `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc` | Only the separately identified existing long-plus-diagonal exclusion; not needed for (7) |

The weighted proof uses exact arc geometry and radical comparisons,
with full actual width classification supplied explicitly in Section4.
No numerical pose search, sampled angle, numerical trigonometric
comparison, finite contact table, original gate mutation, Lean
compilation, CI execution or publication is used by this derivation.
All original packing units, circle masks and means remain unchanged.
