# One D leaf excludes a boundary fan with any number of genuine direct leaves

Date: October 26, 2026.

**Status: accepted complete uniform hand extension after the full root and
independent reviews named in the single-leaf source.** This source changes no gate. It uses the physical pocket/arc
assembly of D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, but proves the
new endpoint and moment argument needed for all additional original leaves.

## 1. Complete graph and exact scope

Keep the same original nine units, radius window and compatible selected
physical certificate. Let a complete positive component consist of a hub
H, a physical boundary path B_1,...,B_k, all its positive spokes H B_i,
and m genuine direct leaves L_1,...,L_m at H. Assume

    k>=2, m>=1, 1+k+m<=9,
    L_1 is an actual D leaf.

Every other leaf has its full actual S or D form. The B endpoints have
their genuine positive degree two, and internal B bodies degree three.
They physically touch the circle; all physical masks, zero individual
weights, actual means and extra zero-weight contacts remain. The other
8-k-m physical units are arbitrary. No positive root force is deleted.
If k+m=8, these eight distinct actual boundary units alone give the
eight-arc contradiction of Section6. Thus the remaining embedding
argument can assume k+m<=7 and, in particular, k<=6. It does not
discard the physical boundary graph's separate seven-cycle exception.

**Theorem.** The complete stated family has no nine-square completion.

The original same-nine lower-bound theorem reduces to R>2 and retains
all its declared arithmetic dependencies. Orient the true D leaf east.
The unchanged chart and margins of the single-leaf source are

    H=[-s,r] times [-b,a],  a,b>0, a+b=1,
    r=R-sqrt(2), s=1-r,
    7/12<r<2/3, 1/3<s<r,
    r^2-s^2>1/16.                                      (1)

The bound r>7/12 follows from R>2 and sqrt(2)<17/12. Every point
of a physical boundary unit has norm at least r. O is in int(H).

Write p_i,n_i,mu_i for the original fan spoke data, and alpha_j e_j
for the original positive radial leaf forces. Every genuine leaf has
zero origin moment, so the entire H equations give

    sum_i mu_i n_i + sum_j alpha_j e_j=0,
    sum_i mu_i det(p_i,n_i)=0.                          (2)

All m leaf forces occur in the first equation. The second is valid
for this whole family precisely because all actual outside forces
are genuine radial leaves. No whole-fan force equation is assumed.

## 2. The endpoint angular margin from the original D leaf

The physical boundary-center separation in CENTERED_INNER_ARC.md is
strictly greater than2pi/9. Every nonzero actual circle resultant is
within pi/12 of its own center direction, by the local calculation in
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, Section1. That calculation
requires no four-body force balance. The actual D leaf center lies on
the positive x axis. Consequently each loaded B endpoint resultant F
has circular angular distance

    dist(arg(F),0)>2pi/9-pi/12=5pi/36.                 (3)

Each B endpoint is loaded: its two genuine neighbors H and the next
boundary body physically touch, so it cannot be an unloaded normal
transmitter. The complete loaded degree-two concurrence lemma in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma2.1, applies because
the other neighbor is a real boundary unit. It gives, at its actual
root application,

    q=tF=p+ell n,        t>0, ell>=0.                  (4)

Physical radial corner masks and individual zero weights are included;
q need not be inside the endpoint unit.

## 3. If a horizontal side is shallow, no genuine leaf points toward it

If a,b>1/4, (1) puts a strictly larger concentric disk than D_(1/4)
inside int(H). Every other actual square then has distance greater
than1/4, and the eight-arc contradiction in Section6 is immediate.
It remains to consider a<=1/4 or b<=1/4. These two alternatives
are disjoint and are exchanged by vertical reflection. Assume

    0<a<=1/4,       b>=3/4.                            (5)

Every genuine direct leaf has e_j,y<=0. Here is the full owner cover.
A D leaf must have its inner vertex in a relative side interior of H
under the unchanged compatible selection. Positive vertical direction
would therefore be exactly e_y, with radial contact (0,a). It requires
a=r>1/2, contradicting (5).

For an S leaf, its actual radial support point is d e_j, where
d=sqrt(R^2-1/4)-1>9/10. If e_j,y>0, that point is on the top
side: it is either (0,a), or one of its two endpoints. By (1),(5),
every such vertex has squared norm at most r^2+a^2<73/144<9/16.
Neither this vertex nor the top-side radial point can have norm d.
This excludes every positive-vertical S normal, including axis endpoints.

There is also no additional horizontal genuine leaf. A horizontal S
would require support r or s equal to d, whereas both are below2/3<d.
A westward D would require s=r, contrary to (1). An eastward D has
exactly L_1's occupied square and cannot be a distinct physical unit.
Thus, if m>1, every additional genuine leaf has strictly negative
vertical force.

## 4. The first boundary endpoint has strictly positive origin moment

The actual fan embedding puts every genuine leaf in its exterior face.
Cut the H boundary at L_1's point (r,0), reverse the B labels if needed,
and use the unchanged ordered normal lifts

    0<=theta_1<=...<=theta_k<=2pi.                     (6)

The coincident-port and side-axis cases are exactly the normal-order
argument of Section3 of the single-leaf source. Its exterior H arc E
contains all actual leaf attachments. No leaf is inserted in an original
bounded triangular face.

There is a positive-vertical spoke. For m>1 this follows from the first
equation(2) and Section3. For m=1, a nonhorizontal spoke forces both
vertical signs. If all spokes were horizontal, their connected boundary
path forces one common sign, since opposite supports of H separate
consecutive boundary units by width one. All-east cannot balance L_1.
All-west would give p_i=(-s,y_i), with |y_i|>1/4 by (1), while
y_i<=a<=1/4; hence every y_i<0. The second equation(2), now
sum_i mu_i y_i=0, is impossible. This exhausts m=1 as well.

Thus theta_1 in[0,pi). If n_1 is east, p_1 is on the upper right
side, with 0<(p_1)_y<=a. Equation(4) places q_1 in the angular
interval from0 to arctan(a/r). But

    arctan(a/r)<a/r<3/7<5pi/36,                        (7)

using r>7/12 and pi>31/10 (31/72-3/7=1/504>0).
This contradicts (3). The actual leaf point cannot be another body
contact, as proved in the single-leaf source. Thus that zero-height
endpoint is not a missing alternative.

A strict northwest n_1 would put p_1=(-s,a), whose norm is less
than r by (1),(5), contradicting its membership in a boundary unit.
The only remaining first-port features are the northeast vertex and
the upward side axis. For the side axis, p_1=(x_1,a) satisfies
x_1^2>=r^2-a^2>s^2, so x_1>s>1/3 and

    det(p_1,n_1)=x_1>0.

For the northeast vertex p_1=(r,a), suppose its moment were nonpositive.
Its normal angle would then be at most arctan(a/r). Equation(4)
puts q_1 between that normal direction and p_1's direction, again
contradicting (3),(7). Therefore in every surviving case

    p_1 is a top-side point with x_1>1/3,
    det(p_1,n_1)>0.                                   (8)

## 5. The other endpoint must leave the shallow top-side segment

Suppose p_k were also on the top side, including its northeast vertex.
The boundary norm bound makes its first coordinate x_k>s>1/3, exactly
as for p_1. The original order (6) puts all intermediate hub applications
on that same positive-x top segment or at the northeast vertex.

At a top side-interior application the actual normal is e_y and its
moment is its positive first coordinate. At the northeast vertex the
moment is r sin(theta)-a cos(theta). This is strictly increasing on
[0,pi/2]. Every such theta in the original ordered path is at least
theta_1, whose moment is positive by (8). Thus every original spoke
has strictly positive origin moment. The second equation(2) is
impossible. This includes all coincident northeast applications and
their actual positive weights.

Therefore p_k is not on the top side or its northeast vertex. It also
cannot be on the upper right side: that precedes p_1 in the cut boundary
order. If p_k is on the left side, (1) and its boundary norm give
|(p_k)_y|>1/4; (5) then makes (p_k)_y<-1/4. Every remaining location
is on the bottom side, the lower right side, or the stated negative-height
part of the left side. In each case the complementary arc E from p_k
through the D leaf to p_1 has distance strictly greater than1/4:

* its upper portion is the eastward top segment from x_1>1/3;
* its right portion has x=r>1/2;
* any bottom portion has y=-b<=-3/4;
* any left portion remains below the negative-height p_k.

The reflected proof treats b<=1/4. The no-shallow-side case was
already handled in Section3. Hence the whole remaining domain has
the same strict exterior-arc margin as the single-leaf theorem.

If k=2 and the endpoint applications coincide, the shallow-side proof
just given places both at the prohibited top feature and contradicts
the original moment equation. Thus in every shallow-side case the
two endpoints are distinct. For k>=3 their physical boundary cycle
obstruction already gives distinctness. The occupied Jordan construction
therefore has no unhandled coincident endpoint in the cases where it
is needed.

## 6. Exact face count and common completion contradiction

Use the same actual occupied Jordan boundary and face cover as
D_LEAF_BOUNDARY_FAN_COMPLETE_EXCLUSION.md, Sections5--6. O is in
int(H), on the opposite side from the exterior hub pocket. The actual
boundary misses the closed quarter disk with a strict margin, so the
whole hub pocket has distance greater than1/4. This remains true after
all m physical leaves and every zero-weight contact subdivide it.

Every fan triangle and every consecutive boundary-pair exterior pocket
has unit capacity zero. Thus every one of the 8-k-m arbitrary other
physical units lies in the closing hub pocket. All of them, all k
boundary path units, and all m genuine leaves have distance greater
than1/4. There are exactly

    (8-k-m)+k+m=8

such original physical units. The force-free radius5/4 arc theorem
gives each an open-interior arc longer than pi/4. Their interiors
are disjoint, contradicting total angular measure2pi.

If no side is shallow, the disk strictly inside H already places all
eight other units at that same distance and the identical arc argument
applies without a pocket decomposition. This completes every case.

## 7. Whole-family scope and limits

The theorem excludes the entire finite family of fan-at-one-root
components with any number of genuine direct leaves and at least one
D leaf, within the original nine-body budget. It retains all SS/SD/DD
patterns that satisfy that condition, all original force magnitudes,
root degrees, actual means and corner masks. It requires no finite
coefficient packet or numerical sample.

The single-leaf k=4 caller gives the already specified original
M6.B5L.FAN.HUB.L1234.D and M6.B5L.FAN.HUB joins. Larger rooted fan
profiles receive a complete uniform exit, but no whole coarse parent
is declared closed without its other attachment layouts. An arbitrary
bridge branch is not a genuine leaf and is outside this theorem; its
possible upward small application invalidates Section3's leaf argument.
Other attached cyclic blocks also require their original force systems.
No external force is deleted to apply the result.

No original checklist edit, numerical pose, new arithmetic certificate,
Lean compilation, CI or remote action was performed by this source.
