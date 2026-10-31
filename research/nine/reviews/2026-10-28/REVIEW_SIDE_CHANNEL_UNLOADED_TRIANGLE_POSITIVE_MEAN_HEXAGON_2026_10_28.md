# Full independent audit: the original side-channel mean is positive

Date: October 28, 2026. Reviewer: hexagon.

**Decision: ACCEPTED, with no correction.** This is a full independent
mathematical and literal-scope review of the new local theorem. I read
its entire source and the operative rectangle, parallel-force,
support-span, strict-singleton and actual-channel arguments. I
independently derived the negative and zero-mean cases, retaining the
complete C2 and D3 stars and every original application mean.

## 1. Exact source and complete premise

Reviewed source:

    SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md
    SHA256 5a1607a588e45d0702c46c3d74074561f31109dccc0b8f94c665991cd4a9f5ee.

The actual positive edges are AB,BC,CD,DA,AT,DT. B is genuinely
unloaded degree two; C is loaded degree two with its entire pair
neighborhood B,D; D is unloaded degree three with its entire pair
neighborhood A,C,T. T is physically boundary. A and T retain arbitrary
additional forces and loads. The high-radius interval and support
premises are exactly those stated in the source.

The complete bypass theorem at the true B channel gives reserve one
and the physical transverse separation of the actual bypass D. With
the source's orientation the chart is

    B=[h,h+1] x [b,b+1],
    P_AB=(h,q), P_BC=(h+1,q), b<=q<=b+1,
    A subset {x<=h}, C subset {x>=h+1},
    max_D y<=b<=q, -epsilon<=h<=epsilon.

Here q is the unchanged transmitted application height. The proof
does not replace it by a center height, select b, infer a BD force,
or require a zero transverse gap. The asserted conclusion q>0 is
a necessary-domain theorem, not an exclusion of the positive-q house.

## 2. Conditional proper concurrence without a boundary neighbor

I read the entire operative proof of Lemma 2.1 in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md and rechecked the corresponding
rectangle calculations in C7_FORCE_POLYGON.md, Sections 3--5.
The distinction made in the new source is correct: a boundary-neighbor
premise excludes a parallel pair in the original lemma, but is not
used by its conditional nonparallel properness calculation.

For nonparallel pair forces, torque about their common line intersection
c makes c parallel to the full positive circle resultant. If the two
actual applications coincide, c is their actual point. For every
physical circle corner z of that square,

    z dot c >= R(R-sqrt(2))>0,

because |c-z|<=sqrt(2). Thus the scalar relating c to the full circle
resultant is positive, including when one of the two physical corner
weights is zero. Both proper distances are zero in this case.

For distinct applications and a unique physical circle corner, the
own-frame rectangle is [a-1,a] x [b-1,b], a>=b>=1/2. The complete
normal-line cover excludes concurrence outside that rectangle using
only distinctness, the unshareability of a containing-circle point,
and unit-neighbor width. In particular an outer concurrency leaves
only the circle corner and inner corner; after removing the circle
corner it cannot provide two distinct applications. The other
potential exterior lower-right contact has support at least
R/sqrt(2)>R-1, so a unit neighbor is impossible. The exact polynomial
comparison in C7 Section 4 is nonnegative throughout b<3/2 and does
not use either neighbor's boundary status. The resulting interior
concurrence is on the positive circle ray, and each original
application is c+ell w with ell>=0.

For two physical circle corners, write the actual unit as
[d,d+1] x [-1/2,1/2] and c=tau(d+1,eta), |eta|<=1/2. The same
distinct-contact and width tests exclude tau<d/(d+1). For the
remaining tau<=1 interval c lies in the unit. When tau>1, the
normal-line cover allows two distinct non-circle applications only
if |c_y|<=1/2; every such application is on the inner face or one
of its endpoints. The outer face is excluded by width. The vector
from c to each such inner application points along its outward
normal, so the same proper-distance assertion holds. Both transverse
equalities and a concurrence outside the radial square are retained.

This deliberately does not use C7's additional shallow-inner-face
screen to force the radial concurrence inside: that later step
requires boundary neighbors and is not available here. The new source
uses only the weaker, valid positive/proper conclusion.

## 3. Entire nonparallel C row

Write n=(1,0), let lambda>0 be B's actual transmitted magnitude,
nu>0 the original CD magnitude, and g the actual C-to-D normal.
The complete C force equation is

    F_C=lambda n-nu g.

Properness at its two unchanged applications gives

    P_BC=c-ell0 n, P_CD=c+ell1 g,
    ell0,ell1>=0, c=alpha F_C, alpha>0.

Therefore c_y=q. If q<0, the full force equation gives g_y>0.
The actual CD point and bypass separation then give

    q <= q+ell1 g_y <= max_D y <= b <= q.

All comparisons must be equalities, including ell1=0. The same
point is a maximum-y point of D, but its original D-outward normal
is -g with negative y component. This is impossible even at a
maximum-y vertex: both outward side-axis generators there have
nonnegative y components, as does their closed cone. At a flat
maximum side the same assertion includes its endpoints. Thus the
zero proper-distance case does not escape the contradiction.

For q=0, the force equation instead forces g_y=0, which makes the
two original C pair normals parallel. This contradicts the present
case premise. Hence all nonparallel C cases have q>0.

## 4. Entire parallel C row and original weighted mean

I read the full parallel-load classification N.4 in
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md. Opposite signs cannot occur
here: the normal in the circle-resultant direction would expose an
unshareable circle corner, or the outward radial face whose support
is greater than R-1. Both pair normals must consequently be -n.

N.4 applies to their actual magnitude-weighted support mean. It does
not replace either original application or require them to coincide.
The D-type radial alternative has minimum support R-sqrt(2), whereas
the actual incoming support here is h+1>=1-epsilon>59/60. The
radius inequalities give

    R-sqrt(2)<25/12-7/5=41/60<59/60.

Thus C is the literal radial S unit [d,d+1] x [-1/2,1/2], and
h=epsilon. Write its unchanged CD application (d,z). It belongs to
D, so z<=q. The full original moment equation is

    lambda q+nu z=0.

For q<0 both terms are strictly negative. For q=0 it forces z=0.
This retains the whole original mean interval and its exact zero
endpoint rather than invoking strict properness at a parallel star.

## 5. Complete q=0 physical frames

The actual point (d,0) belongs to D and is its support for the
original DC normal n. Its y coordinate, together with
max_D y<=b<=q=0, forces max_D y=b=0. Thus it simultaneously
maximizes both x and y on D. The two orthogonal inward edges must
lie in the closed Southwest quadrant. Orthogonality forces them to
be its two bounding axes, giving the actual whole boxes

    D=[epsilon,d] x [-1,0],
    B=[epsilon,d] x [0,1].

At the actual AB point (epsilon,0), if A did not own n then both
bodies would meet only at their exposed vertices with B's side-axis
normal. This is excluded by the existing selected strict singleton
convention. Hence A owns n and has its actual frame

    A=[epsilon-1,epsilon] x [a-1,a], 0<=a<=1.

If a=0, AB is again an aligned point-only corner contact carrying
the side-axis normal, so the same initial convention excludes it.
The source correctly retains exactly 0<a<=1; it does not infer a
new strictly interior mean in a positive-length shared contact.

For 0<a<1, AD has a genuine positive-length common side. Its
D-outward normal is -n. The unchanged full D3 horizontal equation
then makes DT parallel to n. Its sign cannot be +n: the actual T
would lie in x>=d, while A lies in x<=epsilon=d-1 and physically
touches T. Therefore DT is -n. Both actual DA and DT applications
have height at most zero; DC has height zero. Their full moment
with strictly positive coefficients forces both heights to be zero.
In particular DT applies at (epsilon,0). No boundary unit T can
contain that point: its distance from a circle corner would exceed
the unit diameter since epsilon<R-sqrt(2). This uses T's physical
boundary status, not a positive circle weight or a T2 equation.

For a=1, AD is the actual singleton (epsilon,0), and its selected
D-outward normal is strictly Northwest. Full D3, with DC East,
forces the DT normal w to have w_y<0. Every maximum-w feature of
the aligned D is on its bottom y=-1, including the entire South
side mean and both vertex sectors. At that same original point
P, T minimizes w. The full unit support-span lemma gives

    max_T(y-P_y)<1,

because w dot e_y<0. Hence max_T y<0, whereas A is wholly in
y>=0. This contradicts the actual AT contact. I rechecked the
support-span proof at a vertex, a side-interior mean and both side
endpoints; its strictness is valid for every nonzero negative
component, with no quantitative lower bound on that component.

These two cases exhaust the full zero-mean endpoint.

## 6. Literal house transfer and exact bounds

In the stated TC.S and TC.D house domains the complete stars are
indeed unloaded B2, loaded C2, unloaded D3 and physical boundary T;
the actual A leaf adds a fourth force that this local theorem never
shortens. The genuine radial leaf gives the claimed near point:
for type S, the actual inward unit segment from its root application
d e contains epsilon e; for type D the inward segment crosses the
origin since 0<R-sqrt(2)<1. Thus A meets D_epsilon. The actual
incoming C support is h+1, and the sharp degree-free contained-unit
support bound gives h+1<=d, hence h<=epsilon. The near point gives
h>=-epsilon. The original bypass provides the remaining actual
chart, with no equation at A or T.

For the endpoint estimates, the following exact positive reserves
were independently reconstructed:

| Comparison | Reserve |
| --- | ---: |
| (25/12)^2-1105/256 | 55/2304 |
| (121/60)^2-1041/256 | 31/57600 |
| 59/60-41/60 | 3/10 |
| 1/2-1/60 | 29/60 |
| 9/4-1105/512 | 47/512 |

The first two give the strict radius and epsilon bounds used above;
the fourth is a weaker sufficient reserve for
epsilon<R-sqrt(2), using R>=sqrt(17)/2>2 and sqrt(2)<3/2.
All exact critical values epsilon=0 and both zero proper distances
remain covered. No sampled angle or optimized pose is a premise.

## 7. Exact current inputs and final acceptance

The seven full prerequisite pins printed in the source were checked
against the current bytes. In particular the conditional properness
uses C7 d50d8ca4 and the chain lemma 0d61292a at the literal scopes
described above, while the support-span/triangle input is ee865704
and the initial point-only selection is eb26f19b.

The new implication q>0 is fully accepted for its exact original
C2/D3 and arbitrary A/T scope. It preserves the physical radial
two-corner case, both original means, the strict singleton endpoint,
and the entire unloaded D3 equation. It supplies a necessary domain
for either stated house leaf type; it does not close the positive-q
remainder, another graph or a completion-capacity problem.

No source correction was requested. No source, normal, force,
physical pose, circle mask, ledger, frozen cover, remote state,
Lean compilation or CI result was changed by this review.
