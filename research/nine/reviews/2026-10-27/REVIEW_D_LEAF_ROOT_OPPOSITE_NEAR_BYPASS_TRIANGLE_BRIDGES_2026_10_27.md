# Independent review: a D root, two boundary neighbors, and a near bypass

Date: October 27, 2026.

Reviewer: triangle-bridges, independently of the source author and root review.

**Verdict: ACCEPTED after complete source and exact original-caller review.**
The reviewed source is
`D_LEAF_ROOT_OPPOSITE_NEAR_BYPASS_EXCLUSION.md`, SHA-256
`1a9c4d2b446d0c9fabbcae96d655f6264545a6ec12a963425b66343917eb2064`.
An acceptance-only header edit does not alter this mathematical review.

I read all five sections of that source, the complete physical
`D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md`, the full separating-axis
argument in `UNIT_BYPASS_NORMAL_CHANNEL.md`, the original genuine D/S
leaf classification in `RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, and the
complete pertinent opposite-root graph/load/type cover in
`FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md`. I also checked the exact
existing fine-family name in `DEEP_GATED_ROADMAP.md`. No gap was found.

## 1. The original domain supplies the shallow D-root chart

The true D leaf has its original radial contact in a relative side
interior of its root. Thus A is exactly

    [-s,r] times [h-1,h],   r=R-sqrt(2), s=1-r, 0<h<1,

with the actual leaf application (r,0), outward normal east, and
zero origin moment. The strict slider is inherited from the common
compatible bridge selection, not imposed at a later contact.

The high-radius bounds used in the source are valid on the whole
declared interval. In particular R>sqrt(17)/2>103/50 and
sqrt(2)<283/200 give r>129/200; r<2/3 gives s>1/3, while
r>5/8 gives s<3/8. Also r^2-s^2=2r-1>1/16. Both horizontal
origin margins therefore exceed epsilon.

An actual point of the distinct C in the closed epsilon disk
cannot lie in int A. The horizontal margins exclude both
horizontal escape directions, so one of the actual vertical
margins is at most epsilon. Vertical reflection gives precisely
0<h<=epsilon, including the equality h=epsilon. No load or
force equation at C is needed for this step.

## 2. The full true A3 equation forces opposite horizontal normals

The shallow-side theorem is genuinely force-free and covers all
actual support owners, arbitrary side means, and the entire
vertex/vertex normal cone. Its hypotheses are satisfied separately
by B and D, because each is a physical boundary unit touching A
and the actual D leaf remains present. It excludes a positive
vertical component of either A-to-neighbor normal.

The unchanged full equation

    alpha e_x+beta n_B+gamma n_D=0,  alpha,beta,gamma>0,

therefore makes both normals horizontal. They cannot both point
east by its horizontal component. At any west application
(-s,y), physical boundary distance gives

    y^2>=r^2-s^2>1/16.

The entire actual height interval has y<=h<1/60, so y<-1/4.
The original west-normal moment is y, strictly negative. Two
west normals would violate A's full zero-origin-moment equation,
since the real leaf moment is zero. Exactly one west and one
east normal remain. This argument retains both original positive
magnitudes and never treats one original force as dispensable.

The resulting half-planes B_x<=-s and D_x>=r are exact physical
support statements. The later proof only uses the actual west
mean P=(-s,y), so neither endpoint nor side-centering convention
is introduced.

## 3. The bypass separation is purely physical

The two actual contacts from C to B,D imply that C's horizontal
projection contains [-s,r], whose length is exactly one. This is
sufficient for the separating-axis calculation; collinearity of
the two A applications and a transmitter equation at A are not
premises of that calculation.

I checked the displayed algebra directly. With C coordinate width
w=c+t, c,t>=0, c^2+t^2=1, its center displacement (u,v) from A
satisfies |u|<=(w-1)/2. A separating C side axis gives

    t|v| >= [w+1-c(w-1)]/2 >= t(w+1)/2,

because

    (1-t)(w+1)-c(w-1)=2c(1-t)>=0.

The zero-t axis is horizontal and cannot separate projections
that overlap in a length-one interval. The other C axis is the
same calculation with c,t exchanged; an A vertical axis gives
the conclusion immediately. Hence the actual vertical projections
are disjoint, including equality and all tilted frames.

The lower alternative would place all of C below h-1<-59/60,
contradicting its actual closed-epsilon-disk point. Therefore C
lies wholly above y=h, possibly with a positive gap. Its real
contact with B supplies max_y(B)>=h; the source does not invent
an A--C contact or any additional positive edge.

## 4. The complete west-neighbor frame cover gives strict clearance

The physical data used here are exactly

    B_x<=-s, (-s,y) in B, h-1<=y<-1/4,
    max_y(B)>=h>0.

If the maximum-x support is a side, B is aligned. Its unchanged
side mean implies z<=y and hence z+1<=y+1<3/4. The real high
contact implies z+1>=h and z>=h-1>-1. Every corner consequently
has |x|<11/8, |y|<1 and squared norm less than 185/64<4.
This includes both endpoints of the original positive-length
side mean interval.

Otherwise the unique maximum-x point is the actual vertex P.
The parametrization

    P+[0,1](-c,t)+[0,1](-t,-c),  c,t>0, c^2+t^2=1,

is the complete tilted frame cover, with no omitted reflection.
Its highest vertex gives y>=h-t. The source's four separate
corner estimates then follow on their full domains:

* P has squared norm below 73/64.
* The upper adjacent vertex has squared norm below 157/64.
* The lower adjacent vertex has squared norm below 249/64<4,
  because its height exceeds h-(c+t)>-sqrt(2).
* The opposite vertex has height strictly between -1 and 3/4
  and horizontal magnitude below 43/24, so squared norm is below
  2425/576<2448/576=17/4.

All inequalities are strict, including every mean endpoint and
every limit in the actual tilted domain. Thus every actual B
corner lies strictly inside the original circle, contradicting
physical boundary contact. The argument is independent of B's
circle mask and all individual zero weights, because it excludes
physical circle contact itself.

## 5. The exact original mixed C4 family is fully covered

The original opposite-root C4 has cycle A--B--C--D--A and genuine
leaves at A,C. The accepted load cover proves B,D loaded: an
unloaded one would be a true normal channel between two genuine
near-origin roots, with width at least one but endpoint separation
at most 2epsilon. Thus B,D are actual physical boundary units.
Both roots retain true positive degree three. Every extra physical
square remains in the same nine-square packing.

The actual graph symmetry exchanging A,C preserves the BD load
set, so the whole original mixed orbit may be labeled with the
D leaf at A and the S leaf at C. At d<=1, A contains O openly
and C contains O closed; physical overlap excludes the whole low
and critical interval. At d>1, C supplies its unchanged point
epsilon e_C and physically touches both B,D, which are exactly
the local theorem's hypotheses. Neither B2 nor D2 is used in
that theorem beyond establishing their physical boundary status.

The source therefore closes exactly the complete existing family

    M6.B4L2.C4.OPPOSITE.LBD.SD.

The D/D overlap is already a separate complete exit. The opposite
S/S family and the full C1.4.b2 parent are correctly not claimed
closed. No positive force, original degree, normal, mean, physical
circle mask, or arbitrary completion unit has been removed.

No Lean compilation, CI, numerical pose or coefficient packet,
remote mutation, or shared-ledger edit was used in this review.
