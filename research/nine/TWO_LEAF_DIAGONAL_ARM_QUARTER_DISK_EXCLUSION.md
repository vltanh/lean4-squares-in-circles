# A genuine S leaf cannot have an unloaded diagonal neighbor

Date: October 27, 2026.

**Status: complete hand proof; full root and separate independent source
and direct-dependency reviews accepted.**
Work in the unchanged nine-square packing and closed radius window

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1.

All nine original independently oriented unit squares remain, with disjoint
open interiors and physical containment in the same centered circle.
The theorem permits arbitrary positive degree and arbitrary additional
positive forces at the far endpoint of the actual two-edge arm.

## 1. Exact hypotheses and geometric conclusion

Let L--U--A be two original positive edges. Assume L is a genuine
degree-one S leaf and U has true positive degree two, with no positive
circle load. Its actual two forces therefore transmit in one common
normal direction; suppose its reserve is sqrt(2), the diagonal case.
No equation at A is restricted and no positive force at U is removed
to obtain this premise.

Rotate the genuine S-leaf direction to a unit vector e. The actual leaf
classification gives

    L=[d,d+1]e + [-1/2,1/2]Je,
    p_(U,L)=d e,

and the U-to-L normal is e. In particular the radial application is the
original weighted mean of the actual leaf contact, fixed by L's genuine
force and moment equations. It is not chosen for convenience.

Force balance at the true unloaded degree-two U makes the other contact
normal -e with the same magnitude. Its true torque says the two
applications differ in the direction e. The complete transmitter
classification in PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, Lemma N.1,
then says that reserve sqrt(2) is precisely diagonal transmission.

Thus e is a diagonal direction of the actual U, p_(U,L)=d e is its
unique outer support vertex, and the opposite vertex is
(d-sqrt(2))e. The actual U is fixed exactly:

    c_U=(d-1/sqrt(2))e,
    U=c_U+[-1/2,1/2]u+[-1/2,1/2]v,
    e=(u+v)/sqrt(2),       u,v orthonormal.              (1)

Changing the signs of the square's actual axes, if necessary, gives the
last identity. There is no transverse slider in a diagonal transmitter:
both relevant supports are unique vertices. The entire physical leaf,
transmitter and far endpoint A remain unchanged.

## 2. The actual transmitter contains the quarter-disk strictly

In the true own-axis coordinates u,v, equation (1) gives

    c_U.u = c_U.v = d/sqrt(2)-1/2.                      (2)

The original full-window estimates are

    9/10<d<61/60.

For completeness, d>9/10 follows by squaring
sqrt((79/40)^2-1/4)>19/10. The upper bound follows by squaring
sqrt(1105/256-1/4)<121/60; the exact squared reserve is
31/57600>0.

Both entries in (2) lie strictly between zero and 1/4. The lower
comparison follows from (9/10)^2>1/2. For the upper comparison,

    (61/60)^2 < 9/8=(3sqrt(2)/4)^2,
    9/8-(61/60)^2 = 329/3600>0,

so d<3sqrt(2)/4 and hence d/sqrt(2)-1/2<1/4.
Every true side of U is consequently at distance strictly greater than
1/4 from O. Equivalently,

    D_(1/4) is contained in int(U).                    (3)

This strict inclusion covers both radius endpoints, d=1, every original
circle-corner weight and every contact mean. It uses no position,
orientation, circle mask or force equation at A.

## 3. The unchanged eight other physical units give the contradiction

The force-free central-disk obstruction
CHORDED_HEXAGON_QUARTER_DISK_COMPLETION_OBSTRUCTION.md, Theorem 2,
says that no actual unit in a nine-square packing inside
D_(sqrt(1105)/16) can contain the closed quarter-disk. Equation (3)
contradicts it directly.

Only the strict version of its input is needed here. To make the
completion accounting explicit, (3) gives a larger concentric disk
D_h in int(U) for some h>1/4. Each of the other eight actual squares
is disjoint from that open disk, including its own boundary; otherwise
its interior would overlap int(U). Therefore each has distance from
O at least h>1/4.

GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md, Section 1, applies to each such
physical square at its own orientation. Its nearest point supplies a
unit support direction at height at least h. Its open interior
therefore occupies an arc of angular length strictly greater than pi/4
on the same radius-5/4 circle. The eight open interiors are pairwise
disjoint, so these eight arcs are pairwise disjoint. Their total
length would exceed 2pi, impossible.

This uses every one of the eight original other squares, whether
positively stressed, physically boundary, or an arbitrary completion
unit. It does not call an isolated-core exclusion.

**Theorem.** No genuine S leaf can have a true unloaded degree-two
diagonal transmitter as its neighbor in the stated nine-square domain.

## 4. Four complete original unchecked families close at once

The full six-body attachment cover in
FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md assigns a genuine arm
A--U--L to each of the following four original families. In every row,
L is S and U is its true unloaded degree-two diagonal transmitter.
Thus Sections 1--3 exclude their entire original domains:

| Original gate | Original block loads | Preserved other roles |
| --- | --- | --- |
| M6.B4L2.C4.CHAIN.LBC.S_DIAGONAL | Adjacent loads B,C, including reflected C,D | True A3; the actual second unloaded channel and all three extras |
| M6.B4L2.C4.CHAIN.LBD.S_DIAGONAL | Opposite loads B,D | True A3 and true middle C2; all original widths and three extras |
| M6.B4L2.C4.CHAIN.LBCD.S_DIAGONAL | All three nonroot block vertices loaded | True A3/B2/C2/D2 and three extras |
| M6.B4L2.DIAMOND.CHAIN_HUB.LKBC.S_DIAGONAL | Other hub K and both page tips B,C loaded | True H4/K3/B2/C2 and three extras |

The original S/side and D/side arms remain separate alternatives.
Their actual U need not satisfy (3), so no claim about them follows
by deleting or replacing a force. The entire C4-arm and diamond-hub-arm
parents remain open until those siblings close.

The same proof applies in every larger original positive graph that
has the displayed genuine S leaf and true unloaded diagonal neighbor.
This statement introduces no new fine ID and does not close an
uncovered larger coarse parent. It needs no new generic normal
selection, secondary minimizer, scalar certificate, numerical sample,
Lean compilation or CI.

