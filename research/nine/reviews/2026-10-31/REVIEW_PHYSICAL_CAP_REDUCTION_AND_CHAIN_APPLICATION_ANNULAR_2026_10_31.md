# Independent review of the physical cap reduction and unrestricted 4+3 application

October 31, 2026. Reviewer: annular agent.

**Result: Sections 1–2 and 7 of PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md pass the assigned independent hand review.** The positive- and negative-normal scalar bounds are assigned to separate reviewers; this record does not substitute for those checks.

## 1. Physical separation and the sign of the dual support terms

For actual disjoint open square interiors, the Minkowski difference of their centered squares is a convex polygon with edge directions drawn from those two squares. An exterior or boundary point has a violated or tight facet inequality. Thus a separating axis owned by one of the two actual frames exists, including all contact endpoints.

With v_M=-a e-k n and v_B=-b e+k n, adding the two actual disk-support inequalities gives

    -a e.c_M-b e.c_B+k n.(c_B-c_M)
      +h_M(ae+kn)+h_B(be-kn) <=R(L_a+L_b).

The separating gap has the correct nonnegative sign and is at least h_M(n)+h_B(n). Subtracting the two objective halfwidth terms gives precisely the stated P_M and P_B. No normal is assumed to belong to both squares. At R<sqrt(Q), replacing R by sqrt(Q) is strictly increasing because L_a+L_b>0.

## 2. Rectangle reduction

The three vectors we,kn,we+kn are the edge vectors of the triangle with vertices 0,we,-kn, up to signs. In either own-frame coordinate, half the sum of their absolute projections is the range of the three projected vertices. Summing the two frame coordinates therefore gives the bounding-rectangle semiperimeter.

Between changes of the extremal projected triangle vertex, that semiperimeter has the form A cos(theta)+B sin(theta)>0, so its second derivative is strictly negative. It cannot have an interior minimum on such an interval. Its transition endpoints are exactly alignments of a triangle edge with a frame axis. The collinear cases c=±1 are obtained directly and involve no zero denominator because w>k.

Therefore the E/N/D list exhausts the possible frame minima. If the square owns n, its penalty is the actual N expression, rather than an unrestricted minimum. This justifies exactly the five owner/minimum combinations printed in (8).

## 3. Application to arbitrary physical chains

For a projection-disjoint four-chain, telescoping the three ordered interval gaps gives endpoint separation minus endpoint halfwidths at least the sum of the two interior projection widths, hence at least two. The analogous three-chain quantity is at least one.

The endpoint pairs in the two cap applications are distinct actual squares because the two chains partition seven squares. Their physical nonoverlap supplies the sole pair premise of the new cap theorem. Applying the cap in e and then in -e produces exactly

    a*(four-chain endpoint gap)+b*(three-chain endpoint gap)<=2T.

The lower bound is 2a+b=2T. Thus every inequality is equality at R<=sqrt(Q), and strict subcritical radius is impossible. No perpendicular separation assumption is inserted.

At equality, the two cap theorems align all four chain endpoints. The intermediate widths are exactly one, forcing those three squares to share the same unoriented axis pair. Their perpendicular offsets remain subject to physical containment and nonoverlap; the manuscript correctly does not assert that they coincide or are rigid.

## 4. Extraction boundary and exact negative control

The new terminal does not automatically supply two chains. In particular a genuine four-square force channel plus three completing units on one side of its force line need not supply a parallel three-chain.

An exact negative control is the aligned horizontal channel with centers

    (-3/2,0), (-1/2,-1/2), (1/2,-1/2), (3/2,0),

and contact applications (-1,0),(0,0),(1,0). Equal horizontal forces balance both internal units, with zero moment. The three upper squares centered

    (-1/2,1/2), (1/2,1/2), (0,3/2)

have disjoint open interiors, fit together with that channel in squared radius 17/4, and form a T rather than a horizontal projection chain. A further lower square at (0,-3/2) makes the standard eight-square cross. All pairwise nonoverlap is immediate from a unit coordinate separation; each outer unit has farthest corner norm squared 17/4.

Therefore the useful whole-channel extraction target is a joint completion dichotomy: either a side triple produces the new 4+3 terminal, or its non-chain geometry forces the opposite-side capacity down to one. This review does not prove that dichotomy. The existing true-channel barrier and the completed common-coordinate theorem do not fill the arbitrary-oblique antichain gap.

No mathematical scripts, numerical sampling, Lean, CI, or GitHub mutation were used in this review.

