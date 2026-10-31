# The three-load triangle-attached C4 cannot have a physical radial middle load

**Status: complete whole-domain hand assembly; root and separate independent full source, owner/radius and prerequisite audits passed.**

Work throughout
\[
79/40\le R\le\sqrt{1105}/16
\]
with the common physical certificate selected before extracting its multipliers. The entire positive component has edges
\[
HA,\ AB,\ BC,\ CH,\ HX,\ XY,\ YH.
\]
H retains its true positive degree four and its original zero circle load in the ABC block-load orbit. A,B,C,X,Y have true positive pair degree two and positive total circle loads. All nine physical squares, all three completion squares, every individual nonnegative circle weight, every actual normal and every original shared-side mean remain.

**Theorem.** B cannot have two physical circle corners. This excludes the entire radial-middle ABC subfamily over the whole radius interval. In the negative-endpoint mask notation (B,A,C), it closes both SUS and SUU. It does not close the remaining unique-middle UUS or UUU families.

Here U and S denote the actual one-corner and two-corner physical masks. A physically two-corner body remains S when one original corner weight is zero.

## 1. The actual petal and boundary-path cone select a negative unique endpoint

Keep the actual circle resultants \(F_A,F_B,F_C,F_X,F_Y\). The complete intact-triangle pressure theorem gives
\[
c_H\cdot(F_X+F_Y)>0
\]
with H's other actual neighbors present. Summing all genuine force equations of the exact component gives
\[
F_A+F_B+F_C=-(F_X+F_Y).
\tag{1}
\]
There is no replacement load or deleted force at H.

BOUNDARY_THREE_PATH_RESULTANT_CONE.md, Sections1--2 and its complete ABC application in Section4, applies to the physical boundary path A--B--C. It gives positive coefficients \(\lambda,\mu\) such that
\[
F_B=\lambda F_A+\mu F_C.
\]
Consequently (1) implies
\[
(1+\lambda)c_H\cdot F_A+(1+\mu)c_H\cdot F_C<0.
\tag{2}
\]
At least one actual endpoint has negative projection.

RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md makes the projection at c_H of each physical circle corner of a radial neighbor strictly positive. Its statement includes every individual zero-weight endpoint. Thus a negative endpoint is physically unique. Exchange A,C if needed, using only the root-preserving reflection of the same graph, and label that actual endpoint A. Its positive unique-circle load then gives
\[
c_H\cdot z_A<0.
\tag{3}
\]

This is a relabeling of original bodies, not a motion or a new load selection. If both endpoints are physically radial, (2) is already impossible. If only one is unique, it must be the negative one. If both are unique, either genuinely negative endpoint may be named A.

The negative-contact theorem also makes H physically circle-clear. Indeed, if H touched the circle, its center would satisfy \(|c_H|\ge R-1/\sqrt2\). An actual HA contact gives \(|c_H-z_A|\le3/\sqrt2\), so
\[
c_H\cdot z_A\ge R^2-R/\sqrt2-2>0,
\]
contrary to (3). This determines a physical mask; it removes no square or force.

Assume henceforth that B is physically radial. The only masks remaining after (3), in order(B,A,C), are SUS and SUU.

## 2. The parallel-root domain is already completely excluded

TRIANGLE_C4_THREE_LOAD_PARALLEL_EXCLUSION.md applies to precisely the actual H4, loaded A/B/C and intact loaded HXY petal now present. It covers both opposite and equal parallel root normals, every physical B mask, all endpoint alignments and every original shared mean.

Thus the actual H-to-A and H-to-C normals are nonparallel in any purported remaining representative. This invocation does not extend the parallel theorem to a different root degree or an attachment whose pressure has not been proved.

## 3. Every A-owned HA, including a shared HA, is impossible

If HA is genuinely shared, its actual normal is an A side axis. If HA is an A-owned singleton, it has the same owner condition. The all-radius theorem
NEGATIVE_UNIQUE_ENDPOINT_OWNED_RADIAL_MIDDLE_EXCLUSION.md excludes both alternatives for every physical radial B.

Its feature input is the complete strict northwest AB normal at the unchanged A vertex \((a-1,b)\), with positive support and no radial-B side-axis owner. Therefore that point would have to be a non-circle vertex of B. Its squared radius is \(R^2-2a+1\), whereas every non-circle radial-B vertex has squared radius \(R^2-2d-1\), where \(d=\sqrt{R^2-1/4}-1\). Physical uniqueness gives \(b>1/2\), hence \(a<d+1\), so the former radius is strictly larger. This is the physical contradiction for the whole owner branch.

Every original HA shared mean is retained. The argument uses no degree reduction at B or H.

## 4. Every genuinely free HA is impossible

NEGATIVE_ENDPOINT_FREE_SHARED_RADIAL_MODULE.md applies with A and B's true degree-two equations and positive total circle loads. It gives the complete pinned module
\[
A=[N-1,N]\times[1/2,3/2],\quad
B=[d,d+1]\times[-1/2,1/2],
\]
\[
H\cap A=(N-1,1/2),\quad B\cap C=(d,-1/2),
\qquad N=\sqrt{R^2-9/4}.
\tag{4}
\]
AB is genuinely shared with its original mean, and both original B corner weights are forced positive by the actual equations.

If C is radial, FREE_NEGATIVE_C4_RADIAL_FAR_ENDPOINT_EXCLUSION.md excludes the full physical return. This is the entire free-HA SUS branch, retaining either individual C weight endpoint.

If C is unique, the complete free-HA return partition is:
\[
\begin{array}{c|c}
\text{actual HC feature}&\text{whole-domain exclusion}\\ \hline
\text{genuinely shared}&
\text{FREE_NEGATIVE_C4_SHARED_RETURN_EXCLUSION.md}\\
\text{C-owned singleton}&
\text{FREE_NEGATIVE_C4_FAR_TIP_OWNED_RETURN_EXCLUSION.md}\\
\text{H-owned singleton}&
\text{FREE_NEGATIVE_C4_H_OWNED_RETURN_EXCLUSION.md}.
\end{array}
\]
After the shared case is excluded, C's two applications are distinct fixed physical points. The coincident radial-D exception is impossible at \(|P|>d>91/100\). The compatible preselection therefore removes free BC/HC, and BC is C-owned because its actual two positive world components are not B axes. This justifies the two singleton rows exhaustively; no normal is changed after extraction.

Thus every free-HA SUU representative is excluded too. No chosen AB mean is substituted for its original one.

## 5. Every H-owned singleton HA is impossible

NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md covers every actual AB support feature and H-side offset in this owner branch. It excludes all A-owned/shared AB features over the whole radius window and gives the full remaining B-owned tangential chart.

For \(R^2\ge17/4\), its complete high-radius pressure theorem excludes the entire chart. This includes the exact joining radius \(R^2=17/4\).

For \(R^2<17/4\), B's true degree-two force and torque equations fix BC at B's other inner vertex and retain its full original individual-weight interval. If C is radial, NEGATIVE_H_OWNED_RADIAL_MIDDLE_RADIAL_RETURN_EXCLUSION.md proves strict physical H/C separation over every original H-side offset. This excludes the entire low-radius H-owned-HA SUS branch.

If C is unique, use NEGATIVE_H_OWNED_RADIAL_MIDDLE_UNIQUE_RETURN_DOMAIN.md. Its complete physical owner partition is:
\[
\begin{array}{c|c}
\text{actual HC feature}&\text{retained BC alternatives}\\ \hline
\text{genuinely shared}&\text{C-owned or genuinely free BC}\\
\text{singleton}&\text{C-owned BC; HC C-owned or H-owned}.
\end{array}
\tag{5}
\]
The shared case keeps its original mean; it is never put under a false fixed-point selection. The singleton case follows from the same distinct-application selection and the strict radial-D norm exclusion at P.

NEGATIVE_H_OWNED_RADIAL_MIDDLE_UNIQUE_RETURN_OWNER_EXCLUSION.md excludes the complete shared-HC domain, including its free-BC subbranch, and the complete C-owned singleton domain. Its whole pressure, derivative, physical-corner and diameter arguments retain all original means and H offsets.

NEGATIVE_H_OWNED_RADIAL_MIDDLE_H_OWNED_RETURN_EXCLUSION.md excludes the remaining H-owned singleton in the nonparallel domain of Section2. Its true C-force positivity forces \(q/p>8\), while the unchanged full upper B-weight endpoint forces \(q/p<54/7\). The opposite C vertex is already too far from the actual HA point. Q remains an H-side point, and every original H-side offset is retained.

This closes the full low-radius H-owned-HA SUU branch. The high/low proofs join without a missing radius or an individual-weight endpoint.

## 6. Complete owner and physical-mask assembly

Every actual HA intersection has positive length or is a singleton. A shared interval is A-owned. Under the existing strict point-normal convention, every singleton has an A side-axis owner, an H side-axis owner, or a genuinely free normal. Sections3--5 therefore exhaust all HA features for both physical C masks.

Every row has a complete continuous-domain contradiction. Hence both negative-endpoint masks SUS and SUU are impossible. By the actual negative-endpoint selection in Section1, this excludes every radial-middle B in the entire ABC block-load orbit, including configurations initially labeled with the negative endpoint at C.

The remaining ABC mask representatives have physically unique B and are UUS or UUU in the same negative-endpoint labeling. Their separate owner and radius obligations remain; this theorem does not close the ABC parent.

This assembly is not transferred to a diamond with a degree-three middle K. The free pinned module and the opposite-inner-vertex/weight interval used in Section5 require B's actual degree two. A geometric endpoint-force-cone statement may apply at higher degree, but it does not remove the additional middle force or authorize those two-force equations.

H keeps all four original forces and its intact HXY petal; every completion square and physical zero-weight contact remains. The contradiction is in the actual core and needs no invented completion capacity. No new normal, motion, sampled angle box, Lean compilation or CI is used.
