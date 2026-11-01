# Complete exclusion when all three unloaded-triangle internal applications coincide

Date: November 1, 2026. **Proposed full-domain hand proof at its precise conditional scope; independent review pending.** This is a second proper-feature theorem uncovered in preparing the computer-assisted direct-triangle split. It needs no solver, sample, script, Lean or CI.

## Statement

Retain the same actual nine interior-disjoint unit squares in a disk with \(R^2\le1105/256\), and the same original selected physical force-and-torque certificate. Let three entirely selected-circle-unloaded actual squares A,B,C have **exactly** the original positive triangle edges AB,BC,CA internally and one original positive outside edge at each. The outside terminals can repeat and have arbitrary original degrees, forces, loads, means and physical masks. Assume there is one actual common point \(P\in A\cap B\cap C\) and that **all three ORIGINAL positive internal edge applications equal that very point**. This is stronger than physical common-point incidence: a shared-side original mean need not equal P.

**Theorem.** No such original stress and packing exists in the stated disk. More sharply, if the three core frames are not all parallel modulo quarter turns, these full conditions force

\[
             R^2\ge |P-O|^2+(1+\sqrt2)^2>1105/256.
\]

The parallel-core case is independently excluded by the existing complete parallel-frame three-force triangle theorem, which gives \(R^2>9/2\) on its entire original physical T chart, all side means and two contact-corner endpoints. That existing theorem is imported only for the parallel case.

## Proof for every nonparallel core frame

At the common point P, every core square must contribute an inward quarter-plane sector of angle pi/2. Indeed, if one had P in a side interior, its tangent halfplane plus the other two sectors would exactly fill a full turn, forcing all three frames parallel. Four distinct unit squares through P would likewise have four vertex quadrants tiling the plane and would force parallel frames. Thus P is a genuine vertex of each of the three core squares and **no outside square can contain P**.

Write each original core square in its *own* inward vertex axes as

\[
                   S_i=P+[0,1]u_i+[0,1]v_i.
\]

At most one internal physical pair shares a positive-length side from P. If two did, their shared core square would have both other frames parallel to its own, contrary to the nonparallel hypothesis. Therefore each of the three original core squares is incident to **at least one point-only vertex/vertex internal edge**, whose original selected strict common normal exposes P uniquely.

For either original internal edge from i toward j, because its actual application P maximizes its outward unit normal \(n_{ij}\) on \(S_i\), we have

\[
   n_{ij}\cdot u_i\le0,\qquad n_{ij}\cdot v_i\le0.
\]

For i's point-only edge, the strict singleton selection makes **both** inequalities strict. The two original internal magnitudes are positive, and the complete unloaded translation equation at i says its ONE outside force is their negative sum. Hence the outside unit normal \(e_i\), from i toward that original outside neighbor, has

\[
                   e_i\cdot u_i>0,\qquad e_i\cdot v_i>0.
\]

Its original application \(q_i\) therefore uniquely maximizes e_i on \(S_i\), so it is exactly \(P+u_i+v_i\) (not a chosen mean). Both internal original moments about P vanish because all three internal applications equal P. Complete torque about P therefore forces \(\det(q_i-P,e_i)=0\). Combining this exact equation with the two strict positive components of e_i yields

\[
             e_i=(u_i+v_i)/\sqrt2.
\]

At the unchanged outside neighbor, q_i is a **minimum** support point in direction e_i. The inward-unit-segment fact for a unit square puts \(q_i+e_i\) in that same actual outside square. Thus the original disk contains, for each i,

\[
       w_i=q_i+e_i=P+(1+\sqrt2)e_i.
\]

Summing the three complete unloaded core translations cancels the three internal original forces and gives \(\sum_i z_i e_i=0\), where every outside magnitude \(z_i>0\). Normalize \(\alpha_i=z_i/\sum_j z_j>0\). Then \(\sum_i\alpha_i=1\) and \(\sum_i\alpha_i e_i=0\). Since all three **actual** points w_i belong to the same original disk of radius R,

\[
\begin{aligned}
 R^2&\ge\sum_i\alpha_i|w_i-O|^2\\
 &=\sum_i\alpha_i|P-O+(1+\sqrt2)e_i|^2\\
 &=|P-O|^2+(1+\sqrt2)^2.
\end{aligned}
\]

But \((1+\sqrt2)^2=3+2\sqrt2>5>1105/256\). Contradiction. No outside neighbor was rotated or assumed distinct; no original force or shared-side mean was moved. QED.

## Exact boundary of this conclusion

The result excludes all *point-only common junctions* (where all three pair intersections are the one point P), and any original shared-side variant in which all three positive internal applications happen nevertheless to equal P. It does **not** exclude a shared physical junction where an original side/side pair force acts at some other point along its nondegenerate shared segment. Nor does it cover three distinct pairwise contact applications at noncoincident points. Those full-contact/mean cases remain to be screened by the computer-assisted physical-geometry stage.

The parallel case depends on the existing full parallel-core theorem; the nonparallel proof is self-contained given the original selected strict singleton convention. No whole original coarse/fine case is marked closed; the unrestricted n=9 lower bound and equality remain open.