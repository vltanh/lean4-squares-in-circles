# Independent review: complete common-junction unloaded triangle exclusion

Date: November 1, 2026. Reviewer: `vector_analytic`, a noncontributor to the manuscript's derivation. Source: [COMPLETE_COMMON_JUNCTION_UNLOADED_TRIANGLE_EXCLUSION_2026_11_01.md](../../COMPLETE_COMMON_JUNCTION_UNLOADED_TRIANGLE_EXCLUSION_2026_11_01.md). Reviewed source SHA256: `ca7e5db0dc7842954545d2405c8e4fe3a00ec6925cd08b2f1dd19f506edd7cf5`.

**Verdict: ACCEPT at the manuscript's complete conditional physical scope.** The new shared-side argument is correct for every original application mean, including both endpoints, and proves the stronger strict bound `R² > |P−O|²+5` in that nonparallel branch. No numerical approximation, external proof script, Lean, or CI was used in this review. This is an independent mathematical review, not formal verification.

## Reconstruction and coverage

1. At a common physical point P, disjoint interior tangent sectors have total angle at most one turn. A side-interior sector forces the other two sectors to be quadrants tiling the complementary halfplane; their frames are parallel. Thus a nonparallel junction uses three vertices. If two pairs shared positive segments, the two corresponding pairs of frames would be parallel, forcing all three frames parallel. Consequently the all-point branch and exactly-one-shared-segment branch exhaust the nonparallel case.

2. In the one-segment branch the two unit squares really can be written `A=[0,1]×[0,1]`, `B=[0,1]×[−1,0]`: P is an endpoint of both equal-length shared sides, so their common segment has length one. The third vertex quadrant lies in the complementary left halfplane. A boundary ray on its vertical boundary would make the third frame parallel as well, so the nonparallel branch has two strictly negative horizontal inward components. Its inward diagonal e_C therefore satisfies `e_C,x<0` and `|e_C,y|<−e_C,x`.

3. The retained strict common-normal convention at AC and BC exposes P uniquely on both squares of each pair. Full unloaded translation therefore forces the outside normals at A and B into the strict northeast and southeast quadrants respectively, and forces their unchanged applications to `(1,1)` and `(1,−1)`. At C, both internal applications are P, so full torque forces its sole outside normal onto the inward diagonal. These are consequences of the original certificate, not choices of replacement normals or means.

4. With the arbitrary original AB application `(s,0)`, `0≤s≤1`, and force `t(0,−1)`, the exact torque equations are `z_A(b−a)=st` and `z_B(d−c)=st`. The signs are correct. They imply `b≥a` and `d≥c` uniformly, including s=0 and s=1. This is the step absent from the earlier equal-application lemma, and it is sufficient for the entire shared-side branch.

5. The actual-unit-step lemma is valid for every outside square frame and support mean: in each own coordinate a unit normal moves a minimizing support coordinate inward by a number of absolute value at most one. Thus all three displayed w-points belong to their unchanged physical outside squares. Repeated outside terminal identities do not affect this reasoning.

6. Writing the points as `w_A=(x_A,y_A)`, `w_B=(x_B,−y_B)`, `w_C=(−x_C,y_C)` gives `y_A≥x_A>0`, `y_B≥x_B>0`, `x_C>|y_C|`. The source's denominator `D=x_A y_B+x_B y_A` is positive. Its two numerators are strictly positive, and direct expansion verifies both coordinates of `lambda_A w_A+lambda_B w_B+w_C=0`. The lambdas are auxiliary convex weights, so there is no requirement that they equal the original force magnitudes.

7. Each actual outside point has squared distance strictly greater than 5 from P: for the two axis-frame points this is `3+2(a+b)>5`, using strict positivity and unit length; the third has squared distance `3+2sqrt(2)>5`. The positive convex cancellation makes the cross term vanish after translation to the actual disk center O. Thus the disk-radius inequality gives `R²>|P−O|²+5`. No favorable disk-center placement was assumed.

8. The all-point argument independently reconstructs the previous diagonal exit result and gives `R²≥|P−O|²+3+2sqrt(2)`. The parallel branch is explicitly imported at its previously reviewed whole-feature scope; this new manuscript does not need a stronger parallel result. Together the three source table rows cover the entire actual common-junction feature.

## Boundary of this acceptance

The conclusion is conditional on the unchanged selected strict normal convention and the three genuinely unloaded full-degree-three stars stated in the source. It covers all positive internal force ratios, arbitrary original shared-side means and endpoints, arbitrary repeated outside neighbors, and their untouched loads and other contacts. It does not replace the still-open global compatibility audit for selecting that certificate.

The distinct-contact branch remains open. Without a common physical point, no two original pair applications can coincide, since such a coincidence would itself belong to all three squares. The canonical original coverage consequently stays 41/58 coarse parents, 2,373/2,513 fine flags and 18/38 six-body exterior rows until a complete original caller is joined. The source makes precisely this limitation.
