# Root review: analytic force screen and executable full physical model

November 1, 2026. Input branch head ad00eaa16a27e5e1000d1a9dc7be0c4421c54b91. The source constructor was a separate agent; this review reconstructs its mathematical equations and executed checks. No Lean, Lake or CI.

## Analytic force screen: accepted

For x=au,y=bv,z=cw with unit u,v,w, W=a+b+c and m=min(a,b,c), decompose x-y=m(u-v)+(a-m)u-(b-m)v and apply the triangle inequality. Summing all three pair distances yields the common-unit perimeter term plus 2(W-3m). Cauchy and the exact identity sum|u-v|^2=9-|u+v+w|^2<=9 give that perimeter at most 3sqrt(3). Hence

    |x-y|+|y-z|+|z-x| <= 2W-(6-3sqrt(3))m.

Every coefficient a-m is nonnegative and no direction restriction is needed. The original center bound |c_i|<91/60 follows from the actual four-corner inequality |c_i|^2+|c_i|+1/2<=1105/256 and the positive rational reserve 31/57600. Each full cut-edge work term is strictly below31/60 times its magnitude, while the sum of the three internal support gaps weighted by their original magnitudes is at leastW. The full unloaded center-work identity therefore gives C>(60/31)W. No original cut or torque premise is replaced.

Combining these two inequalities and rationalizing the positive denominator gives

    m/W < (4+2sqrt(3))/93 < 1/12.

The last comparison is equivalent to sqrt(3)<15/8 and follows by positive squaring. The older all-lengths-at-least1/12 screen also follows directly from C/W<=3/2+sqrt(3)/4<60/31. The source's independent replay matched all four exact interval roots. Its wording correction is valid: a bound-certified box need not contain a feasible vector configuration, so nonemptiness is not certified by that leaf.

The analytic theorem is accepted at the full stated vector and original three-port scope. It is a necessary weak-edge bound, not a complete triangle or global packing exclusion.

## Full physical model: accepted as a necessary constraint encoding

Read the complete emitter and its companion coverage document. Reconstructed the following interfaces:

* Every frame satisfies u dot u=1, with v=Ju, and all four actual corners are constrained by0<=q<=Q. The common rotation gauge u_0=(1,0) preserves every original pose, contact and equation by rotating them together.
* Each of the36 unordered pairs has its actual four-axis SAT disjunction, including boundary equality and pairs or entire bodies with zero stress.
* A positive pair uses one shared actual application p in both squares, a unit normal, and simultaneous max/min support equalities. These give the true tight support gap.
* The vertex/vertex branch strictly exposes both corners. The two vertex/side branches require actual side-interior membership. The side/side branch requires a positive true overlap and represents every original mean by eta in[0,1], including endpoints. The tangent intervals of both unit sides have halfwidth1/2, so their max/min intersection formulas are correct.
* Pair signs match the original constraint-gradient convention. The circle terms2lambda*p and both moment terms dot(force,J(application-center)) have the correct determinant sign. All nine full force and torque balances remain.
* Normalization sum lambda=1 and circle complementarity retain individual zero corner coefficients and loaded/unloaded distinctions. Each root gives exactly the positive triangle and one outside positive pair per hub; all other hub-exterior forces are explicitly zero, while every exterior-exterior pair remains available.
* The five outside identity partitions AAA,AAB,ABA,ABB,ABC exhaust all repetitions by relabeling only the six actual exterior units. The optional algebraic screen keeps sqrt(3) positive and all internal forces strictly positive.

Executed from the repository root:

    python research/nine/computer_assisted/emit_full_triangle_system.py --self-check
    python research/nine/computer_assisted/emit_full_triangle_system.py --all-cases /tmp/nine_triangle_root_model --weak-screen

The exact rational self-check passed. The known oblique equality packing satisfies the full base constraints. A changed original shared-side mean fails exactly the two affected torques. Overlap of two unstressed squares fails SAT. A strict rational singleton normal is accepted and its boundary normal rejected. All five screened roots were emitted.

The base has 289 real variables,108 definitions and 257 assertions; a screened triangle root has 290 variables and 293 assertions. No solver was run, and emission is not a proof of infeasibility. The model deliberately omits later planarity/sparsity/matched-normal/generic-avoidance restrictions. This enlarges its solution set and preserves forward coverage of every selected physical certificate; it does not certify that an arbitrary solution has the project's entire common-selected-certificate provenance.

At that explicit boundary, the model and its coverage argument are accepted. CA1's physical encoding exists; exhaustive exact solving, small-table extraction for the remaining contact families, and original-parent joins remain open.
