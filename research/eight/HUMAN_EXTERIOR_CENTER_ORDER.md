# Uniform angular order for all exterior square centers

**Theorem.** In any unit-square packing in a disk of radius at most two, if two square centers p,q have norms at least 1/2, their smaller angular separation is greater than pi/8. In an eight-square packing below the analytic central-square ceiling, this applies to the seven exterior squares. No angular sector of width pi/4 contains three exterior centers. Their labeled cyclic order cannot change along a continuous packing deformation.

**Hand proof.** The greatest squared vertex norm of a square with center p and orthonormal frame e,f is
|p|^2+1/2+|p dot e|+|p dot f| >= |p|^2+|p|+1/2.
Thus r=|p| and s=|q| lie in [1/2,M] with M=(sqrt(15)-1)/2 <36/25. The last inequality follows by squaring sqrt(15)<97/25.

The open inscribed disks of the squares have radius 1/2 and are disjoint. Thus |p-q|>=1. If delta denotes their smaller angular separation,
cos(delta)<=(r^2+s^2-1)/(2rs)=F(r,s).

At fixed s, the derivative of F in r is (r^2+1-s^2)/(2r^2 s). It is positive throughout or changes sign exactly once from negative to positive. Hence the maximum on r in [1/2,M] is attained at an endpoint. By symmetry the global maximum is at one of four rectangle corners. Their values are -1, M-3/(4M), and 1-1/(2M^2). The last two are increasing in M, so
F(r,s)<max(36/25-75/144,1-625/2592)=3309/3600<23/25.

But cos(pi/8)^2=(2+sqrt(2))/4>17/20>(23/25)^2, using sqrt(2)>7/5 and 17*625>20*529. Cosine decreases on [0,pi], hence delta>pi/8.

Three center rays in an angular sector of width pi/4 would have two intervening gaps each greater than pi/8. An exterior square has center norm greater than 1/2, since otherwise its inscribed disk would contain zero, impossible when a different central square contains zero in its open interior. Along a continuous labeled deformation these rays cannot exchange cyclic order without coinciding; the central label stays fixed by the analytic central-square theorem and its compactness corollary.

**Limitation.** The theorem separates center directions, not square shadows. It does not imply that an actual contact joins consecutive exterior centers or the five-corner inequalities. The rational counterexample in HUMAN_OUTER_ANGLE_COUNTEREXAMPLE.md shows why the stronger pi/4 claim even for outer centers is false.
