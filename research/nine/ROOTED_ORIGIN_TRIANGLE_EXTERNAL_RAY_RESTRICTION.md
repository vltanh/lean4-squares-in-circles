# An origin-interior triangle root restricts both other full external rays

Date: October 26, 2026.

**Status: accepted complete local theorem after full root review in `REVIEW_ORIGIN_TRIANGLE_EXTERNAL_RAY_ROOT_2026_10_26.md` and independent review in `REVIEW_ORIGIN_TRIANGLE_EXTERNAL_RAY_GLOBAL_2026_10_26.md`.** No original gate or shared ledger is changed. This is a tool for the original mixed-block chain, not a complete C3.334 closure.

## 1. Actual scope and statement

Let three distinct actual interior-disjoint unit squares A,B,C have all three positive physical triangle edges. Keep every actual application, normal and shared-side mean. At each body let F_A,F_B,F_C be the resultant of its entire external force system, including every actual circle force and every force from any other attached block. Assume each external system has zero origin moment, and keep the full original force and moment equations. Suppose

    O is in the open interior of A.

Then:

1. The triangle's common directed cycle moment is nonzero.
2. If n is the actual outward normal from B toward A, then

       h_B(n)<0,             n.F_B<0.

3. The actual closed B contains no point of the nonpositive external-resultant ray:

       B intersect {-s F_B : s>=0} is empty.

The same statements hold with B and C exchanged. These conclusions use full external aggregates, not forces obtained by deleting an original positive load. No radius or circle-mask assumption is needed.

The three external systems need not be individual radial forces. In the intended mixed-block chain, F_A is the actual intact-petal resultant, F_B is the sum of B's own actual circle resultant G_B and all actual circle resultants in the private terminal four-body branch, and F_C is the original circle resultant of its true degree-two tip. The branch moment identity is obtained by summing that actual branch's origin moments, with every force retained. Identifying F_B with the private branch sum alone requires a separate proof that G_B=0; the local theorem does not supply that clearance.

## 2. The support toward A is strictly negative

Let p be the actual common BA application and n the actual outward normal of B toward A. The unchanged supporting half-planes are

    B subset {x : n.x<=n.p},
    A subset {x : n.x>=n.p}.

Because O is in A's open interior, the second support is strict at O. Consequently

    h_B(n)=n.p<0.                                         (1)

This statement includes side means, endpoints and vertex contacts. In particular it concerns the original support, not a selected alternative line.

## 3. The cycle moment cannot vanish

The complete actual external-resultant theorem
`RADIAL_TRIANGLE_EXTERNAL_RESULTANTS_NONCOLLINEAR.md` gives nonzero, noncollinear F_A,F_B,F_C. Its purely physical parallel-pair fact also says that any parallel cycle pair at a body has the same outward sign. There can be at most one parallel cycle pair: two would make all three edge-force directions collinear, which is impossible for the physical triangle (and would make the external resultants collinear).

Thus at least one of B,C has a nonparallel pair. Suppose the common directed cycle moment were zero, and call that body B after exchanging B,C if necessary. Each of its two actual cycle force lines passes through O, so their genuine concurrence is q_B=O. The physical triangle proper-port theorem gives at the actual BA edge

    p=q_B+a n,                a>=0.

Taking scalar product with n gives h_B(n)=a>=0. This contradicts (1). Hence the actual common cycle moment is nonzero. No positive-concurrence theorem has been used before this nonzero-moment premise is proved.

## 4. Every full external resultant points across the negative support

First suppose B's cycle pair is nonparallel. The accepted nonzero-moment theorem `RADIAL_TRIANGLE_CONCURRENCE.md` applies to the three complete external systems. Its actual concurrence is

    q_B=tau F_B,              tau>0.

The unchanged proper BA port has p=q_B+a n, a>=0. Thus

    tau(n.F_B)=h_B(n)-a<0.

This proves n.F_B<0.

If B's cycle pair is parallel, its two outward normals both equal n. Their positive magnitudes have some sum gamma>0, and the full B force equation is

    F_B+gamma n=0.

Hence n.F_B=-gamma<0 directly. No concurrence is assigned to B in this alternative.

For any s>=0, the point x=-s F_B satisfies n.x>=0. Every B point instead satisfies n.x<=h_B(n)<0. Therefore x cannot belong to B. This proves the complete forbidden-ray statement, including s=0 and the whole parallel case.

## 5. Intended original-graph inheritance and limitations

For a block-tree chain with middle triangle A-B-C, an intact end triangle at A and a terminal rooted block at B, the accepted `ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md` gives exactly O in int A. Sum the true private-body equations separately in each attached branch. Internal pair forces and origin moments cancel at their common actual applications; all original circle atoms have zero origin moment. Add each root's own actual circle resultant to its private-branch sum to obtain its complete external resultant. A is physically clear in the stated packing radius window because it contains O; B's possible G_B remains unless separately excluded. This gives the required full external systems without changing either root degree. The untouched C remains a true loaded degree-two tip, since its two neighbors physically touch.

The theorem does not assert that either B or C contains O, that any concurrence lies in a square, or that a terminal block has a particular pressure sign. It does not transfer the intact-petal pressure to an arbitrary other root. Those are separate geometric obligations. The result is the exact nonzero cycle moment and the forbidden nonpositive ray for each actual full external aggregate.

No normal is reselected, no force is omitted, and no extra physical square moves. No Lean compilation, CI, numerical pose, remote action, or shared-ledger edit is used.
