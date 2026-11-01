# Computer-assisted first: exact force-triangle screen and next certificate/table strategy

November 1, 2026 — n=9 / PR #11. This is **one certified proper-feature reduction**, not a solution of the full nine-square theorem. User has authorized computer-assisted proof as a discovery/certification stage, followed by table extraction. No Lean, Lake, or CI.

## A new certified necessary theorem

Keep the original full physical contact-force-and-torque system on nine independently oriented, interior-disjoint unit squares in a disk with \(R^2\le Q=1105/256\). Let \(K=\{A,B,C\}\) be an entirely circle-*unloaded* original positive three-cycle. Its three internal positive edges are \(AB,BC,CA\); each of the three members has exactly one other original positive edge, to an arbitrary actual outside square. Outside terminals may coincide and have arbitrary other contacts, loads and degrees.

Denote the three original internal force magnitudes by \(a,b,c>0\). Then

\[
\boxed{\min(a,b,c)<\frac{a+b+c}{12}.} \tag{T}
\]

The strong inequality is verified with **exact rational interval arithmetic**, not a floating-point search. It applies across all internal orientations, all original shared-side means (including their endpoints), and all outside degrees and physical zero-weight masks. It does **not** exclude the remaining weak-edge regime or a whole original coarse parent.

### The completely analytic part: the full-cut work budget

For an actual square center \(c_i\), the farthest-corner bound gives
\(|c_i|^2+|c_i|+1/2\le Q\). The rational check

\[
 (91/60)^2+91/60+1/2-Q=31/57600>0
\]

therefore gives \(|c_i|<M=91/60\) for **every** square, not only loaded ones. Write \(h_i(n)\) for actual projection halfwidth. Any original positive pair \(i\to j\) has tight support gap \(n\cdot(c_j-c_i)=h_i(n)+h_j(n)\ge1\).

Let \(I\) be the sum of the magnitudes times actual full support gaps for the three internal original positive edges, and \(C\) the sum of magnitudes of all three original outside cut edges. Set \(W=a+b+c\). Then \(I\ge W\). At any original cut \(i\to t\),

\[
 n\cdot c_i=n\cdot c_t-h_i(n)-h_t(n)<M-1=31/60.
\]

Dot the **three complete** unloaded force equations with their actual centers and add. The internal edges contribute \(-I\), all external edges remain and yield

\[
 W\le I<\frac{31}{60}C,
 \qquad\text{hence}\qquad C>\frac{60}{31}W. \tag{1}
\]

Orient the three internal original edges \(A\to B\to C\to A\) and put \(x=a n_{AB}\), \(y=b n_{BC}\), \(z=c n_{CA}\). The *complete* force equation at each unloaded hub makes the single outside exit magnitude respectively \(|x-z|\), \(|y-x|\), \(|z-y|\). Consequently

\[
 C=|x-y|+|y-z|+|z-x|. \tag{2}
\]

### The exactly certified finite part

The attached no-dependency checker `verify_force_triangle.py` proves:

> For **every** three vectors \(x,y,z\in\mathbb R^2\), if their lengths sum to one and each length is at least \(1/12\), then
> \[
> |x-y|+|y-z|+|z-x|\le60/31. \tag{3}
> \]

For proof coverage, permute the three vector names so \(a\ge b\ge c\), rotate \(x\) onto the positive horizontal axis, and reflect so \(y\) lies in the upper half-plane. Parameterize all unit directions with the two rational half-circle charts

\[
 \sigma\left(\frac{1-t^2}{1+t^2},\frac{2t}{1+t^2}\right),\quad t\in[-1,1],\quad\sigma\in\{-1,+1\}.
\]

The upper half-circle for \(y\) needs the two chart pieces \((\sigma,t)=(+1,[0,1])\) or \((-1,[-1,0])\); \(z\) needs both full semicircles. Thus exactly four **complete** chart roots suffice. Also \(a\in[1/3,5/6]\), \(b\in[1/12,1/2]\), and \(c=1-a-b\) with \(a\ge b\ge c\ge1/12\). The checker discards a box only when these inequalities have **no** solution there.

On every other box it computes enclosing component intervals via rational monotonicity of the chart, encloses all three squared distances with rational arithmetic, then upper-bounds their square roots by the exact integer `isqrt` operation. The rational square-root upper bound \(r/32768\) is constructed to satisfy \(r^2/32768^2\ge q\) **by integer comparison** for each squared-distance upper bound \(q\). If the sum of all three upper bounds is not at most \(60/31\), the box is split at a rational midpoint. The proof succeeds only if *every* final leaf is either mathematically empty or satisfies the exact bound. There is no numerical tolerance, sampling conclusion, or unproved limiting box.

The following is the checker output, using the default \(1/12\) threshold:

| \(y\)-chart sign | \(z\)-chart sign | Tree nodes | Bound-certified leaves | Proven empty leaves | Max depth |
|---:|---:|---:|---:|---:|---:|
| +1 | −1 | 7,661 | 3,351 | 480 | 21 |
| +1 | +1 | 657 | 268 | 61 | 17 |
| −1 | −1 | 118,437 | 45,241 | 13,978 | 25 |
| −1 | +1 | 48,627 | 17,055 | 7,259 | 22 |
| **Total** | | **175,382** | **65,915** | **21,778** | **25** |

The **least** certified gap at a bound-certified leaf is exactly \(29/1,015,808>0\). This is an exhaustive finite computational proof of (3), with a four-row *summary* table. Run:

```bash
python verify_force_triangle.py
```

The command uses Python's standard-library `fractions.Fraction` and `math.isqrt` only. A reviewer can inspect the short arithmetic kernel and independently rerun all 175,382 nodes. Combining (1), (2), and (3) proves (T), by contradiction. Only the final vector lemma is machine-assisted; the transfer to the actual nine-square packing is written above.

## Next: use the certificate to create a SMALL geometric table

The certified weak-edge alternative gives, after relabeling the true triangle, one original edge with \(c/W<1/12\). The other two original forces are not deleted. In the next stage, subdivide only the physical relative-frame/contact charts that survive this restriction. A usable solver must preserve:

1. All three core originals' **complete** translations and moments, and their one outside edge each.
2. Every pair's real contact feature, actual support point and shared-side mean; point-only contacts use one consistent strict common-normal chart.
3. The whole-square containment of the **actual** outside neighbors and the other three actual packing units; repeat-terminal identities must be included.
4. Full original SAT disjunctions for all nine pairwise nonoverlaps; numerical candidates may guide branch selection but do not certify a cell.

A useful next certificate leaf will carry a named contradiction such as: an exact cut-work gap, an outward point beyond the original disk, a violated physical SAT separator, or a certified nonoverlap/region-capacity bound. Verification should use exact rational inequalities with outward enclosures of radicals. Extract a short human table by merging adjacent leaves with the same contradiction and identical original hypotheses; retain the full machine proof for the small genuine exceptions.

Do not try to certify a fixed \(Q-\varepsilon\) and silently infer all \(q<Q\); either work symbolically at \(q\le Q\) on cases with no equality, or establish the exact equality branches separately. The current theorem screens a proper feature at the **closed** upper radius, so it has no such limit gap.

## Status and verification boundary

This force screen has now been independently replayed and reviewed, and replaced by the shorter, stronger [analytic force-perimeter inequality](FORCE_TRIANGLE_ANALYTIC_COMPRESSION_AND_AUDIT_2026_11_01.md). The original checker remains reproducible; its leaf counter certifies an upper bound, not feasibility/nonemptiness within each box. It is **not formally verified in Lean**. The proof checker establishes its arithmetic claim assuming its explicit mathematical chart-cover and interval-bound arguments, printed above. It does not settle the direct unloaded triangle or global n=9 sharpness. Canonical status remains **41/58 coarse**, **2,373/2,513 fine**, and **18/38** nested exterior. No original flags should change because of this proper-feature theorem.
