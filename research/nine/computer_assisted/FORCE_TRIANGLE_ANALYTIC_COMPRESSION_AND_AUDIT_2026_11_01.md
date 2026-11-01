# Analytic compression and independent audit of the force-triangle screen

November 1, 2026 — n=9 / PR #11.

**Result.** The exact interval screen from
[`FORCE_TRIANGLE_EXACT_INTERVAL_SCREEN_2026_11_01.md`](FORCE_TRIANGLE_EXACT_INTERVAL_SCREEN_2026_11_01.md)
has a short analytic proof. The proof below replaces all 175,382 interval-tree
nodes for that vector lemma, and slightly strengthens the resulting necessary
weak-edge restriction. This is still a proper-feature reduction: the complete
unloaded direct triangle and the unrestricted nine-square theorem remain open.

The source checker was independently inspected and replayed at PR head
`ad00eaa16a27e5e1000d1a9dc7be0c4421c54b91`. Its four root counts and least margin
were reproduced exactly. No Lean, Lake, or CI was used. The analytic argument
below was separately checked by the integrating reviewer.

## 1. A universal planar vector inequality

Let \(x,y,z\) be three nonzero vectors, write

\[
 x=a u,\qquad y=b v,\qquad z=c w,
 \qquad |u|=|v|=|w|=1,
\]

and set \(W=a+b+c\), \(m=\min(a,b,c)\). Then

\[
\boxed{
 |x-y|+|y-z|+|z-x|
 \le 2W-(6-3\sqrt3)m.
} \tag{A}
\]

**Proof.** Decompose

\[
 x-y=m(u-v)+(a-m)u-(b-m)v.
\]

The triangle inequality and \(a-m,b-m\ge0\) give

\[
 |x-y|\le m|u-v|+(a-m)+(b-m).
\]

Summing the three analogous inequalities yields

\[
 |x-y|+|y-z|+|z-x|
 \le m\bigl(|u-v|+|v-w|+|w-u|\bigr)+2(W-3m).
\]

For the three unit vectors,

\[
 |u-v|^2+|v-w|^2+|w-u|^2
 =9-|u+v+w|^2\le9.
\]

Cauchy–Schwarz therefore implies

\[
 |u-v|+|v-w|+|w-u|\le3\sqrt3.
\]

Substitution proves (A). The same proof works in any real inner-product space;
no direction chart, genericity, angle separation, force ordering, or physical
contact classification is needed. Zero vectors can also be included by setting
\(m=0\), in which case (A) is the ordinary perimeter bound \(P\le2W\).

## 2. The previous machine-certified threshold follows immediately

If \(m\ge W/12\), then \(6-3\sqrt3>0\) and (A) imply

\[
 \begin{aligned}
 |x-y|+|y-z|+|z-x|
 &\le\left(2-\frac{6-3\sqrt3}{12}\right)W\\
 &=\left(\frac32+\frac{\sqrt3}{4}\right)W
 <\frac{60}{31}W.
 \end{aligned} \tag{B}
\]

The strict numerical comparison is exact: it is equivalent to
\(\sqrt3<54/31\), and both sides are positive with

\[
 3\cdot31^2=2883<2916=54^2.
\]

Thus the vector inequality previously checked by the rational interval program
is now an analytic consequence of two triangle inequalities, the displayed
norm identity, and Cauchy–Schwarz. The four-root table remains a reproducible
independent computational check, but is no longer necessary for this theorem.

## 3. Transfer to the full physical three-cut triangle

Keep all hypotheses of the original screen. Nine actual, independently oriented,
interior-disjoint unit squares lie in a disk of squared radius at most
\(Q=1105/256\). A connected completely circle-unloaded three-square module
\(K=\{A,B,C\}\) has the three original positive internal edges \(AB,BC,CA\),
and exactly one other original positive edge at each of its three members.
Each such cut edge has its actual outside square, full support gap, original
force, and original application-point data. Outside terminals may coincide.

For every actual square center \(c_i\), the farthest-corner bound gives

\[
 |c_i|^2+|c_i|+\frac12\le Q.
\]

The function \(r^2+r+1/2\) increases for \(r\ge0\), and

\[
 \left(\frac{91}{60}\right)^2+\frac{91}{60}
 +\frac12-Q=\frac{31}{57600}>0.
\]

Consequently every actual center satisfies \(|c_i|<M=91/60\).
For an original positive cut edge from an inside member \(i\) to an outside
square \(t\), let \(n\) be the outward unit normal from \(i\) toward \(t\).
Tight support separation and the unit-square halfwidth bound give

\[
 n\cdot(c_t-c_i)=h_i(n)+h_t(n)\ge1,
 \qquad n\cdot c_i<M-1=\frac{31}{60}.
\]

Let \(I\) be the sum of internal original force magnitudes times their full
support gaps, and \(C\) the sum of the three original cut magnitudes.
Each internal gap is at least one, so \(I\ge W\). Dot the three **complete**
unloaded force equations with the actual centers and sum. The internal edges
contribute \(-I\); keeping all three cut edges gives

\[
 W\le I<\frac{31}{60}C,
 \qquad C>\frac{60}{31}W. \tag{C}
\]

The strict sign uses positive cut magnitudes and the strict bound on actual
outside centers. It does not assume distinct outside terminals, circle loads on
those terminals, any bound on their degrees, or any chosen shared-side mean.

Orient the internal triangle \(A\to B\to C\to A\) and let
\(x=a n_{AB}\), \(y=b n_{BC}\), \(z=c n_{CA}\). At each completely unloaded
member, its complete force equation makes its single cut magnitude the norm of
the difference of the adjacent two internal force vectors. Hence

\[
 C=|x-y|+|y-z|+|z-x|. \tag{D}
\]

Applying (A) to (C)–(D) gives the strengthened necessary condition

\[
 \frac{60}{31}W<C\le2W-(6-3\sqrt3)m,
\]

and therefore

\[
\boxed{
 \frac{\min(a,b,c)}{a+b+c}
 <\frac{2}{31(6-3\sqrt3)}
 =\frac{4+2\sqrt3}{93}
 <\frac1{12}.
} \tag{E}
\]

For the last comparison, \(\sqrt3<15/8\) follows from
\(192<225\); equivalently \(12(4+2\sqrt3)<93\). The exact algebraic
threshold in (E), approximately \(0.08026\), is the usable output.

The derivation retains the three full original cuts throughout. It makes no
modification to support points, normal owners, shared-side means, moments, or
other pairwise nonoverlaps. These additional physical constraints remain part
of the caller even though this necessary inequality does not use them.

## 4. Independent audit of the prior executable certificate

The review found no invalid exclusion in `verify_force_triangle.py`.

1. **Root coverage.** Permuting magnitudes, rotating \(x\) to the positive
   horizontal axis, and reflecting \(y\) into the upper half-plane preserve the
   claimed perimeter inequality. The two stated rational chart pieces cover
   that entire upper half-circle, while the two full semicircle charts cover
   every direction of \(z\), including all endpoints and overlaps. The length
   intervals cover \(a\ge b\ge c\ge1/12\), \(a+b+c=1\).
2. **Discarded boxes.** The returned `None` cases are necessary-condition
   failures: the enclosure for \(c\) is empty, \(a\ge b\) is impossible, or
   \(a+2b\ge1\) is impossible. None requires the converse. A box that survives
   can still be infeasible; this merely weakens the interval upper bound.
3. **Interval kernel.** The component formulas use valid chart monotonicity on
   the declared domains. Positive-scalar interval multiplication, interval
   subtraction, and endpoint absolute-value maxima give outward enclosures.
   The integer square-root construction satisfies the explicit exact rational
   squared inequality, so no floating-point rounding enters the certificate.
4. **Tree coverage.** Every split is a closed midpoint bisection covering its
   parent. The depth-first traversal processes both children and succeeds only
   after every leaf has passed an emptiness or perimeter-bound check. The
   heuristic changes performance only.
5. **Full-cut transfer.** The center bound, tight full support gaps, all three
   cut edges, and all three complete unloaded force equations are retained in
   the original derivation, as restated in Section 3. The argument is uniform
   over repeated outside terminals and original shared-side means.

The independent replay reproduced:

| \(y\)-chart sign | \(z\)-chart sign | Nodes | Bound-certified leaves | Proven empty leaves | Maximum depth |
|---:|---:|---:|---:|---:|---:|
| +1 | −1 | 7,661 | 3,351 | 480 | 21 |
| +1 | +1 | 657 | 268 | 61 | 17 |
| −1 | −1 | 118,437 | 45,241 | 13,978 | 25 |
| −1 | +1 | 48,627 | 17,055 | 7,259 | 22 |
| **Total** | | **175,382** | **65,915** | **21,778** | **25** |

Each root's least certified rational margin is \(29/1,015,808\).
**Terminology correction:** the checker establishes an upper bound on each
bound-certified leaf; it does not establish that the normalized length and
direction constraints have a feasible point in that leaf. The original phrase
“certified nonempty leaves” should therefore be read as “bound-certified
leaves.” This affects reporting only, not the universal inequality.

## 5. Status boundary

CA0's vector-screen replay, arithmetic-kernel audit, analytic full-cut transfer,
and analytic compression are complete at the mathematical level described
above. This is neither a formal-kernel verification nor an audit of the whole
repository's earlier structural arguments. The direct triangle can still lie
in the strict weak-edge regime (E), which must be treated with the remaining
physical contact and torque constraints. **No original coarse parent, original
fine flag, or nested exterior row is closed by this result alone.**
