# n=9: exact sharp packing with no globally separating coordinate frame

**Status (2026-10-22): exact constructed counterexample to a proposed
G2 normalization.** It is NOT a counterexample to the conjectured
sharp radius. It disproves the idea that *every* nine-square packing
at \(q\le1105/256\) admits any common perpendicular coordinate
frame in which every square pair is separated by a coordinate
projection. This remains false even at the conjectured optimal
radius, and all inequalities are exact rational comparisons.

## A. The nine squares

Put \(q_*=1105/256\) and center the disk at the origin. The seven
axis-aligned anchors are:

* Four squares centered at \((x,1/16)\) for
  \(x=-3/2,-1/2,1/2,3/2\).
* Three squares centered at \((x,-15/16)\) for \(x=-1,0,1\).

These anchors have disjoint open interiors: squares in a row touch
along vertical sides; the two rows touch along horizontal sides
since \(1/16-(-15/16)=1\). Their farthest vertices have squared norm
at most \(q_*\), with equality at the four outside corners described
in HAND_PROOF.md.

Add TWO FURTHER squares, both oriented along the orthonormal axes
\[
 u=(99/101,\ 20/101),\qquad
 v=(-20/101,\ 99/101),\qquad 99^2+20^2=101^2,
 \tag{1}
\]
with centers
\[
 c_-=\left(-\frac{11}{20},\frac{19}{16}\right),\qquad
 c_+=\left(\frac{11}{20},\frac{19}{16}\right).
 \tag{2}
\]
Both squares are genuinely rotated relative to the seven anchors.

## B. Exact disk and separation checks

The horizontal and vertical projection halfwidth of either new
square in the original anchor frame is
\[
 h=\frac12\left(\frac{99}{101}+\frac{20}{101}\right)
    =\frac{119}{202}. \tag{3}
\]

**Above all anchors:** their lowest vertical coordinate is
\(19/16-119/202\), while the highest vertical coordinate of any
anchor is \(1/16+1/2=9/16\). The clearance is
\[
 \frac{19}{16}-\frac{119}{202}-\frac9{16}
                  =\frac{29}{808}>0. \tag{4}
\]

**Separation of the two new squares:** their center difference is
\(\Delta c=(11/10,0)\). Project onto their own side axis \(u\).
The projected center gap equals
\[
 \Delta c\cdot u=\frac{11}{10}\frac{99}{101}
               =\frac{1089}{1010}
               =1+\frac{79}{1010}. \tag{5}
\]
Each of the two new squares has width **one** along \(u\), so
(5) strictly separates their projection interiors by
\(79/1010\). Hence the squares have disjoint open interiors.

**Inside the record circle:** for a unit square with center c
and orthonormal side axes u,v, the maximal squared vertex norm is
\[
 \|c\|^2+\frac12+|c\cdot u|+|c\cdot v|. \tag{6}
\]
Exactly substituting (1)--(2) gives
\[
\begin{aligned}
 \max_{z\in S_-}\|z\|^2
   &=q_*-\frac{42573}{80800},\\
 \max_{z\in S_+}\|z\|^2
   &=q_*-\frac{22173}{80800}.
\end{aligned}\tag{7}
\]
Both slacks are strictly positive. Every vertex is inside the disk;
convexity of the disk then proves containment of the whole squares.

The anchors attain \(q_*\), so the minimal circle of THIS construction
has precisely squared radius \(q_*\), regardless of whether some
different nine-square packing fits in a smaller disk.

## C. No single common orthogonal coordinate frame works

In the original anchor-aligned frame, the two new squares have
horizontal projection **overlap**
\[
 2h-\frac{11}{10}
 =\frac{119}{101}-\frac{11}{10}
 =\frac{79}{1010}>0. \tag{8}
\]
Their vertical projected intervals have identical centers,
so the vertical overlap is positive too. Thus their interiors
are **not** separated by the horizontal or vertical projection
in the anchor frame, even though they are strictly separated
by the oblique direction \(u\).

Now consider ANY rotated orthonormal coordinate frame
\(e=(\cos\phi,\sin\phi)\), \(f=(-\sin\phi,\cos\phi)\).
Two horizontally adjacent axis-aligned anchors in the middle row
have center difference \((1,0)\). Each anchor has projection
width
\[
 w_e=|\cos\phi|+|\sin\phi|\quad\text{along }e,
 \qquad
 w_f=|\sin\phi|+|\cos\phi|\quad\text{along }f.
\]
For these two adjacent anchors to have disjoint interiors
in the e-projection we need
\[
 |\cos\phi|\ge|\cos\phi|+|\sin\phi|,
\]
which forces \(\sin\phi=0\). Separation in the f-projection
instead forces \(\cos\phi=0\). Hence **any common coordinate
frame separating this adjacent anchor pair must align with
the original horizontal/vertical axes, up to swaps and signs.**
But (8) shows that neither original direction separates the
two rotated upper squares. Therefore:

> **Theorem.** This exact nine-square packing inside the disk
> \(q=q_*\) has no orthonormal frame in which every pair of
> squares is separated by at least one of the two coordinate
> projections.

This proves a bona fide unrestricted G2 *normalization obstruction*,
not just an example of a rotated square.

## D. Structural lesson and precise scope

The rank-grid theorem in ORTHOGONAL_RANK_DICHOTOMY.md remains valid
under its **explicit common-frame separability hypothesis**. That
hypothesis cannot be deduced from the original Packing predicate
even for sharp-radius packing candidates, as proved above.

The new example still has the seven-anchor 4-over-3 pattern, and
satisfies FOUR_ANCHOR_STRESS.md. Thus the right G2 target should
allow the nonanchor squares to use their **own** separating axes
without forcing a common coordinate frame for ALL nine.

A plausible structural split is:

* **G2.A (anchor extraction):** find the four rigid boundary
  anchors with long/short spans, or another sharp terminal
  pattern, without controlling all pairwise separator directions.
* **G2.B (free-square completion):** once such anchors are
  obtained at equality, classify all additional squares using
  actual edge-normal SAT tests; nonanchor oblique contacts are
  permitted and demonstrably occur.

No G2.A universal extraction theorem is proved here. The
construction establishes a **false assumption that must not
recur**, and closes that negative-test subgate. No Lean/CI
or kernel verification is claimed.
