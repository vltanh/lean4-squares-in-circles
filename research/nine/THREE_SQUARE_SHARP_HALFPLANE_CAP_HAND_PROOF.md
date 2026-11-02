# Three physical squares in the cap above 7/16 satisfy the sharp bound

November 2, 2026. Complete hand proof. No mathematical scripts, numerical
enumeration, Lean, Lake, or CI are used.

Put

\[
 Q=\frac{1105}{256},\quad R=\sqrt Q,\quad
 \rho=\frac{91}{60},\quad b_0=\frac7{16},\quad
 \kappa=\frac76,\quad K=\kappa-b_0=\frac{35}{48}.
\]

## 1. The sharp physical theorem

**Theorem.** Suppose three interior-disjoint physical unit squares lie in
a centered disk of squared radius q, and each whole square lies in the
half-plane y≥7/16. Then

\[
                              q\ge\frac{1105}{256}.     \tag{1}
\]

The square frames are arbitrary. This is a genuine physical three-square
cap theorem, with no coordinate-separation premise.

The bound is attained by three aligned squares centered at

\[
                    (-1,15/16),\quad(0,15/16),\quad(1,15/16).
\]

Their lower edges are at 7/16; the outer corners
\((\pm3/2,23/16)\) have squared norm Q. Thus (1) is sharp.
The complete equality family for this three-square terminal is given in
Section 8. It does not classify unrestricted nine-square equality.

The proof uses the completed unrestricted center-cap theorem
`THREE_SQUARE_DIRECTIONAL_CAP_21_OVER_20_HAND_PROOF.md` only for an
individual square's two-point capture. All other arguments are printed
below.

## 2. A two-point capture statement with closed markers

We first prove that every individual physical unit square contained in
the Q-disk and entirely above y=7/16 contains at least one of the two
**closed** points

\[
                         P_-=(-1/2,\kappa),
                         \qquad P_+=(1/2,\kappa).       \tag{2}
\]

Closed containment is intentional. In the sharp aligned three-square
packing, the markers can be shared on boundaries; they are not asserted
to lie in the interiors of all captured squares.

Write the square's center as \((X,Y)\), its projection halfwidth as h,
and its side-axis absolute components as a≥b≥0, where a²+b²=1 and
h=(a+b)/2. The cap hypothesis is exactly

\[
                               Y\ge h+b_0.              \tag{3}
\]

The horizontal section at height κ has length at least one. To check
this, recall the elementary slice formula: with j=(a−b)/2, the length
at vertical offset t is 1/a for |t|≤j, and (h−|t|)/(ab) for
j≤|t|≤h when b>0. Thus |t|<h−ab suffices; the aligned case has
length exactly one.

If Y≤κ, then by (3)

\[
 \kappa-Y\le K-h<h-ab,
\]

because \(K<\sqrt2-1/2\le2h-ab\). If Y≥κ, use Y+h≤R and
\(R<\sqrt2+2/3\) to get

\[
 Y-\kappa\le R-h-\kappa<h-ab.
\]

Both inequalities are strict. The section is therefore a nondegenerate
closed interval I of length at least one, strictly between the square's
extreme vertical coordinates. If it missed both points (2), it would
have to lie strictly to the right of 1/2 or strictly to the left of −1/2.
It cannot lie between the two points while avoiding them, because that
open interval has length one. Reflection reduces us to

\[
                               \inf I>\frac12.          \tag{4}
\]

We will exclude (4).

## 3. The larger-halfwidth case follows from the center-cap theorem

If h≥49/80, (3) gives

\[
                              Y\ge\frac{21}{20}.
\]

The two-point theorem at 21/20 says the physical square contains one of
\((\pm499/1000,\kappa)\) in its interior. This is incompatible with
(4), and its reflected version. Hence all h≥49/80 squares satisfy
the desired closed-marker capture.

For the rest of the proof assume

\[
                  h<\frac{49}{80},\qquad a+b<\frac{49}{40}. \tag{5}
\]

This forces

\[
                            b<\frac{13}{50},
                            \qquad a>\frac{24}{25}.     \tag{6}
\]

Indeed b+√(1−b²) increases on [0,1/√2]. At b=13/50 it is
strictly greater than 49/40, because
\(\sqrt{2331}>193/4\), whose squared check is 37296>37249.
This proves the first bound in (6); the second follows from
\(a>\sqrt{2331}/50>193/200>24/25\).

## 4. An actual inward normal of the side missing the marker

A side bounding the left endpoint in (4) supplies an inward physical
side normal \(n=(p,s)\), with p>0 and p²+s²=1, such that

\[
                 pX+sY>\frac12+\frac p2+s\kappa.      \tag{7}
\]

The strict inequality is justified by (4). Each component magnitude of
this actual normal is a or b. We call it shallow when p=a, |s|=b,
and steep when p=b, |s|=a.

### 4.1. A steep upward normal is impossible

If n=(b,a), then (7) and (6) give

\[
 n\cdot c>\frac12+\frac b2+\kappa a
 >\frac12+\frac76\frac{24}{25}=\frac{81}{50}>\rho,
\]

contradicting the universal center bound \(|c|<\rho\).

### 4.2. A steep downward normal is impossible

If n=(b,−a), inequality (7) requires

\[
                  b(X-1/2)+a(\kappa-Y)>\frac12.
\]

But X<ρ, Y≥h+b0, h≥1/2, and (6) give

\[
\begin{aligned}
 b(X-1/2)+a(\kappa-Y)
 &<\frac{13}{50}\left(\rho-\frac12\right)
      +\left(K-\frac12\right)\\
 &=\frac{987}{2000}<\frac12.
\end{aligned}
\]

In taking a≤1, the factor K−h is positive by (5). This is a contradiction.

It remains to treat the two shallow signs.

## 5. A shallow upward normal gives the sharp corner bound

Write n=(p,s), with p=a>24/25 and 0≤s=b<13/50. Put

\[
 \eta=h+b_0,\qquad
 J=\frac12+\frac p2+\kappa s,
 \qquad \alpha=n\cdot c,
 \qquad\beta=(-s,p)\cdot c.
\]

By (7), α>J>0. Also β=(Y−sα)/p>0: one has Y≥15/16,
s<13/50 and α<ρ. The maximal squared corner norm is therefore

\[
                          (\alpha+1/2)^2+(\beta+1/2)^2. \tag{8}
\]

For fixed α, lowering Y to η decreases (8). At Y=η, half its
derivative with respect to α is

\[
                     \frac{\alpha-s\eta+(p^2-ps)/2}{p^2}>0,
\]

since p>s and
\(J-s\eta=1/2+p/2+s(K-h)>0\). Thus (8) is strictly greater than
its value at \(Y=\eta,\alpha=J\).

The latter center has horizontal coordinate

\[
                  X'=\frac12+\frac{1/2+s(K-h)}p\ge1.  \tag{9}
\]

Its relevant physical corner has coordinates
\((X'+j,p+s+b_0)\), where j=(p−s)/2. Compare it with
\((3/2,23/16)\), whose norm squared is Q. If the coordinate
increments are Δx,Δy, then

\[
 \Delta x\ge\frac{p-s-1}{2},\qquad
 \Delta y=p+s-1.
\]

The linear part of the squared-norm difference satisfies

\[
\begin{aligned}
 3\Delta x+\frac{23}{8}\Delta y
 &\ge\frac{35}{8}(p-1)+\frac{11}{8}s\\
 &=\frac s8\left(11-\frac{35s}{1+p}\right)\ge0.        \tag{10}
\end{aligned}
\]

Indeed s/(1+p)<13/98<11/35 by (6). Adding the nonnegative
Δx²+Δy² proves that the minimizing corner norm is at least Q.
The strict inequality α>J in (7) makes the actual norm greater than Q,
even in the aligned case s=0. This contradicts containment.

## 6. A shallow downward normal gives the same sharp bound

Write n=(p,−u), where p=a>24/25 and 0≤u=b<13/50. Equation (7)
and (3) give

\[
 X>\frac12+\frac{1/2+u(Y-\kappa)}p
   \ge X':=\frac12+\frac{1/2-u(K-h)}p.                \tag{11}
\]

The actual corner \((X+h,Y+j)\), with j=(p−u)/2, has norm strictly
greater than the corresponding norm at \((X'+h,p+b_0)\). All
coordinates used in this comparison are positive.

The increments from the same sharp corner \((3/2,23/16)\) are

\[
 \Delta x=\frac{1-p+u(p-K)}p,
 \qquad \Delta y=p-1.                                  \tag{12}
\]

This is a direct simplification of (11) using p²+u²=1 and h=(p+u)/2.
Their linear norm contribution is

\[
\begin{aligned}
 3\Delta x+\frac{23}{8}\Delta y
 &=(1-p)\left(\frac3p-\frac{23}{8}\right)
       +\frac{3u(p-K)}p\ge0.                          \tag{13}
\end{aligned}
\]

Here p≤1 gives 3/p−23/8≥1/8, and (6) gives p>K.
Adding the nonnegative increment squares again yields a norm at least Q.
The strict horizontal inequality in (11) makes the actual corner norm
greater than Q. This is impossible.

All four actual-side cases are exhausted. Hence (4) is impossible, as
is its reflection. The closed-marker capture statement (2) is proved.

## 7. Closed-marker capture proves the sharp three-square theorem

Suppose, for a contradiction, that three interior-disjoint units meeting
the cap condition fit in a disk with q<Q. Keep every frame fixed and
multiply all centers by the same factor t>1.

For every physical pair, a separating-axis inequality has the form

\[
 n\cdot(c_j-c_i)\ge H_i(n)+H_j(n)>0.
\]

After the common center expansion its left side is multiplied by t,
so each pair's chosen separator becomes strict. The closed squares are
then pairwise disjoint. The maximal corner norms vary continuously, and
for t>1 sufficiently close to one they remain below Q. We may instead
continue the expansion until the maximal corner norm equals Q; the
strict pair separations remain valid throughout.

The cap condition is preserved, since each original center has Y>0 and

\[
                  tY-h=(Y-h)+(t-1)Y\ge\frac7{16}.
\]

Thus three pairwise disjoint **closed** units would lie in the Q-disk
and in the cap. By (2), each contains at least one of two fixed closed
points. Two units must contain the same point, contradicting closed
disjointness. This proves q≥Q.

No strict-interior claim about the half-unit markers is used in this last
argument. Equality packings may share them on boundaries, as the attaining
aligned example demonstrates.

## 8. Complete equality classification for this cap

Suppose the three squares satisfy the cap hypothesis and fit in the Q-disk.
Take their horizontal sections at height kappa, and order the resulting
closed intervals as I_L, I_M, I_R. Each has length at least one, each
contains a marker from {-1/2,1/2}, and their open intervals are pairwise
disjoint. The latter follows because the slicing line lies strictly between
each square's extreme vertical coordinates.

These facts force

\[
\sup I_L=-\frac12,\qquad
I_M=[-1/2,1/2],\qquad
\inf I_R=\frac12.                                      \tag{14}
\]

Here is the complete interval argument. The first interval cannot contain
the right marker: otherwise the second must start there to meet either
marker, and its length at least one leaves no marker for the third.
Symmetrically the third cannot contain the left marker. If the middle
contains the left marker, disjoint interiors force its left endpoint and
the first interval's right endpoint to equal -1/2. Its length at least one
then forces its right endpoint and the third interval's left endpoint to
equal 1/2. If it contains the right marker, the reflected argument gives
the same conclusion.

For a nonaligned frame, the strict offset bound proved in Section 2 makes
the section length strictly greater than one: in the opposite-side regime
it equals 1/a>1, and in the adjacent-side regime it is greater than one by
|t|<h-ab. Hence the middle square is aligned. Equation (14) puts its center
at (0,t). The cap and corner-containment inequalities are exactly

\[
\frac{15}{16}\le t\le
\rho_*:=\sqrt{Q-\frac14}-\frac12
       =\frac{\sqrt{1041}-8}{16}.                       \tag{15}
\]

For the right square, (14) gives the side inequality (7) with a weak
inequality instead of a strict one. The larger-halfwidth case of Section 3
is still impossible: its section would contain an interior point with
horizontal coordinate at most 499/1000, although its left endpoint is
1/2. Both steep-normal cases remain strictly impossible by their unchanged
center bounds.

In the shallow upward case, (10) is strictly positive whenever s>0. In the
shallow downward case, (13) is strictly positive whenever u>0 because p>K.
All remaining squared increments are nonnegative. Thus a nonzero tilt would
force a corner norm strictly above Q. The right square is aligned. Its left
section endpoint fixes its center x-coordinate at 1; the cap gives Y>=15/16,
while the corner (3/2,Y+1/2) has norm at most sqrt(Q). These inequalities
force Y=15/16. Reflection gives the left center (-1,15/16).

Consequently all equality configurations for the stated cap, up to
relabeling, are precisely the three aligned squares with centers

\[
\boxed{(-1,15/16),\quad(0,t),\quad(1,15/16),
\qquad 15/16\le t\le\rho_*.}                          \tag{16}
\]

Conversely, every value in (15) gives a valid packing: the open horizontal
projections are disjoint, all lower edges meet the cap guard, the outer
squares attain Q, and the middle square is contained exactly by (15).
This proves necessity and sufficiency, including both endpoints.

## 9. Rotated form and exact scope

For any unit direction e, if three whole physical unit squares lie in
the half-plane \(e\cdot x\ge7/16\), their enclosing centered disk
has squared radius at least Q. Reflection gives the corresponding lower
cap statement. Therefore a strict subcritical nine-square packing has
at most two whole squares in each such cap.

This supplies an unrestricted physical terminal, with its complete
three-square equality family, that can be used without first proving
coordinate separation among those three squares. It does not assert that
a full nine-square configuration must contain such a triple, and it makes
no unrestricted nine-square equality-classification claim.

