# Exact all-frame sanity check for three Q-attaining controls

November 2, 2026. This is a complete hand argument about the three explicitly
listed equality controls. It is not a closure of an unrestricted fixed-mask
family or a classification of equality configurations. No Lean, Lake, or CI.

## A diameter lemma

Suppose a collection consists of physical axis-aligned unit squares with
pairwise disjoint open interiors. Suppose every two centers satisfy

\[
 |\Delta x|\le3,\qquad |\Delta y|<3,
 \qquad |\Delta x|+|\Delta y|<4.                 \tag{1}
\]

Then no orthonormal frame admits a four-original cone chain with two
actual projection links and one genuinely weak link, in any of the three
positions. This statement concerns all frames and all labelings; it does
not choose a preferred extractor.

To prove this, write the frame's unnormalized horizontal direction as
\(e=(a,b)\ne0\), and put

\[
 N=\sqrt{a^2+b^2},\qquad w=|a|+|b|,
 \qquad h=\frac{w}{2N},\qquad g=\frac1{4h}=\frac{N}{2w}.
\]

Every original square has coordinate halfwidth h in this frame and
contains the aligned square of halfwidth g. An actual link therefore
has unnormalized forward projection at least \(2Nh=w\).
For any physical cone link, its two contained aligned squares also have
disjoint open interiors. At least one coordinate difference has absolute
value at least 2g, and the cone says the forward coordinate is the larger
one. Its unnormalized forward projection is consequently at least
\(2Ng=N^2/w\).

The endpoints of any proposed four-chain would thus satisfy

\[
              e\mathbin{\cdot}\Delta c\ge2w+N^2/w.    \tag{2}
\]

On the other hand, put \(A=|a|\), \(B=|b|\),
\(X=|\Delta x|\), \(Y=|\Delta y|\). Their actual displacement gives

\[
 \begin{aligned}
 w(e\mathbin{\cdot}\Delta c)
 &\le(A+B)(AX+BY)\\
 &=XA^2+(X+Y)AB+YB^2\\
 &<3A^2+4AB+3B^2=2w^2+N^2
 \end{aligned}                                      \tag{3}
\]

whenever \(b\ne0\). The strictness follows from \(Y<3\) and
\(B>0\), including the vertical frame \(a=0\). This contradicts (2).

If \(b=0\), the frame is horizontal up to sign. For two original
axis-aligned squares, physical nonoverlap gives
\(\max(|\Delta x|,|\Delta y|)\ge1\). A horizontal cone link has
\(|\Delta x|\ge|\Delta y|\), so it is automatically an actual
horizontal projection link. A genuinely weak marked bit is impossible.
This proves the lemma, including every boundary direction.

## Two exact equality controls

The first collection is the nine-center control in
`WEAK_OUTER_NUMERIC_BOUNDARY_CONTROL.md`, whose coordinates are retained
unchanged by the arithmetic companion. Its exact diameter bounds are

\[
 \max|\Delta x|=3,\qquad
 \max|\Delta y|=577/240,\qquad
 \max(|\Delta x|+|\Delta y|)=58/15.
\]

The second is the standard three-row 4+3+2 aligned construction:

- Four centers \((x,-1/16)\), with \(x=-3/2,-1/2,1/2,3/2\).
- Three centers \((x,15/16)\), with \(x=-1,0,1\).
- Two centers \((x,-17/16)\), with \(x=-1/2,1/2\).

Each collection has all 36 physical corners in the closed
\(Q=1105/256\) disk, with at least one corner attaining Q, and all
36 original pairs have disjoint open interiors. The second collection's
diameter bounds are 3, 2, and 7/2 respectively.

For the first control the three quadratic coefficient reserves in (3)
are at least \(0,2/15,143/240\); for the second they are at least
\(0,1/2,1\). Thus neither control admits an alternate `001/00` or
`100/00` witness under any frame or permutation, regardless of the
transverse gap. In particular neither is a counterexample to a proposed
closed-Q large-gap exclusion for those two marked masks.

## The oblique attaining construction

The third control has centers

- A,B,C,D at \((x/2,1/16)\), for \(x=-3,-1,1,3\).
- E,F,G at \((x,-15/16)\), for \(x=-1,0,1\).
- H,I at \((\pm11/20,19/16)\).

The first seven originals are aligned. Both H and I have physical axes
\(u=(99/101,20/101)\), \(v=(-20/101,99/101)\). All 36 physical corners
lie in the Q-disk and every original pair is physically nonoverlapping;
the exact arithmetic companion verifies these facts directly. The first
and third diameter bounds of (1) alone would not justify applying the
common-width proof to these differently oriented originals.

Instead, any four-original cone chain with two actual links has endpoint
projection, and therefore endpoint Euclidean distance, at least

\[
                     2+1/\sqrt2.                    \tag{4}
\]

Each actual link contributes at least one. The third physical cone link
contributes at least \(g_i+g_j\ge1/\sqrt2\), without any assumption on
its two original orientations. In this control every center pair except
A,D has squared Euclidean distance at most \(29/4\). But

\[
 (2+1/\sqrt2)^2=9/2+2\sqrt2>29/4,
\]

because \(\sqrt2>11/8\), with squared reserve \(7/64\). Thus the
endpoints must be A,D, up to reversal.

For a proposed chain A,P,Q,D, its three directed edge vectors all lie
within 45 degrees of the same forward frame axis. Every two of these
vectors must consequently have nonnegative dot product. The following
finite table lists the least of the three edge-pair dot products. Rows
give P and columns give Q; a diagonal dash repeats an original and is
therefore inadmissible.

| P / Q | B | C | E | F | G | H | I |
|---|---:|---:|---:|---:|---:|---:|---:|
| B | — | 1 | -9/4 | -1/4 | -1/4 | -2189/1600 | -429/1600 |
| C | -2 | — | -19/4 | -7/4 | -3/4 | -5469/1600 | -1949/1600 |
| E | -3/4 | -1/4 | — | -1/4 | -3/4 | -19/10 | -27/20 |
| F | -7/4 | -1/4 | -5/2 | — | -1/4 | -5629/1600 | -2989/1600 |
| G | -19/4 | -9/4 | -5 | -5/2 | — | -6 | -13/4 |
| H | -1949/1600 | -429/1600 | -13/4 | -2989/1600 | -27/20 | — | -581/1600 |
| I | -5469/1600 | -2189/1600 | -6 | -5629/1600 | -19/10 | -451/200 | — |

Only A,B,C,D survives. Its three adjacent displacement vectors are all
\((1,0)\), and all four originals are physically aligned. In a forward
frame direction \(e=(a,b)\), each such link is actual precisely when
\(a\ge |a|+|b|\), namely when \(a>0,b=0\). Then all three links are
actual. Every other cone-compatible direction makes all three weak.
There is no frame with exactly two actual links and one weak link.
Reversing A,D and the whole chain proves the other endpoint ordering.

This is a complete finite exclusion of an alternate `001/00`, `100/00`,
or one-weak-middle main witness for the oblique control. No transverse
gap restriction and no property of a selected short chain is needed.

## Arithmetic companion

`computer_assisted/extraction_search_boundary_frame_check.py` verifies
all three sets of corners, all physical pairs, every rational diameter
bound, and the 42 entries of the oblique edge table using exact fractions.
Its output is saved in the adjacent JSON file. No angular sample,
tolerance, optimizer output, or unlisted frame endpoint is used.

## Scope retained

This rules out alternate weak-one-link witnesses only for these three
explicit Q-attaining collections (and, by the first lemma, any other aligned
collection satisfying (1)). It does not imply that every equality packing
satisfies (1), nor prove the whole `001/00` closed-Q domain empty.
