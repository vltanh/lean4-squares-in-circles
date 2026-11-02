# Independent physical review of the two-shoulder main-height reduction

2026-11-02. Reviewed source:
`WEAK_MIDDLE_TWO_WEAK_SHORT_MAINHEIGHT_QUARTER.md`.
Accepted prerequisite sources are pinned at
`ddadfdd3bd2ef39a2e698680f9a2f3b7d73876ab`.

**Scope.** This review checks the implication from an original 010/11
configuration with selected bad floor to the sixteen exact scalar
roots. Arithmetic acceptance requires the separate complete replay.
Neither this review nor the local main-height result by itself closes
the whole mask. No Lean, Lake, CI, human review, or kernel verification
is claimed.

## 1. Original identities and complete root coverage

The unconditional routing source supplies P above both original inner
mains, L above its own left main, R above its own right main, and
\(y_L,y_R>-9/20\). It supplies the complete larger inner-width interval
\([1/2,13/20]\), rather than the narrower actual-four bound.

One offending original main M has \(y_M\ge-1/4\). Horizontal reflection
and simultaneous chain reversal make \(x_P\ge0\), without fixing which
original main is offending. The main distance estimate used below is
valid for either one. The two main orientations are not incorrectly
identified: only M's original halfwidth is retained, while the other
main contributes a nonnegative orientation excess to the true resource
\(V\ge\eta_M\).

The selected original cone comparisons and the inscribed half-unit
disks give the required positive horizontal gaps. In particular
\(z_R-x_P\ge1/\sqrt2>7/10\). The roots

\[
 t_P,t_L,t_R\in[0,1],\quad x_P\in[0,23/60],\quad
 z_R\in[7/10,13/12],\quad h_M\in[1/2,13/20]
\]

and \(z_L\in[19/60,3/5]\) or \([3/5,13/12]\) contain the complete
routed domain. All eight independent sign triples are retained. Both
roots contain the shared \(z_L=3/5\) face, and both zero-angle and
45-degree faces are retained. The same physical P frame occurs in both
selected pair constraints. The other two original squares are unused
in this local implication; no conclusion about the full mask follows
from dropping them here.

## 2. The main-to-P lower bound is necessary for either original main

Let \(h=h_M\), \(g=1/(4h)\), \(\eta=h+g-1\), and \(x=x_P\).
The actual main coordinate bands give

\[
 |x-x_M|\le d=61/60-h+x\le9/10,
 \qquad g-|x-x_M|\ge\delta=\eta-x-1/60.
\]

The second estimate also follows directly from the first by
\(g-d=\eta-x-1/60\). Thus it does not depend on a freely relocated
main inset. In particular \(d-g\le2/5<1/2\), which excludes the
inset's horizontal coordinate separator. Since P lies above M, a
downward P-owned axis has adjusted projection below one half. The
vertical coordinate axis and both upward P-owned component orders
therefore give the displayed minimum \(R_P\). Relaxing the horizontal
component to its absolute value covers both original P chiralities.

The main and P support minimum is

\[
 s_{MP}=\max\left(1+|h-p|,
 \frac12+\max(k_Ma_P+h b_P,h a_P-k_Mb_P)\right).
\]

The second entry is also exactly

\[
 \frac{1+a_Ma_P+b_Mb_P+|a_Mb_P-b_Ma_P|}{2}.
\]

It is the smaller of the two actual relative-chirality support sums;
the accepted support lemma proves the additional \(1+|h-p|\) lower
bound. For any original separator, Cauchy's inequality gives center
distance at least \(s_{MP}\). Since \(s_{MP}\ge1>d\), every original
separating normal in the direction from M to P has positive vertical
component. The four upward owner alternatives, with their horizontal
components enlarged to absolute values, therefore give the minimum
F. Both the radial lower bound and this four-axis lower bound are
necessary for the same original pair.

Every numerator divided by a possibly small component is at least
\(1/10\). Replacing that component by its maximum with \(1/40\)
is at least a sound weakening. It in fact leaves each displayed
minimum unchanged: when the floor is active its ratio is at least
four, while the unchanged vertical alternatives are less than two,
and the inset minimum includes \(p<1\). This covers aligned faces
without discarding a separator.

Combining these necessary clearances with \(y_M\ge-1/4\) gives exactly
the lower P height in the source. The selected bad floor and each actual
original corner give its upper height. Retaining four physical corners
in the independent checker can only strengthen this upper bound.

## 3. The endpoint loads and tilt terms have the correct shared identity

Let \(A_0=-x_A-h_A\), \(A_3=x_D-h_D\). The outer actual links and
weak middle yield \(A_0+A_3\ge2+V\), and the original endpoint bounds
give \(A_i<61/60\). The two accepted physical pair tolls apply to the
original pairs (A,L) and (D,R), with independent and unrestricted frames.

Eliminating \(A_3\) from its weighted cap gives

\[
 A_0\ge157/184+(27/92)(z_R-h_R)+\tau_R/46+V.
\]

Together with \(A_0>59/60+V\) and \(V\ge\eta\), this is precisely
\(A_L\); the reflected calculation gives \(A_R\). Adding the two
caps gives the summed resource, and the individual lower endpoint
bounds give the two \(451/810\) resources. Every toll belongs to the
same original shoulder whose corners and physical pair axes are later
used. These eliminations introduce no independent orientation choice.

## 4. The raised endpoint rectangle and all its separator cases

The original endpoint inset contains the fixed horizontal interval
\([503/480,937/480]\). Its vertical margin is at least both

\[
 4421/12000+(32/9)\eta,
 \qquad 1-\sqrt{Q-(A_*+29927/30000)^2}.
\]

For the second inequality use that same endpoint's outward corner,
\(h_E+k_E\ge29927/30000\), and \(h_E+g_E\ge1\). On the necessary
load domain \(A_*\le61/60\), clipping \(A_*\) above at \(61/60\)
does not change its value. Off that domain it gives a well-defined
weaker extension. The minimum radical throughout the extension has
the exact positive lower bound

\[
 Q-(61/60+29927/30000)^2=3645989/14062500.
\]

To justify the shoulder's vertical side, first suppose \(z\ge3/5\)
and \(-9/20<Y\le0\). Its half-unit center disk would meet the fixed
endpoint rectangle, because

\[
 \frac14-(503/480-3/5)^2-(9/20-221/600)^2
       =245959/5760000>0.
\]

Thus \(Y>0\). Against the raised rectangle the horizontal distance
is still less than one half, so \(Y\le c\) would again make that
center disk intersect the rectangle. Consequently \(Y>c\).

The coordinate horizontal separator is impossible since
\(z+h_S\ge3/5+1/2>503/480\). A downward/left physical normal has
adjusted projection bounded by

\[
 a_S(503/480-z)-b_S(Y+c)
 <a_Sh_S-b_S(Y+c)
 =1/2+b_S(k_S-Y-c)<1/2.
\]

Here \(Y+c>2(221/600)>k_S\). The swapped-component downward/left
normal is also below one half, and the downward/right normal has
nonpositive center projection. This completes the original-square
axis routing; it is not inferred just from the center disk's normal.

For the two upward physical axes, the wrong-way threshold is dominated
by the vertical coordinate threshold since
\(937/480-z\ge139/160>k_S\). The remaining threshold gives exactly
the sign-dependent loss in the source. Horizontal reflection flips
the left shoulder's chirality, while its global chirality remains
unchanged in the L/P pair equations.

The negative-chirality denominator floors are exact on their complete
roots. The positive squared reserves are

\[
 k(1/16)^2-(503/480-3/5)^2=43207/2368512>0,
\]

\[
 k(1/4)^2-(503/480-7/10)^2=44287/3916800>0.
\]

Thus below the relevant cutoff the numerator of the positive-part loss
is negative, and its loss is exactly zero. In the low-z left root the
weaker \(-9/20\) bound is valid throughout, including its boundary.

## 5. The two original pair intervals and the 21 scalar channels

Each height-difference interval is obtained from the two necessary
original height intervals, then intersected with the same original
cone inequality \([-D,D]\). Both vertical orders are retained.
The original signed support sum is common to the four owner axes.
The maximum absolute projection and maximum squared displacement over
a nonempty interval occur at its endpoints, giving the two physical
pair rejection tests. If the interval is empty, its separate interval
length channel already rejects it.

The selected weak bits supply \(D\le h_i+h_j\); enlarging the strict
weak relation to this closed inequality is harmless. The center disks
supply \(D>7/10\), and the two contained aligned insets supply
\(D\ge g_i+g_j\). These are necessary, not assumed actual separators.
All four genuine owner axes and all independent signed frames occur.

The resulting nine single/resource quantities and six quantities for
each of the two original pairs are exactly the 21 ordered channels
used by the independent checker. No physical implication requiring the
previous 010/01 actual short link is imported.

## 6. Arithmetic independence and conclusion

`verify_two_shoulder_mainheight_exact.cpp` is a standalone 48-bit
directed-integer interval checker. It imports no discovery code. Its
frame ranges are reconstructed from exact endpoint radicals and their
proved monotonicities. Its toll range uses the derivative critical point
\(t=4/9\). It evaluates all four original corners and reconstructs the
main support through relative cosine/sine as well as its exact folded
identity. It retains the pointwise identity that every physical pair
support is at least one.

`verify_two_shoulder_mainheight_exact.py` checks the JSON metadata and
binds the complete candidate bytes to a hash. It accepts plain JSON or
standard-library gzip packaging and records both the delivered byte
hash and the decompressed JSON hash. The C++ engine rebuilds
the sixteen fixed rational roots and every rational midpoint from the
preorder tags, requires every claimed scalar leaf to have a strictly
negative outward upper bound, and rejects missing or trailing nodes.

The physical reduction and complete root union pass this independent
review. The fresh complete arithmetic replay also passed: all
9,688,640 strict leaves in 19,377,264 nodes across all sixteen roots,
with maximum depth 44 and no unresolved frontier. The smallest positive
outward rejection reserve is exactly

\[
                     3012203/281474976710656>0.
\]

The independently replayed JSON has SHA256
`749759fed4eada8d9fa646d2a1bae6c394cd3c2d4723c33b6951b53fecadcf16`.
Its deterministic gzip, `two_shoulder_mainheight_cover.json.gz`, has
SHA256
`96a56f82b46083b380ad17d85d343cfa20ae56cfbea26e6de6b429de369e5897`.
The complete decompressed bytes match the replayed JSON exactly. The
original arithmetic report is preserved separately; the delivered
report records this lossless packaging identity and does not claim a
second arithmetic replay. The checker C++ source has SHA256
`3366f6870300d6fe0d7bd71acf8238d590cb8526bb2ebfeb309e5e6fc6cba40b`.

All eighteen damaged or false proof objects were rejected, including
missing roots, unfinished status, invalid split/scalar tags, incorrect
counts, and a purported forest of sixteen false whole-root leaves. The
complete evidence is in
`two_shoulder_mainheight_cover_independent_exact_replay.json`,
`two_shoulder_mainheight_gzip_identity.json`, and
`two_shoulder_mainheight_rejection_controls.json`.

Thus the stated local theorem is accepted by this independent physical
and exact arithmetic review: under the original 010/11 hypotheses and
the selected bad-floor condition, both original inner main heights are
strictly less than -1/4. This conclusion alone does not close 010/11 or
the full nine-square problem.
