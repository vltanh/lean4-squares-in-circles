# The accepted singleton-floor proof needs no actual middle link in its narrow inset range

November 2, 2026. Scope extension by direct hand verification of every
geometric input to the accepted computer-assisted singleton-floor table.
No new numerical premise, Lean, or CI.

Retain an original cone main four-chain A,B,C,D with actual outer links
in the closed Q-disk, Q=1105/256. Assume only

\[
                  1/2\le h_B,h_C\le31/60.             \tag{1}
\]

The middle link may be weak. Let F be an original central unit above
both mains and G,H two distinct original central units below both.
All three have \(|x|\le l=29/60\).

**Conclusion.** F has whole floor strictly above 1/10.

## 1. The precise inset hypotheses that survive

Put \(\delta=331/20000\), \(g_0=15/31\). The universal original
center-radius bound gives

\[
 |c|\le\sqrt{Q-1/4}-1/2<3/2+\delta,
\]

because \((2+\delta)^2-(Q-1/4)=27061/400000000>0\).
The actual outer comparisons and the completed middle inset comparison
therefore give the strict main bands

\[
 h_B-1-\delta<x_B<\delta-g_B-\eta_C,
\quad
 g_C+\eta_B-\delta<x_C<1+\delta-h_C.                 \tag{2}
\]

Here \(g_M=1/(4h_M)\), \(\eta_M=h_M+g_M-1\ge0\).
By (1), both main inset halfwidths are at least g0. Equations (2) imply

\[
 x_B+g_B>\eta_B-\delta\ge-\delta,
\quad x_B-g_B<\delta-2g_B\le\delta-2g_0,
\]

\[
 x_C-g_C<\delta-\eta_C\le\delta,
\quad x_C+g_C>2g_C-\delta\ge2g_0-\delta.            \tag{3}
\]

Since \(g_0>l\), every central x in [-l,l] satisfies

\[
 |x-x_B|-g_B<x+\delta,
\qquad |x-x_C|-g_C<-x+\delta.                       \tag{4}
\]

For the first inequality, when x>=xB use the first line of (3).
When x<=xB use \(x_B-g_B<\delta-2g_0<\delta-2l\le\delta+2x\).
The second inequality follows by reflection. Thus the inequalities do
not require either main center to lie in a side column. Moreover

\[
                 l+\delta=1/2-7/60000<1/2.          \tag{5}
\]

## 2. Every subsequent input of the accepted proof is unchanged

Sections 2--6 of `CENTRAL_SINGLETON_FLOOR_HAND_TABLE_PROOF.md` use
the actual-four hypothesis only to obtain the following statements:

1. The original inner mains contain aligned insets of halfwidth at
   least g0.
2. For any central original with folded slope t, its losses against
   the two original main insets are bounded by
   \(L(x+\delta,t)\) and \(L(-x+\delta,t)\).
3. The horizontal inset distance in each use is strictly below 1/2,
   including aligned slope t=0.

Statements (1), (4), and (5) above supply all three. No later step uses
actual middle separation, a side-column location of an inner main, or
the main center-height difference. All upper/lower orders in that proof
are supplied by the present theorem's original F,G,H hypotheses.

In particular, the unchanged own-half loss bound A=27/200 gives both
reflected lower centers above 3/5. The upper-column theorem puts G,H
on opposite strict horizontal sides. The unchanged own-half whole-floor
bound exceeds 9/20, and the ordered two-square central-strip cap fixes
their relative heights. The accepted coupled-loss elimination then
removes F using the same delta, g0, and positive exact reserves.

Replacing strict g>g0 by g>=g0 causes no endpoint gap: the needed strict
center clearances follow from (5), and every later numerical comparison
has the displayed positive rational reserve. The strict terminal table
is unchanged.

The small-slope hand complement and the entire four-variable certificate
`central_singleton_floor_cover.json` therefore apply verbatim. Its
4,512 strict leaves have the accepted independent dyadic and independent
Fraction replays, with certificate SHA256

`9dd295e9755acfa9087736752fd8d33d4b1c52604fcfd41a43952bb56a0639f9`.

This proves the conclusion throughout (1), with an actual or weak main
middle link. Wider inner frames remain a separate gate. No whole marked
mask is reclassified by this scope extension alone.
