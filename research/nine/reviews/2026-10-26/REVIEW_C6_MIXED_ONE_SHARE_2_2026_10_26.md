# Independent review: the whole mixed sole-incoming-share-2 C6 orbit

Date: October 26, 2026.

**Result: PASS.** Independently reviewed the complete saved source
SIX_CYCLE_MIXED_ONE_SHARE_2_CLOSURE_EXCLUSION.md, including its
original physical normalization, all three actual support directions,
the actual shared mean, the diagonal projection, strictness, and the
symmetry join.

The proof excludes the entire mixed corner pattern 110 with its
sole genuine incoming share at loaded unit 2. It needs no
computational certificate, force-ratio restriction, numerical
premise, radius estimate, or angular partition. No Lean compilation
or CI was run.

## 1. Independent expansion of the original vectors

The normalization divides by the actual positive \(\mu_0\), so
the other magnitudes remain \(p,q>0\). The proper rotated normals
are those of the accepted full-domain source.

For nonshared bit-one units 0 and 1, independently expanding the
true support formula \(g_i=f_{i-1}+J(f_{i-1}-f_i)\) gives

\[
 g_0=(qA_0,-1-qh_0),\qquad
 g_1=(1+ps_1,1+pc_1).
\]

Their squared norms are respectively
\(1+2q^2+2qh_0\) and \(2+p^2+2ph_1\), exactly as
displayed. Thus all normalized directions and all strict positive
denominators have the correct signs.

The sole shared unit has bit zero, so its incoming original interface
has
\[
 u_2=Jn_1=(-s_1,-c_1),\qquad
 \ell_2=1-(q/p)A_2,\qquad 0<\ell_2\le1.
\]
This is the correct actual incoming-share torque formula. The proof
does not replace \(\ell_2\) by one: it only uses the valid weak
inequality supplied by its complete interval.

## 2. The exact diagonal projection

The true side-transmitter equations give
\[
 n_0+n_1+n_2+u_0+u_1+\ell_2u_2=0.
\]
With \(d=(1,-1)\), its four contributions are exactly
\[
 1-h_1+A_0,\qquad U+V,\qquad X-Y,\qquad-\ell_2A_1.
\]

The signs \(U\ge0,V>0\), and \(U^2+V^2=1\), prove
\(U+V\ge1\). The second support vector gives
\(X-Y=pA_1/E_1\ge0\). Finally \(A_1\ge0\) and
\(\ell_2\le1\) prove \(-\ell_2A_1\ge-A_1\), including
every original shared-mean endpoint.

The total projection is therefore at least
\[
 2-h_1-A_1+A_0=2(1-s_1)+A_0.
\]
The accepted strict turn \(\pi/2<\theta_1\le3\pi/4\)
gives \(s_1<1\), while \(A_0\ge0\). The displayed total is
strictly positive. This directly contradicts the required zero
projection. No hidden nonstrict-to-strict inference is present.

## 3. Whole-orbit join and scope

All three genuine body equations are retained, and the actual
incoming-share mean is used before its valid interval inequality.
The contradiction applies to every positive force triple, both
radius endpoints, every admissible original shared-mean endpoint,
all actual transmitter positions, and all three extra physical
squares. The physical unique-corner and strict-turn prerequisites
are those of the original all-unique adjacent-side normal form.

Cyclic relabeling and reflection followed by reversal carry the
whole original physical configuration and the actual means. They
therefore give all symmetry copies of this incoming-share orbit,
including the reflected pattern whose sole share is at its unique
bit-one body.

This is a new closure of the canonical mixed sole-share-2 orbit.
The separately supplied short sole-share-1 vertical proof is a valid
alternative proof of the already accepted
SIX_CYCLE_MIXED_ONE_SHARE_MIDDLE_EXCLUSION.md; it must not be
counted as an additional newly closed orbit. Neither argument
excludes the canonical mixed sole-outgoing-share-0 orbit.
