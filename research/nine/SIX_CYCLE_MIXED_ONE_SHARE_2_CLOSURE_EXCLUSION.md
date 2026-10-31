# One projection excludes the mixed one-share orbit with sole incoming share 2

Date: October 26, 2026.

**Status: accepted complete analytic physical contradiction after
independent saved-source reviews in REVIEW_C6_MIXED_ONE_SHARE_2_2026_10_26.md
and REVIEW_C6_ONE_SHARE_COVER_ROOT_2026_10_26.md.** This excludes the entire mixed
corner pattern 110 with its sole genuine share at loaded unit 2,
including every actual mean endpoint and every positive force triple.
It uses one projection of actual contact closure and no computational
certificate, force-ratio bound, radius estimate, or angular partition.

Retain all nine original physical unit squares, the common selected
certificate, original positive forces, actual application means and
physical unique-corner masks, the true unloaded transmitter equations,
all three extra squares and their positions, and the full retained
radius interval. The contradiction already follows from necessary
equations of the six actual cycle bodies.

## 1. The original normal form

Use `SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md` and
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`. The mixed corner bits and
sole genuine share are

\[
       (\chi_0,\chi_1,\chi_2)=(1,1,0),\qquad W_1S_2.
\tag{1}
\]

Thus loaded units 0 and 1 are nonshared, and unit 2 has an incoming
share. Normalize only the common positive force scale, writing
\(\mu=(1,p,q)\), with \(p,q>0\). Put

\[
 s_i=\sin\theta_i,\quad c_i=-\cos\theta_i,\quad
 A_i=s_i-c_i,\quad h_i=s_i+c_i,
\]
\[
 \pi/2<\theta_i\le3\pi/4,\qquad
 \sum_i\theta_i=2\pi,\qquad A_i\ge0.
\tag{2}
\]

Rotate the original normals to

\[
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad n_2=(-c_0,-s_0),
 \qquad f_i=\mu_i n_i,\quad F_i=f_{i-1}-f_i.
\]

The two actual nonshared chords are one. Their support vectors are
\(g_i=f_{i-1}+JF_i\), and direct expansion gives

\[
 g_0=(qA_0,-1-qh_0),\qquad
 u_0=(U,-V):=\frac{(qA_0,-1-qh_0)}{E_0},
 \quad E_0=\sqrt{1+2q^2+2qh_0},
\]
\[
 g_1=(1+ps_1,1+pc_1),\qquad
 u_1=(X,Y):=\frac{(1+ps_1,1+pc_1)}{E_1},
 \quad E_1=\sqrt{2+p^2+2ph_1}.
\tag{3}
\]

All denominators are positive. The original incoming-share torque
normal form is

\[
             u_2=Jn_1=(-s_1,-c_1),\qquad
             \ell_2=1-(q/p)A_2,\qquad 0<\ell_2\le1.
\tag{4}
\]

In particular the actual mean has not been replaced by a vertex. A
genuine share with \(\ell_2=1\) remains included.

## 2. The actual closure has a strictly positive diagonal projection

The exact unloaded-transmitter channel equations imply

\[
                n_0+n_1+n_2+u_0+u_1+\ell_2u_2=0.
\tag{5}
\]

Project (5) on \(d=(1,-1)\). From (3),
\(U\ge0\), \(V>0\), and \(U^2+V^2=1\), so
\(U+V\ge1\). Also \(X-Y=pA_1/E_1\ge0\).
The four projection terms are therefore

\[
 (n_0+n_1+n_2)\cdot d=1-h_1+A_0,
\]
\[
 u_0\cdot d=U+V\ge1,\qquad
 u_1\cdot d=X-Y\ge0,
\]
\[
               \ell_2u_2\cdot d=-\ell_2A_1\ge-A_1.
\]

Their sum is at least

\[
 2-h_1-A_1+A_0
       =2(1-s_1)+A_0>0.
\tag{6}
\]

The final strict sign uses the accepted strict turn
\(\theta_1>\pi/2\), together with \(\theta_1\le3\pi/4\),
so \(s_1<1\). Equation (6) contradicts the zero projection
required by (5).

## 3. Whole-orbit scope

The contradiction covers every original positive force triple and
every allowed incoming-share mean, including its endpoint case.
No upper or lower force ratio was imposed, no radius value was
optimized, and no actual transmitter or extra square was moved. The
proof applies throughout the complete retained radius window because
it needs only the unchanged strict-turn and contact normal form.

The cyclic and reflection-plus-reversal operations described in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md` carry along
the full physical data and preserve the contradiction. Thus all
allowed copies of the orbit (1) are excluded, including the reflected
mixed pattern with its sole outgoing share at the unique bit-one
loaded unit. In these copies the sole share is at the minority corner
bit. The two sole-outgoing-share placements in the canonical 110
pattern are distinct types; no conclusion about them is inferred from
this projection. The share-1 type is already excluded independently
in `SIX_CYCLE_MIXED_ONE_SHARE_MIDDLE_EXCLUSION.md`. The canonical
sole outgoing share at unit 0 remains the mixed one-share completion
obligation.

The strictly obtuse one-radial family, global sharp inequality,
equality classification, and earlier prerequisite-chain audit remain
separate obligations. No coefficient certificate, numerical proof
premise, Lean compilation, CI, or workflow dispatch was used.
