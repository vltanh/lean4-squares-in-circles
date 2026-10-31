# One vertical projection excludes the mixed one-share orbit with sole share 1

Date: October 26, 2026.

**Status: independently reviewed alternative short proof of an already
accepted contact-type exclusion; see
REVIEW_C6_ONE_SHARE_COVER_ROOT_2026_10_26.md.** The same
entire orbit is already excluded in
`SIX_CYCLE_MIXED_ONE_SHARE_MIDDLE_EXCLUSION.md`; this manuscript must
not be counted as a newly closed case. This proof excludes the mixed
corner pattern 110 with its sole genuine outgoing share at loaded
unit 1. It includes every actual share mean and every positive force
triple. The proof uses one projection of actual contact closure, with
no computational certificate, radius estimate, force-ratio bound, or
angle partition.

Retain all nine original physical squares, the common selected
certificate, actual application means and their endpoints, all
original positive forces and physical unique-corner masks, the true
unloaded transmitter equations, all three additional squares, and
the complete retained radius interval. The contradiction already
follows from necessary equations of the six actual cycle bodies.

## 1. Exact original directions

Use `SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md` and
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`. The original type is

\[
        (\chi_0,\chi_1,\chi_2)=(1,1,0),\qquad S_1W_1
                  \text{ the sole genuine share}.
\tag{1}
\]

Normalize the common positive force scale to
\(\mu=(1,p,q)\), with \(p,q>0\). Set

\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\quad
 \sum_i\alpha_i=\pi/2,
\]
\[
 s_i=\cos\alpha_i,\quad c_i=\sin\alpha_i,\quad
 A_i=s_i-c_i,\quad h_i=s_i+c_i,\quad \sigma=1/\sqrt2.
\tag{2}
\]

Choose the original rotated normals
\(n_0=(1,0)\), \(n_1=(-c_1,s_1)\),
\(n_2=(-c_0,-s_0)\). The actual bit-one nonshared unit 0 has

\[
 g_0=f_2+J(f_2-f_0)=(qA_0,-1-qh_0),
 \qquad u_0=(U,-V)=g_0/|g_0|.
\tag{3}
\]

Since \(A_0\ge0\), \(U\ge0\), and
\(1+qh_0-qA_0=1+2qc_0>0\), its unit direction satisfies

\[
                              V>\sigma.
\tag{4}
\]

At the actual outgoing shared unit 1, the mean-preserving normal form
gives

\[
 u_1=-Jn_1=(s_1,c_1),\qquad
 \ell_1=1-A_1/p,\qquad 0<\ell_1\le1.
\tag{5}
\]

In particular no genuine share with chord one is relabeled or
discarded. Units 0 and 2 have actual nonshared chords one.

The bit-zero nonshared support at unit 2 is exactly

\[
 g_2=f_2+J(f_1-f_2)
       =q(-h_0,-A_0)+p(-s_1,-c_1),
 \qquad u_2=(-X_2,-Y_2)=g_2/|g_2|.
\tag{6}
\]

The two summands in (6) have directions
\(\pi+(\pi/4-\alpha_0)\) and \(\pi+\alpha_1\).
The angle sum and \(\alpha_2\le\pi/4\) imply
\(\pi/4-\alpha_0\le\alpha_1\). A positive sum remains in
that cone, which lies in \([\pi,5\pi/4]\). Its absolute
vertical coordinate consequently satisfies

\[
 Y_2\ge\sin(\pi/4-\alpha_0)=\sigma A_0.
\tag{7}
\]

## 2. Vertical contact closure is impossible

The actual transmitter equations give

\[
               n_0+n_1+n_2+u_0+\ell_1u_1+u_2=0.
\]

Its vertical component, using (3), (5), and (6), is

\[
 V+Y_2=s_1-s_0+\ell_1c_1\le h_1-s_0.
\tag{8}
\]

Equations (4) and (7) therefore force

\[
 \begin{split}
 h_1&>s_0+\sigma(1+A_0)\\
    &=\sigma+(1+\sigma)s_0-\sigma c_0\\
    &\ge\sigma+(1+\sigma)\sigma-\sigma^2
       =2\sigma=\sqrt2.
 \end{split}
\tag{9}
\]

The last inequality uses only \(s_0\ge\sigma\) and
\(c_0\le\sigma\). But \(h_1=s_1+c_1\le\sqrt2\),
contradicting (9).

## 3. Exact scope and remaining one-share type

This contradiction covers all original positive force triples and
all actual means of the sole outgoing share, including its endpoint
case. It uses neither a force-ratio bound nor an individual radius
estimate. No transmitter, application mean, or additional square is
moved or replaced.

Cyclic relabeling and reflection followed by reversal carry along
all original physical data, so every allowed copy of (1) is excluded.
The sole outgoing share at unit 0 in the canonical mixed pattern 110
is a distinct contact type and is not excluded by this argument.
The constant-corner one-share orbit and the sole incoming-share-2
orbit have their separate manuscripts and must be joined with their
own independent reviews.

The strictly obtuse one-radial family, global sharp inequality,
equality classification, and earlier prerequisite-chain audit remain
separate obligations. No coefficient certificate, numerical proof
premise, Lean compilation, CI, or workflow dispatch was used.
