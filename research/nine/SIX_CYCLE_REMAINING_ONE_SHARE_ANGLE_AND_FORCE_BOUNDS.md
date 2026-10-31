# Two strict whole-orbit bounds for the remaining mixed one-share C6

Date: October 26, 2026.

**Status: accepted complete short hand reduction after independent
review in REVIEW_C6_REMAINING_ANGLE_FORCE_BOUNDS_ROOT_2026_10_26.md.**
The original closure gives \(q>1\), the strict angular
bound \(c_0>3-2\sqrt2>1/6\), and the sharper single angle
restriction displayed below. No radius optimization, sampled pose,
parameter grid, or computational certificate is a premise.

Retain the full physical domain of
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md:
the actual nine squares, common selected certificate, all positive
forces, physical unique-circle-corner masks, original application
means and their endpoints, all three side-transmitter sliders,
all extra squares, and
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The canonical remaining contact type is
\(\chi=(1,1,0)\), with sole genuine outgoing share \(S_0W_0\).
These are necessary whole-orbit reductions; they do not assert
\(R\le2\), a complete coordinate box, or a completion exclusion.

## 1. Unchanged exact normal form and direction bounds

Normalize only by the original positive \(\mu_0\), so
\(\mu=(1,p,q)\), \(p,q>0\). Put
\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\quad
 \sum_i\alpha_i=\pi/2,\qquad
 c_i=\sin\alpha_i,\quad s_i=\cos\alpha_i,
\]
\[
 A_i=s_i-c_i\ge0,\quad h_i=s_i+c_i,\quad r=1/\sqrt2.
\tag{2}
\]
The actual normals and directed loaded sides are
\[
 n_0=(1,0),\quad n_1=(-c_1,s_1),\quad
 n_2=(-c_0,-s_0),\qquad u_0=(0,-1),
\]
\[
 \ell_0=1-qA_0,\quad0<\ell_0\le1,\qquad
                     \ell_1=\ell_2=1,
\]
\[
 u_1=(X,Y)=\frac{(1+ps_1,1+pc_1)}
                    {\sqrt{2+p^2+2ph_1}},
\]
\[
 u_2=(-M,-N)=
 \frac{q(-h_0,-A_0)+p(-s_1,-c_1)}
                    {\sqrt{p^2+2q^2+2pqh_2}}.
\tag{3}
\]
In particular the true positive shared chord gives
\[
                              qA_0<1.
\tag{4}
\]
The endpoint \(\ell_0=1\) is initially retained.

The first nonshared direction lies between angles
\(\alpha_1\) and \(\pi/4\). Equivalently, its positive unit
coordinates obey
\[
                         r\le X\le s_1,\qquad 0<Y\le r.
\tag{5}
\]
The lower bound for \(X\) also follows directly from
\(X-Y=pA_1/E_1\ge0\).

For the second direction, the two positive vectors
\((h_0,A_0)\) and \((s_1,c_1)\) have angles
\(\pi/4-\alpha_0\) and \(\alpha_1\). They are ordered because
\(\alpha_0+\alpha_1\ge\pi/4\), and both belong to
\([0,\pi/4]\). Their positive linear combination therefore
gives the complete coordinate bounds
\[
                 s_1\le M\le r h_0,\qquad
                 rA_0\le N\le c_1.
\tag{6}
\]
These are direction-cone consequences of the original norm
formula. No force ratio or actual mean is changed.

The two components of the actual contact closure are exactly
\[
                 M=1-c_0-c_1+X,
\]
\[
                 N=s_1-s_0-1+qA_0+Y.
\tag{7}
\]
Combining (6)--(7), one may retain the useful unsimplified bounds
\[
       h_1+c_0-1\le X\le c_0+c_1-1+r h_0,
\tag{8}
\]
\[
 1+s_0-s_1-Y+rA_0\le qA_0
               \le1+s_0-s_1-Y+c_1,\qquad qA_0<1.
\tag{9}
\]
All signs in (8)--(9) follow directly from positive original
forces and the unchanged closure.

## 2. The exact sharper angular restriction and \(c_0>1/6\)

The upper bound in (8), together with \(X\ge r\), gives
the whole-angle restriction
\[
 \boxed{\qquad c_1+(1+r)c_0+r s_0\ge1+r.\qquad}
\tag{10}
\]
This inequality preserves the full original angle domain; it is
not a partition into angular cells.

Since \(c_1\le r\), equation (10) gives
\[
 (1+r)c_0\ge1+r-c_1-rs_0\ge1-rs_0>1-r.
\]
The last inequality is strict because the original turn
\(\theta_0>\pi/2\) gives \(c_0>0\), hence \(s_0<1\).
Therefore
\[
 \boxed{\qquad
      c_0>\frac{1-r}{1+r}=3-2\sqrt2>\frac16.
      \qquad}
\tag{11}
\]
The last fixed comparison follows from \(\sqrt2<17/12\),
whose squared reserve is \(1/144>0\). Thus both the sharper
radical lower bound and the convenient rational lower bound
are strict over the entire remaining physical orbit.

## 3. The original force ratio satisfies \(q>1\)

Suppose instead that \(q\le1\). Since \(A_0\ge0\),
the vertical closure, \(Y\le r\), and (6) imply
\[
 r(s_0-c_0)\le N
      =s_1-s_0-1+qA_0+Y
      \le s_1-c_0-1+r.
\]
Consequently
\[
                  s_1\ge1-r+r s_0+(1-r)c_0.
\tag{12}
\]
The function
\[
                \varphi(\alpha)=r\cos\alpha+(1-r)\sin\alpha
\]
is positive and concave on \(0\le\alpha\le\pi/4\),
since \(\varphi''=-\varphi<0\). Its values at both endpoints
are \(r\). The chord inequality therefore gives
\(\varphi(\alpha)\ge r\) throughout that full interval.
Applying it at the original \(\alpha_0\), the right side
of (12) is at least one.

But \(\alpha_1>0\) gives \(s_1=\cos\alpha_1<1\), a
contradiction. This includes the proposed endpoint \(q=1\);
the exact strict consequence is
\[
                             \boxed{q>1.}
\tag{13}
\]
No division by \(A_0\), shared chord or force difference occurs
in this proof.

For completeness, the original \(\ell_0=1\) endpoint is still
handled by its actual closure contradiction. It would give
\(A_0=0\), \(s_0=c_0=r\), and then
\[
                   N=s_1-r-1+Y\le s_1-1<0,
\]
contradicting \(N\ge0\). Thus \(A_0>0\) and
\[
               0<\ell_0<1,\qquad
                  1<q<1/A_0,\qquad c_0<r
\tag{14}
\]
hold for every actual remaining core. The mean endpoint was
explicitly contradicted, not omitted or relabeled.

## 4. Precisely retained scope

Equations (8)--(14) are simultaneous necessary consequences of
the original full physical model. They hold for every positive
force triple, every original shared mean, and every allowed
transmitter position in the remaining orbit, throughout (1).
Their reflected and cyclic images follow by carrying the
original packing and certificate through the accepted symmetry.

The complete individual channel equations, physical containment,
nonoverlap and all nine squares remain required. In particular
the five-scalar compatibility reduction is available but was
not needed for these two closure consequences.

The central capacity-one theorem and the empty exterior pocket-1
theorem remain unchanged. No further exterior allocation is
excluded here. The conditional pocket-0 capacity theorem still
requires its separate coordinate hypotheses; this source does
not assert those hypotheses or \(R\le2\). No new certificate,
numerical premise, Lean compilation or CI was used.
