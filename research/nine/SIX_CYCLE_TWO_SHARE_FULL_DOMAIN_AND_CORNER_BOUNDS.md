# The complete two-share C6 domain and its physical corner inequalities

Date: October 25, 2026.

**Status: complete hand reduction accepted after independent saved-source
and physical-scope review.** See
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS_REVIEW_C6.md`.
This source gives the exact three-orbit
cover and necessary force-ratio inequalities for the remaining two-share
alternating C6. It does not yet exclude that family or close a roadmap
gate. No numerical optimization or coefficient certificate is a premise.

Retain all nine physical unit squares, the common selected certificate,
every original positive force, actual shared mean and physical circle
mask, and the entire radius window

\[
             79/40\le R\le \sqrt{1105}/16.
\tag{1}
\]

The three loaded units have exactly one physical circle corner each;
the three alternating transmitters have their true unloaded degree-two
equations and side-normal reserve one. All three extra squares and all
transmitter positions remain arbitrary and present.

## 1. Original coordinates and means

Use `SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md` and
`SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md`. With cyclic indices, write

\[
 f_i=\mu_i n_i,\qquad F_i=f_{i-1}-f_i,
 \qquad \mu_i>0,\quad |n_i|=1,
\]
\[
 \pi/2<\theta_i\le3\pi/4,\qquad \sum_i\theta_i=2\pi,
 \qquad D_i=|F_i|>0.
\tag{2}
\]

The actual circle corner is \(z_i=R F_i/D_i\). Let \(J\) be
counterclockwise rotation through \(\pi/2\). The two distinct actual
applications on each loaded unit lie on its directed inner side:

\[
 p_i^-=b_i+t_i^-u_i,\quad p_i^+=b_i+t_i^+u_i,
 \quad 0\le t_i^-<t_i^+\le1,
\]
\[
 v_i=-Ju_i,\qquad z_i=b_i+\chi_i u_i+v_i,
 \qquad \chi_i\in\{0,1\},\quad \ell_i=t_i^+-t_i^-.
\tag{3}
\]

At a nonshared loaded unit the original applications are its two side
vertices, so \((t_i^-,t_i^+)=(0,1)\). At a genuine share, the full
mean-preserving normal form is

| Actual share | Corner bit | Side direction | Actual chord and endpoints |
| --- | --- | --- | --- |
| Outgoing interface \(S_iW_i\) | \(\chi_i=1\) | \(u_i=-Jn_i\) | \(\ell_i=1-(\mu_{i-1}/\mu_i)(\sin\theta_i+\cos\theta_i)\), \((t_i^-,t_i^+)=(0,\ell_i)\) |
| Incoming interface \(W_{i-1}S_i\) | \(\chi_i=0\) | \(u_i=Jn_{i-1}\) | \(\ell_i=1-(\mu_i/\mu_{i-1})(\sin\theta_i+\cos\theta_i)\), \((t_i^-,t_i^+)=(1-\ell_i,1)\) |

Always \(0<\ell_i\le1\). A genuine share whose actual mean is a
side endpoint is retained. In particular \(\ell_i=1\) at
\(\theta_i=3\pi/4\) is not relabeled as a singleton interface.

## 2. Exactly three symmetry types, with no omitted mixed placement

The accepted double-shared-channel exclusion says that no transmitter
can share with both loaded neighbors. Together with at most one share
at each loaded unit, the two genuine shares form a matching in the
original six-cycle.

The allowed relabelings are cyclic permutations, and reflection of the
whole physical packing followed by reversal of its cyclic labeling.
Under the latter operation the incoming and outgoing applications are
interchanged, \(u_i\) becomes \(-T u_{-i}\), and \(v_i\)
becomes \(T v_{-i}\), where \(T\) is the reflection. Choosing the
new side base to be \(T(b_{-i}+u_{-i})\) gives

\[
                   \chi'_i=1-\chi_{-i}.
\tag{4}
\]

Thus all constant-bit patterns reduce to \(111\), and all
nonconstant patterns reduce to \(110\). These operations carry along
every original mean, force, corner, transmitter and extra square.

For \(111\), every possible share is outgoing. Cyclic relabeling
therefore places its two shared loaded units at \(0,1\).

For \(110\), a share at \(0\) is outgoing to \(W_0\), a
share at \(1\) is outgoing to \(W_1\), and a share at \(2\)
is incoming from \(W_1\). The pair \(1,2\) would share the same
transmitter and is already excluded. The other two placements are
distinct and both must be retained. The complete cover is precisely:

| Corner bits \((\chi_0,\chi_1,\chi_2)\) | Shared loaded units | Original shared interfaces |
| --- | --- | --- |
| \(111\) | \(0,1\) | \(S_0W_0,\ S_1W_1\) |
| \(110\) | \(0,1\) | \(S_0W_0,\ S_1W_1\) |
| \(110\) | \(0,2\) | \(S_0W_0,\ W_1S_2\) |

This is an enumeration of genuine contact types, not a subdivision of
an angular or force-ratio interval. Excluding only one mixed placement
does not exclude the whole two-share family.

## 3. Exact scalar and vector equations for every row

For one loaded unit abbreviate

\[
 a=\mu_{i-1},\quad b=\mu_i,\quad
 s=\sin\theta_i,\quad c=\cos\theta_i,\quad h=s-c,
 \quad D^2=a^2+b^2-2ab c.
\]

Its actual support vector and magnitude are

\[
 K_i=(\chi_i-t_i^-)f_{i-1}+(t_i^+-\chi_i)f_i,
 \qquad g_i=K_i+JF_i,\quad E_i=|g_i|,
 \quad u_i=g_i/E_i.
\tag{5}
\]

Substitution of the actual means in Section 1 gives the following
closed formulas, including every shared-mean endpoint:

| Original local type | Exact magnitude \(E_i\) |
| --- | --- |
| Nonshared, \(\chi_i=1\) | \(\sqrt{2a^2+b^2+2ab h}\) |
| Nonshared, \(\chi_i=0\) | \(\sqrt{a^2+2b^2+2ab h}\) |
| Outgoing share | \(b+a h\) |
| Incoming share | \(a+b h\) |

For example an outgoing share has
\(g_i=-(b+a h)Jn_i\); an incoming share has
\(g_i=(a+b h)Jn_{i-1}\). The shared means cancel in these
identities only after their original torque formulas are substituted.
They have not been moved to a preferred endpoint.

The true channel equations, their closure consequence, and the true
virial value are respectively

\[
 p_{i+1}^- -p_i^+=n_i,\qquad
 \sum_i(n_i+\ell_i u_i)=0,
 \qquad R\sum_iD_i=\sum_i\mu_i+\sum_iE_i.
\tag{6}
\]

The last two equations alone are necessary relaxations. They do not
replace the first equations, physical containment, nonoverlap, or the
three-extra completion problem. The exact support functional also
remains valid:

\[
 \min_t\left(\sum_i|f_i+t|+\sum_i|g_i+\ell_i t|\right)
       =\sum_i\mu_i+\sum_iE_i=R\sum_iD_i.
\tag{7}
\]

These statements are the unchanged physical identities in the cited
support-functional source. In particular a shared chord in (6)--(7)
cannot be replaced by length one.

## 4. The actual unique-circle corner supplies two strict inequalities

The neighboring vertices of the actual square are
\(z_i-v_i\) and \(z_i-(2\chi_i-1)u_i\). Since \(z_i\)
is its only physical circle corner, both of those vertices lie strictly
inside the same circle. Subtract their squared radii from \(|z_i|^2\):

\[
       z_i\cdot v_i>1/2,\qquad
       (2\chi_i-1)z_i\cdot u_i>1/2.
\tag{8}
\]

This uses the physical mask, independently of the individual load
weights. Inserting \(z_i=RF_i/D_i\) gives two additional necessary
inequalities. Written without any trigonometric denominators, they are:

| Original local type | Both required strict inequalities |
| --- | --- |
| Outgoing share | \(D<2Ra s\) and \(D<2R(b-a c)\) |
| Incoming share | \(D<2Rb s\) and \(D<2R(a-b c)\) |
| Nonshared, \(\chi_i=1\) | \(E_iD<2Ra(a-b c)\) and \(E_iD<2R(D^2+ab s)\) |
| Nonshared, \(\chi_i=0\) | \(E_iD<2Rb(b-a c)\) and \(E_iD<2R(D^2+ab s)\) |

For the nonshared rows, direct dot products in (5) give

\[
 F_i\cdot u_i=
 \begin{cases}a(a-bc)/E_i,&\chi_i=1,\\
              -b(b-ac)/E_i,&\chi_i=0,
 \end{cases}
 \qquad
 F_i\cdot v_i=(D^2+ab s)/E_i.
\tag{9}
\]

All quantities divided by here are strictly positive. Thus (8) and
the table are equivalent for their actual local type; none is inferred
from a sampled configuration. In any necessary relaxation, replacing
\(R\) on the right by \(\sqrt{1105}/16\) preserves necessity.

## 5. Uniform analytic force-ratio bounds

The first corner inequality in each shared row immediately gives

\[
 \begin{array}{ll}
 \displaystyle\frac{b}{a}
  <\cos\theta_i+\sqrt{4R^2-1}\sin\theta_i
  \le\frac{\sqrt{1041}}8<\frac{81}{20},
   &\text{outgoing share},\\[6pt]
 \displaystyle\frac{a}{b}
  <\cos\theta_i+\sqrt{4R^2-1}\sin\theta_i
  \le\frac{\sqrt{1041}}8<\frac{81}{20},
   &\text{incoming share}.
 \end{array}
\tag{10}
\]

To verify the first, square its positive premise \(D<2Ra\sin\theta_i\),
divide by \(a^2\), and complete the square in \(b/a\):

\[
 (b/a-\cos\theta_i)^2
          <(4R^2-1)\sin^2\theta_i.
\]

The other row is the same calculation with \(a,b\) exchanged.
Since \(\cos\theta_i<0\) and \(\sin\theta_i\le1\), (1)
gives the uniform bound. The final positive squared reserve is
\((81/20)^2-1041/64=219/1600\).

The corresponding nonshared bound is stronger:

\[
       b/a<27/10\quad(\chi_i=1),\qquad
       a/b<27/10\quad(\chi_i=0).
\tag{11}
\]

Indeed \(E_i^2-D^2\) equals \(a^2+2ab\sin\theta_i>0\)
in the first case, and \(b^2+2ab\sin\theta_i>0\) in the second.
Put \(x=b/a\) or \(x=a/b\), respectively, and
\(k=-\cos\theta_i\). The first nonshared corner inequality and
\(E_iD>D^2\) give

\[
             x^2<(2R-2)k x+2R-1.
\tag{12}
\]

The exact comparisons

\[
 R<133/64,\qquad k\le1/\sqrt2<99/140
\]

follow from \((133/64)^2-1105/256=9/4096>0\) and
\((99/70)^2-2=1/4900>0\). Therefore

\[
       x^2-\frac{6831}{4480}x-\frac{101}{32}<0.
\tag{13}
\]

The polynomial on the left is increasing for \(x\ge27/10\):
its derivative there is at least \(17361/4480>0\), and its value
at \(27/10\) is \(151/8960>0\). This proves (11) over every
angle and force ratio, with no subdivision or coefficient packet.

Equations (8)--(13) are local and in fact apply to all unique-corner
loaded units in this exact adjacent-side normal form, irrespective of
how many of the other interfaces are shared. They impose no equation
on an artificial aggregate body and do not discard any genuine share
whose mean happens to be an endpoint.

## 6. Retained proof obligation

The entire two-share family requires a whole-domain contradiction or
completion bound for all three rows of Section 2. The exact equations
(2)--(9) and analytic inequalities (10)--(13) are necessary inputs to
that work, not a completed exclusion. The one-share family and the
strictly obtuse one-radial family also remain open.

No original gate is newly checked here. The unrestricted sharp bound,
all original equality packings and the earlier prerequisite-chain
audit retain their separate open status. No Lean compilation, CI,
workflow dispatch, numerical proof premise or coefficient certificate
is used.
