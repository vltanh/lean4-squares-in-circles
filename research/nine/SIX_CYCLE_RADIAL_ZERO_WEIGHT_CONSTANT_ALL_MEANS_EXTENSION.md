# The zero-weight radial endpoint uses the common constant-corner all-means bound

Date: October 26, 2026.

**Status: accepted freshly reconstructed analytic dependency extension**,
after the fresh full-source independent review
REVIEW_C6_RADIAL_ZERO_WEIGHT_CONSTANT_ALL_MEANS_ROOT_2026_10_26.md.
The previous local copy was absent after
workspace restoration. This text is derived from the surviving exact
endpoint and common-point sources below; no earlier review is assigned
to this reconstructed text.

The conclusion is a nine-square completion exclusion. The older
constant one-share and two-share matrix arguments remain valid
historical alternatives proving a stronger six-body radius bound.
Their earlier shared retirement is not counted again here.

## 1. The original physical endpoint supplies the scalar identities

Keep the exact alternating all-side C6 and all nine physical squares
of SIX_CYCLE_ONE_RADIAL_ZERO_CORNER_WEIGHT_EXCLUSION.md. Exactly one
loaded unit S is physically two-circle-corner, and exactly one of
its two original individual corner weights is zero. Its other weight
is positive. The other two loads have their actual unique corners.
Every pair force, mean, owner label and transmitter slider remains.

Sections 1--3 of that surviving source prove, for the original
positive-weight corner at S, the same identities as at the other
two actual selected corners:
\[
 \begin{gathered}
 f_i=\mu_i n_i,\quad \mu_i>0,\quad |n_i|=1,\qquad
 F_i=f_{i-1}-f_i,\quad D_i=|F_i|>0,\\
 z_i=R F_i/D_i,\qquad
 \pi/2<\theta_i\le3\pi/4,\qquad \sum_i\theta_i=2\pi.
 \end{gathered}
\tag{1}
\]
The physical second corner of S and its zero weight remain present.
Equation (1) follows from the actual given zero coefficient; it is
not an all-unique-mask assumption or a limiting perturbation.

The actual directed loaded sides and applications have
\[
 z_i=b_i+\chi_i u_i+v_i,\quad v_i=-Ju_i,\qquad
 p_i^\pm=b_i+t_i^\pm u_i,\quad
 0\le t_i^-<t_i^+\le1,\quad
 \ell_i=t_i^+-t_i^-\in(0,1].
\tag{2}
\]
S has no genuine shared interface and its two applications are the
actual endpoints of its inner side. Thus \(\ell_S=1\).
The two physically unique units retain the full actual shared means,
including means already at an endpoint.

Define the unchanged support vector
\[
 g_i^{\rm act}
   =(\chi_i-t_i^-)f_{i-1}+(t_i^+-\chi_i)f_i+JF_i.
\tag{3}
\]
The original torque and support identity give
\[
 u_i=g_i^{\rm act}/|g_i^{\rm act}|,\qquad |g_i^{\rm act}|>0.
\tag{4}
\]
At S the selected corner maximizes its original resultant, which
justifies the same positive support sum; neither adjacent-corner
containment inequality is strengthened.

The actual three channel equations and the original virial yield
\[
 \sum_i(n_i+\ell_i u_i)=0,\qquad
 R\sum_iD_i=\sum_i\mu_i+\sum_i|g_i^{\rm act}|.
\tag{5}
\]
These are precisely equations (11)--(17) of the endpoint source.
No new force equation is supplied by the present extension.

## 2. Every constant bit and every actual mean fit one common functional

Suppose \(\chi_i=\chi\in\{0,1\}\) for all three loaded sides.
Put
\[
 \Delta_i=1-\ell_i\in[0,1],\qquad
 g_i=\chi f_{i-1}+(1-\chi)f_i+JF_i,\qquad
 k_i=\chi f_i+(1-\chi)f_{i-1}.
\tag{6}
\]
For \(\chi=1\), the actual full mean form is
\((t_i^-,t_i^+)=(0,\ell_i)\), so
\[
 g_i^{\rm act}=f_{i-1}+JF_i-\Delta_i f_i.
\]
For \(\chi=0\), it is
\((t_i^-,t_i^+)=(\Delta_i,1)\), so
\[
 g_i^{\rm act}=f_i+JF_i-\Delta_i f_{i-1}.
\]
Both are the exact identity
\[
                         g_i^{\rm act}=g_i-\Delta_i k_i.
\tag{7}
\]
A nonshared unit, including S, has \(\Delta_i=0\). A genuine share
with \(\ell_i=1\) also has this scalar value but keeps its original
genuine contact label. No physical interface is reclassified.

Let \(P=\sum_i|F_i|>0\), and use the purely geometric functional
from TRIANGLE_CONSTANT_CORNER_ALL_MEANS_RADIUS_TWO.md, Section 2:
\[
 \Phi_{\boldsymbol\Delta}(x)
 =\sum_i|f_i-x|
   +\sum_i|g_i-\Delta_i k_i-(1-\Delta_i)x|.
\tag{8}
\]
Its common-point theorem has no physical-circle-mask premise.
For the original counterclockwise force triangle it provides one
Fermat point o satisfying, simultaneously for all mean triples,
\[
                         \Phi_{\boldsymbol\Delta}(o)<2P.
\tag{9}
\]
The triangle here is nonconstant: all \(D_i>0\), and its original
strict positive turn data in (1) supply the required cyclic order.
The general theorem also treats its own collinear and coincident
limits; no such unexamined endpoint is imported here.

At zero every norm in (8) is differentiable by \(\mu_i>0\) and
(4). Its gradient is
\[
 \nabla\Phi_{\boldsymbol\Delta}(0)
   =-\sum_i n_i-\sum_i(1-\Delta_i)u_i=0
\tag{10}
\]
by the actual closure (5). Convexity therefore makes zero a global
minimum. The second identity of (5) is exactly
\[
                         RP=\Phi_{\boldsymbol\Delta}(0).
\]
Consequently
\[
 RP=\Phi_{\boldsymbol\Delta}(0)
       \le\Phi_{\boldsymbol\Delta}(o)<2P,
 \qquad\boxed{R<2}.
\tag{11}
\]
All actual means remain fixed when (10) is used. The common point
in (9) is chosen for the original force triangle before any norm
convexity estimate; independent endpoint minimizers are not combined.

## 3. The original nine-square contradiction and exact replacement

NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md gives \(R>2\) for the same
nine unchanged squares, irrespective of their chosen circle weights
or which six form the selected component. This contradicts (11).
Thus every constant-corner row of the given zero-weight radial
boundary has no nine-square completion.

In Section 6 of SIX_CYCLE_ONE_RADIAL_ZERO_CORNER_WEIGHT_EXCLUSION.md,
the constant zero-, one- and two-share rows may all use this single
argument. In particular, its constant one-share and two-share rows
need not import their historical six-matrix arguments. The mixed
rows, doubly shared channel exclusion, exact physical symmetry cover
and final supported-corner short-angle contradiction retain the
surviving original proofs and their full physical scope.

The older stronger conclusion \(R<79/40\) for an isolated six-body
constant row is not claimed by (11). That remains available through
the old matrix route. This extension instead states the complete
nine-square route required by the original gate, with the global
measure theorem as one explicit shared dependency.

No new matrix or parameter certificate is introduced, and no matrix
retirement is counted twice. The global measure proof retains its
five fixed mass checks, one fixed derivative enclosure and displayed
analytic comparisons. This source neither assigns a new corner
weight nor replaces S's physical two-corner mask by a unique mask.
