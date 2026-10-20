# Signed-coordinate extensions of the positive-GA sole-E stresses

## 1. The existing strict endpoint theorems

Use the same Q1, positive weights, angle variations and actual
owners as in

- [the EH1/DE2 theorem](HAND_G5_POSITIVE_GA1_POSITIVE_EH1_WITH_TD0_EXCLUSION.md);
- [the DE3/EH0 theorem](HAND_G5_POSITIVE_GA_OUTER_E_SOLE_DE_AND_SECONDARY_EXCLUSION.md).

Both retain HG2, nonnegative GA1, either AB0 or AB2, BT2 and
arbitrary TD0. H,A have positive tangents, B,D have negative
tangents, and all actual squares are sorted and contained at
\(q\le Q_1=1957767069/500000000\). T has arbitrary sign and
radial kind. The extensions below require no new scalar
certificate and change no actual square.

**Signed G.** Both strict theorems permit either sign of G.

**Signed E for the EH1 endpoint.** The EH1/DE2 strict theorem
also permits either sign of E. In particular, it applies to
an actual sole nonnegative EH1 primary reached after E has
crossed its zero tangent. This additional assertion is not
made for the DE3/EH0 theorem.

## 2. Either sign of G

Write \(b_G=-y_G\), now as a signed coordinate. The exact
HG2 and GA1 projections are still
\[
 a_H\sin u+b_H\cos u+b_G\ge W(u),\qquad
 a_A+a_G\sin x-b_G\cos x\ge W(x).
\tag{1}
\]
The G force with the existing weights is
\[
                k\sin x(a_G+g b_G).
\tag{2}
\]
Here \(x\ge0\), \(g>0\). Replacing \(b_G\) by \(|b_G|\)
increases (2), and actual containment gives
\[
 (a_G+1/2)^2+(|b_G|+1/2)^2\le Q_1.
\]
Consequently the same support used in both parent proofs is
valid:
\[
 a_G+g b_G\le R\sqrt{1+g^2}-(1+g)/2=\sigma_g.
\tag{3}
\]
No later expression contains the actual G coordinates or
uses the sign of \(b_G\). In particular the split-curvature
bound concerns the unchanged H tangent residual, and all
four remaining force vectors are unchanged. Thus the
complete parent proofs and their strict certificates apply.

## 3. Either sign of E for EH1/DE2

For this section write \(b_E=-y_E\) as a signed coordinate.
The exact E-edge inequalities are
\[
 a_D\cos\delta+b_D\sin\delta+b_E\ge W(\delta),
 \qquad a_H+a_E\sin e-b_E\cos e\ge W(e),
 \quad e\ge0.
\tag{4}
\]
If \(b_E\ge0\), this is the parent theorem. Suppose instead
\(b_E<0\). Let \(a_0=\sqrt{Q_1-1/4}-1/2\), so actual
containment still gives \(a_E\le a_0\).

For the low and middle families the parent coefficients are
\(p(e)=\cos e+\eta\sin e\), \(\eta>0\), on DE2 and 1 on EH1.
The E force is
\[
                 \sin e(a_E+\eta b_E)\le a_0\sin e.
\tag{5}
\]
For the high family p=1, and its E force is
\[
             a_E\sin e+b_E(1-\cos e)\le a_0\sin e.
\tag{6}
\]
Use these axis upper bounds before the primary split.
In the parent notation the contribution of the E width
minus this support has second derivative
\[
                -.5\cos e+(a_0-.5)\sin e
                         <-.5\cos e+.915\sin e.
\tag{7}
\]
The low/middle changing D coefficient still contributes at
most \(.415p(e)\), by the same radial D residual bound;
all G and H terms are unchanged. Thus the resulting second
derivative is smaller than the parent's bound (22), which
used .935 in place of .915. For the high family it is
exactly bounded by the parent's (24). The strict full-split
concavity therefore remains valid on all three intervals.

At either split endpoint, the axis upper support in (5) is
no larger than the parent's \(\sigma_\eta\sin e\): the actual
axis point \((a_0,0)\) is among the points used by that
complete-circle support. Similarly,
\[
 a_0\sin e\le2R\sin(e/2)-\tfrac12(\sin e+1-\cos e)
\tag{8}
\]
for the high family, by evaluating its complete-circle
support at that same point. Hence the axis-relaxed endpoint
weighted expressions are bounded below by the parent
endpoint scalars. All eighteen parent certificates remain
strictly positive. Concavity now proves the contradiction
for the original signed E as well.

These extensions are inequalities on the full actual domain.
They do not enlarge any actual containing circle, reselect an
unavailable owner, or infer equality from an intermediate
state. In the current DE3/EH0 theorem the E force has second
component \(\cos e-r(e)\le0\), with
\(r(e)=\cos e+.7\sin e\) in the low and middle families
and r=1 in the high family. Its axis bound uses \(b_E\ge0\);
the argument (5)--(6) does not extend that theorem to
\(b_E<0\). That different endpoint remains a separate
interface.
