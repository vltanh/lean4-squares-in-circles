# Independent audit: the final two mixed edge-3 families for 0011011

**Result: PASS for both complete stated families. No correction is needed.**

The review covers:

| Manuscript | Full family | Author comparisons |
|---|---|---:|
| WRONG_0011011_EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER_HAND_PROOF.md | \(C^-\to O^+\) | 118 |
| WRONG_0011011_EDGE3_OUTER_TO_NEGATIVE_CORE_HAND_PROOF.md | \(O^-\to C^-\) | 64 |

Both manuscripts and their JavaScript/checker JSON files are under
m5_agent/hand_conversion. The independent script
audit_wrong_0011011_edge3_final_mixed_hand.py and its output
wrong_0011011_edge3_final_mixed_independent_audit.json are under
proof_integration.

The two author replays pass and reproduce their complete published JSON
byte for byte. The independent Fraction calculation makes **82 strict
comparisons**, reconstructing all **41 displayed Bernstein lower bounds**
in the two notes, the critical angular-envelope values and derivatives,
the core-height derivative bounds, and all twelve endpoint-speed rows.
Each Bernstein basis was solved by triangular coefficient elimination,
then expanded back to the original polynomial. The printed tables were
parsed and compared to these independently reconstructed coefficients.
This is an arithmetic replay of explicitly fixed hand bounds, with no
adaptive cover or sampled premise.

## 1. Negative core to positive outer

I rederived all four signed axes from the stated signs and checked both
half-angle substitutions. The core-norm exclusions, corner exclusions,
and side-contact continuations cover every closed state endpoint.
The core-label majorant includes the corner correction with the correct
sign. The outer affine majorant follows from strong concavity on its
first interval and convexity of its derivative on the second.

The main lower-secondary argument is valid. Completing
\(-gb+vb^2\) gives the affine lower tangent with the stated error.
After \(b+.5=P\sin\phi-V\cos\phi\), the feasible shifted angle lies in
\((0,\pi)\). Exact minimization of
\(\theta-h\sqrt T\sin\theta\) therefore gives
\(\arctan S-S\), with the claimed positive radical.
Differentiation gives
\[
 \beta'=\frac{Q-U}{UT},\qquad
 (\arctan S-S)'=-\frac{rS}{T}.
\]
I independently differentiated these identities twice. The resulting
\(A_0\) and \(C_h\) are precisely the two polynomials stated in the note.
In particular the product-rule coefficients \(3,-1,-6,-4,8\) in
\((rS/T)''\) are correct. Positivity of \(D_0=U^5T^3-A_0\) and of
\(C_h\) gives \(G_h'''<1\); the independent lower bound on \(J'''\)
then gives \(E_h'''<0\). The entire scalar interval follows by the
stated strong-convexity and concavity arguments, including its two
different affine slopes.

For lower primary contacts, I checked the formulas for \(b_\phi\)
and \(b_{\phi\phi}\), the concavity direction, and both endpoints.
The small zero-curve branch really satisfies the secondary separator:
its squared margin reduces to \(349/144-Q+2m>0\), with the unsquared
factor positive. The middle zero-curve bound uses an **upper** second
derivative to obtain a lower chord bound; the sign and constant
\(9(.04)^2/8\) are correct.

The final zero-curve interval imports only the already stated positive
core theorem's Section 5.2. Its geometry and target label are identical
at the source coordinate \(b=0\), and the source constant changes by
exactly \(709/150000\). Thus its resulting lower bound remains strictly
above .89765. This dependence is not circular.

The upper-half contact derivatives, both possible zero exits, the
global full-circle support formula, its squared polynomial, and the
last direct axis bound all have the correct signs. The source-core
corner is covered either by an explicit impossibility bound or by the
global core-label majorant. No omitted contact clamp was found.

## 2. Negative outer to negative core

The whole-core direct bounds correctly remove every upper angle and
the late lower angles. On the remaining interval the first two signed
axes are impossible, leaving precisely the two axes proved in the note.

I rederived the source affine-label majorant, then both full-circle
support formulas by subtracting their positive SAT multipliers.
For the transverse support,
\[
 N''+\frac N4=\frac{(g^2-q^2)^2}{4N^3}>0
\]
has the required direction; the displayed endpoint comparison therefore
proves strict concavity of the complete scalar. The primary-side
polynomial uses the lower sine/cosine Taylor sums and upper cosine
sum with the correct signs. The omitted negative tail is strictly
below its stated .000299 allowance.

For the target corner, I expanded the negative outer label in the
height \(u=a+.5\) and obtained exactly the stated \(M,M',M'',M'''\).
The continued contact height stays in \((1.4,1.7)\), while \(M'>.75\)
on the entire interval needed to compare original centers to contact.
Thus the height reduction applies to arbitrary feasible source states.

The corner is globally concave in its own transverse coordinate:
\[
 f_{BB}<3.212(1+w^2)
         -12(.75)(.455)(1+w^2)^{3/2}<0.
\]
This uses the correct core-circle second derivative and Cauchy–Schwarz
bound. The two resulting endpoint curves have positive derivatives
on the three fixed angle intervals. Convexity of \(M'\) justifies
using its two endpoint values in each product; the speed factor
increases. All twelve products were independently checked, and both
initial endpoint costs exceed the asserted bounds.

## 3. Source binding and theorem scope

The reviewed manuscript hashes are:

- Negative core to positive outer:
  82f8681b84775f395079192b4d4ca23a39b863b65efe5640466776e9496bbba3.
- Negative outer to negative core:
  207165df31ee62bdbb1068cfaf06bbfd63a229d70296323ba849b34868ccd4ea.

The machine-readable audit binds all six author files and the two
explicitly imported manuscript dependencies by SHA-256.
The approval is for the full stated pair inequalities at \(Q=9789/2500\),
all four retained axes, both core pieces, and all closed angle endpoints.
Every final bound is strict above the declared .89765 role entry.
The cyclic wrong-word assembly and the separate candidate-word capture
are outside the scope of this pair audit.
