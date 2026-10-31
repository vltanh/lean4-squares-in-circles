# Independent review of the exact C6 five-scalar compatibility reduction

Date: October 26, 2026.

Reviewed source: SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md.

**Verdict: PASS at its stated reduction scope.** This review independently
checks both directions of the residual equivalence, the exact recovery
of the original shared mean and force ratio, all orientation signs,
and the retained physical conditions. It does not infer a core
exclusion, a root count or a completion-capacity estimate.

## 1. Residual identities and equivalence

Starting from the displayed actual port formulas, direct telescoping
gives sum r_i=-C. For the weighted dot product, the local term is
F_i dot z_i-K_i dot u_i-F_i dot v_i. Since v_i=-Ju_i,
F_i dot v_i=(JF_i) dot u_i, so this term is RD_i-E_i.
Subtracting sum f_i dot n_i=sum mu_i proves the exact virial residual.

For the determinant identity, v_i cross F_i=u_i dot F_i
=u_i cross JF_i. Thus the actual local torque is
-u_i cross (K_i+JF_i)=0, since u_i is the positive direction of
that actual nonzero vector. Summing the local equations gives the
claimed zero determinant-weighted residual without any channel
equation or numerical rank premise.

Conversely, r_0=C=0 gives r_2=-r_1. With V=0 the remaining dot
and determinant identities are exactly F_2 dot r_1=0 and
F_2 cross r_1=0, where F_2=f_1-f_2 is nonzero by the original
strict turns. Their squared sum is |F_2|^2|r_1|^2, proving that
both remaining vector channels vanish. Thus the five-scalar
equivalence has no missing exceptional branch.

## 2. Original residual-orbit directions and norms

I rederived g_2=f_2+J(f_1-f_2) for the actual bit-zero unit. In
the displayed normalization this is
q(-h_0,-A_0)+p(-s_1,-c_1), exactly as printed. Its squared norm is
p^2+2q^2+2pq h_2, because
s_1 h_0+c_1 A_0=s_2+c_2. Similarly g_1 has coordinates
(1+ps_1,1+pc_1), giving the required constant 2 in E_1^2.
The virial numerator includes the unchanged shared unit term
E_0=1+qh_0, and consequently its constant is also correctly 2.

## 3. Both directions of the three-parameter reconstruction

For unit 0, the actual directions u_0=(0,-1), v_0=(-1,0)
give p_0^-=(-a+1,-b+1) and
p_0^+=(-a+1,-b+1-ell). Unit 1 has
v_1=(Y,-X), hence
p_1^-=(A-X-Y,-B-Y+X). Equating their channel difference to
(1,0) gives exactly the printed a and H, including both vertical
signs and the formula ell=1+H-b.

The original force relation is F_0=kappa(-a,-b), with
kappa=D_0/R>0. The shared torque gives
ell=kappa(a-b)>0, so a>b>1/2 and the stated division by a-b is
legitimate. The original negative vertical corner coordinate chooses
the positive radical b; there is no omitted second physical branch.

In the reverse construction, f_2=(1-kappa a,-kappa b) gives
F_0=kappa z_0 and D_0=kappa R. Moreover
q(s_0-c_0)=1-kappa(a-b)=1-ell. Substituting this into the actual
shared expression gives exactly
g_0=(0,-kappa(a+b)), E_0=kappa(a+b)=1+qh_0>0.
The reconstructed channel-0 ports are then identically separated
by the original vector (1,0). The equivalence from Section 1
therefore supplies the remaining channels from C_x=C_y=V=0.

The final height comparison is also exact:
kappa a>1 is equivalent to
a(1+H-b)>a-b, hence H>b(1-1/a). Since a>b and
a^2+b^2=R^2, one has a>R/sqrt(2)>1, giving H>0.

## 4. Physical scope retained

The reconstruction retains the real positive radical, positive force
ratios, all three strict turn domains and their allowed upper
endpoints, the original shared mean interval, and its separately
proved ell=1 exclusion. Its unique-corner conditions have the
correct signs: z_i dot v_i>1/2 and
(2chi_i-1)z_i dot u_i>1/2. These are statements about actual
physical masks, independent of individual multiplier endpoints.

Every reconstructed unit, original contact type, actual application,
transmitter slider, pairwise nonoverlap condition and all three extra
squares remain explicit admissibility conditions. Thus the source
does not treat solutions of its three equations alone as physical
packings. No numerical diagnostic box or presumed uniqueness is
used to restrict the original domain.

The reduction and its scope pass. No Lean compilation, CI or
numerical feasibility claim was used in this review.
