# Root review: all H-owned unloaded-end returns reduce to two opposite vertices

Date: October 28, 2026 UTC. Reviewer: root continuation.

**Verdict: PASS of the complete radius-free necessary-domain theorem.
Both original H4_D0 load families remain open.**

I read and independently reconstructed the complete source
`INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md`,
SHA256 bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c.
Its original full H4 scope and exact H-owned-end inputs were checked
against the already adopted shared-end and opposite-sign sources.

The sharpened support-span inequality holds at a unique support vertex
and at every mean on a support side. With n.e<0, at most one inward
axis contributes a positive e component; that component is at most
sqrt(1-(n.e)^2). The side proof keeps the full original tangent interval.

I checked the whole CD contact-set visibility argument for both HC
features. For Northeast, the actual point (1,1) has D-frame coordinates
(a q,-b q), with the first strictly between zero and one. Any contact
with positive v coordinate creates an actual C point in int(D). For
East HC, the whole C has x>=1, so a contact with positive v has positive
u; the segment from the actual HC point again enters int(D), including
both possible u endpoints. The point P itself violates the original
HC support. Thus every actual CD point lies on the single stated edge.

The complete D-owned CD cover is valid. The alternative endpoint axis
u would create another contact along positive v if C were side-interior,
and would violate the original strict convention at a point-only double
vertex. The remaining -v axis and full D3 force make E supported at
the top vertex with positive vertical normal. Its whole unit lies above
y=1, contradicting the actual AE contact and max_A y<1.

For the surviving strict CD vector (xi,-eta), full D3 gives the exact
E vector (gamma b-xi,gamma a+eta). A positive first component gives the
same entire top-vertex exclusion. At equality xi=gamma b, the original
side mean has tau=eta/(gamma a+eta), strictly inside its full interval
as a consequence of torque. The sharpened support-span bound gives
min_E y>=1+a(1-gamma b/Gamma).

For Northeast HC, direct support comparison at S=(1,1) is exactly
b(q Gamma-gamma)>=0, giving Gamma>=gamma/q>gamma b. For East HC,
the actual HC point lies below and weakly left of the actual CD point;
its support inequality gives gamma b^2-eta a<=0, hence
Gamma>=gamma/a>gamma b. Both original HC owner types and all means
therefore exclude the whole E-side case.

The remaining opposite-vertex torque is xi=eta+gamma b. The printed
world components and subsequent inequalities (14),(15) follow directly.
In particular the weak equality in the East-HC slope bound is retained.
No loaded E2 equation, long-port premise, circle bound or shortened H
star was used. E2 and H4 remain present in the unexcluded residue.

Both actual original substitutions (A,B,C,D,E)=(0,1,2,3,4) preserve all
degrees and loads. Only the L124 unloaded end admits the reflected
second-end application; the loaded end of L0124 is never unloaded.
This is a full owner-interface reduction, not a whole fine-family
closure. All original units, applications and masks remain, with no
Lean run, CI, numerical pose or mesh.
