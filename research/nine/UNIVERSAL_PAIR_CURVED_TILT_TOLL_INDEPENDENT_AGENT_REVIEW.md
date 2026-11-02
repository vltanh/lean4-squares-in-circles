# Independent agent review of the curved shoulder-tilt toll

November 2, 2026. Reviewer: `root_certificates`, independently of the
`whole_mask` author. This is an agent analytic/code review and a separate
exact replay, not a human review, proof-kernel verification, or CI result.

Reviewed theorem:
`UNIVERSAL_PHYSICAL_PAIR_CURVED_TILT_TOLL.md` in `agent_whole_mask`.
Certificate SHA256:
`9ba10374718180ebdc4fe1d95675f898c4b549919785ad2d5f8bf62142617cb0`.
Independent verifier SHA256:
`e904494852880d9cde3d8d891c880650cad80b8a5e855e7e4e8448d87cae3b86`.

## Analytic and implementation checks

The support triangle inequality gives

    P_B >= 2b h_B(e) = b(alpha_B+beta_B).

On each fixed projected-extreme/fold interval, subtracting
Phi=6 beta_B-b(1-alpha_B) therefore leaves second derivative at most
-(b-6) beta_B <= 0. Concavity suffices to put its minimum at an
interval endpoint, including any endpoint at which beta_B vanishes.
The same four candidate frames from the linear-toll proof remain complete.
The two physical owner alternatives are unchanged.

The N, D and 45-degree evaluations of Phi agree with the original frame
components. The absolute-support N and D formulas in the verifier were
already independently checked for the linear theorem. In the 45-degree
candidate the adjusted penalty simplifies to

    b + [max(b-kc,ks)+k max(|c|,s)-6]/sqrt(2),

as implemented. Both signs of c and all folded-frame endpoints are covered.

I independently reconstructed all four near-zero coefficients. Keeping
the positive b(1-s) contribution cancels the b part of the quadratic loss
in G0 and of the a+b loss in G1. The resulting coefficients are exactly
33/512, 6945/512, 1027/32 and 401/32, all positive on the stated
collars. Their branch conditions are satisfied.

Combining the curved and linear inequalities by taking the maximum of
their two tolls is valid for the same original shoulder orientation.
The endpoint evaluation rule in Section 5 is also valid: Phi is concave
as a function of folded angle, so its minimum on the angle interval
corresponding to a tangent interval is at one of its endpoints. The
linear toll increases on that interval. The maximum of the two separately
valid interval lower bounds remains a lower bound for their pointwise
maximum.

The resulting deductions tau/92 and adaptive additions tau/46 follow
directly from the same original pair-cap algebra. No original shoulder
frame is chosen independently of its other constraints.

## Separate exact replay and acceptance boundary

A fresh execution of `verify_universal_pair_curved_tilt_toll.py`
reconstructed all seven roots and passed all 860 strict leaves, 1,713
nodes, and maximum depth 16. It also verified every printed table lower
bound and all four collar coefficients. The least exact reserve was

    21015472069061 / 576460752303423488 > 0.

The separate saved report is
`universal_pair_curved_tilt_toll_independent_replay.json` in `agent_roots`.
The runtime interval dependency is the existing
`verify_joint_five_dyadic.py`; no producer or producer bound is imported.

No analytic or implementation gap was found. This accepts the curved
unrestricted physical pair theorem. A middle-main exclusion and a full
mask still require their own completed covers and caller assembly.
