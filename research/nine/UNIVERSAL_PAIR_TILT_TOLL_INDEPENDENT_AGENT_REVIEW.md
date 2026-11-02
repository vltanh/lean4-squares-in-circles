# Independent agent review of the universal shoulder-tilt toll

November 2, 2026. Reviewer: `root_certificates`, independently of the
`whole_mask` author. This is an agent analytic/code review and a separate
exact replay, not a human review, proof-kernel verification, or CI result.

Reviewed theorem:
`UNIVERSAL_PHYSICAL_PAIR_SHOULDER_TILT_TOLL.md` in `agent_whole_mask`.
The certificate SHA256 is
`b9930b443ad91e853d35087cccab68e822a2ba71dcf38654ccadca839512fe2d`.
The reviewed independent verifier SHA256 is
`81874e3955133a2b3e93515f1165a0dee5fefd19e6231650e614df01f9ea6230`.

## Physical reduction and complete candidate set

The inherited separating-axis support reduction applies to either
original owner and to independent original square frames. Subtracting
twice the shoulder's folded sine from its support penalty does not change
that physical reduction.

On each interval with fixed triangle projection extremes and fixed folded
sine branch, the modified penalty is a linear combination of sine and
cosine. Its second derivative is its negative. It is strictly positive:
the first and third support terms alone are at least (b+k)/2 > 13,
whereas the subtracted toll is at most sqrt(2) < 3/2. Hence each such
interval has its minimum at an endpoint. No assumption that both
individual trigonometric coefficients are positive is needed.

The projected-extreme transitions are exactly the frames parallel to one
of the triangle's three edges. The folded-sine transitions add only the
45-degree frame; the e-aligned endpoint was already included. Quarter
turns identify all equivalent descriptions. This includes both
chiralities and the degenerate collinear endpoint triangles.

For M-owned separation this gives E_B, N_B, D_B and the 45-degree
candidate. For B-owned separation the B penalty and folded sine are
exact, while M has its original three candidates. The N_M/N_B entry is
duplicated, so the five new scalar channels plus the inherited E_B
channel are exhaustive.

## Formula and boundary checks

I reconstructed the absolute N and D expressions directly from their
three support terms. The formulas in the manuscript and independent
verifier agree. In particular the diagonal denominator stays positive
because both weights exceed k.

At the shoulder-owned frame the folded sine is min(|c|,s). At its
diagonal candidate it is min(b-kc,ks)/L_b(-c), with b-kc > 0. The
45-degree penalty is the displayed expression with two maxima; after
subtracting the toll, replacing its leading b by b-2 is correct. These
expressions cover all signs of c on the closed interval [-1,1].

For the near-zero collars of F0 and F1 I independently substituted the
appropriate exact N branches, the tangent bound for H, s >= 1-c^2,
and the folded-sine upper bound |c|. The four coefficients are exactly
149/128, 1877/128, 963/32 and 337/32. Their positivity and the branch
conditions hold on the whole stated intervals, including c=0 and both
shared endpoints.

The Section 5 consequences for the original main tilt are algebraically
correct: each individual bound acquires -bSide/46, the sum acquires
-(bL+bR)/46, and the adaptive opposite endpoint load acquires
+bOpposite/23. Each application keeps the same original shoulder frame.

## Independent exact replay

A fresh execution of `verify_universal_pair_tilt_toll.py` reconstructed
all seven advertised roots and midpoint trees. It passed all 511 strict
leaves, 1,015 nodes, and maximum depth 15. Its least exact reserve was

    2989620761972115 / 18446744073709551616 > 0.

The saved separate report is
`universal_pair_tilt_toll_independent_replay.json` in `agent_roots`.
The checker uses the already existing directed-integer interval kernel
`verify_joint_five_dyadic.py`; it imports no producer and no producer
bound. Its closed-root/tree checks and support-derived scalar formulas
match the physical theorem above.

No analytic or implementation gap was found. This accepts the stated
unrestricted two-square toll theorem. It does not by itself accept a
middle-main exclusion, a partial discovery tree, or a whole mask caller.
