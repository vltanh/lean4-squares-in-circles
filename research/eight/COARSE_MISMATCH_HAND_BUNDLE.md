# Complete coarse mismatch hand package

The fixed full-SAT candidate table proves `S<2/5`. Concavity strengthens
this to `S<109/400`, and retaining seven parts of the already printed
positive cost reserves strengthens it further to **`S<13/50`**.
Only the established G/T bounds and the normalization `u_E<=0` are used;
no H/D cut, desired owner, or smaller initial mismatch is assumed.

## Reconstruction and replay

The original input is stored in three ordered text parts so that each
repository upload stays within the connector's request-size limit.
This changes no byte of the mathematical input or any reviewed source.
From this directory run:

```sh
python restore_candidate_coarse_mismatch_hand_input.py
python replay_candidate_coarse_mismatch_hand.py
python audit_coarse_mismatch_assembly.py
python verify_coarse_mismatch_concavity_strengthening.py
python verify_coarse_mismatch_printed_reserves.py
```

The first command verifies every part and reconstructs the exact original
`CANDIDATE_COARSE_MISMATCH_HAND_DATA.json`, with SHA-256
`ffa48df0d02e18880314907a72a70fcc6aaceea4ee1060ea76b4fdb04c23a5fa`.
The rest of the proof and every independent audit use that unchanged file.
The original full coefficient replay has SHA-256
`9e44e1fe7a0df8c7f2f4e7203a2c5f5f154fd07322852574539ccddb6df19b11`.

The hand argument is `CANDIDATE_COARSE_MISMATCH_HAND_PROOF.md`.
The strongest corollary is
`COARSE_MISMATCH_PRINTED_RESERVE_STRENGTHENING.md`.
The complete package is bound by
`CANDIDATE_COARSE_MISMATCH_HAND_MANIFEST.json`, including the original
independent continuous/domain/replay review and both corollaries.

## Additional package and reserve review

The integration review checked that each cost polynomial in the affine
kernel bounds the original charged pair expression directly, without a
variable positive scaling. Its Bernstein basis is nonnegative and sums
to one on its closed interval. Therefore a minimum printed cost coefficient
is a uniform additive reserve for that expression. Taking the minimum of
all endpoint costs and then of all rows for a fixed original edge gives
the seven reserves listed in the supplementary proof. Each retained
increase is strictly smaller than its corresponding reserve, and the
seven increases sum to `51/500000`.

For `0<=S<2/5`, concavity and `h(0)=0` give
`sum h(abs(d_i))>=h(S)` by the weights `abs(d_i)/S`; the zero case is
immediate. Monotonicity of h on that interval and the displayed alternating
lower Taylor polynomial at `13/50` give the exact positive cyclic surplus
`9154605884982919/494375000000000000000` above `710/113`.
Thus the strengthened bound uses the complete original table and adds no
geometric premise. The ordered-parts reconstruction was also checked in
a fresh directory against the original input bytes.
