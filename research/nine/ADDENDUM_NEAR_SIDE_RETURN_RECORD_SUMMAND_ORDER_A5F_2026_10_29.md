# Clarification of two summand-order labels in the independent near-side return record

Date: October 29, 2026 UTC. Author: `review_load_union_c62`, independent reviewer of the source identified below.

This addendum corrects two ordinal descriptions in the exact record's `scope` strings. The displayed algebraic identities are correct; symbolic canonicalization printed their summands in a different order from the order assumed by those two descriptions. The mathematical source, complete review, exact record, their hashes, and the accepted theorem scopes remain unchanged.

## Exact unchanged artifacts

| Artifact | SHA256 |
| --- | --- |
| `NEAR_SIDE_BOUNDARY_RETURN_FULL_STAR_AXIS_OBSTRUCTION_AND_STRICT_HOUSE_RETURN_EXCLUSION.md` | `d92ec80546d6ae608494626e6f05c52c5f8ff2c7548be0bd98b93bbbc892c8ff` |
| `REVIEW_NEAR_SIDE_BOUNDARY_RETURN_FULL_STAR_AXIS_STRICT_HOUSE_COMPLETE_INDEPENDENT_A5F_2026_10_29.md` | `454fbb5a0d12ed5f3ee144e61da53e8118d689aa4d96af4d44335a573db65a30` |
| `INDEPENDENT_NEAR_SIDE_BOUNDARY_RETURN_FULL_STAR_AXIS_STRICT_HOUSE_EXACT_RECORD_A5F_2026_10_29.json` | `3703439b6b26131b9fe00381aabfa44792ded2113f32491fef3210dff8671439` |

## 1. `Strict scalar inference decomposition`

The record serializes the right-hand side in the order

    mu*(a*q*K-t*V*W)
      = V*(rho*K-mu*t*W) + K*(mu*a*q-rho*V).

Its scope sentence calling the first term positive by `eta*w` and the second term nonnegative must be read with the following corrected named-summand description:

- `V*(rho*K-mu*t*W)` is **nonnegative**, by the actual original AD support inequality and `V>0`.
- `K*(mu*a*q-rho*V)` equals `K*eta*w` and is **strictly positive**, by the full original A4 moment equation and `K,eta,w>0`.

Thus the entire left-hand side is strictly positive. The complete review's Section 13 prints the same two summands in the opposite order and assigns their signs correctly. No source identity, original equation, force, support point, or hypothesis changes.

## 2. `Parallel-C force lower comparison`

The record serializes the right-hand side in the order

    a*nu-rho-eta
      = (2*mu*a*q-rho-eta) + a*(nu-2*mu*q).

Its scope sentence saying the second term is strictly positive must be replaced by this named-summand description:

- `2*mu*a*q-rho-eta` is **strictly positive**. The full A4 moment and `w<=V`, `w>1/2` give `rho+eta<=mu*a*q/w<2*mu*a*q`.
- `a*(nu-2*mu*q)` is **nonnegative**, by `a>0` and the full parallel C2 moment with its unchanged `-1/2<=y<0` mean. It may vanish at `y=-1/2`.

Consequently the original T horizontal resultant is strictly positive, exactly as stated and proved in source Section 5 and complete review Section 12. The weak coefficient endpoint remains included.

## Preservation and verdict

These are corrections to the two record labels only. Both exact symbolic differences remain zero, and both complete mathematical arguments were already correct in the frozen source and full review. The verdict remains **full independent PASS UNCHANGED**, with zero whole-original-row or certificate credit. This addendum is to accompany the unchanged report and exact record in root adoption; no frozen artifact has been edited.
