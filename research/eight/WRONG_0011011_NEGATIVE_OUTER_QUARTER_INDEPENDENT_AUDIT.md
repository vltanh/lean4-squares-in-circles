# Independent audit: the whole negative outer edge-2 quarter row

**PASS.** I independently rederived the continuous proof in
WRONG_0011011_NEGATIVE_OUTER_QUARTER_HAND_PROOF.md, reconstructed its ten
fixed contact-curvature bounds and twelve endpoint/reference comparisons,
and replayed all 97 author comparisons in an isolated temporary directory.
The author replay is byte-identical and has no diagnostics.

This review concerns the complete OO edge 2 \((-,-)\) quarter-one row,
and its reflected reversal, with the exact rational role labels.
It does not infer a whole-word exclusion from one pair theorem.

## Continuous checks

1. The retained-axis signs agree with the own-frame centers. The derivatives
   of the two labels, their positive first derivatives, the outer chord for
   \(P\), and the convexity arguments establishing the global derivative
   bounds are valid.

2. I independently differentiated \(M(a)=-P(b(a))\). Both displayed
   formulas for \(M''\) and \(M'''\) are correct. The aligned minimum follows
   from the two negative-curvature intervals and the positive derivative
   at \(a=1\); it occurs at the stated diagonal endpoint.

3. The whole-angle reductions for axes 1 and 2 preserve the inequality
   direction. The upper axis-3 contact flow stays within the target arc:
   its threshold is increasing when \(b\le1/2\), and convex otherwise.
   For upper axis 4, the exact identity for the threshold speed is
   bounded by \(Q-2a_0-(a-1/2)^2\). The proof that
   \(M'(a)\sqrt{Q-2a_0-(a-1/2)^2}\) increases uses the correct lower
   bound for \(M''\) and upper bound for \(M'\).

4. For lower axis 4, the active contact cost increases while the inactive
   cost decreases. Every possible minimum therefore reaches the diagonal
   boundary or alignment. The diagonal parametrization and its three
   derivative identities are correct. The early and middle strict
   concavity bounds and the late negative derivative cover the full
   boundary, including its final contact.

5. For lower axis 3, I independently eliminated the angle from
   \(B=1/2-(a-1/2)\cos x+(b+1/2)\sin x\). This gives
   \[
   -x_b=\frac{Q-u}{u(Q+1-2u)}
       +\frac{(B-1/2)(b+1/2)}
              {u(Q+1-2u)\sqrt{Q+1-2u-(B-1/2)^2}}.
   \]
   Differentiating at fixed \(B\) gives precisely the displayed second
   derivative. The five rational rows bound the signed middle term by
   its absolute value in the safe direction; all square-root denominators
   are positive. Since the contact angle decreases strictly with \(b\),
   each fixed-target feasible set is an interval. Its endpoints are
   exactly the four listed boundary types. Thus strict concavity proves
   completeness of that boundary reduction.

6. I checked both subsequent derivative hierarchies. On the diagonal,
   \(H'''=B'[T'''(B')^2-3T''(B-1/2)-T']\); the signs and all coarse
   derivative bounds are correct. On the final angle boundary,
   \(J'''=-P'''+T'''k^3+3T''kk_1+T'k_2\).
   The endpoint choices in the three lower-bound rows handle the negative
   \(T''\) factor correctly. Concavity followed by increasing second
   derivative excludes additional stationary minima. Both final
   strong-convexity estimates use reference points inside their physical
   domains and retain strictly positive reserve over \(.89777\).

No omitted sign branch, reversed curvature bound, or unproved feasible
continuation was found.

## Exact arithmetic and source binding

The independent checker
audit_wrong_0011011_negative_outer_quarter_independently.js has 22 strict
comparisons: five fixed-target concavity rows, two early curvature rows,
three third-derivative rows, and twelve alignment/reference checks.
It uses an independently written exact-fraction implementation and
separately instantiated label/derivative formulas. All 22 comparisons pass.

The original 97-check Python script was copied to
\(/tmp/m5_negative_oo_independent_x4da_ily\) and replayed without editing
the author files. Its output matches the original arithmetic JSON exactly.

| Artifact | SHA-256 |
|---|---|
| Manuscript | 313f4d93c388669ed1d1210399808bbf267bad7f9f0fb2994ae3813bf0655552 |
| Author checker | e9f3caff2c01e3d997cd807e33e84b1a20aa53352e53bd88f2548b91f2a0462a |
| Author arithmetic | 8ba29abdf9ad3ccaa8eabe36a05ae4f99b9b9754a0064b9747836e03719c4f61 |

The machine-readable replay binding is
negative_outer_quarter_author_replay_audit.json.

