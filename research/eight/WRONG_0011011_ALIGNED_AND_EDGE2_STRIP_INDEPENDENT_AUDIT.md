# Independent audit: 0011011 aligned mixed quarter and edge-2 strip

Result: **PASS** for the exact aligned theorem and the whole closed edge-2 strip |phi-pi/2|<=1/50.

The aligned proof covers all twelve permitted kind/sign rows at edges2/3 and their exact reflected partners. I independently checked the coincident-axis alternatives, the derivative of the ratio L prime/r, the mixed contact reductions, the G and H2 strong-convexity bounds, the H3 decreasing-curvature argument and .63 split, and the K contact bound. All85 fixed arithmetic comparisons replayed successfully.

The strip proof covers both radial orders and both target signs before reducing to core-side contacts. I checked all four signed-axis formulas, the side-range bounds, and each direction of cost decrease. Zero-core-coordinate exits have a unique outer continuation for outer-to-core cases; core-to-outer exits satisfy the stated direct bound. The argument does not omit core-corner inputs or assume that a contact path can pass through an infeasible upper-side endpoint. All146 fixed comparisons replayed successfully.

One intermediate comparison in the original strip manuscript was corrected during this review: for positive e, F_e is bounded by max(b-1/2,0), then by.4; the previous F_e<=b-1/2 expression was false when b<1/2. The corrected sentence is bound below. The actual derivative threshold and all arithmetic were unaffected.

This audit does not claim any nonaligned edge3 range or the edge2 angles outside the declared strip.

## Bound artifacts

- WRONG_0011011_ALIGNED_MIXED_QUARTER_HAND_PROOF.md: 52a89ca440dd06f96f9ba3fe7ac7d0775a4c2f2ad2dcfc24f9be79c63177048d
- verify_wrong_0011011_aligned_mixed_quarter.js: 3d3e75b47db1e4151decfdd126aa75f5bf056a0cd91f11ef84f8125c2cac2735
- wrong_0011011_aligned_mixed_quarter_arithmetic.json: ab3fa22ef1c504bd50d7128b2861dbd7cd8d2e80edc83308f85ad38bba9929a1
- WRONG_0011011_EDGE2_MIXED_QUARTER_STRIP_HAND_PROOF.md: a79ab9bc25cd0b62a7636fa14051068f92a16dafee4af326df1fedd930aa87d7
- verify_wrong_0011011_edge2_mixed_quarter_strip.js: dbe6ccfb0ad4c66ec6e2b50c1c1a598665b7c316e573733d6470342469dc8662
- wrong_0011011_edge2_mixed_quarter_strip_arithmetic.json: 252d444ed90416bdee7ffd462fce410aee3cced926658b3023d0e5d4a13bf717
