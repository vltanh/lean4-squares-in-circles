# Independent audit of the complete core/low and low/low entries

Date: 2026-10-17 UTC.

**Result: PASS for both whole-domain entries.**

CORE_LOW_WHOLE_PAIR_HAND_PROOF.md proves the four-type cost bound
\(\mathcal C>.91\) for every core/low pair. It covers all sixteen
ordered source-axis branches and their retained target-axis images.
The independent review checked the complete angle and sign cover, the
core-corner loss estimate, the side cancellation with multiplier
\(g/\sin\phi\), both width formulas across \(\pi/2\), and the
directions of all five polynomial lower bounds. Its optional exact replay
passed 120 strict rational comparisons, including 47 displayed positive
Bernstein coefficients. A fresh temporary-directory replay reproduced
the arithmetic JSON byte for byte.

LOW_LOW_WHOLE_PAIR_HAND_PROOF.md proves the bound \(\mathcal C>.91\)
for every low/low pair. It covers all eight source-axis branches and their
retained target-axis images. The independent review checked both source
losses, the clipped target support, the impossible small-angle primary
branch, every coefficient in the remaining endpoint bounds, and complete
sign/angle coverage. In particular, the norm-squaring argument establishes
the required positivity before squaring. Its five fixed rows have
40 positive Bernstein coefficients, and all 36 additional strict rational
comparisons passed. A fresh temporary-directory replay reproduced its
arithmetic JSON byte for byte.

The reviewed proof-file SHA256 values are:

| File | SHA256 |
|---|---|
| CORE_LOW_WHOLE_PAIR_HAND_PROOF.md | 0d4ea9d15b63f269702e97e6b89b743993c6bb74c135768410eac80c4489b599 |
| LOW_LOW_WHOLE_PAIR_HAND_PROOF.md | 116a24b9ad572a2825acd5427197bf68488e4be3cf8b0caeed4f0e47ed8bb76a |

These are whole-domain frame-pair theorems. They use the earlier
common-point gap and retained-axis reductions, and **do not assume frame
concentration**. Thus they can be used to prove the upstream frame gate.
They are logically separate from the completed three-row quarter table,
which assumes that frame gate.

Together with CORE_CORE_WHOLE_PAIR_HAND_PROOF.md, three of the ten
unordered pair entries are now closed by hand, comprising 32 complete
ordered source-axis branches. Seven whole entries remain. The existing
five named strips cover parts of those remaining entries and do not count
as complete entries. The unrestricted hand proof remains active until
the rest of the frame theorem and the remaining word/candidate arguments
are supplied.
