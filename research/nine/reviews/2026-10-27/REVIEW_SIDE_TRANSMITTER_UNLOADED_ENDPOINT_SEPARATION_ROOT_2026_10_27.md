# Root audit: unloaded endpoints of a side transmitter and its bypass

Date: October 27, 2026.

**Verdict: ACCEPT the entire radius-free one-endpoint theorem, its
two-endpoint physical separation corollary, and the full original
`M6.B6.PENTAGON.H2_D0.L134` join.** No whole H2_D0 or coarse-cell
closure or shared-ledger edit is inferred.

## 1. Frozen complete source and independent review

I read all of
`CHORDED_HEXAGON_SIDE_TRANSMITTER_BYPASS_UNLOADED_ENDPOINT_SEPARATION.md`,
SHA-256
`4a979638b562040455e3058351db24358e7ecb093e5c0c1635dcd6438492eecd`,
and the full separate review
`REVIEW_SIDE_TRANSMITTER_UNLOADED_ENDPOINT_SEPARATION_ROOTED_BLOCKS_2026_10_27.md`,
SHA-256
`0ee225e71d43495f66a126b382bffe3e75cc40d2c93d3031604dc69ebd047574`.

The entire `UNIT_BYPASS_NORMAL_CHANNEL.md`, including its actual
separating-axis proof in Section4, and the full original
`SIX_BODY_INNER_PENTAGON_LOAD_COVER.md` were reread directly.
The first has SHA-256
`db073cd024a4f2e763e7cd0a21bf5cb6a2a8be67069f3f9d3aff638b8a40b258`;
the second has SHA-256
`cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a`.

## 2. Full support and force calculations

The support-point inward-normal segment holds even for a side endpoint
or a variable common mean. The backward reach bound for n_x<0 follows
from the two actual orthogonal inward edges: at most one can increase
the horizontal coordinate, and its increase is at most |n_y|<1.
The side-support case gives the same bound for the entire interval.
The steep-normal forward reach c+d likewise covers both vertex and
side support; its monotonicity is used only on the proved range c<d.

Because the real bypass reaches the opposite endpoint x>=1, its normal
at A has n_x>=0. The full three-force unloaded equation makes the
external normal's horizontal component strictly negative. For aligned
A this already places the entire external unit strictly in x<0.

For oblique A, I reconstructed the complete feature cover. The bypass
can use only P, the actual upper side with its full mean interval, or
the upper vertex U. Its lower and opposite features fail the physical
upper-half-plane, diameter, or normal-sign constraints. The external
support is exactly W, V, or the entire side V+[0,1]u with normal v.
No feature at a limiting mean is discarded.

At coincident bypass and transmitter ports P, the complete torque
equation makes the external port a positive multiple of its normal.
The U and V cases contradict projections of the complete force
equation on the other own axis; only W remains and gives strict
half-plane separation. For the full A-owned upper-side feature, the
external v-side is excluded by force projection and the V point by
the sum of two strictly negative actual torques. The endpoints of
both mean intervals are included.

At the upper vertex, the actual bypass diameter first gives a<1/2
and b>a. The whole opposite-side external mean gives strict separation
directly. In the remaining V case the actual force and torque equations
give t=c/d<(b-a)/(a+b), then the forward reach gives

    (1+a)^2-2b^2=(3a-1)(a+1)<0,

so a<1/3. The full external force ratio gives
D0=b-a-bt>a(b-a)/(a+b)>a^2/b. The last comparison has numerator
1-2a^2-2ab>1/9. Hence |m_y|<b and the entire external unit again
has x<0. All denominators and strict signs were checked. The displayed
factorization was independently verified coefficientwise.

## 3. Both real endpoints and the exact original contradiction

The actual unloaded transmitter has reserve one by its real bypass.
The full transverse-separation theorem puts the bypass entirely on one
transverse side, allowing precisely the source's chart with both
unchanged endpoint means at the same height and 0<=k<=1. No contact
between transmitter and bypass, common frame for the endpoints, or
centered mean is assumed.

The one-endpoint theorem and its rigid reflection place the entire
two external squares in x<0 and x>1. They therefore cannot be the
same unit or have any closed physical contact. This is stronger than
the absence of a positive contact multiplier.

For H2_D0.L134 the unchanged roles are

    S=H, A=0, D=2, T=1, B=4, C=3.

H has its real two positive forces. Bodies0 and2 are genuinely
unloaded degree three with complete neighbor sets H,1,4 and H,1,3.
The original positive rim edge34 supplies the forbidden physical
intersection. The equations at loaded1,3,4 are neither needed nor
shortened. The graph-preserving reflection is already included by
the two-endpoint argument.

This is a complete radius-free exclusion with all actual means,
physical circle masks, zero individual weights, zero-stress physical
contacts and all three other packing units retained. No selected
normal is changed. The theorem cannot be applied to a higher-degree
endpoint by dropping one of its actual forces.

The exact arithmetic was checked alongside the sibling doubled-channel
and one-proper-diagonal reviews. No sampling, optimization, Lean
compilation, CI, remote action or shared-ledger mutation was used.
