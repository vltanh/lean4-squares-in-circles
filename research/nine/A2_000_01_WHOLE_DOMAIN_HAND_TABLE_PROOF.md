# Complete moving nine-square proof for 000/01 and its reversed mask

This proof closes the full fixed domain `000/01` from
`A2_COVERAGE_AND_CLOSURE_CONTRACT.md`. It retains all nine original
physical unit squares, all independent orientations, all corner
containment conditions and all physical nonoverlap conditions. The
reversed domain `000/10` follows by the contract's exact reversal.

The proof is a mathematical argument with exact finite tables. It uses
no Lean, Lake, CI, sampled-angle premise or numerical optimizer result
as a logical assumption. The strict-radius conclusion is complete.
Section 5 also excludes the strict-weak mask at the closed radius.

## 1. Exact statement and notation

Put

    Q=1105/256, r=sqrt(Q), a=46, b=27/2, K=207/16, T=211/4.

Suppose nine physical unit squares with pairwise disjoint open interiors
lie in the centered closed disk of squared radius at most Q. In one
orthonormal witness frame, four distinct squares M0,M1,M2,M3 form an
actual horizontal projection chain and a center-cone chain. Three other
distinct squares L,P,R form a center-cone chain, with L--P actual and
P--R strictly weak. Thus the designated gaps satisfy

    x_j-x_i >= |y_j-y_i|,

and the actual edges satisfy `x_j-x_i>=h_i+h_j`, while

    x_R-x_P<h_P+h_R.

Here h is the coordinate projection halfwidth of the original physical
square. The two remaining original squares F,G have no extra chain
hypothesis. Set g=1/(4h); the centered aligned square of halfwidth g is
contained in the corresponding original square.

We prove that this configuration is impossible. In particular its
strict-radius part is empty and has no unhandled boundary approach.

Write

    D=x_M3-x_M0-h_M0-h_M3.

The three actual main-chain comparisons give

    D>=2(h_M1+h_M2)>=2,     aD+b>=2a+b=2T.             (1)

All later uses of D refer to these same original endpoints.

## 2. Uniform routing from the original predicate

Section 1 of `A2_000_01_ATTEMPT.md` gives a complete routing argument,
using only the original actual and cone edges, physical nonoverlap, and
actual-four-chain geometry. After one common vertical reflection,
L,P,R all lie above both inner main centers. In this unchanged frame,

    -91/60<x_M0<-89/60,       89/60<x_M3<91/60,
    -31/60<x_M1<-29/60,       29/60<x_M2<31/60,
    1/2<=h_M0,h_M3<8/15,     1/2<=h_M1,h_M2<31/60,
    |y_M0|+|y_M3|<=1/8,
    -139/120<y_M1,y_M2<7/20,
    -13/12<x_L<-23/30,       23/30<x_R<13/12,
    -1/12<x_P<23/60.

The independent original-square refinements in
`WHOLE_MASK_SHOULDER_AND_NORMAL_REDUCTIONS.md` give

    25/32<y_L,y_R<21/16.                              (2)

The universal center-radius bound is `|c_S|<91/60`. The physical
adjacent-proxy barrier gives

    y_P-h_P>min(y_M1,y_M2)+869/1860.                    (3)

These are derived consequences of the entire fixed mask. No floor,
separator owner or extra-square placement has been added to its
hypotheses.

The complete source proofs for the geometric inputs are
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`,
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_INNER_CLEARANCE_HAND_PROOF.md`,
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`
Sections 1–6, `ADJACENT_PROXY_BARRIER_HAND_PROOF.md`, and the two
physical strip-cap hand proofs. The outsider-strip source includes a
self-contained derivation of the elementary four-chain bounds.

## 3. The complete high-floor five-square cap

The completed theorem
`UNRESTRICTED_JOINT_FIVE_SQUARE_HIGH_FLOOR_CAP.md` applies whenever an
original physical square U has

    |x_U|<=29/60,       y_U-h_U>=1/10,                 (4)

with original shoulders satisfying (2) and original main endpoints in
the preceding bands. These are five distinct original physical squares.
No cone comparison or actual horizontal link involving U and a shoulder
is required.

The theorem proves

    aD+b<=2T,                                         (5)

strictly if the original containing radius is less than r. For the
closed-radius statement, equality can occur only when both central
separating slopes vanish. This follows from the strict central transfer
away from its zero pair. That limited equality consequence is sufficient
for Section 5.

For clarity, its complete support argument retains U once. With actual
central normals `m_L=(-1,z_L)`, `m_R=(1,z_R)`, write

    p=(z_L)_++(z_R)_+, n=(-z_L)_++(-z_R)_+,
    C=H_U(m_L)+H_U(m_R)+(z_L+z_R)y_U.

The original outer pairs admit nonnegative row multipliers such that

    Phi_L+Phi_R<=2T+(29/2)p-16n,
    C>=1+(29/27)p-(32/27)n.

Adding the four genuine physical separating slacks gives

    aD+b<=b+Phi_L+Phi_R-bC<=2T.

The two linear slope costs cancel exactly because b=27/2. The four
outer tables and the central table cover every actual separator owner,
every permitted slope, every independent original frame and every
equality face. Their local and signed-sum complements are hand proofs.

## 4. Exhaustive floor split for the complete nine-square mask

### 4.1 The selected P already has the required floor

If `y_P-h_P>=1/10`, take U=P. Its routed x-band is contained in
`[-29/60,29/60]`; its center satisfies `3/5<=y_P<91/60`. Every other
hypothesis of Section 3 is already supplied by Section 2.
Thus (5) holds for the original endpoints.

### 4.2 The selected P has low floor

Suppose instead `y_P-h_P<=1/10`. The two cases overlap harmlessly at
equality; there is no omitted floor value.

The complete left and right side-extra barriers prove that every extra
square in either closed side strip lies below its corresponding inner
main. The one-sided physical main-height theorem then forces that inner
main above −7/20 whenever its side strip contains an extra.

The first complete table in
`BADFLOOR_INNER_MAINS_AND_CENTRAL_EXTRAS_EXACT_PROOF.md` proves

    y_M1,y_M2<-7/20.                                  (6)

Its crucial shared quantity is `W=1+h_R-h_P-(x_R-x_P)`. The actual
main span and the two original weighted endpoint caps imply

    h_M1+h_M2<=1+(27/184)W,
    g_Mi>=max(15/31,1/(2+(27/46)W)).

These dynamic original insets force a lower P/main clearance incompatible
with either `y_Mi>=-7/20`. The table retains original R corners,
original endpoint inset clearance and original P/R physical separation.

Combining (6) with the complete side barriers gives

    |x_F|,|x_G|<29/60.

Their physical main clearances and the main-height range place each
extra above both inner mains or below both. At most one can lie below
both: the reflected adjacent-proxy bound would put two such central
squares wholly below −9/20, contrary to
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md`.

Consequently at least one original central extra is above both mains.
The second complete table in the same manuscript proves that every
such extra has center strictly above P. It retains the full physical
P/extra four-axis separating alternatives, including both chiralities.
Thus some original extra U satisfies

    |x_U|<29/60,       y_U>y_P.                         (7)

The complete 356-leaf hand/table theorem
`CENTRAL_UPPER_EXTRA_WHOLE_FLOOR_HAND_TABLE.md` now gives

    y_U-h_U>1/10.                                     (8)

Its proof keeps the original physical L, P and U. It uses the actual
L--P link, original L/U center clearance and containment, and every
genuine P/U side-axis possibility. Its final section verifies precisely
the original five-square bands required by Section 3.

Therefore (5) also holds in this entire low-floor branch. Together the
two branches prove (5) over the full moving nine-square mask. For an
original radius less than r, it is strict and contradicts (1).

## 5. Closed-radius equality is incompatible with the weak P--R edge

Suppose the original radius is r. By (1) and (5), equality holds. The
strict central transfer in Section 3 forces z_L=z_R=0. The original
physical central separators are therefore horizontal, so the same
original L,U,R have actual projection-separated links. Put

    B=x_R-x_L-h_L-h_R.

These two actual links give B>=2h_U>=1. The two original weighted
physical endpoint caps give

    aD+bB<=2T=2a+b.

Since D>=2, both spans and both cap inequalities must be equalities:
D=2, B=1, and each physical pair cap equals T. The equality case of
Theorem 1 in
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`
therefore makes the original R square coordinate aligned. In particular
h_R=g_R=1/2. No endpoint-normal or U-frame classification is needed.

The original L--P actual edge and original P--R cone/inset comparison
then give

    B>=h_P+g_P>=1.                                    (9)

The preceding cap equality already gave B=1. Hence equality holds
throughout (9), so `h_P+1/(4h_P)=1`. With h_P>=1/2 this forces
`h_P=g_P=1/2`. The original cone/inset comparison now implies

    x_R-x_P>=g_P+g_R=1=h_P+h_R,

contradicting the designated strict-weak edge. This excludes the whole
mask even at closed Q. No complete equality classification of U, F or G
is required.

## 6. Finite acyclic assembly and complete certificate record

The proof dependencies can be ordered as follows. Each item uses only
earlier items and its own stated hand argument or complete table:

1. Physical support, inset and center-radius facts; the weighted physical
   two-square cap; the central and side strip-cap hand theorems.
2. Actual-four center bands, outsider strip, inner clearance, one-sided
   main-height bound, and adjacent-proxy barrier.
3. Uniform routing and shoulder bounds from the original mask.
4. Complete low-floor left/right side-extra barriers.
5. Dynamic main-inset table, central placement, upper-extra/P table.
6. Complete central-upper whole-floor table.
7. Complete four outer scalar envelopes and central transfer, using only
   original-square support and the stated fixed center bands.
8. The unrestricted joint cap, then Sections 4–5 of this assembly.

The exact finite tables used by this proof are:

| Component | Dimension | Strict interval leaves | Certificate |
|---|---:|---:|---|
| Left side extra above its main | 4 | 11,744 | `left_above_extra_certificate.json` |
| Either inner main at least −7/20 | 4 | 59,225 | `badfloor_mainheight_certificate.json` |
| Central upper extra at or below P | 5 | 62,000 | `central_upper_below_p_certificate.json` |
| Central U>P with floor at most 1/10 | 4 | 356 | `upper_extra_floor_certificate.json` |
| R-owned negative outer envelope | 2 | 1,700 | `outer_R_linear_negative_cover.json` |
| R-owned positive outer envelope | 2 | 490 | `outer_R_linear_positive_cover.json` |
| E-owned negative outer envelope | 1 | 25 | `E_variable_k_linear_negative_cover.json` |
| E-owned positive outer envelope | 1 | 28 | `E_variable_k_linear_positive_cover.json` |
| Central transfer | 2 | 1,684 | `central_linear_transfer_compact.json` |

There are 137,252 strictly verified interval leaves and 34 additional
central analytic leaves. Every complementary local domain is proved by
hand. Each prescribed root and every exact midpoint split is reconstructed
by an independent verifier; no pending or missing cell remains. The
certificates, exact replay reports and standalone checkers are in
`computer_assisted`. The optional P-height table and older fork or
separator-ownership covers are not dependencies of this proof.

Finally the contract's simultaneous coordinate and chain reversal sends
`000/01` to `000/10`, preserving all nine physical squares, their
original corners and all pairwise nonoverlap conditions. It therefore
proves the same closed-Q exclusion for that full reversed mask.
