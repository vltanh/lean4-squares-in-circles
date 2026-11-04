# An actual outer link gives a full-angle two-link terminal

November 4, 2026. This is a new conditional geometric theorem. Its scalar
certificate has 28 complete domains, 103 leaves and 12,875 independently
reconstructed exact Bernstein coefficients. It makes no whole-original or
whole-mask claim without the stated caller and complete complement.

## 1. Physical theorem and original caller

Retain seven distinct physical unit squares A,B,I,D,E,F,G, with independent
frames, all physical pairs, and all corners in the disk of squared radius q.
Use the canonical signed angles in [-pi/4,pi/4], and put

\[
Q=1105/256,\quad h_j=(\alpha_j+|\beta_j|)/2.
\]

Assume the three actual projection links

\[
x_B-x_A\ge h_A+h_B,\quad
x_F-x_E\ge h_E+h_F,\quad
x_G-x_F\ge h_F+h_G.                                      \tag{1}
\]

Assume also

\[
\theta_D\ge0,\qquad y_G-y_D\ge0,\qquad |x_G-x_D|<1,       \tag{2}
\]

\[
x_B\le x_I\le x_D,\qquad
W:=|y_I-y_B|+|y_D-y_I|\le3/5.                            \tag{3}
\]

Then q>=Q. At equality, A,B,I,D are aligned and x_D-x_A=3.
There is no magnitude restriction beyond the canonical angle interval; D
has the sign required in (2). There is no variation term involving the
actual AB edge. Neither a common side for E,F,G nor a
shoulder condition on A,E is required.

For the unchanged original-nine 001/00 caller, retaining actual AB,BC,EF,FG,
all five original center cones, strictly weak CD, all nine frames, all 36
corners and all 36 physical pairs, (2)--(3) exclude closed Q too. Original
C and H remain physical throughout. Section 5 gives the equality blocker.

## 2. Two actual endpoint caps

It suffices to assume q<=Q. All owned separating normals from D toward G
have positive vertical component. In fact, if such a normal n had n_y<=0,
then (2) would give n.(c_G-c_D)<=|x_G-x_D|<1, whereas the support sum of two
unit squares in an owned unit direction is at least one. This is impossible.
The closed y condition causes no degeneracy: the same argument excludes
y_G=y_D under the strict horizontal guard.

Rotate coordinates by pi, sending D to the left and the separator downward.
The canonical angle of D is unchanged. The accepted oriented physical cap
therefore gives

\[
46[x_D-h_D]+\frac{27}{2}[x_G-h_G]+46T_g(D)\le\frac{211}{4},
\]

where

\[
T_g(D)=\frac{55}{64}|\beta_D|-\frac{119}{92}(1-\alpha_D).
\]

Apply the accepted universal endpoint cap to A,E in the original coordinates.
Its normalized toll T_u(A) is at least 2|beta_A|/23, hence nonnegative:

\[
46[-x_A-h_A]+\frac{27}{2}[-x_E-h_E]+46T_u(A)\le\frac{211}{4}.
\]

These are original-pair inequalities with both owners and all independent
frames retained. Both are strict if q<Q. Summing and using the actual EFG
chain, x_G-x_E-h_E-h_G>=2h_F>=1, gives

\[
x_D-x_A-h_A-h_D+T_g(D)+T_u(A)\le2,                       \tag{4}
\]

strictly if q<Q. The precise source proofs are
`ORIENTED_GOOD_ENDPOINT_TILT_TOLL_HAND_PROOF.md` and
`UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md`, already bound and independently
reviewed in the full_angle_common_side_row_v1 packet.

## 3. Only the two non-actual links pay for height variation

Reverse the selected row by the same pi rotation, and number D,I,B by 0,1,2.
Write their angles as theta_0,theta_1,theta_2, with theta_0>=0. Let

\[
R_{ij}=\frac{1+\cos(\theta_i-\theta_j)
                 +|\sin(\theta_i-\theta_j)|}{2}.
\]

For each of the two adjacent physical pairs, choose its genuine original
owned separator; its owner o_j belongs to {j,j+1}. Let d be the positive
horizontal center gap and v its signed vertical gap. The open half-unit
incircles give d^2+v^2>=1. Since |v|<=3/5 and 2(3/5)^2<1, we have d>|v|
and in particular d>0. A backwards horizontal normal cannot separate,
since its projection is at most |v|<1 while required support is at least one.
For either forward axis owned by o_j, its projection is at most
alpha_o d+|beta_o||v|: for the steep axis use alpha_o>=|beta_o| and d>|v|.
Thus the same actual pair satisfies

\[
d\ge R_{j,j+1}/\alpha_{o_j}-|\tan\theta_{o_j}|\,|v|.       \tag{5}
\]

There are all four owner patterns, with no lost axis, chirality or face.
The actual AB edge instead contributes h_A+h_B directly from (1), without
any vertical error. Define

\[
C=\frac{R_{01}}{\alpha_{o_0}}+
  \frac{R_{12}}{\alpha_{o_1}}+h_2-h_0+T_g(0)-2.           \tag{6}
\]

The exact scalar table proves, for each k in {o_0,o_1},

\[
C\ge\frac{601}{1000}|\tan\theta_k|,                       \tag{7}
\]

with strict inequality unless all three angles are zero. The remaining
original A is absent from this scalar statement; its nonnegative universal
toll was retained separately.

## 4. Scalar certificate, full domain, and exact positivity

Set x_i=tan(|theta_i|/2), z_i=s_i x_i, s_0=1 and s_1,s_2 independently plus
or minus one. The common rational box 0<=x_i<=5/12 contains the physical
range 0<=x_i<=sqrt(2)-1. Set

\[
D=\prod_{i=0}^2(1-x_i^4)>0.
\]

For an edge i,j and owner o, with its other endpoint r,

\[
\frac{R_{ij}}{\alpha_o}
=\frac{(1+z_i z_j)^2+(1+z_i z_j)|z_i-z_j|}
       {(1-x_o^2)(1+x_r^2)}.                            \tag{8}
\]

On the physical domain cosine differences are nonnegative. The rational
extension to the slightly larger box uses the right side of (8) directly;
its proof is an enlargement of the scalar domain, not an assumption about
angles outside the canonical range.

The other exact expressions are

\[
T_g(0)-h_0=\frac{-368+529x_0-1536x_0^2}{736(1+x_0^2)},
\qquad h_2=\frac{1+2x_2-x_2^2}{2(1+x_2^2)},
\qquad |\tan\theta_k|=\frac{2x_k}{1-x_k^2}.
\]

Multiply (7) by 736000D. Its left-minus-right is
P_0+|P_1|+|P_2|, three separately reconstructed polynomials of degree at
most four in each coordinate. Each leaf supplies two integers w_1,w_2
in [-8,8]. Therefore

\[
8(P_0+|P_1|+|P_2|)\ge8P_0+w_1P_1+w_2P_2.                \tag{9}
\]

The right side has all strictly positive degree-(4,4,4) Bernstein
coefficients on each recorded rational leaf box, with one exception:
when the leaf contains the origin, only the origin coefficient is zero;
all other 124 coefficients are strictly positive. Bernstein basis
nonnegativity proves (7), and proves its stated strictness away from the
origin. At any nonzero point of an origin leaf, a non-origin Bernstein
basis term is positive, including every closed box face.

The independent checker derives cosine numerators from original frame dot
products and sine numerators from determinants. It does not import the
producer. It uses rational Bernstein transforms distinct from the discovery
program's integer transforms, checks every literal coefficient and integer
minimum, and reconstructs each full binary partition. The 28 domains are
four sign choices times all four owner patterns and every distinct selected
owner. No frontier is accepted.

Delivered replay: `EXACT_SCALAR_REPLAY.json`, status
`PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER`: 103 leaves, 12,875 coefficients,
zero frontier. Reproduce with:

    python check_three_angle_cover.py cover_0601 EXACT_SCALAR_REPLAY.json

## 5. Physical conclusion and strict-mask equality blocker

Let M=max(|tan(theta_o0)|,|tan(theta_o1)|). From the actual AB edge, (5),
and the two-link variation W, the left side of (4) is at least

\[
2+C-MW+T_u(A)
\ge2+\left(\frac{601}{1000}-\frac35\right)M+T_u(A)
=2+\frac{M}{1000}+T_u(A)\ge2.                            \tag{10}
\]

This contradicts strict (4) below Q. At closed Q, strictness in the scalar
certificate forces all three frames D,I,B to align. Then C=0 and (10)
forces T_u(A)=0, so A aligns as well. Every selected row link now has
horizontal gap at least one: AB is actual, and each remaining vertical
gap is at most 3/5<1, so physical separation of its aligned squares must
be horizontal. Equation (4) then forces x_D-x_A=3.

Return to the unchanged nine-original 001/00 caller. Original AB and BC are
actual. The original CD center cone and its original inset separation give
x_D-x_C>=g_C+g_D, where g=1/(4h). Consequently

\[
3=x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D
=1+2h_B+h_C+g_C\ge3.
\]

Here A,D are aligned, h_B>=1/2 and
h_C+g_C-1=(2h_C-1)^2/(4h_C)>=0. Equality forces B,C aligned and
x_D-x_C=1=h_C+h_D, contradicting the retained strictly weak CD bit.
This uses the same original C and the exact CD comparison, including the
closed Q face; no numerical margin substitutes for equality handling.

## 6. Complete closed complement for the certified D821 original

Its freshly reconstructed and independently replayed whole-original state
proves (2), and x_I<x_D. Once those exact guards are bound, the complement
of (3) is covered by just these five closed domains:

1. x_I-x_B<=0;
2. y_D-y_B>=3/5;
3. y_B-y_D>=3/5;
4. 2y_I-y_B-y_D>=3/5;
5. y_B+y_D-2y_I>=3/5.

Indeed |u|+|v| is the maximum of its four signed sums. Each domain retains
all original nine-square and exact-mask hypotheses and can be solved using
its printed linear necessary row. Shared boundary faces are retained.
Neither this complement declaration nor the scalar theorem closes D821
until every declared complementary domain has a complete independent proof.
