# Actual-AB terminal with height variation 7/10 and bounded extra slope

This proves a conditional strengthening of the accepted `16/25` terminal.
The extra original I must additionally satisfy `|tan(theta_I)|<=1/2`.
It does not by itself close an original cell. All nine current originals
and the same fixed registers remain unchanged.

## Statement

Let A, B, I, D, E, F, G be seven distinct original physical unit squares,
with their own independent frames, disjoint open interiors, and every
corner contained in the disk of squared radius q. Put Q=1105/256.
Use canonical frame angles in [-pi/4,pi/4], alpha=cos(theta), beta=sin(theta),
and horizontal halfwidth h=(alpha+|beta|)/2. Suppose

- AB, EF and FG are actual horizontal projection links;
- theta_D>=0, y_G>=y_D and |x_G-x_D|<1;
- x_B<=x_I<=x_D;
- W=|y_I-y_B|+|y_D-y_I|<=7/10;
- the extra original frame satisfies |tan(theta_I)|<=1/2.

Then q>=Q. If q=Q, A, B, I and D are aligned and x_D-x_A=3.
In the unchanged original-nine `001/00` caller, its actual BC link,
original CD cone and strictly weak CD bit exclude this equality too.
Original C and H are retained throughout. The other original extra may
replace I by the same literal substitution already allowed in the source.

## Exact stronger scalar inequality

Reverse the selected row, so indices 0,1,2 denote D,I,B. The endpoint
angle theta_0 is nonnegative. For each adjacent physical pair choose its
actual original separating owner o_j in {j,j+1}, with both owner choices
retained. Set

    R_ij=(1+cos(theta_i-theta_j)+|sin(theta_i-theta_j)|)/2,
    T_g(0)=(55/64)|beta_0|-(119/92)(1-alpha_0),
    C=R_01/alpha_o0+R_12/alpha_o1+h_2-h_0+T_g(0)-2.

For each distinct selected owner k in {o_0,o_1}, the new complete table proves

    C >= (701/1000)|tan(theta_k)|,

strictly unless all three angles are zero. This is the same expression
as the earlier scalar theorem, now on the stated smaller domain of the
extra original. The full extra-slope interval still uses the accepted
641/1000 scalar coefficient and physical threshold 16/25.

Here is the full domain and certificate mechanism. Write
x_i=tan(|theta_i|/2), with sign of theta_0 positive and the other two
signs free. For D and B the physical half-angle range is contained in [0,29/70],
because 99^2=9801>9800=2*70^2. For I the extra slope premise gives
x_1<=sqrt(5)-2<17/72, since 161^2=25921>25920=5*72^2.
The complete box is therefore [0,29/70] x [0,17/72] x [0,29/70]. The common positive
denominator is D=product_i(1-x_i^4). Multiply the scalar difference
by 736000D. It is P_0+|P_1|+|P_2|. The separately reconstructed
polynomials retain degree at most four in each coordinate.

Each rational leaf gives integers w_1,w_2 in [-8,8], so

    8(P_0+|P_1|+|P_2|) >= 8P_0+w_1 P_1+w_2 P_2.

All degree-(4,4,4) Bernstein coefficients on that leaf are positive,
except for the origin coefficient on a leaf containing the origin.
That coefficient is exactly zero and the other 124 are positive.
Therefore the scalar inequality is strict at every nonzero point,
including every closed leaf boundary. The complete binary partitions
cover all four sign patterns, all four owner patterns, and every
selected owner: 28 domains, 127 leaves, 15,875 exact coefficients,
and no open frontier. The independent reconstruction uses Fraction
arithmetic and the physical frame dot products and determinants;
it imports no discovery module or numerical optimizer.

## Physical lifting

The accepted original endpoint caps give

    x_D-x_A-h_A-h_D+T_g(D)+T_u(A) <= 2,

strictly below Q. Here T_u(A)>=2|beta_A|/23>=0. The same D/G
guards force every genuine owned separator from D toward G to
have positive vertical component: otherwise its projection would
be less than 1 while the physical support sum is at least 1.
Thus the oriented endpoint cap has exactly the same hypotheses
as in the accepted 3/5 theorem. Its proof and universal A/E cap
are unchanged dependencies, byte-bound in PREMISE_BINDINGS.json.

On either remaining row link, let d be its nonnegative horizontal
gap and v its signed vertical gap. Then |v|<=7/10 and the disjoint
open half-unit incircles give d^2+v^2>=1. Since

    2*(7/10)^2=49/50<1,

we have d>|v| and d>0. Every actual forward owned axis therefore gives

    d >= R_ij/alpha_owner-|tan(theta_owner)|*|v|.

Backward normals cannot separate; their projection is at most |v|<1.
For a steep forward owned axis, alpha>=|beta| and d>|v| justify the
same upper projection bound as for the shallow axis. Thus no physical
axis, sign or owner has been discarded.

Actual AB contributes h_A+h_B with no height-variation charge. If
M=max(|tan(theta_o0)|,|tan(theta_o1)|), summing yields

    x_D-x_A-h_A-h_D+T_g(D)+T_u(A)
      >= 2+C-MW+T_u(A)
      >= 2+M/1000+T_u(A) >= 2.

This contradicts the strict cap below Q. At Q, strictness of the
scalar table forces D,I,B to align; T_u(A)=0 forces A to align.
Each remaining pair has vertical gap less than 1, so its aligned
physical separation is horizontal. The cap then forces x_D-x_A=3.

For the unchanged `001/00` caller, actual AB and BC plus the original
CD cone and inset separation give

    3=x_D-x_A >= h_A+2h_B+h_C+g_C+g_D
                 =1+2h_B+h_C+g_C >= 3,
    g_C=1/(4h_C),  h_C+g_C-1=(2h_C-1)^2/(4h_C)>=0.

Equality forces C aligned and x_D-x_C=1=h_C+h_D, contradicting the
strictly weak original CD bit. This handles the closed-Q equality
face analytically; it does not assume numerical clearance at Q.

## Conditional complement and application to A-c744

This threshold is available only where the extra original has certified
slope interval contained in [-1/2,1/2]. On that domain, once the D/G guards
and x_I<x_D are proved, the same five closed complement domains are
x_I<=x_B, y_D-y_B>=7/10, y_B-y_D>=7/10,
2y_I-y_B-y_D>=7/10, and y_B+y_D-2y_I>=7/10.
The absolute-value identity in the accepted proof supplies complete
coverage, including each equality face.

For the A-c744 original, the already closed old components 0,1,2,4 at
threshold 3/5 exclude the corresponding stronger domains. The remaining
central-slope case therefore has 2y_I-y_B-y_D>=7/10. A complete orientation
cover may use the three closed intervals [-1,-1/2], [-1/2,1/2], [1/2,1].
The outer intervals keep the full-angle 16/25 threshold; they cannot be
discarded or given the 7/10 threshold by this result. The shared endpoints
belong to both adjacent intervals.

The other original extra H may replace I literally, with the bounded
slope hypothesis applied to H. In particular, a guard must check the
selected extra original's certified slope bounds. It must not use B's or
D's bounds in their place. All nine originals, the 36 original corner and
pair conditions, actual links, strict CD, and frozen original paths remain
in the caller. This conditional theorem grants no original or mask credit.

## Reproduce

Run from this folder:

    python -B -S check_conditional_three_angle.py cover fresh_replay.json

The delivered EXACT_SCALAR_REPLAY.json records the fresh exact run.
No Lean, Lake or CI was run. The earlier 3/5 source and its proof
packets are unchanged.
