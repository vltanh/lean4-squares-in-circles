# An explicit shoulder-tilt loss in the universal physical two-square cap

November 2, 2026. Complete hand reduction and exact one-variable table.
Computer discovery preceded this proof. A separate directed-integer replay
checks every one of the 511 strict finite rows. No Lean or CI.

## 1. The strengthened physical statement

Put

\[
 Q=1105/256,\quad r=\sqrt Q,\quad a=46,\quad b=27/2,
 \quad k=207/16,\quad T=211/4.
\]

Let M,B be two original physical unit squares with disjoint open interiors,
both contained in the closed disk of squared radius Q. Their frames are
independent and unrestricted. Fix any unit direction e, and write
\(h_S(v)=(|v\cdot u_S|+|v\cdot v_S|)/2\) for centered square support.
Define the folded shoulder sine by

\[
 \beta_B=\min\{|e\cdot u_B|,|e\cdot v_B|\}\in[0,1/\sqrt2].
\]

Then

\[
 \boxed{a[-e\cdot c_M-h_M(e)]
       +b[-e\cdot c_B-h_B(e)]+2\beta_B\le T.}
\tag{1}
\]

For a smaller radius the inequality is strict. This statement imposes no
center band, shoulder height, floor bound, endpoint frame restriction,
separator owner, or chain edge. It strengthens the original universal
physical pair cap solely by retaining the shoulder's actual orientation.

## 2. Physical support reduction

Use a signed separating unit normal n owned by M or B, so

\[
 n\cdot(c_B-c_M)\ge h_M(n)+h_B(n).
\]

Choose the perpendicular coordinate sign so that
\(n=(c,s)\), \(c\in[-1,1]\), \(s=\sqrt{1-c^2}\ge0\), with
\(e=(1,0)\). The support argument in Section 2 of
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`
gives the upper bound

\[
 H(c)-P_M-P_B
\tag{2}
\]

for the first two terms of (1), where

\[
 L_w(c)=\sqrt{w^2+k^2+2wkc},\qquad
 H(c)=r\{L_a(c)+L_b(-c)\},
\]

\[
 P_M=a h_M(e)+h_M(ae+kn)+k h_M(n),
\]

\[
 P_B=b h_B(e)+h_B(be-kn)+k h_B(n).
\]

For a smaller containing radius the corresponding bound is strictly below
(2). Thus it suffices to prove
\(H-P_M-(P_B-2\beta_B)\le T\) at the closed radius.

## 3. The augmented rectangle lemma has four frame candidates

The usual three-direction rectangle lemma interprets P_B as the sum of
the two side lengths of the rectangle enclosing the triangle with vertices
\(0,be,kn\), in the original frame of B. On every interval of frame
angles where the projected extremes and the folded-angle branch are fixed,

\[
                      P_B-2\beta_B=A\cos\theta+B\sin\theta.
\]

This function is positive: the first and third support terms alone give
\(P_B\ge(b+k)/2>13\), whereas \(2\beta_B\le\sqrt2<3/2\).
Its second derivative is therefore strictly negative on each such interval.
Its minimum is at an interval endpoint.

The projected-extreme endpoints are exactly the frames parallel to one of
the three triangle edges e,n,be-kn. The only additional folded-angle
endpoint is the frame at 45 degrees to e. The e-aligned folded endpoint
was already among the triangle-edge candidates. Quarter turns identify
the two descriptions of the 45-degree square frame. Hence there are four
candidate values, including every original B chirality.

For convenience define the original three candidate penalties by absolute
support expressions valid on the entire closed c interval:

\[
 E_w(c)=w+k\{s+\max(c,0)\},
\]

\[
 N_w(c)={w|c|+2ws+|wc+k|+k\over2},
\]

\[
 D_w(c)={L_w(c)^2+w^2+wkc+2wks+k|wc+k|\over2L_w(c)}.
\tag{3}
\]

These are the same E,N,D expressions as in the original pair-cap proof.
All denominators are positive since a,b>k. They can also be obtained
directly by evaluating the three support terms in the e-, n-, and
\(we+kn\)-aligned frames.

For the B candidates put

\[
 \beta_N=\min(|c|,s),\qquad
 \beta_D={\min(b-kc,ks)\over L_b(-c)}.
\tag{4}
\]

Here b-kc>0 because b>k. In the 45-degree frame,

\[
 P_{45}(c)={b+\max(b-kc,ks)+k\max(|c|,s)\over\sqrt2},
 \qquad 2\beta_{45}=\sqrt2.
\tag{5}
\]

Consequently

\[
 P_B-2\beta_B\ge
 \min\{E_b(-c),N_b(-c)-2\beta_N,
                   D_b(-c)-2\beta_D,P_{45}(c)-\sqrt2\}.
\tag{6}
\]

If M owns n, its exact penalty is N_a(c), and (6) applies to the independent
original B frame. If B owns n, its exact penalty is N_b(-c), its actual
folded sine is \(\beta_N\), and the unmodified rectangle lemma gives
\(P_M\ge\min(E_a,N_a,D_a)\). This covers every possible physical
separator owner, including ownership by both squares.

## 4. Five scalar inequalities suffice

The M-owned E_b entry is exactly the already proved universal scalar
inequality \(T-H+N_a+E_b(-c)\ge0\). The remaining requirements are
the following five lower bounds:

\[
 \begin{array}{ll}
 F_0=T-H+E_a(c)+N_b(-c)-2\beta_N,\\
 F_1=T-H+N_a(c)+N_b(-c)-2\beta_N,\\
 F_2=T-H+D_a(c)+N_b(-c)-2\beta_N,\\
 F_3=T-H+N_a(c)+D_b(-c)-2\beta_D,\\
 F_4=T-H+N_a(c)+P_{45}(c)-\sqrt2.
 \end{array}
\tag{7}
\]

We prove \(F_j\ge0\) on \([-1,1]\). Only F0,F1 meet zero at c=0;
their entire neighborhood is handled analytically below. The other three
rows are strictly positive on their complete closed intervals.

### 4.1. Exact analytic neighborhood of c=0

The original support identities give

\[
 H(0)=1105/8,\quad H'(0)=k/2,\quad H''(c)<0,
 \quad T=H(0)-(a+b+2k).
\]

Thus \(H(c)\le H(0)+(k/2)c\). Also \(s\ge1-c^2\),
and \(\beta_N\le|c|\). On \(|c|\le1/8\), the exact N branches
are the near-zero ones because \(1/8<k/a,k/b\). Substitution in (7)
gives, with x=|c|,

| Row and sign | Exact lower bound on the whole stated interval |
|---|---|
| F0, \(0\le c\le1/8\) | \((149/128)c\) |
| F0, \(-1/8\le c\le0\) | \((1877/128)x\) |
| F1, \(0\le c\le1/8\) | \((963/32)c\) |
| F1, \(-1/8\le c\le0\) | \((337/32)x\) |

For example the first coefficient is
\(k/2-2-(k+b)/8=149/128\); the remaining three are respectively
\(k/2+b-2-(k+b)/8\), \(a-k/2-2-(a+b)/8\), and
\(k/2+b-2-(a+b)/8\). They are all positive. These hand inequalities
include c=0 and both shared boundary points.

### 4.2. Complete exact table on the complement

`universal_pair_tilt_toll_cover.json` is a complete binary midpoint cover
of the following seven closed intervals. All leaves have a strictly
positive lower bound on the indicated F row. Every split retains both
closed children, including their common face.

| Row | Closed root interval | Strict leaves | Replayed lower bound at every leaf |
|---|---|---:|---:|
| F0 | \([-1,-1/8]\) | 12 | \(546970/10^6\) |
| F0 | \([1/8,1]\) | 71 | \(13295/10^6\) |
| F1 | \([-1,-1/8]\) | 17 | \(496498/10^6\) |
| F1 | \([1/8,1]\) | 15 | \(535035/10^6\) |
| F2 | \([-1,1]\) | 289 | \(162/10^6\) |
| F3 | \([-1,1]\) | 70 | \(19648/10^6\) |
| F4 | \([-1,1]\) | 37 | \(55676/10^6\) |

The cover has 1,015 nodes and 511 strict leaves, maximum depth 15.
`certify_universal_pair_tilt_toll.py` constructed it with exact Fraction
intervals and outward 80-bit square roots. It checks both the piecewise
E,N,D formulas and the equivalent absolute support expressions (3).

The separate verifier `verify_universal_pair_tilt_toll.py` imports neither
the producer nor its Fraction evaluator. It reconstructs every root and
midpoint child, and recomputes (3)--(7) using outward 64-bit integer dyadic
intervals. In particular N,D come directly from the absolute support
expressions. The verifier also reconstructs the four analytic-neighborhood
coefficients. The exact least reserve is

\[
                  2989620761972115/18446744073709551616>0.
\]

Certificate SHA256:
`b9930b443ad91e853d35087cccab68e822a2ba71dcf38654ccadca839512fe2d`.
The saved replay is `universal_pair_tilt_toll_replay.json`; four damaged
controls (root, split tag, scalar channel, and forged leaf) were rejected
in `universal_pair_tilt_toll_negative_controls.json`.

Combining Sections 4.1 and 4.2 proves all five scalar requirements (7).
Together with the inherited E_b requirement and the exhaustive physical
owner/candidate reduction, this proves (1).

## 5. Exact main-tilt resource for the pending middle-main caller

This is an application, not an extra hypothesis of the theorem. In an
actual four-chain let
\(A_0=-x_0-h_0\), \(A_3=x_3-h_3\),
\(e=h_1-1/2\), and suppose original left/right outsiders have reflected
horizontal center coordinates Z,X and original halfwidths hL,hR. Their
folded sines are bL,bR. Applying (1) to the two original endpoint/outsider
pairs gives

\[
 46A_0+(27/2)(Z-h_L)+2b_L\le T,
\]
\[
 46A_3+(27/2)(X-h_R)+2b_R\le T.
\tag{8}
\]

The existing actual-four bounds \(A_0+A_3\ge2+2e\) and
\(A_i<61/60\) therefore strengthen the caller's individual and summed
upper bounds on e to

\[
 e\le\min\left\{{1\over60},
 {27\over184}(451/810-Z+h_L)-{b_L\over46},
 {27\over184}(451/810-X+h_R)-{b_R\over46},
 {27\over184}(1-Z-X+h_L+h_R)-{b_L+b_R\over46}\right\}.
\tag{9}
\]

The adaptive opposite loads likewise become

\[
 A_0\ge\max\{59/60,157/184+(27/92)(X-h_R)+b_R/23\}+2e,
\]
\[
 A_3\ge\max\{59/60,157/184+(27/92)(Z-h_L)+b_L/23\}+2e.
\tag{10}
\]

These retain the same original shoulder frames as the corner and physical
pair tests in that caller. No orientation is replaced independently.
The seven-unit exclusion and the full actual-four mask still require their
own complete caller; the present result by itself changes no mask count.
