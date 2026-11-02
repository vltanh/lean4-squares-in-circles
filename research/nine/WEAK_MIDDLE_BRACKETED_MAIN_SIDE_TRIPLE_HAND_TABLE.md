# A wide main bracketed by a lower side original and the selected upper triple

November 2, 2026. Physical reduction for a complete finite-domain check.
The low-right cover has passed a complete independent exact C++ replay
and independent physical/formula/parity review. The low-floor cover is
still being produced; that consequence is not yet accepted. This note
does not declare the full mask closed.
No Lean or CI.

## 1. The unchanged original-square scope

Keep all nine original physical unit squares of the fixed 010/11 domain.
Write A,B,C,D for the horizontal main cone four-chain: its two outer
links are actual, and its middle link is weak. The designated outsider
cone triple is L,P,R with both links weak. Suppose its endpoints occupy
the actual side columns,

\[
 x_L\le-l,\qquad x_R\ge l,\qquad l=29/60.
\]

The accepted common routing permits one vertical reflection after which
P is above B,C, L is above B, and R is above C. Suppose additionally
that one of the remaining original outsiders S is on the left side and
below B:

\[
 x_S\le-l,\qquad y_S<y_B.
\]

This is exactly the original lower helper present when the full left side
has its main between its two outsiders and both selected endpoints are
side units. The ninth original square remains unrestricted. We retain
all original frames; no actual comparison between B and C is introduced.

The two target consequences are

\[
              y_R>3/5,\qquad y_P-h_P>1/10.          \tag{1}
\]

The low-right consequence is accepted; the low-floor consequence still
requires complete exact coverage. Each has its own full closed parameter
root. Neither target is assumed
in proving the other. In particular the low-floor reduction below does
not assume the low-right conclusion.

Write Q=1105/256, rho=91/60, u=13/12. As usual h is a coordinate
halfwidth, g=1/(4h), k=sqrt(1/2-h^2), and eta=h+g-1. Put
V=eta_B+eta_C. The common outer-actual-link reductions give

\[
 0\le V<1/30,\quad 1/2\le h_B,h_C<13/20,
 \quad |x_P|<23/60,\quad l\le -x_L,x_R<u.          \tag{2}
\]

The original S enters through the separately accepted physical theorem
`LOWER_SIDE_WIDTH_DEPENDENT_MAIN_HEIGHT.md`, which proves

\[
 y_B>f(h_B),\qquad
 f(h)=-2h/3+\max\{0,\min((h-1/2)/6,(27/50-h)/3)\}+1/400.       \tag{3}
\]

That theorem retains both original frames and every physical owner; its
3,387-leaf cover has an independent exact Fraction replay. Its center
band is a consequence of the current outer actual links, so (3) requires
no extra positional premise on B or S.

## 2. The full nine-parameter root and endpoint resources

Use the folded slopes of L,P,R, their three horizontal centers, the
actual left endpoint symmetric inset height, and the two main halfwidths:

\[
 (t_L,t_P,t_R,Z,x,X,c_0,h_B,h_C)
 \in[0,1]^3\times[l,u]\times[-23/60,23/60]\times[l,u]
 \times[c_*,1/2]\times[1/2,13/20]^2,               \tag{4}
\]

where Z=-x_L, x=x_P, X=x_R, and c_*=4421/12000. For each square,

\[
 a=(1+t^2)^{-1/2},\quad b=ta,\quad
 h=(a+b)/2,\quad k=(a-b)/2,
\]

and the two original signed frames are (a,sb),(-sb,a), s=±1. For a
main with given h use a=h+k and b=h-k. All five independent chirality
choices for B,C,L,P,R remain in the finite union.

The actual endpoint inset heights are c_0=g_A-|y_A| and
c_3=g_D-|y_D|. Put K=80669/93000 and

\[
 \psi(t)=\min\{a/2+19b/54,\ 1-a/2+b/18\}.
\]

The accepted universal physical-pair orientation tolls and the main span
give the common resources in Section 6 of
`WEAK_MIDDLE_BOTH_WEAK_COMMON_REDUCTIONS.md`:

\[
 V\le\min\left\{1/30,
 {27\over92}(451/810-Z+\psi_L),
 {27\over92}(451/810-X+\psi_R),
 {27\over92}(1-Z-X+\psi_L+\psi_R)\right\},         \tag{5}
\]

\[
 A_0\ge157/184+V+(27/92)(X-\psi_R),
\quad A_3\ge157/184+V+(27/92)(Z-\psi_L),          \tag{6}
\]

where A_0=-x_A-h_A, A_3=x_D-h_D. These tolls impose no shoulder-height
premise and do not use the five-square cap.

The endpoint reserve also gives

\[
 c_0,c_3\ge c_*+(32/9)V,
\qquad c_0+c_3\ge K+(32/9)V.                     \tag{7}
\]

For a live c_0 define

\[
 H_0=\min\{8/15,1/(4c_0)\},\quad
 J_0=H_0+\sqrt{1/2-H_0^2},
\quad A_0^{\max}=\min\{61/60,\sqrt{Q-(1-c_0)^2}-J_0\}.        \tag{8}
\]

Indeed c_0<=g_A bounds h_A by H_0, and h+k decreases with h.
The same actual outward-quadrant endpoint corner gives
\(A_0+h_A+k_A\le\sqrt{Q-(h_A+g_A-c_0)^2}\), so (8) is
an upper bound for the actual A_0. Its lower bound in (6) must not exceed
this upper bound.

There are two further lower bounds for c_3. The original two endpoint
corners and their span imply

\[
 \sqrt{Q-(1-c_0)^2}+\sqrt{Q-(1-c_3)^2}
                      \ge4-73/30000+V.           \tag{9}
\]

The right endpoint separately, using (6) and h_D+k_D>=29927/30000,
implies

\[
 \sqrt{Q-(1-c_3)^2}\ge
       157/184+V+(27/92)(Z-\psi_L)+29927/30000.     \tag{10}
\]

Solve (9),(10) for c_3, retaining their nonnegative square-root domains,
and combine them with (7). Write \(\underline c_3\) for the resulting
lower bound. The necessary inequality \(\underline c_3\le1/2\) is
retained. A negative radicand excludes the branch; no square root is
taken across a missing real domain.

## 3. Original main boxes and signed physical clearance

The actual horizontal main centers lie in

\[
 b_-:=h_B-A_0^{\max}\le x_B\le b_+:=1/60-g_B-\eta_C,
\]
\[
 c_-:=g_C+\eta_B-1/60\le x_C\le c_+:=61/60-h_C.   \tag{11}
\]

Retain both interval nonemptiness conditions. The original outer cones,
the endpoint height reserve, and the symmetric inset heights give

\[
 y_B\ge B_-:=\max\{f(h_B),\ g_B+\eta_C-199/120+(32/9)V,
                              c_0-121/60-b_+\},
\]
\[
 y_C\ge C_-:=\max\{g_C+\eta_B-199/120+(32/9)V,
                         \underline c_3+c_--121/60\}.        \tag{12}
\]

The two cone-budget lower bounds in (12), without f, can also be
vertically reflected to supply corresponding upper bounds. The third
terms follow from \(|y_E|\le g_E-c_E\le1/2-c_E\), the endpoint
center bound rho, and (11).

For two original unit squares with signed frames s and t, every owned
axis has the same support sum

\[
 \sigma(s,t)={1+|a_sa_t+s_ss_t b_sb_t|
                   +|s_sb_sa_t-s_ta_sb_t|\over2}\ge1.        \tag{13}
\]

Consider an original outsider F above an inner main M. Its signed
horizontal displacement lies in an interval d=[d_-,d_+] obtained from
(11). In all four uses here, F=P or the same-side selected endpoint,
the absolute horizontal gap is below 9/10<1. A separating normal with
nonpositive vertical component therefore has projection less than one
and cannot separate the physical pair. The complete upward owner list is

\[
 (s_Ma_M,b_M),\quad(-s_Mb_M,a_M),\quad
 (s_Fa_F,b_F),\quad(-s_Fb_F,a_F).                 \tag{14}
\]

An axis with zero vertical component is impossible by the same horizontal
gap bound. Each other owner requires

\[
 y_F-y_M\ge{\sigma-\max(n_xd_-,n_xd_+)\over n_y}.
\]

Take the minimum over (14). Also retain the original center-distance
bound \(\sqrt{\sigma^2-D^2}\), where D=max(|d_-|,|d_+|), and the
main-inset bound

\[
 g_M+\min\left\{h_F,{1/2+(g_M-D)b_F\over a_F},
                         {1/2+(g_M-D)a_F\over b_F}\right\}.  \tag{15}
\]

Terms with zero denominator are omitted. In (15), the horizontal inset
axis and wrong vertical signs are impossible because D-g_M<1/2; all
retained numerators are positive on the full root. The maximum of these
three independent lower bounds is denoted C(M,F). It preserves the
actual signed frames and is used with the same M chirality for both of
that main's selected outsiders. We do not minimize those chiralities
independently across the two pairs.

Thus the selected height bounds initially include

\[
 y_P\ge\max\{B_-+C(B,P),C_-+C(C,P)\},
\quad y_L\ge B_-+C(B,L),\quad y_R\ge C_-+C(C,R). \tag{16}
\]

## 4. Endpoint separation and all original selected corners

The original endpoints contain the rectangles

\[
 [-937/480,-503/480]\times[-c_0,c_0],
\quad[503/480,937/480]\times[-\underline c_3,\underline c_3].
\]

The inward horizontal edge can additionally be replaced by rho-c.
For a right-side selected unit with center X, set
\(E=\min(503/480,\rho-c)\) and \(\delta=X-E\).
If X+h<=E, retain its preceding lower height bound. Otherwise its
horizontal projection overlaps the endpoint rectangle. Define

\[
 r_+=\min\{h,(1/2+\delta b)/a\},\qquad
 r_-=\min\{h,(1/2+\delta a)/b\}.                 \tag{17}
\]

The complete rectangle/original-square separating-axis argument gives
either y>=c+r_s or y<=-c-r_{-s}, where s is the original chirality.
The zero-b limit omits the unavailable axis. If the preceding lower
bound plus c+r_{-s} is positive, the latter alternative is impossible;
then retain y>=c+r_s as well. Otherwise retain the preceding lower bound.
Horizontal reflection applies the same argument to L with chirality
-s_L. This is precisely the physical endpoint-rectangle reduction already
reviewed in `MIDDLE_MAIN_SIDE_CONE_TRIPLE_HAND_TABLE.md`; it needs only
the endpoint bands and the original side-unit domain, which are unchanged.

For every selected original square, its four actual corners give

\[
 y\le\min_j\left\{\sqrt{Q-(x+v_{j,x})^2}-v_{j,y}\right\},   \tag{18}
\]

where its signed corner offsets are
\((h,-sk),(sk,h),(-h,sk),(-sk,-h)\). The universal y<=rho bound
is also retained. A negative radicand excludes that branch. Reflection
uses the actual negative center of L. Write the resulting selected
height intervals as [L_-,L_+], [P_-,P_+], [R_-,R_+].

For the low-right root intersect R_+ with 3/5. For the low-floor root
intersect P_+ with h_P+1/10. These are separate complementary hypotheses.

## 5. The two selected separators share one P height

Write d_L=x+Z and d_R=X-x. The original cone/inset comparisons and
weak bits require

\[
 g_L+g_P\le d_L\le h_L+h_P,
\quad g_P+g_R\le d_R\le h_P+h_R.                 \tag{19}
\]

The weak boundaries are retained outward. For a horizontal cone pair
S,T, a genuine owned normal can always be chosen with nonnegative
horizontal component: if a separating owned axis points left, rotate it
through a right angle toward the displacement's horizontal cone. Both
unit-square supports are unchanged by that rotation, while the projection
does not decrease because dx>=|dy|. Thus the complete owner list is

\[
 (a_S,s_Sb_S),\ (b_S,-s_Sa_S),\
 (a_T,s_Tb_T),\ (b_T,-s_Ta_T).                   \tag{20}
\]

For each owner n, intersect -d<=E<=d with
\(n_yE\ge\sigma-n_xd\). This gives a closed allowed interval
\([e_-,e_+]\) for E=y_T-y_S; an impossible interval removes only
that owner. Zero vertical coefficients retain or reject the horizontal
alternative according to its original inequality.

For an LP owner, the possible P heights are consequently within
\([L_-+e_-,L_++e_+]\). For a PR owner they are within
\([R_--e_+,R_+-e_-]\). Intersect these two intervals with
[P_-,P_+] for every one of the 4×4 owner pairs. Each surviving interval
[p_-,p_+] concerns the same original P height and frame on both edges.

## 6. Retain the original weak middle physical pair

For each surviving P interval, (16) and the shoulder upper heights imply

\[
 y_B\le B_+:=\min\{p_+-C(B,P),L_+-C(B,L),
                  -(g_B+\eta_C-199/120+(32/9)V)\},
\]
\[
 y_C\le C_+:=\min\{p_+-C(C,P),R_+-C(C,R),
                  -(g_C+\eta_B-199/120+(32/9)V)\}.             \tag{21}
\]

The middle horizontal gap is at most
\(d_M=\min(c_+-b_-,h_B+h_C)\), and at least g_B+g_C.
The original main cone and (12),(21) confine its vertical difference to

\[
 \max(-d_M,C_--B_+)\le y_C-y_B
             \le\min(d_M,C_+-B_-).               \tag{22}
\]

Both main height intervals and (22) must be nonempty. At least one of
the four original B/C normals in (20) must have scalar projection at
least \(\sigma(B,C)\). Maximize its horizontal term over the retained
gap bound and its signed vertical term over (22). If all four upper
bounds are below \(\sigma(B,C)\), this original chirality and selected
owner-pair alternative is impossible.

This is a physical condition on the original weak pair. A computation
which replaces it only by dx>=g_B+g_C admits relaxed wide-inner poses;
those are not valid inputs to this reduction.

## 7. Exact finite coverage and current acceptance state

`discover_weak_middle_side_eight.cpp` is an untrusted floating interval
producer. It emits only a preorder binary tree: a tag 0,...,8 bisects the
corresponding interval of (4) at its midpoint, and tag 9 marks a rejected
leaf. The complete low-right tree has 594,539 nodes, 297,270 leaves,
maximum depth 32, and no remaining box.

`verify_weak_middle_side_eight.py` independently reconstructs (4), all
rational midpoints, every signed physical formula above, and all radical
enclosures with integer square roots and directed 80-bit dyadic arithmetic.
It imports no discovery code, accepts a leaf only after reconstructing a
strict negative necessary margin, and rejects missing subtrees, trailing
events, and unknown tags. No producer reserve is trusted.

The accepted low-right tree has also been completely reconstructed by
the separate exact implementation `verify_weak_middle_side_eight_exact.cpp`.
It uses directed 48-bit integer arithmetic, exact rational root endpoints,
and integer radical enclosures. Every one of the 297,270 leaves passed;
the least exact reserve is

\[
                       1559179356/2^{48}>1/200000.
\]

All four damaged controls were rejected. The independent physical and
formula review is `WEAK_MIDDLE_BRACKETED_SIDE_TRIPLE_INDEPENDENT_REVIEW.md`;
the exact port has its additional complete parity audit. The complete
replay report is `weak_middle_side_eight_low_right_cpp_replay.json`.
The readable Python evaluator's optional full repeat was stopped after
the complete exact C++ acceptance; no full Python repeat is claimed.

The low-floor discovery remains in progress. It will require its own
complete exact replay under the same reviewed reduction. There is no
change to the fixed mask ledger from this supporting theorem.
