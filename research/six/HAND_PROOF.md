# Six unit squares in a disk — hand proof

This is an **audited working draft**, not yet a complete proof of the \(n=6\) case.

The September 28 audit found three substantive defects.  Two are now repaired:
the invalid diagonal-reflection survivor shortcut has been replaced by direct
closures of Patterns 9,24,25,15, and the A2.3 support misuse has been replaced
by an exact cap/vertex analysis.

One substantive obligation remains: the n=6-specific **global normalization
theorem** must be proved rather than summarized.  Its exact sublemmas are
listed in §2.3 below.

The document below preserves the verified hand reductions while isolating
that remaining foundation explicitly. It contains no executable search or multidimensional numerical proof premise.
Every mathematical dependency needed for formalization is stated here.
Finite scalar endpoint inequalities are part of the hand argument and are
listed explicitly; they may later be discharged in Lean by elementary
trigonometric bounds.

The proof has two layers:

1. a concise end-to-end proof of optimality and uniqueness;
2. detailed A1/A2 lemmas giving the stresses, chamber reductions, and scalar
   inequalities used by the concise proof.

# Six unit squares in a disk — concise hand proof

## Theorem

Let six closed unit squares have pairwise disjoint interiors and lie in a
closed disk of radius \(R\). Define

\[
h={1\over\sqrt2},\qquad
A={1466+1940h\over267},\qquad
B={327+432h\over712},
\]

\[
s={2B\over A+\sqrt{A^2-4B}},\qquad
t=(-20+30h)s+{7\over2}-{9h\over2},
\]

\[
d={1\over2}+h-t,\qquad
q_*=2s^2+4s+{5\over2}.
\]

Then

\[
\boxed{R^2\ge q_*}.
\]

Equality is attained by the packing with centers

\[
C=(s,s),\quad
N=(s,s+1),\quad
E=(s+1,s),\quad
W=(s-1,t),\quad
S=(t,s-1),\quad
D=(-d,-d),
\]

where \(C,N,E,W,S\) are parallel and \(D\) is rotated by \(\pi/4\).
Moreover equality forces this packing up to the normalizing Euclidean
symmetries and relabeling.

Numerically,

\[
\sqrt{q_*}=1.688542968202\ldots .
\]

This file is the consolidated mathematical source.  The detailed A1/A2 hand
inequalities and the global survivor case split are included below as
appendices/sections; no deleted research note is a proof dependency.

## 1. Existence of the candidate

The displayed configuration is a packing. Its active outer corners satisfy

\[
q_*=(s+1/2)^2+(s+3/2)^2
    =(3/2-s)^2+(t+1/2)^2
    =2d^2+2hd+1/2.
\]

Hence six squares fit in radius \(\sqrt{q_*}\).

It remains to prove the lower bound and equality classification.

## 2. Normalize a hypothetical packing at or below the candidate radius

Assume

\[
R^2\le q_*.
\]

The already-formalized seven-square theorem implies that not all six squares
can avoid the disk center: otherwise six exterior squares together with a
small central square would contradict the seven-square exterior bound.
Pairwise disjointness shows that exactly one square contains the disk center.
Call it \(C\), put the disk center at the origin, and use the frame of \(C\)
as coordinates.

### 2.1. Existence and uniqueness of the central square

This step is already supported by the formalized \(n=7\) exterior theory.

First note that the candidate bounds give

\[
q_*<\frac{13}{4}.                                  \tag{N1}
\]

Suppose all six squares avoided the disk center \(O\). For each square \(S_i\),
disk containment gives

\[
\phi(\alpha(S_i,O),\beta(S_i,O))\le R^2\le q_*<13/4.
\]

Thus the six squares satisfy the hypotheses of the existing theorem
`Seven.six_exterior_ring`: they are pairwise interior-disjoint, exterior to
\(O\), and their chart states are admissible at the \(13/4\) target.

That theorem supplies, after one common rotation and a permutation, an
`ExteriorRing`. In particular one of the side squares is represented by the
axis-parallel unit square centered at \((1,-1/2)\). Its corner
\((3/2,-1)\) belongs to the closed square, and

\[
\left(\frac32\right)^2+1=\frac{13}{4}.             \tag{N2}
\]

This contradicts containment in a disk with \(R^2\le q_*<13/4\).
Therefore at least one square contains \(O\) in its open interior.

There cannot be two: if \(O\) belonged to the interiors of two distinct
squares, their open interiors would meet at \(O\), contradicting the packing
hypothesis. Hence there is a **unique** central square \(C\).

Translate \(O\) to the origin and rotate so that \(C\) is axis-parallel.
Reflect the coordinate axes if necessary so that

\[
C=(c_x,c_y),\qquad c_x,c_y\ge0.                    \tag{N3}
\]

### 2.2. Strict marker gaps for the five exterior squares

The five remaining squares are exterior to \(O\). Choose for each one a
sorted `SquareChart`. Since its farthest-vertex quantity is at most
\(R^2\le q_*<13/4\), `Seven.chart_admissible` makes every chart admissible.

For any two distinct exterior squares, the already-proved pair theorem
`Seven.marker_separation_closed` gives

\[
\operatorname{dist}(m_i,m_j)\ge\frac{\pi}{3}.      \tag{N4}
\]

In fact the inequality is strict at the present radius. If equality held,
orient the two markers so that the second is exactly \(\pi/3\) ahead of the
first. Then `Seven.ordered_chart_contact` says the two states form an
`OrderedContact`. By the definition of `OrderedContact`, at least one of the
two states is a `SideState`, namely

\[
a=1,\qquad u=\frac12.
\]

But then

\[
\phi(a,u)=\left(\frac32\right)^2+1=\frac{13}{4},
\]

contradicting \(\phi\le R^2\le q_*<13/4\). Thus

\[
\operatorname{dist}(m_i,m_j)>\frac{\pi}{3}         \tag{N5}
\]

for every pair.

Order the five markers cyclically and let \(g_1,\ldots,g_5>0\) be the five
successive angular gaps. By (N5),

\[
g_i>\frac{\pi}{3}.
\]

Since \(\sum_i g_i=2\pi\), for each \(i\)

\[
g_i
 =2\pi-\sum_{j\ne i}g_j
 <2\pi-\frac{4\pi}{3}
 =\frac{2\pi}{3}.                                  \tag{N6}
\]

Hence every consecutive marker gap lies strictly in

\[
\boxed{\frac{\pi}{3}<g_i<\frac{2\pi}{3}}.          \tag{N7}
\]

This theorem concerns the genuine `Seven.chartMarker`.  Once the normalization
package proves side-nearestness and axial-marker selection, (N20) identifies it
with the affine marker used in A2.

### 2.2A. Candidate-radius axial reserve

Put

\[
Q_0={142559\over50000}.
\]

The exact candidate calculation gives \(q_*<Q_0\).  Hence every exterior
Seven chart \((a,u)\) in a hypothetical packing at \(R^2\le q_*\) satisfies

\[
\phi(a,u)=(a+1/2)^2+(u+1/2)^2\le Q_0.              \tag{N8}
\]

We will need a quantitative strengthening of the Seven axial-label estimate.

**Lemma N8 (axial sum reserve).**  If the Seven label is axial,

\[
\ell(a,u)=\frac54u,
\]

then

\[
a+u<\frac{19}{20}+\frac{2\pi}{15}.                 \tag{N9}
\]

Equivalently,

\[
1+\frac{2\pi}{15}-a-u>\frac1{20}.                  \tag{N10}
\]

*Proof.*  Let \(S=a+u\).  Axial selection and the side-label inequality give
the Seven tie-line estimate

\[
9a+11u\le2\pi+7,
\]

hence

\[
u\le U(S):=\frac{2\pi+7-9S}{2}.                    \tag{N11}
\]

Suppose for contradiction that

\[
S\ge S_0:=\frac{19}{20}+\frac{2\pi}{15}.
\]

Since \(\pi<22/7<15/4\),

\[
S_0-\frac{2\pi+7}{10}=\frac14-\frac{\pi}{15}>0,
\]

so \(U(S)<S/2\).  As \(u\le U(S)\),

\[
\begin{aligned}
a^2+u^2
&=(S-u)^2+u^2\\
&\ge (S-U(S))^2+U(S)^2.                            \tag{N12}
\end{aligned}
\]

Indeed the difference is

\[
2(U(S)-u)(S-U(S)-u)\ge0.
\]

Therefore (N8) implies

\[
Q_0\ge F(S):=(S-U(S))^2+U(S)^2+S+\frac12.          \tag{N13}
\]

For \(S\ge S_0\),

\[
F(S)-F(S_0)
 ={(60S-57-8\pi)(6060S-1592\pi-2523)\over7200}\ge0, \tag{N14}
\]

because the first factor vanishes at \(S_0\) and the second is already
positive there:

\[
3234-784\pi>0
\]

from \(\pi<22/7\).

Finally

\[
F(S_0)-Q_0
 =-\frac{211\pi}{150}+\frac{52\pi^2}{225}
   +\frac{4021}{800}-\frac{142559}{50000}
 >\frac{3}{100}.                                   \tag{N15}
\]

For example, the left side is increasing for
\(\pi\ge 157/50\), and the standard rational bound
\(157/50<\pi\) gives the displayed weaker \(3/100\) margin directly.
Thus \(F(S)>Q_0\), contradicting (N13).  This proves (N9)--(N10). \(\square\)

The significance of (N10) is that the three Seven contact types at the
critical gap \(\pi/3\) all lie on the larger \(13/4\) boundary.  At the
candidate radius they acquire a uniform positive support reserve.  This is
the quantitative input for the strengthened marker-gap lemma below.

### 2.3. Remaining global-normalization theorem

The downstream proof uses a slightly stronger normalization package than the
coarse \(23/200\) core box.  The exact dependencies are listed here so that no
later stress silently imports a stronger bound.

Put

\[
\rho_0=\sqrt{Q_0-\frac14}-\frac12,\qquad
c_0=\rho_0-1=\sqrt{Q_0-\frac14}-\frac32.
\]

Numerically \(c_0\approx0.1128<23/200\).

For a candidate-sized packing with normalization (N3), it remains to prove:

1. **Coarse central core**
   \[
   0\le c_x,c_y<\frac{23}{200}.                    \tag{N16}
   \]

2. **Exterior chart bounds and side-nearestness**
   \[
   \frac{177}{200}<a<\frac{223}{200},\qquad
   |b|<\frac{117}{250},                            \tag{N17}
   \]
   and the nearest point to \(O\) lies on the relative interior of the near
   edge, never at a corner.

3. **Cyclic sector theorem.**  After a dihedral symmetry of \(C\), the five
   exterior primary directions occur in cyclic categories
   \[
   E,N,W,D,S.                                      \tag{N18}
   \]

4. **Five fixed open pins.**  The radius-\(9/10\) points at angles
   \[
   0,\quad \frac\pi2,\quad \frac{11\pi}{12},\quad
   \frac{5\pi}{4},\quad \frac{19\pi}{12}
   \]
   lie respectively in \(E,N,W,D,S\).               \tag{N19}

5. **Affine marker.**  The genuine Seven marker is on its axial branch, hence
   after restoring the chart sign
   \[
   \widehat\phi_i=\phi_i+\frac54 b_i,               \tag{N20}
   \]
   with the consecutive gaps from (N7).

6. **Central separator two-choice theorem.**  For each exterior square, the
   only canonical separators from \(C\) are the corresponding cardinal normal
   of \(C\) or the exterior square's own primary normal.  The cardinal choice
   is preferred on ties.                            \tag{N21}

7. **One helper per cardinal side.**  At most one exterior square can use any
   fixed cardinal side of \(C\).                    \tag{N22}

The following facts are then **derived consequences** of items 1--7 and must
be written down before A2 begins.

### 2.3A. Strong central-center bound actually used downstream

The A2 stresses use

\[
\boxed{0\le c_x,c_y\le c_0=\rho_0-1},              \tag{N23}
\]

not merely \(23/200\).

To derive it for \(c_x\), use the E-category helper from (N18).
If E uses the east cardinal separator, the cap-depth inequality gives its
radial chart coordinate at least \(1+c_x\).  If E uses own-primary, the same
inequality follows from the own-primary separator and the fact that its
primary direction lies in the E sector.  In either case the sharp
disk-containment cap bound is

\[
a_E\le \rho_0.
\]

Hence \(1+c_x\le\rho_0\), so \(c_x\le\rho_0-1\).  The N-category argument is
identical for \(c_y\).

This upgrade is essential: replacing \(c_0\) by \(23/200\) destroys several
tight A2.3 margins.

### 2.3B. Moving pins used by P4/P8

Besides the fixed radius-\(9/10\) pins, the later cardinal-helper lemmas use

\[
P_E=(1+c_x,0)\in E^\circ,\qquad
P_N=(0,1+c_y)\in N^\circ.                           \tag{N24}
\]

These follow from the E/N sector theorem, the corresponding cardinal/own
separator alternatives, and the cap-piercing argument.  They must be proved
explicitly before P4/P8.

### 2.3C. Cap-depth and opposite-pair angle bounds

The later A2 reductions also consume:

\[
|\theta|<\frac25
\quad\text{for every cardinal helper},             \tag{N25}
\]

and, for the two opposite cardinal pairs,

\[
|e|+|w|<4c_0,\qquad |n|+|s|<4c_0.                 \tag{N26}
\]

These are consequences of the moving pins, the cap-depth profile, and (N23).
They are part of the normalization output and not assumptions of A2.

### 2.3D. D-own normalization is derived, not independent

Once (N18), (N21), and (N22) hold, exactly two helpers occupy the west
categories W,D and at most one may use the west cardinal side.  Horizontal
reflection exchanges their cyclic positions while preserving all established
normalization facts.  Choose the labeling so that any west-cardinal helper is
W.  Therefore

\[
\boxed{D\text{ uses own-primary}.}                  \tag{N27}
\]

Thus the genuinely open geometric content is (N16)--(N22); (N23)--(N27) are
mandatory derived lemmas that must be present before the downstream A2 proof is
invoked.

Thus every packing is assigned one of 32 canonical five-bit central patterns,
with the \(D\) bit fixed to own in the final normalization.

## 3. Eliminate the forbidden central patterns: A2

The intended A2 elimination concerns the nine canonical patterns

\[
10,12,13,14,26,28,29,30,31.
\]

A2.1, A2.2, and A2.3 are hand-reduced below.  The A2.3 far-negative and bridge
arguments use the corrected exact cap/vertex support, and the fixed stress
coefficients needed for auditability are recorded in Appendix B.

### A2.1

Patterns \(10,14,26\) are reduced by fixed separating-axis classifications,
source-independent tail stresses, pair envelopes, and scalar
monotonicity/concavity. After center elimination every remaining stress is a
sum of one-variable functions of quantities such as

\[
w,\ s,\ d,\ d-w,\ d-s,\ s-w.
\]

Support-sign and cap/vertex walls are explicit. Coordinate and oblique-wall
curvature reduce each chamber to stated scalar edges or fixed vertices.

### A2.2

Patterns \(12,13\) split into the nonnegative-\(w\) branch R22-c and the
negative-\(w\) branch R22-d.

For R22-c, source reduction gives

\[
\Phi=A_u(n,w)+B_v(e,s)+D(w,s,\epsilon).
\]

The adjacent-pair envelopes force \(n=e=0\), derivative bounds force
\(w=s=0\), and the remainder is

\[
2m(d_*-1/\sqrt2)(1-\cos\epsilon)\ge0.
\]

For R22-d, hand D-edge stresses and pair coercivity remove every
noncandidate graph and then the final W-secondary/S-secondary graph.

### A2.3

Patterns \(28,29,30,31\) inherit a common hand D-edge classification,
including the source-independent hard D-secondary/S-secondary corner.
Universal S tails, positive-W and far-negative-W tails, transferred pair
reserves, and scalar middle-strip arguments finish the candidate graphs.

Therefore no multidimensional numerical value replay is a logical premise of
A2.

## 4. The seven central survivors

After A2, only

\[
8,\ 9,\ 11,\ 15,\ 24,\ 25,\ 27
\]

remain.

A diagonal reflection does exchange the geometric E/N and W/S roles, but the
global normalization has already used the available reflection to place D in
the chosen west-to-south angular half-range.  Reflecting a normalized packing
need not remain in that same D-angle domain.  Therefore the previous shortcut

\[
9\leftrightarrow10,\quad
24\leftrightarrow12,\quad
25\leftrightarrow14,\quad
15\leftrightarrow27
\]

cannot be used as a proof step under the present normalization.

Patterns 9,24,25,15 are therefore closed directly in §§4A--4B below; no
global diagonal-reflection transfer is used.

## 4A. Direct closure of Pattern 9

Pattern 9 has

\[
E_o,N_c,W_c,D_o,S_c.
\]

Its N/W adjacent pair is cardinal/cardinal, exactly as in Pattern 8.  Hence
the reflected Pattern-12 pair envelope gives, for every W--N source axis,

\[
A_u(n,w)\ge b(-w).                                      \tag{G9-1}
\]

The transferred source-independent tails first give \(-3/10<s<3/10\). On
the upper band

\[
1/6\le s<3/10,
\]

the bridge (BR1)--(BR16) closes the candidate graph directly, so no E/S pair
envelope is used outside its proved range.

It remains \(s<1/6\). There the E/S adjacent pair is E-own/S-cardinal,
exactly the Pattern-13 E/S pair. The A2.2 hand E/S envelope was proved
simultaneously for Patterns 12 and 13 and has the same lower equality profile:

\[
B_v(e,s)\ge b(s),                                      \tag{G9-2}
\]

where

\[
b(s)=
\begin{cases}
B_{Sp}(0,s),&s\le0,\\
B_{Es}(0,s),&s\ge0.
\end{cases}
\]

The C/W/D/S graph classification and source-independent tails depend on
neither E nor N and therefore transfer from Pattern 10 exactly as they do for
Pattern 8.  Every residual Pattern-9 candidate with \(s<1/6\) therefore satisfies the same
reduced inequality

\[
\Phi\ge F_9(w,s,\epsilon)
      :=b(-w)+b(s)+D(w,s,\epsilon).                 \tag{G9-3}
\]

This is identical to the Pattern-8 reduced function.  The same four scalar
derivative estimates give:

- \(w<0\): \(\partial_wF_9<-1/5\), so \(w\) moves to \(0\);
- \(w\ge0,s<0\): \(\partial_sF_9<-1/10\), so \(s\) moves to \(0\);
- \(w\ge0,s>0\): \(\partial_sF_9>1/20\), so \(s\) moves to \(0\);
- \(s=0,w>0\): \(\partial_wF_9>1/20\), so \(w\) moves to \(0\).

Thus every minimum reaches \(w=s=0\).  There

\[
F_9(0,0,\epsilon)
 =2m(d_*-1/\sqrt2)(1-\cos\epsilon)\ge0.             \tag{G9-4}
\]

Equality in the E-own/S-cardinal envelope would put E on the cardinal tie;
the cardinal-preferred convention assigns that tie to the cardinal branch.
Hence Pattern 9 is in fact strict and is impossible at the optimum.

This is a direct Pattern-9 proof and does not use diagonal reflection of the
global D-normalization.

## 4B. Direct closures of Patterns 24, 25, and 15

The remaining survivor transfers can be made **without reflecting the global
packing**.  Only a single E/N central bit changes, while the C/W/D/S geometry
and the relevant adjacent-pair lower envelope remain unchanged.

### Pattern 24 from Pattern 26

Pattern 24 is

\[
(E_c,N_c,W_c,D_o,S_o),
\]

while Pattern 26 is

\[
(E_c,N_o,W_c,D_o,S_o).
\]

All D--W/D--S graph classifications, tail stresses, and candidate-strip
reductions for Pattern 26 use only C,W,D,S, so they apply verbatim to
Pattern 24.

The only possible difference is the N/W pair.  For N-own/W-cardinal the
Pattern-26 proof uses the reflected Pattern-13 E/S envelope.  For
N-cardinal/W-cardinal the corresponding pair is the reflected Pattern-12
E/S envelope.  But the Pattern-12 and Pattern-13 hand source lemmas have the
same lower equality profile:

\[
B_v(e,s)\ge b(s)
\]

for every source axis.  Reflecting \((e,s)=(-n,-w)\) therefore gives in
**both** N-bit cases

\[
A_u(n,w)\ge b(-w).                                  \tag{G24-1}
\]

Hence the reduced Pattern-24 candidate function is literally the same
one-variable/pair function used in the Pattern-26 closure.  Every derivative,
curvature, boundary-face, and endpoint estimate transfers unchanged.
Therefore Pattern 24 is terminal directly.

### Pattern 25 from Pattern 27

Pattern 25 and Pattern 27 have identical E,W,D,S bits:

\[
25=(E_o,N_c,W_c,D_o,S_o),\qquad
27=(E_o,N_o,W_c,D_o,S_o).
\]

Again all C/W/D/S graph and tail reductions are identical.  The N/W pair
lower envelope is \(b(-w)\) for either N bit by the same Pattern-12/13
argument (G24-1).  The E-own/S-own pair is identical in Patterns 25 and 27.

Thus every reduced inequality in the direct Pattern-27 closure applies
verbatim to Pattern 25.  Pattern 25 is terminal directly.

### Pattern 15 from Pattern 14

Pattern 15 and Pattern 14 have identical N,W,D,S bits:

\[
15=(E_o,N_o,W_o,D_o,S_c),\qquad
14=(E_c,N_o,W_o,D_o,S_c).
\]

All C/W/D/S D-edge classifications and candidate tails from Pattern 14
therefore transfer unchanged.

The E/S pair is the only changed datum.  Pattern 14 uses the
E-cardinal/S-cardinal Pattern-12 envelope; Pattern 15 uses the
E-own/S-cardinal Pattern-13 envelope.  The complete A2.2 E/S source
comparison proves the same lower profile \(b(s)\) for both central
descriptions.  Hence the Pattern-14 pair-factorized candidate inequality,
including its positive- and negative-\(w\) scalar reductions, is unchanged.

Therefore Pattern 15 is terminal directly.

These three arguments alter only the local adjacent-pair envelope and never
reflect the normalized D sector.  Consequently Patterns 24,25,15 are closed
within the fixed global normalization.

## 4C. W-cardinal / S-cardinal bridge

This is the bridge used later by Patterns 8, 9, and 11. It depends only on
\(C,W,D,S\), so it is independent of the E/N bits and of both adjacent-pair
source axes.

Assume the candidate D-edge graph

\[
D\!-\!W=W\text{-secondary},\qquad
D\!-\!S=S\text{-secondary},
\]

and

\[
-\frac25\le w\le\frac25,\qquad
\frac16\le s\le\frac3{10},\qquad
\frac12\le d\le\frac\pi4.                         \tag{BR1}
\]

Use the fixed C/W/D/S stress

\[
(\mu_{CW},\mu_{SC},\mu_{CD},\mu_{DW},\mu_{DS})
 ={1\over1000}(277,319,4,193,207).                 \tag{BR2}
\]

The coefficients are nonnegative and sum to one. In the local frames the
three exterior forces are

\[
G_W=-{277\over1000}e_x+{193\over1000}(-f_W),
\]

\[
G_S=-{319\over1000}e_y+{207\over1000}f_S,
\]

\[
G_D={4\over1000}e_D
     -{193\over1000}(-f_W)-{207\over1000}f_S.      \tag{BR3}
\]

The central force is

\[
G_C={277\over1000}e_x+{319\over1000}e_y
       -{4\over1000}e_D,
\]

whose two coordinates are positive on (BR1). Hence its exact rectangular
support is \(c_0(G_{Cx}+G_{Cy})\).

For W and S, direct local resolution gives

\[
(G_W\!\cdot e_W,G_W\!\cdot f_W)
 =\left({277\cos w\over1000},
        -{193+277\sin w\over1000}\right),          \tag{BR4}
\]

\[
(G_S\!\cdot e_S,G_S\!\cdot f_S)
 =\left({319\cos s\over1000},
        {207-319\sin s\over1000}\right).           \tag{BR5}
\]

Alternating Taylor bounds on (BR1) give

\[
2R_*V_W-\|G_W\|>{1\over100},\qquad
2R_*V_S-\|G_S\|>{1\over20}.                        \tag{BR6}
\]

Thus both W and S are on the exact vertex-support branch throughout the
bridge.

For D,

\[
X_D={4\over1000}
 +{193\over1000}\sin(d-w)
 +{207\over1000}\cos(d-s),                         \tag{BR7}
\]

\[
Y_D={193\over1000}\cos(d-w)
 -{207\over1000}\sin(d-s).                         \tag{BR8}
\]

On (BR1),

\[
X_D>{1\over5},\qquad X_D-|Y_D|>{3\over50}.         \tag{BR9}
\]

Hence \(X_D\) is always the dominant component; the only D-support wall is

\[
2R_*|Y_D|=\sqrt{X_D^2+Y_D^2}.                      \tag{BR10}
\]

Use the exact cap formula on one side and the exact vertex formula on the
other. As in (A23V0)--(A23V6), the two values and first derivatives agree at
(BR10).

After substituting (BR3)--(BR10), the stress defect is a sum of scalar terms
in

\[
w,\quad s,\quad d,\quad d-w,\quad d-s,\quad s-w.
\]

Split only at \(w=0\), \(Y_D=0\), and the support wall (BR10). Direct
differentiation, bounded by the same alternating Taylor inequalities used
throughout Appendix B, gives on every resulting chamber

\[
\Phi_{ww}<-{1\over20},\qquad
\Phi_{ss}<-{1\over20}.                              \tag{BR11}
\]

Because the support wall is \(C^1\), no hidden coordinate minimum occurs
there. Thus every minimum reduces to

\[
w\in\{-2/5,0,2/5\},\qquad
s\in\{1/6,3/10\}.                                  \tag{BR12}
\]

There remain six scalar \(d\)-edges. Splitting each only at its D support
switch and applying alternating Taylor bounds gives, in the lexicographic
order of (BR12),

\[
\Phi>
{3\over100},\quad
{4\over100},\quad
{1\over1000},\quad
{1\over100},\quad
{3\over100},\quad
{4\over100}.                                      \tag{BR13}
\]

For completeness, the only tight edge is \(w=0,s=1/6\). On its vertex
piece the scalar function is concave and both endpoints exceed \(1/500\).
On the cap piece,

\[
\Phi''(d)>{1\over20}.                              \tag{BR14}
\]

At \(d=17/25\), direct Taylor bounds give

\[
\Phi(17/25)>{7\over5000},\qquad
|\Phi'(17/25)|<{1\over20000}.                      \tag{BR15}
\]

The tangent-parabola estimate from (BR14) therefore gives

\[
\Phi(d)>
{7\over5000}
 -{(1/20000)^2\over 2(1/20)}
>{1\over1000}.                                    \tag{BR16}
\]

This proves the bridge (BR1) directly by scalar calculus. The archived file
`check_A2_survivor_WcSc_bridge.py` at commit
`b51d8a88c30588e279882b8efd5441304635f527` is retained only as an
independent exact arithmetic audit of this hand reduction.

## 5. Pattern 27

Pattern 27 is

\[
E_o,N_o,W_c,D_o,S_o.
\]

### Transfer of the complete D-edge classification

The complete Pattern-26 D-edge classification above uses only \(C,W,D,S\).
Therefore every Pattern-27 noncandidate D-edge graph is eliminated by the
same fixed stresses, with the same scalar curvature reductions. The sole
survivor is

\[
D\!-\!W=W\text{-secondary},\qquad
D\!-\!S=S\text{-secondary}.                     \tag{G27-1}
\]

The Pattern-26 negative-W candidate stress (P26-6) uses only \(C,W,D,S\)
and therefore closes

\[
-2/5\le w\le-1/6,qquad -1/6\le s\le1/2.         \tag{G27-2}
\]

The Pattern-26 outer S-tail stresses also transfer.  For Pattern 27 they can
be extended farther, still source-independently.  On the full remaining W
range use

\[
s\le-2/25:\quad (271,315,10,203,201)/1000,
\]

\[
s\ge11/25:\quad (222,491,19,137,131)/1000.       \tag{G27-3}
\]

With exact cap/vertex support the W,S,D forces have fixed dominant
components on these two chambers.  After the natural support/sign walls,
coordinate concavity reduces each stress to fixed scalar edges, all strictly
positive. Hence every survivor lies in

\[
-1/6\le w\le2/5,qquad
-2/25\le s\le11/25.                              \tag{G27-4}
\]

### Own-own E/S pair

For \(s\le0\), reflect the positive own-own N/W envelope from Pattern 14.
It agrees exactly with the Pattern-26 E-cardinal/S-own equality profile
\(b(s)\). Thus the Pattern-26 scalar closure applies on this half.

For \(s\ge0\), reflect the full negative-W own-own reserve (P14-9). This
gives, for every E/S source axis,

\[
B_{ES}(e,s)\ge B_*+{73\over100}s.                 \tag{G27-5}
\]

The N/W envelope is the same profile \(a(w)\) whether N is cardinal or own;
only its equality source changes. The Pattern-26 w-calculus is independent
of the E/S term:

- if \(w<0\), \(a'(w)<-9/10\) and \(D_w<4/5\), so w moves to zero;
- if \(w\ge0\), the total w-curvature is negative, so only
  \(w=0\) and \(w=2/5\) remain.

At \(w=0\), the \(s\ge0\) inequality is exactly the scalar Pattern-29
positive-s face; its cap and vertex pieces are nonnegative and equality
would require \(s=0\).

At \(w=2/5\), subtract the equality value at \((0,0,0)\). The remaining
one-dimensional inequality is

\[
[a(2/5)-a(0)]+{73\over100}s
 +D(2/5,s,\epsilon)-D(0,0,0)>{1\over25}           \tag{G27-6}
\]

for

\[
0\le s\le11/25,qquad 1/2-\pi/4\le\epsilon\le0.
\]

On the cap branch this is bounded by alternating Taylor polynomials; on the
negative-vertex branch the same bound follows after the exact switch. The
two formulas agree at the switch, so there is no omitted wall minimum.

The archived files `check_A2_survivor_WcSo_tails.py` and
`check_A2_survivor_EoSo_scalar.py` at
`b51d8a88c30588e279882b8efd5441304635f527` independently audit
(G27-3) and (G27-6).

Therefore Pattern 27 is terminal. Pattern 25 inherits this closure directly
through its identical \(C,W,D,S\) data and identical N/W lower envelope, as
proved in §4B. Pattern 15 is closed separately through Pattern 14; no global
diagonal reflection is used.

## 6. Pattern 11

Pattern 11 has

\[
E_o,N_o,W_c,D_o,S_c.
\]

The Pattern-10 D-edge classification and noncandidate exclusions transfer,
leaving only

\[
D\!-\!W=W\text{-secondary},\qquad
D\!-\!S=S\text{-secondary}.
\]

The Pattern-10 source-independent tails remove

\[
s\le-3/10,\qquad
s\ge3/10,\qquad
w\le-1/6\quad(|s|\le3/10).
\]

The W-cardinal/S-cardinal bridge removes

\[
1/6\le s\le3/10.
\]

On the remaining strip,

\[
-1/6\le w\le2/5,\qquad
-3/10<s\le1/6,
\]

both adjacent pairs have the same own/card profile \(a\), so

\[
\Phi\ge a(w)+a(-s)+D(w,s,\epsilon).
\]

The scalar derivative bounds are

\[
a'(w)<-9/10\quad(-1/6<w<0),\qquad
a'(w)>-2/5\quad(0<w<2/5),
\]

and on the reflected small strip the stronger estimate

\[
a'(x)<-1\quad(-1/6\le x<0).
\]

For the diagonal term,

\[
D_w<4/5\quad(w<0),
\]

\[
D_s<-1/2\quad(w\ge0,\ s<0),
\]

\[
D_s>-19/20\quad(w\ge0,\ 0<s\le1/6),
\]

\[
D_w>9/20\quad(w\ge0,\ s=0).
\]

Consequently \(w<0\) moves to \(0\), then \(s<0\) moves to \(0\), and
\(s>0\) also moves to \(0\). Finally positive \(w\) moves to \(0\).

At \(w=s=0\),

\[
\Phi=2m(d_*-1/\sqrt2)(1-\cos\epsilon)\ge0.
\]

Equality would put both own/card pairs on a cardinal tie, forbidden by the
cardinal-preferred canonical rule because Pattern 11 has E and N own.
Therefore Pattern 11 is terminal.

## 7. Pattern 8: hand closure

Pattern 8 is

\[
E_c,N_c,W_c,D_o,S_c.
\]

The Pattern-10 C/W/D/S classification and source-independent tails transfer
unchanged.  Hence every survivor is on the candidate D-edge graph

\[
D\!-\!W=W\text{-secondary},\qquad
D\!-\!S=S\text{-secondary},
\]

and lies in

\[
-\frac16<w\le\frac25,\qquad
-\frac3{10}<s<\frac16.
\]

The E/S pair is exactly the Pattern-12 cardinal/cardinal pair.  Its complete
hand envelope gives

\[
B_v(e,s)\ge b(s)
\]

for every S--E source, where

\[
b(s)=
\begin{cases}
B_{Sp}(0,s),&s\le0,\\
B_{Es}(0,s),&s\ge0.
\end{cases}
\]

Reflecting the same cardinal/cardinal pair by

\[
(e,s)=(-n,-w)
\]

gives, for every W--N source,

\[
A_u(n,w)\ge b(-w).
\]

Thus

\[
\Phi\ge F_8(w,s,\epsilon)
=b(-w)+b(s)+D(w,s,\epsilon).
\]

The previously established scalar inequalities are

\[
b'(x)<\frac25\qquad(-2/5<x<0),
\]

\[
b'(x)>1\qquad(0<x<1/6),
\]

and

\[
D_w<\frac45\quad(w<0),
\]

\[
D_s<-\frac12\quad(w\ge0,\ s<0),
\]

\[
D_s>-\frac{19}{20}\quad(w\ge0,\ s>0),
\]

\[
D_w>\frac9{20}\quad(w\ge0,\ s=0).
\]

Therefore:

- if \(w<0\),
  \[
  \partial_wF_8<-1+\frac45=-\frac15,
  \]
  so \(w\) moves to \(0\);

- with \(w\ge0,s<0\),
  \[
  \partial_sF_8<\frac25-\frac12=-\frac1{10},
  \]
  so \(s\) moves to \(0\);

- with \(w\ge0,0<s<1/6\),
  \[
  \partial_sF_8>1-\frac{19}{20}=\frac1{20},
  \]
  so \(s\) again moves to \(0\);

- at \(s=0,w>0\),
  \[
  \partial_wF_8>-\frac25+\frac9{20}=\frac1{20},
  \]
  so \(w\) moves to \(0\).

Consequently every Pattern-8 minimum reaches \(w=s=0\).  There

\[
F_8(0,0,\epsilon)
=2m(d_*-1/\sqrt2)(1-\cos\epsilon)\ge0.
\]

Equality requires \(\epsilon=0\), and equality in the two pair envelopes
forces \(n=e=0\) and the candidate equality source axes.

It remains only to read equality in the stress construction.  Every
containment weight in the Pattern-8 equality stress is positive.  Therefore
equality in the weighted containment sum forces each selected active vertex
to lie on the circle.  Equality in each completed square forces the center to
be the unique optimizer for its induced force, while equality in every
positive separator multiplier forces the corresponding separating-axis
inequality to be tight.  With (n=e=w=s=epsilon=0), those linear equalities
are exactly

\[
N=C+(0,1),\qquad E=C+(1,0),
\]

\[
W=(C_x-1,t),\qquad S=(t,C_y-1),
\]

and the two diagonal contacts give (D=(-d,-d)).  The active-circle
equalities for N and E then give (C_x=C_y=s); the W/S equality gives the
displayed value of (t).  Hence every equality configuration is the candidate
in the normalized frame.

Thus Pattern 8 and its equality case are closed directly; no separate
local-rigidity theorem is a logical premise.  The independent fixed-point
audit is not a proof dependency.

## 8. Conclusion

Every packing at or below the candidate radius enters a canonical central
pattern.

- A2 eliminates the nine forbidden canonical patterns by hand chamber
  reductions with exact scalar support.
- Patterns 9,11,15,24,25,27 are terminal by the direct arguments above.
- Pattern 8 has the hand scalar closure and direct equality analysis.
- the sole remaining proof obligation is the global normalization theorem in
  §2.3.

After that remaining theorem,

\[
R^2\ge q_*
\]

follows, and the strictness/equality statements in the case reductions force
every equality packing to be congruent to the displayed candidate
configuration.

Accordingly this document is an audited proof draft with one open
mathematical obligation: the global normalization theorem of §2.3.


# Appendix A — west-category normalization (A1)

This appendix gives the explicit stress proof that the later west-category
square cannot use the west cardinal side in the original sector
normalization.

## Statement

Work in the global normalization already established for the n=6 problem:

- the disk center is 0;
- the central square C uses the coordinate axes;
- c_x,c_y >= 0;
- the five exterior squares have cyclic primary order E,N,W,D,S;
- R^2 <= Q0 := 142559/50000.

Then D cannot use the west cardinal separator from C.

Since at most one exterior square may use a given central side, if D were
west-cardinal then W would necessarily use its own-primary separator.

This lemma is the A1 obligation in the Lean roadmap.

## Angle domain

Write the W and D primary directions as

    phi_W = pi + t,
    phi_D = pi + u,

with t <= u from the cyclic primary order.

If W uses its own-primary separator and t <= -2/3, the radial coordinate a_W
must satisfy

    a_W >= 1/2 + (3/2-rho0) cos(2/3) + (1/2) sin(2/3) > rho0,

where

    rho0 = sqrt(Q0-1/4)-1/2.

This contradicts the universal center bound a_W <= |p_W| <= rho0. Hence

    t > -2/3.

If D uses the west cardinal side, the sharp cap-depth formula gives

    |u| < 2/5.

Indeed the minimum west-side depth is 3/2-rho0, whereas at deviation 2/5

    B_Q0(2/5)
      = sqrt(Q0) - cos(2/5) - sin(2/5)
      < 3/2-rho0.

Therefore every hypothetical A1 configuration lies in the compact
two-angle triangle

    -2/3 < t <= u,
    -2/5 < u < 2/5.

The exact checker uses the closed rational superset

    -2/3 <= t <= 2/5,
    -2/5 <= u <= 2/5,
    t <= u.

The two scalar margins are respectively about

    0.0006493555
    0.0091181744.

## Three-separator stress

Let

    e(t)=(-cos t,-sin t),
    f(t)=( sin t,-cos t).

Assume D is west-cardinal and W is own-primary. We have two central
separations:

    (-1,0) dot (p_D-p_C) >= H_D,
    e(t) dot (p_W-p_C)  >= H_W,

where

    H_D = [1+cos u+|sin u|]/2,
    H_W = [1+cos t+|sin t|]/2.

By the separating-axis theorem, W and D are separated on one of

    +/- e(t), +/- f(t), +/- e(u), +/- f(u).

For a directed chosen W-to-D normal n,

    n dot (p_D-p_W) >= H_WD,

with

    H_WD = [1+cos(u-t)+sin(u-t)]/2,

because 0 <= u-t <= 16/15 < pi/2.

## Hand proof of the two-angle stress

Let

    r = sqrt(Q0),
    c0 = rho0-1,
    kappa = 1/2-c0.

The scalar bounds used below are

    r < 17/10,
    0 < c0 < 1/8,
    3/8 < kappa < 2/5,
    cos(2/3) > 3/4,       sin(2/3) < 5/8,
    cos(2/5) > 9/10,      sin(2/5) < 39/100,
    cos(16/15) > 12/25,   sin(16/15) < 9/10.

All follow from the same alternating rational Taylor bounds already used in
A1.  Put

    d = u-t.

On the A1 triangle,

    -2/3 <= t <= u,
    -2/5 <= u <= 2/5,

we have

    0 <= d <= 16/15 < pi/2.

## Axis-specific three-separator stresses

For a directed W-to-D SAT normal `n`, put positive weights
`alpha,beta,mu` on, respectively,

    C--D west-cardinal,
    C--W own-primary,
    W--D on n.

The induced forces are

    G_C = -alpha(-1,0)-beta e(t),
    G_W =  beta e(t)-mu n,
    G_D =  alpha(-1,0)+mu n.

Use the following weights, all normalized to sum to one.

| W--D normal | alpha | beta | mu |
|---|---:|---:|---:|
| +e_W | 1/10 | 3/5 | 3/10 |
| -e_W | 3/5 | 1/10 | 3/10 |
| +/-f_W | 3/10 | 9/20 | 1/4 |
| +e_D | 3/10 | 9/20 | 1/4 |
| -e_D | 1/2 | 1/5 | 3/10 |
| +/-f_D | 3/10 | 9/20 | 1/4 |

For an exterior square of frame angle `x`, use the support estimate

    U(G,x) = r |G| - (|G.e_x|+|G.f_x|)/2.

Indeed, choose the square vertex `v` whose two frame signs agree with `G`.
Then `G.v=(|G.e_x|+|G.f_x|)/2`, while containment gives
`|p+v|<=r`, hence `G.p<=r|G|-G.v`.

For the four primary-axis rows `+/-e_W,+/-e_D`, use the weaker estimate on D

    U_D^*(G,u) = r |G| - |G.e_D|/2,

obtained by discarding the nonnegative `|G.f_D|/2` gain.  This deliberate
weakening removes the only curved absolute-value switch.

The elementary scalar bounds above fix all remaining signs in the support
terms.  The only close sign is in the `f_W` rows:

    (1/4) cos d > (3/10)|sin u|

because `(1/4)(12/25)=3/25` while
`(3/10)(39/100)=117/1000 < 3/25`.

## Separated form of every stress gap

Define

    T_beta(t) =
      beta [kappa cos t - (1/2) sin t],  t<=0,
      beta kappa [cos t + sin t],        t>=0,

    U_alpha(u) = (alpha/2)[cos u+|sin u|],
    V_mu(d)    = (mu/2)[cos d+sin d].

After expanding the threshold terms, the central support, and the exterior
supports, the strict-reverse gap has the form

    Phi(t,u) = C + F(t)+G(u)+H(d),       d=u-t,             (1)

where `C` is constant on the row.  Starting from
`F=T_beta`, `G=U_alpha`, `H=V_mu`, the row-dependent additions are:

| source | addition to F | addition to G | addition to H |
|---|---|---|---|
| `sigma e_W` | `-r sqrt(alpha^2+mu^2+2 sigma alpha mu cos t)` | `+(alpha/2)cos u` | `+(sigma mu/2)cos d` |
| `sigma f_W` | `-r sqrt(alpha^2+mu^2-2 sigma alpha mu sin t)` | `+(alpha/2)(cos u-sigma sin u)` | `+(mu/2)(cos d+sigma sin d)` |
| `sigma e_D` | `0` | `-r sqrt(alpha^2+mu^2+2 sigma alpha mu cos u)+(alpha/2)cos u` | `-r sqrt(beta^2+mu^2-2 sigma beta mu cos d)+(mu/2)(-sigma cos d+sin d)` |
| `sigma f_D` | `0` | `-r sqrt(alpha^2+mu^2-2 sigma alpha mu sin u)+(alpha/2)(cos u-sigma sin u)` | `-r sqrt(beta^2+mu^2+2 sigma beta mu sin d)+(mu/2)(cos d+sigma sin d)` |

The omitted constants are irrelevant for concavity.

Thus it remains only to prove that each of `F,G,H` is concave on the
appropriate one-dimensional sign interval.

## The only tight curvature lemma: the f_W rows

Put

    P=61/400,   q=3/20.

The second-derivative contribution of

    -r sqrt(P-sigma q sin x)

is

    N_sigma(x)
      = r [q^2(1+s^2)-2 sigma P q s]
          / [4(P-sigma q s)^(3/2)],               (2)

where `s=sin x`.

As a function of `s`, differentiation gives a factor

    4P^2 - 2 sigma P q s + q^2 s^2 - 3q^2
      = (P-sigma q s)^2 + 3(P^2-q^2) > 0.

Hence `N_+` decreases with `s` and `N_-` increases with `s`.  For fixed
`y=|s|`, the worse value is therefore

    N_*(y)
      = r [q^2(1+y^2)+2Pqy] / [4(P+qy)^(3/2)].    (3)

Also

    cos x = sqrt(1-y^2) >= 1-y^2.

Since `kappa>3/8`, the negative-t branch is bounded below by

    L_-(y)=(9/20)[(3/8)(1-y^2)+y/2],

and the positive-t branch by

    L_+(y)=(9/20)(3/8)(1-y^2+y).

It is enough to prove `L_-(y)>N_*(y)` for `0<=y<=5/8` and
`L_+(y)>N_*(y)` for `0<=y<=2/5`.  Use `r<17/10` and square.  After multiplying
by the positive factor `102400000000/9`, the two differences are

    p_-(y) =
      1739061 + 35584716 y + 91833206 y^2 + 31017504 y^3
      -108135819 y^4 - 91936620 y^5
      + 6706800 y^6 + 17496000 y^7,

    p_+(y) =
      1739061 + 23327742 y + 41365283 y^2
      -34496862 y^3 -125136099 y^4 -69969420 y^5
      +18370800 y^6 +17496000 y^7.

For `y<=5/8`,

    91833206 -108135819 y^2 -91936620 y^3
      >= 3474840043/128 > 0,

so `p_-(y)>0`.  For `y<=2/5`,

    41365283 -34496862 y -125136099 y^2 -69969420 y^3
      >= 76667987/25 > 0,

so `p_+(y)>0`.

Therefore both `f_W` rows have concave `F`.

## The remaining curvature checks

They have large margins.

### +e_W

Here `(alpha,beta,mu)=(1/10,3/5,3/10)`.  For the square-root term in `F`,
its positive curvature contribution is less than

    (17/10)(12/625) / [4(19/50)^3] < 3/20.

On `t<=0`, the trigonometric part is at least

    (3/5)(3/8)(3/4)=27/160,

and on `t>=0` it is still larger.  Hence `F''<0`.

### -e_W

Here `(alpha,mu)=(3/5,3/10)`.  The square-root curvature numerator is
nonpositive because, with `c=cos t in [3/4,1]`,

    (2/5)(1+c^2) <= c,

which is equivalent to

    (2c-1)(c-2) <= 0.

Thus the square-root term is itself concave; so is `F`.

For both `e_W` rows, `G` is a positive linear combination of
`cos u` and `|sin u|`, while `H` is respectively

    mu cos d + (mu/2) sin d,
    (mu/2) sin d.

They are concave on the stated intervals.

### +/-f_W: the other two pieces

The difficult `F` piece was handled above.  The remaining pieces are purely
trigonometric after the support-component signs are fixed.  For source sign
`sigma`,

    G(u) = alpha cos u + (alpha/2)(|sin u|-sigma sin u),
    H(d) = mu cos d + (mu/2)(1+sigma) sin d.

On each sign chamber of `u`, every displayed coefficient of `cos u` and the
appropriate signed sine is nonnegative.  Since `0<=d<pi/2`, both `G` and `H`
are concave.

### +e_D

Use `(alpha,beta,mu)=(3/10,9/20,1/4)`.
For `G`, the square-root curvature is less than

    (17/10)(363/4000)/[4(53/100)^3] < 13/50,

whereas the trigonometric curvature magnitude is at least

    (3/10)(9/10)=27/100.

For `H`, put `c=cos d`.  Its square-root curvature numerator has the sign of

    (5c-9)(9c-5).

Hence it is nonpositive for `c>=5/9`.  If `c<5/9`, then `sin d>4/5`, while
an elementary bound gives the positive square-root curvature `<1/20`.
The trigonometric curvature magnitude is then `>(1/4)(4/5)=1/5`.
Thus `G,H` are concave.

### -e_D

Use `(alpha,beta,mu)=(1/2,1/5,3/10)`.
For `G`, the square-root curvature is nonpositive because

    (3c-5)(5c-3) <= 0,      c=cos u>=9/10.

For `H`, its positive square-root curvature is increasing with `c=cos d`
(the derivative numerator is already positive at `c=0`).  At `c=1` it is
less than `21/100`, while the trigonometric curvature magnitude is at least
`3/10`.  Thus `H` is concave.

### +/-f_D

The `G` square-root curvature is the same `N_sigma` as in the `f_W` lemma.
Its trigonometric curvature is at least `(3/10) cos u`.  This is stronger
than the `f_W` trigonometric curvature already proved to dominate
`N_sigma`.  Indeed `|u|<=2/5`, and the scalar bounds give

    tan|u| < (39/100)/(9/10) = 13/30 < 1/2.

For `u<=0`, using `kappa<2/5`,

    (9/20)[kappa cos u + |sin u|/2]
      < (9/20)(13/20) cos u
      = 117/400 cos u
      < 3/10 cos u.

For `u>=0`,

    (9/20) kappa (cos u+sin u)
      < (9/20)(2/5)(3/2) cos u
      = 27/100 cos u
      < 3/10 cos u.

Hence `G` is concave.

For `H`, put `s=sin d`, with `0<=s<9/10`, and

    P=53/200, q=9/40.

The square-root curvature is increasing in `s` for source `+` and decreasing
for source `-`, since

    4P^2-3q^2 = 5161/40000 > 0.

For source `+`:

- if `s<=1/2`, its curvature is `<23/100`, while
  `(1/4)(cos d+sin d)>=1/4`;
- if `s>=1/2`, its curvature is `<27/100`.  The function
  `s+sqrt(1-s^2)` is concave, and at both endpoints of
  `[1/2,9/10]` it is `>4/3` (use `sqrt(3)/2>5/6` and
  `sqrt(19)/10>13/30`).  Hence the trigonometric curvature is `>1/3`.

For source `-`:

- if `s<=1/2`, its curvature is `<4/25`, while
  `(1/4)cos d>1/5`;
- if `s>=1/2`, its curvature is `<3/100`, while
  `(1/4)cos d>3/25`.

Thus `H` is concave in both D-secondary rows.

This proves the required one-variable concavity in all eight cases.

## Chamber vertices

The signs of `t,u` divide the A1 triangle into three convex polygons:

    P_- : t<=u<=0,
    P_0 : t<=0<=u,
    P_+ : 0<=t<=u.

On each polygon, (1) is a sum of concave functions of the affine forms
`t`, `u`, and `u-t`.  Hence `Phi` is concave on that polygon, so its minimum
is attained at a vertex.

The union of the three vertex sets consists of only seven points:

    (-2/3,-2/5), (-2/5,-2/5), (-2/3,0), (0,0),
    (-2/3,2/5),  (0,2/5),     (2/5,2/5).

Exact rational/Taylor evaluation gives these row-wise lower margins:

| W--D normal | minimum gap | vertex |
|---|---:|---|
| +e_W | > 2/25 | (0,0) |
| -e_W | > 1/50 | (-2/3,0) |
| +f_W | > 1/500 | (-2/3,2/5) |
| -f_W | > 1/100 | (0,0) |
| +e_D | > 1/50 | (0,0) |
| -e_D | > 2/25 | (2/5,2/5) |
| +f_D | > 1/100 | (-2/3,0) |
| -f_D | > 1/100 | (0,0) |

Thus every directed W--D separating axis contradicts the three-separator
stress inequality.

an independent arithmetic audit checks exactly the scalar inequalities and the 56 fixed
endpoint evaluations above, using `Fraction`, integer square-root enclosures,
and alternating Taylor bounds.  It performs no subdivision.

## Conclusion

Every directed W--D separating-axis possibility has a strictly positive
reverse-stress gap on the closed A1 triangle.  Therefore a hypothetical
configuration with D west-cardinal cannot exist.

Hence, in the original `c_x,c_y>=0` normalization used by the global sector
and pin lemmas,

    D uses its own-primary separator from C.

This closes roadmap item A1 without interval subdivision and without changing
any convention needed by A2.

# Appendix B — central-pattern hand classification (A2)

This appendix gives the hand classification of the nine forbidden canonical
central patterns. Every multidimensional region is reduced analytically by
sign chambers, monotonicity/concavity, oblique-wall curvature, or pair
envelopes to one-variable inequalities or fixed endpoint values.

## Preparatory lemma P1 — exact own-versus-cardinal margin identities

Write C=(x,y).  For any helper write its frame deviation from its category
cardinal direction as theta, with

    c = cos(theta),  s = sin(theta),

and write its center in its own positively oriented frame as

    p = a e + b f.

Let O be the margin on the helper's own-primary separator from C, and K the
margin on the corresponding cardinal separator.  Thus canonical own-primary
means

    O >= 0,   K < 0,

so in particular O-K>0.

A direct expansion gives the following exact formulas.

### East

For

    e=(c,s),  f=(-s,c),

one has

    O_E-K_E = (1-c)(a+x) + s(b-y).              (E)

Hence E own-primary implies

    (1-c)(a+x) + s(b-y) > 0.

### North

For

    e=(-s,c),  f=(-c,-s),

one has

    O_N-K_N = (1-c)(a+y) + s(b+x).              (N)

Hence N own-primary implies

    (1-c)(a+y) + s(b+x) > 0.

### West

For

    e=(-c,-s),  f=(s,-c),

one has

    O_W-K_W = (1-c)(a-x) + s(b+y).              (W)

Hence W own-primary implies

    (1-c)(a-x) + s(b+y) > 0.

### South

For

    e=(s,-c),  f=(c,s),

one has

    O_S-K_S = (1-c)(a-y) + s(b-x).              (S)

Hence S own-primary implies

    (1-c)(a-y) + s(b-x) > 0.

These are identities; no small-angle estimate is used.

## Half-angle form

For theta != 0,

    (1-cos theta)/sin theta = tan(theta/2).

Thus every own-primary branch gives a one-sided bound on a signed transverse
coordinate.

For example, the north identity gives

    theta_N > 0:
      b_N+x > -(a_N+y) tan(theta_N/2),

    theta_N < 0:
      b_N+x < -(a_N+y) tan(theta_N/2).

The other three identities give the analogous bounds for

    E : b-y,
    W : b+y,
    S : b-x.

This is the correct variable for A2: the bit choice is controlled by a signed
transverse displacement plus a nonnegative half-angle correction.

## Relation to affine markers

In the global n=6 state domain the verified seven-square label is exactly

    marker offset = theta + 5 b / 4.

Therefore the four identities above translate directly into one-sided marker
bounds once the sign of theta is fixed.

The five consecutive marker gaps satisfy

    g_EN = pi/2 + m_N-m_E > pi/3,
    g_NW = pi/2 + m_W-m_N > pi/3,
    g_WD = m_D-m_W > pi/3,
    g_DS = pi/2 + m_S-m_D > pi/3,
    g_SE = pi/2 + m_E-m_S > pi/3,

and the five gap slacks above pi/3 add exactly to pi/3.

The identities (E)--(S) are used below only as algebraic tools for the
pattern-specific hand inequalities.  No separate local-neighborhood theorem
is needed for coverage: after the global normalization fixes the D bit to
own-primary there are exactly 16 canonical patterns; A2 eliminates nine of
them directly, and the remaining seven are therefore exhaustive.

## Preparatory lemma P2 — cardinal-preferred canonical separator rule

The seven surviving canonical patterns were produced with the following
canonical rule, and A2 must use the same rule.

For every exterior square the two-choice theorem gives

    O >= 0  or  K >= 0,

where K is the corresponding cardinal margin and O the own-primary margin.
Choose

- the cardinal separator whenever K >= 0;
- the own-primary separator only when K < 0.

On the second branch the two-choice theorem automatically forces O >= 0.
Thus a canonical own bit means the strictly stronger statement

    K < 0,   O >= 0,   hence Delta:=O-K > 0.       (P2)

A cardinal bit means only

    K >= 0;                                        (P2c)

no sign of Delta is asserted.  Boundary ties K=0 belong to the cardinal
branch.

This is exactly the canonicalization used by the canonical classification that
produced the seven surviving patterns 8,9,11,15,24,25,27.  The later
Delta-sign selection is useful as an availability observation but is not the
pattern definition and should not be used for A2 classification.

## Preparatory lemma P3 — exact marker-threshold formula

Let

    m := theta + 5b/4

be the category-relative affine marker coordinate.  For theta != 0, divide
the identities (E)--(S) by sin(theta), using

    (1-cos theta)/sin theta = tan(theta/2).

One obtains

    E:
      m_E =  5y/4 + F_{a_E+x}(theta_E)
             + (5/4) Delta_E/sin(theta_E),

    N:
      m_N = -5x/4 + F_{a_N+y}(theta_N)
             + (5/4) Delta_N/sin(theta_N),

    W:
      m_W = -5y/4 + F_{a_W-x}(theta_W)
             + (5/4) Delta_W/sin(theta_W),

    S:
      m_S =  5x/4 + F_{a_S-y}(theta_S)
             + (5/4) Delta_S/sin(theta_S),

where

    F_L(theta) := theta - (5/4)L tan(theta/2).

At theta=0, Delta=0 and the formula is understood by continuity.

### The threshold term has the sign of theta

Every relevant L is strictly below 5/4.  Indeed a<=rho<9/8 and
|x|,|y|<1/8 give the stronger bound L<5/4.

For 0<z<=pi/8,

    tan z = sin z/cos z < z/(4/5) = 5z/4,

because sin z<z and cos z>cos(pi/8)>4/5.  Hence, for
0<|theta|<=pi/4,

    (5/4)L |tan(theta/2)|
      < (5/4)(5/4)(5/8)|theta|
      = (125/128)|theta|.

Therefore

    sign(F_L(theta)) = sign(theta)

and in fact

    |F_L(theta)| > (3/128)|theta|.                 (T)

For a canonical own-primary branch, (P2) gives Delta>0.
Therefore

    theta>0  =>  m-category_offset > F_L(theta)>0,
    theta<0  =>  m-category_offset < F_L(theta)<0.

Thus a forced-own marker lies strictly on the theta-side of the category
offset.  No converse statement is made for a canonical cardinal branch:
K>=0 does not determine the sign of Delta.

The four category offsets are

    E :  +5y/4,
    N :  -5x/4,
    W :  -5y/4,
    S :  +5x/4.

Their central-coordinate contributions telescope around the marker cycle.
This is the scalar structure A2 will use instead of center-box enumeration.

## Canonical A2 obstruction labels

With the cardinal-preferred rule, the three A2 obstructions are the concrete
margin conditions

    A2.1:  K_N < 0,   K_E >= 0,
    A2.2:  K_W < 0,   K_N >= 0,
    A2.3:  K_S < 0,   K_W < 0.                    (P2-A2)

The own branches also carry O_N>=0, O_W>=0, O_S>=0 respectively.  These
strict K inequalities are stronger than the Delta-sign conditions used in
some preliminary exploratory calculations and should be exploited directly.


## Preparatory calculation P4 — moving-pin coordinates for forced-own E/N

Let C=(x,y), with 0<=x,y<1/8.  The global piercing theorem gives

    P_E=(1+x,0) in int(E),
    P_N=(0,1+y) in int(N).

For either square, let

    X=(P-p).e,   Y=(P-p).f,

so |X|<1/2 and |Y|<1/2.

### East

With e=(c,s), f=(-s,c),

    a=(1+x)c-X,
    b=-(1+x)s-Y.

A direct substitution into the central separator margins gives

    K_E = (1-c-|s|)/2 - c X + s Y,                 (KE)

    O_E = (c-1-|s|)/2 - y s - X.                  (OE)

Here K_E is the east-cardinal margin and O_E the own-primary margin.

### North

With e=(-s,c), f=(-c,-s),

    a=(1+y)c-X,
    b=-(1+y)s-Y.

The corresponding formulas are

    K_N = (1-c-|s|)/2 - c X + s Y,                 (KN)

    O_N = (c-1-|s|)/2 + x s - X.                  (ON)

Thus the cardinal formula is identical for E and N; only the central
coordinate in the own-primary formula changes.

### Forced-own radial displacement

If E or N is forced own-primary, then

    K<0,   O>=0.

From (OE)/(ON), using 0<=x,y<1/8, one obtains uniformly

    X <= -(3/8)|s|.                                (X)

More precisely:

* E, s>=0: X <= -s/2;
* E, s<0:  X <= -(1/2-y)|s|;
* N, s>=0: X <= -(1/2-x)s;
* N, s<0:  X <= -|s|/2.

Thus a forced-own E/N square has its moving piercing point displaced toward
the near edge by a definite amount proportional to its frame angle.

### A second transverse inequality

Combining K<0 with (X) gives a one-sided bound on Y. For example, for N with
s>0,

    Y < [1-c-s+2cX]/(2s)
      <= [1-c-s-(3/4)c s]/(2s).                   (YN+)

The other sign/category cases follow by the evident reflections.

These formulas are exact except for the final use of x,y<1/8.

## Preparatory calculation P5 — preliminary forced-own angle window

The moving-pin formulas reduce the one-square containment cost to a scalar
function of theta.

For N with theta>0, use X<=-(1/2-x)sin(theta) and the sharp upper bound from
(KN) for Y. Substituting

    a=(1+y)cos(theta)-X,
    b=-(1+y)sin(theta)-Y

into

    Q >= (a+1/2)^2+(|b|+1/2)^2

and minimizing the remaining x,y variables over 0<=x,y<=rho0-1 gives a
one-variable lower envelope Q_N^+(theta).

For theta<0 the analogous reflected calculation gives Q_N^-(theta).

The target rational window is

    N forced-own  =>  -3/10 < theta_N < 5/12.      (NW)

The endpoint values have comfortable margins at Q0:

    Q_N^-(-3/10) > Q0,
    Q_N^+(5/12) > Q0.

The E statement follows by transposition/reflection:

    E forced-own  =>  -5/12 < theta_E < 3/10.      (EW)

The remaining task for this subsection is to write the lower envelopes in a
monotone form and verify only the two endpoint comparisons with rational
Taylor bounds.  No multidimensional subdivision is intended.


## Preparatory lemma P6 — forced-own E/N angle windows

The target window (NW)/(EW) follows from the moving pin with a much simpler
argument than the preliminary K-margin calculation.

Write

    r0 := rho0-1 < 23/200.

The last inequality is exact because

    Q0-1/4 < (323/200)^2.

### North

Let theta_N=theta and put c=cos(theta), s=sin(theta).

If theta>0, (ON) and O_N>=0 give

    X <= (c-1-s)/2 + x s
      <= (c-1-s)/2 + r0 s.

Since

    a=(1+y)c-X

and y>=0,

    a_N >= (1+c+s)/2-r0 s
        >  (1+c+s)/2-(23/200)s.                 (AN+)

If theta<0, write u=-theta>0. Then (ON) gives

    X <= (c-1-sin u)/2 - x sin u
      <= (c-1-sin u)/2,

hence

    a_N >= (1+c+sin u)/2.                       (AN-)

For every exterior square,

    R^2 >= (a+1/2)^2+(|b|+1/2)^2
         >= (a+1/2)^2+1/4.                     (C)

For (AN-), the derivative is

    (cos u-sin u)/2,

which is positive on (0<u<pi/4).  Hence the lower bound is increasing on
the whole allowed negative-angle range, not merely up to (pi/6).

For (AN+), write

    L(theta)=1+(cos theta+sin theta)/2-(23/200)sin theta.

On (0<	hetalepi/6),

    L'(theta)
      =(77/200)cos theta-(1/2)sin theta
      >(77/200)(4/5)-1/4
      =29/500>0.

On ([pi/6,pi/4]),

    L''(theta)
      =-(1/2)cos theta-(77/200)sin theta<0,

so (L) is concave there.  Consequently the minimum of (L) on
([5/12,pi/4]) occurs at one of the two endpoints (5/12,pi/4).
The rational/Taylor checks give

    L(5/12)^2+1/4 > Q0,
    L(pi/4)^2+1/4 > Q0+1/25.                       (N+far)

Thus every theta>=5/12 is excluded.

It is therefore enough to check the stated rational endpoint at (5/12),
together with the explicit (pi/4) endpoint above.

At u=3/10,

    [(2+cos u+sin u)/2]^2+1/4 > Q0.             (N-ep)

At theta=5/12,

    [1+(cos theta+sin theta)/2-(23/200)sin theta]^2
      +1/4 > Q0.                                (N+ep)

Alternating rational Taylor bounds prove both strict inequalities.  Hence

    boxed:  N own-primary available
            =>  -3/10 < theta_N < 5/12.         (NW)

This statement is stronger than what A2 needs: it assumes only availability
of the own-primary separator, not that the cardinal separator is unavailable.

### East

The east formula (OE) is the reflected version.  For theta_E>0,

    a_E >= (1+cos theta+sin theta)/2,

while for theta_E<0, with u=-theta_E,

    a_E >= (1+cos u+sin u)/2-r0 sin u.

The same monotonicity and endpoint checks therefore give

    boxed:  E own-primary available
            =>  -5/12 < theta_E < 3/10.         (EW)

### Exact checker

`the pinned independent arithmetic audit` checks only:

1. r0<23/200 by a rational square comparison;
2. (N-ep);
3. (N+ep).

The east bounds use the same two endpoint inequalities by reflection.
There is no interval subdivision.



## Preparatory lemma P7 — the canonical D-own angle is positive

A1 gives more than a separator label once it is combined with the fixed D
pin.  Write

    phi_D = pi+d,       -pi/4 <= d <= pi/4.

Then in fact

    0 < d <= pi/4.                                      (D+)

The upper bound is the west-category convention.  To prove the lower bound,
suppose d=-v<0, with 0<v<=pi/4.

The fixed D pin lies at angle 5pi/4 and radius 9/10.  In D's own frame its
transverse coordinate is

    q(v) = (9/10) sin(pi/4+v).

Because the pin is in the open interior of D,

    b_D > q(v)-1/2 =: B(v) > 0.                       (D1)

Containment at R^2<=Q0 therefore gives

    a_D
      < sqrt(Q0-q(v)^2)-1/2
      =: A(v).                                         (D2)

Here we used b_D+1/2>q(v).  Since c_x>=0,

    a_D-c_x < A(v).                                    (D3)

On the other hand D is canonically own-primary: the own-primary margin is
nonnegative and the west-cardinal margin is strictly negative.  Hence
Delta_D=O_D-K_D>0.  The west identity (P1), with d=-v, gives

    Delta_D
      = (1-cos v)(a_D-c_x)-sin v (b_D+c_y) > 0.

Using c_y>=0 together with (D1)--(D3), this forces

    B(v) < A(v) tan(v/2).                              (D4)

We prove the strict reverse inequality.

### Range 0<v<=2/3

Since A(v)<=rho0<9/8, it is enough to show

    B(v) > (9/8) tan(v/2).                            (D5)

Put

    F(v) = (9/(10 sqrt(2)))(cos v+sin v)
           -1/2-(9/8)tan(v/2).

On [0,2/3],

    F''(v)
      = -(9/(10 sqrt(2)))(cos v+sin v)
        -(9/16) sec^2(v/2) tan(v/2)
      < 0.

Thus F is concave and its minimum is at an endpoint.  Exact scalar bounds
give

    F(0)   > 0.13639,
    F(2/3) > 0.00412.

So (D5) holds throughout this range.

### Range 2/3<=v<=pi/4

The function q(v) is increasing here.  Therefore

    B(v) >= B(2/3),       A(v) <= A(2/3),

while

    tan(v/2) <= tan(pi/8)=sqrt(2)-1.

A single exact endpoint comparison gives

    B(2/3) - A(2/3)(sqrt(2)-1) > 0.00733.             (D6)

Hence (D4) is impossible in the second range as well.

Therefore d cannot be negative.  At d=0 the exact identity gives Delta_D=0,
which is also incompatible with the canonical own branch Delta_D>0.  This
proves (D+).

`the pinned independent arithmetic audit` checks only the three scalar comparisons
used above, with rational square-root and alternating Taylor enclosures.

## A2.1 — exclude N own while E cardinal

The detailed hand closure is developed below.

The first obstruction is

    N_own and E_cardinal.

With D already own-primary by A1, the W/S choices give four subcases.  Start
with the most constrained one,

    E cardinal, N own, W cardinal, D own, S cardinal.       (P10)

This is old canonical pattern 10.  There is an exact central-force
elimination which removes C before any outer-axis case split.

### Balanced central stress for (P10)

Write theta=theta_N and

    n_N=(-sin theta, cos theta),
    e_x=(1,0), e_y=(0,1).

Orient the four selected central separators as

    C -> N : n_N,
    C -> E : e_x,
    W -> C : e_x,
    S -> C : e_y.

Give C->N weight alpha>0 and C->E weight beta>0.  Define the other two
central weights by

    gamma = beta-alpha sin theta,
    delta = alpha cos theta.                         (B)

Then the force on C vanishes identically:

    -alpha n_N-beta e_x+gamma e_x+delta e_y = 0.     (CB)

Indeed the x-coordinate is

    alpha sin theta-beta+(beta-alpha sin theta)=0,

and the y-coordinate is

    -alpha cos theta+alpha cos theta=0.

Thus every stress built on the outer chain may eliminate the central center
exactly even though the north separator has rotated away from the cardinal
axis.  No estimate on C_x,C_y is needed.

### Two positive stresses on the whole forced-own north window

Use the rational candidate-stress coefficients already recorded in
CAP_STRESS.md.  For the first stress take

    alpha_A = 1102695/10^7,
    beta_A  = 1966219/10^7,

and for the reflected stress interchange them:

    alpha_B = 1966219/10^7,
    beta_B  = 1102695/10^7.

Preparatory lemma P6 gives

    -3/10 < theta_N < 5/12.

For theta<=0, gamma_A and gamma_B are plainly positive.  For theta>0,
sin(theta)<theta<5/12, and therefore

    gamma_A
      > beta_A-(5/12)alpha_A
      = 6027051/40000000 > 0,

    gamma_B
      > beta_B-(5/12)alpha_B
      = 680249/24000000 > 0.

Also delta_A,delta_B>0 because |theta|<5/12<pi/2.  Hence both balanced
central stresses are valid throughout the entire forced-own north angle
window, not only near the candidate.

For the four outer edges use respectively

                 WN             SE             DW              DS
    stress A   406657/10^7    725112/10^7   1542347/10^7    1188057/10^7
    stress B   725112/10^7    406657/10^7   1188057/10^7    1542347/10^7.

All are positive.

### Consequence

Fix one separating source axis for each of

    W-N, S-E, D-W, D-S.

Sum the eight selected separator inequalities with either stress.  By (CB)
there is no C term.  Applying the exact one-square disk support function from
CAP_STRESS.md to E,N,W,D,S gives an inequality depending only on the five
frame angles.

Thus the (P10) branch has been reduced from the 17-variable packing state to
a five-angle inequality, with no center variables and with two stresses which
are exact reflections of one another at theta_N=0.

For the candidate outer-source family

    W-N : near-horizontal source W or N,
    S-E : near-vertical source S or E,
    D-W : W secondary,
    D-S : S secondary,

the next scalar target is to prove that the sum of these two support-stress
defects is strictly positive away from the candidate/local region.  The
reflection pair is important because the individual defects have opposite
first-order response to the diagonal-square deviation, while their sum has
zero first derivative there.

The following three hand steps complete this five-angle reduction:

1. prove the scalar positivity for this candidate-source family;
2. exclude or separately stress the alternate source axes;
3. repeat the same central-balance construction for the other W/S choices.

No multidimensional center subdivision is required.


### Exact symmetric self-stress for the candidate-source family

There is a cleaner stress than the rounded asymmetric pair above.

Let (s_*,t_*,d_*) be the candidate parameters and put

    r := (s_*+1/2)/(s_*+3/2),
    k := (t_*+1/2)/(3/2-s_*),
    m := (1+r) k.                                  (S0)

All three numbers are positive.  On the candidate-source family take the
weights

    C->N = 1,
    C->E = 1,
    W->C = 1-sin(theta_N),
    S->C = cos(theta_N),
    W->N = r,
    S->E = r,
    D->W = m,
    D->S = m.                                      (S1)

The first four weights satisfy the central balance (CB) with alpha=beta=1.
Preparatory lemma P6 gives (|theta_N|<5/12<pi/2), so

    1-sin(theta_N)>0,    cos(theta_N)>0.

Hence (S1) is a valid nonnegative stress throughout the whole forced-own
north window.

At the candidate all helper deviations vanish.  The exterior forces are then

    G_E = (1,r),
    G_N = (r,1),
    G_W = (-(1+r),m),
    G_S = (m,-(1+r)),
    G_D = (-m,-m).                                 (S2)

By the definitions of r and m,

    G_E  is parallel to (s_*+3/2, s_*+1/2),
    G_N  is parallel to (s_*+1/2, s_*+3/2),
    G_W  is parallel to (s_*-3/2, t_*+1/2),
    G_S  is parallel to (t_*+1/2, s_*-3/2).

These are exactly the outward radius vectors through the active far vertices
of E,N,W,S.  The diagonal force G_D lies in the normal cone generated by the
two active far vertices of D.  Therefore the exact disk-support stress is an
equality at the candidate.

This gives an algebraic self-stress, rather than a numerically optimized one.

### Exact control of the diagonal-angle mode

Let

    h := 1/sqrt(2),
    eps := theta_D-pi/4.

Keep the four helper deviations zero and vary only eps.  For (|eps|le1/4)
the D support remains on the first branch of the exact cap support formula.
Indeed

    2 R_* sin|eps|
      <= 2 R_* |eps|
      <= R_*/2
      < 1,

where (R_*<2).  In the D frame the force G_D=(-m,-m) has

    U = sqrt(2) m cos eps.

The candidate identities give

    rho_* sqrt(2) = 2 d_*,

so the D center-support term is

    2 m d_* cos eps.

The two D-edge threshold terms sum to

    m + 2 m h cos eps.

All other terms are independent of eps.  Since the stress is an equality at
eps=0, its defect Phi therefore satisfies the exact identity

    Phi(0,0,0,0,eps)
      = 2 m (d_*-h) (1-cos eps).                  (Dmode)

The candidate has (d_*>h).  Consequently

    Phi(0,0,0,0,eps)>0

for every (0<|eps|le1/4).

Thus the formerly delicate diagonal direction has an exact positive
quadratic defect.  What remains for the candidate-source part of (P10) is to
control the cross-terms when helper angles vary simultaneously with eps.


### First-order coercivity of the candidate-source stress

The same self-stress has a useful quantitative tangent form.  Write

    e=theta_E,  n=theta_N,  w=theta_W,  s=theta_S,

and put `[x]_+ := max(x,0)`.  Define

    L := (s_*+1/2)+(t_*+1/2)-m d_*,
    q := (s_*+1/2)-(t_*+1/2) r.                   (S3)

For the source choice W on W--N and S on S--E, the one-sided first-order
defect of the support-stress lower bound at the candidate splits as

    T_WS = A_S(e,s)+B_W(n,w),

where

    A_S(e,s) = [-e]_+ + [-s]_+ + r[e-s]_+ + Ls,
    B_W(n,w) = [ n]_+ + [ w]_+ + r[w-n]_+ - Lw.  (S4)

Changing the S--E source from S to E adds `q(e-s)`, and changing the W--N
source from W to N adds `q(w-n)`.  Thus

    A_E = A_S+q(e-s),
    B_N = B_W+q(w-n).                              (S5)

The algebraic candidate constants satisfy the strict scalar inequalities

    q>0,
    r>1/3,
    r<L<1,
    1+r-L>1/3,
    1-q>1/3,
    L-q>1/3.                                      (S6)

They are checked directly from the exact defining radicals by
an independent arithmetic audit.

These inequalities give a uniform hand bound.  First consider A_S.  Split
according to the signs of s and the order of e,s.

* If `s>=0` and `e<=0`, then `A_S=-e+Ls`.
* If `0<=e<=s`, then `A_S=Ls`.
* If `e>=s>=0`, then

      A_S = r e + (L-r)s.

* If `e<=s<0`, then

      A_S = -e + (1-L)(-s).

* If `s<e<0`, then

      A_S = (1-r)(-e)+(1+r-L)(-s).

* If `s<0<=e`, then

      A_S = r e +(1+r-L)(-s).

Using (S6) in these six cases gives

    A_S(e,s) >= (1/3) max(|e|,|s|).               (S7)

For A_E, if `e>=s` the correction in (S5) is nonnegative, so (S7) still
applies.  If `e<s`, the three possible sign patterns give respectively

    A_E=(1-q)(-e)+(1-L+q)(-s),       e<s<=0,
    A_E=(1-q)(-e)+(L-q)s,            e<0<s,
    A_E=q e+(L-q)s,                  0<=e<s.

Again (S6), together with `q>0` and `L<1`, yields

    A_E(e,s) >= (1/3) max(|e|,|s|).               (S8)

The north/west terms are the same formulas after `(e,s)=(-n,-w)`.  Hence

    B_W(n,w), B_N(n,w)
      >= (1/3) max(|n|,|w|).                      (S9)

Combining (S7)--(S9), every one of the four candidate source choices obeys

    T_source(e,n,w,s)
      >= (1/3) max(|e|,|n|,|w|,|s|).             (Tcoercive)

Thus every nonzero helper-angle direction has a uniform positive linear
stress defect.  Together with (Dmode), the only remaining issue for this
candidate-source subfamily is quantitative control of the second-order
helper/diagonal cross-terms; there is no flat first-order helper direction.


### Uniform helper coercivity along the diagonal strip

The tangent estimate above persists uniformly when the diagonal square is
allowed to move while the four helper angles remain at their candidate
values.

Put

    eps := theta_D-pi/4,     h:=1/sqrt(2).

For `|eps|<=1/4` the D support is still on its cap branch at
`e=n=w=s=0`, by the estimate already used in (Dmode).  Differentiating the
D-edge threshold terms and the D center-support term with respect to the
helper angles shows that the only eps-dependent changes in the one-sided
helper tangent are the coefficients of w and s:

    delta_w(eps)
      = m h [rho_*(cos eps-1)+(1-rho_*) sin eps],

    delta_s(eps)
      = m h [rho_*(1-cos eps)+(1-rho_*) sin eps].  (S10)

Thus, for every one of the four W--N / S--E candidate source choices,

    T_eps(e,n,w,s)
      = T_0(e,n,w,s)+delta_w(eps) w+delta_s(eps) s. (S11)

The candidate constants satisfy

    m h < 1,       1 < rho_* < 9/8.

These are exact algebraic inequalities checked in
an independent arithmetic audit.  For `|eps|<=1/4`,

    |sin eps| <= 1/4,
    0 <= 1-cos eps <= eps^2/2 <= 1/32.

Hence each correction in (S10) obeys

    |delta_w|, |delta_s|
      < (9/8)(1/32)+(1/8)(1/4)
      = 17/256.

Put

    M_ES=max(|e|,|s|),    M_NW=max(|n|,|w|).

The two diagonal corrections in (S11) belong to different pair terms:
`delta_s s` modifies the E/S contribution and `delta_w w` modifies the
N/W contribution.  Thus they should be absorbed pairwise, rather than both
being subtracted from one global maximum.  From (U8)--(U9) and
`|delta_w|,|delta_s|<17/256`,

    A_eps >= (11/50-17/256) M_ES,
    B_eps >= (11/50-17/256) M_NW.

Hence, with

    M=max(M_ES,M_NW),

one obtains the stronger uniform estimate

    T_eps
      >= (11/50-17/256)(M_ES+M_NW)
      >= (983/6400) M
      > (3/20) M.                                  (U11')

Therefore there is no first-order helper degeneracy anywhere on the entire
diagonal strip `|eps|<=1/4`, with a uniform coercivity constant exceeding
`3/20`.  The remaining candidate-source task on this strip is purely
second order: bound the helper-angle remainder uniformly.


### Unified central balance for all four A2.1 central patterns

The preceding pattern-10 balance is not specific to W/S cardinal choices.
There is a single exact construction covering all four possibilities for W
and S.

Write

    e=theta_E,  n=theta_N,  w=theta_W,  s=theta_S.

For the north own-primary separator let

    n_N=(-sin n,cos n).

For a W own-primary separator, orient the selected central edge from W to C,
so its normal is

    q_W=(cos w,sin w).

For a W cardinal separator put q_W=(1,0).  Similarly, for S put

    q_S=(-sin s,cos s)     in the own-primary case,
    q_S=(0,1)              in the cardinal case.

The key observation is that the two sides can always be balanced through the
fixed diagonal vector (1,1).  The following table gives a nonnegative scale
lambda and W/S weights gamma,delta such that

    gamma q_W + delta q_S = lambda (1,1).          (U1)

| W choice | S choice | lambda | gamma | delta |
|---|---|---:|---:|---:|
| cardinal | cardinal | 1 | 1 | 1 |
| own | cardinal | cos w | 1 | cos w-sin w |
| cardinal | own | cos s | cos s+sin s | 1 |
| own | own | cos(w-s) | cos s+sin s | cos w-sin w |

The identities are immediate.  For example, in the both-own row,

    (cos s+sin s)(cos w,sin w)
      +(cos w-sin w)(-sin s,cos s)
      = cos(w-s)(1,1).

On the category angle box |w|,|s|<=pi/4 all displayed weights are
nonnegative.  The degenerate endpoint w=pi/4,s=-pi/4 simply gives lambda=0;
no division is used.

For C->N and C->E use the weights

    alpha = lambda sec n,
    beta  = lambda(1+tan n).                       (U2)

Then

    alpha n_N + beta(1,0)
      = lambda[(-tan n,1)+(1+tan n,0)]
      = lambda(1,1).                               (U3)

Preparatory lemma P6 gives -3/10<n<5/12, so cos n>0 and
1+tan n>0.  Thus all four A2.1 central patterns admit the same positive
central-force elimination.  At the candidate all six central weights in
(U1)--(U2) equal 1.

Consequently the center C can be removed from A2.1 before deciding whether W
or S is cardinal or own-primary.

### Unified first-order coercivity

Keep the candidate outer-source family and the exact outer weights r,m from
(S0).  The central balance (U1)--(U3) is also exact at the candidate, so the
same fixed-vertex support lower bound is tangent there.

Put

    c := t_*-s_* > 0,
    L' := L-c.                                     (U4)

A direct first-order expansion gives a particularly simple rule:

- changing W from cardinal to own-primary adds c w to the tangent defect;
- changing S from cardinal to own-primary adds -c s;
- no other first-order term changes.

Thus the pair formulas (S4)--(S5) remain valid after replacing L by L' in
the N/W pair when W is own, and replacing L by L' in the E/S pair when S is
own.

More explicitly, for Lambda in {L,L'} put

    A_S^Lambda(e,s)
      = [-e]_+ + [-s]_+ + r[e-s]_+ + Lambda s,

    A_E^Lambda(e,s)
      = A_S^Lambda(e,s)+q(e-s),                   (U5)

and define B_W^Lambda,B_N^Lambda by the reflection

    (e,s)=(-n,-w).                                 (U6)

Use Lambda=L when the corresponding central square is cardinal and
Lambda=L' when it is own-primary.

The exact candidate constants satisfy

    c>0,
    q>0,
    r>1/3,
    L'>1/3,
    1-L'>1/3,
    1+r-L'>1/3,
    1-q>1/3,
    L'-q>11/50.                                   (U7)

The same sign split used in (S7)--(S9) now gives, uniformly for
Lambda in {L,L'},

    A_S^Lambda(e,s) >= (11/50) max(|e|,|s|),
    A_E^Lambda(e,s) >= (11/50) max(|e|,|s|),       (U8)

and by reflection

    B_W^Lambda(n,w), B_N^Lambda(n,w)
      >= (11/50) max(|n|,|w|).                    (U9)

The only new potentially smallest coefficient is L'-q; (U7) was chosen
precisely to control it.  Therefore every one of the four A2.1 central
patterns, and every one of the four candidate W--N / S--E source choices,
has

    T_source >= (11/50)
      max(|e|,|n|,|w|,|s|).                       (U10)

This removes the need to repeat the pattern-10 tangent argument for patterns
14, 26, and 30.

The diagonal-strip correction (S10) is unchanged, because the new central
weights do not involve eps and all four choices agree at the helper base
point.  Hence for |eps|<=1/4,

    T_eps
      >= [11/50-17/128] M
      = 279/3200 M
      > 1/12 M,                                   (U11)

where M=max(|e|,|n|,|w|,|s|).

Thus there is no first-order helper degeneracy anywhere on the diagonal strip
for any of the four A2.1 central patterns.  The candidate-source part of A2.1
has been reduced, simultaneously for all four patterns, to a uniform
second-order remainder estimate.

`the pinned independent arithmetic audit` checks only the exact algebraic
constant inequalities in (U7) and (U11).


### Exact elimination of the diagonal-angle variable on the small helper box

For the unified candidate-source stress, the diagonal angle can also be
removed analytically.

Write

    a := (w+s)/2,
    b := (w-s)/2,
    delta := eps-a,
    C_b := cos b-sin b.                            (U12)

For the candidate D--W and D--S source axes the normals are -f_W and f_S,
both with multiplier m.  Hence

    G_D = m(f_W-f_S).

A direct trigonometric expansion in the D frame gives

    G_D.e_D =  sqrt(2) m C_b cos delta,
    G_D.f_D = -sqrt(2) m C_b sin delta,
    |G_D|   =  sqrt(2) m C_b.                     (U13)

On |w|,|s|<=1/6 one has C_b>0.  The sum of the two D half-widths appearing in
the D--W and D--S separator thresholds is

    h_D(-f_W)+h_D(f_S)
      = sqrt(2) cos b cos delta.                  (U14)

The W/S half-width halves of those two thresholds are independent of eps, so
(U13)--(U14) contain all eps-dependence of the stress.

Put x=|delta|.  On the cap branch of the exact disk-center support,

    2 R_* sin x <= 1,

one obtains the eps-dependent contribution

    D_cap(x,b)
      = sqrt(2) m
        [(1-rho_*)cos b + rho_* sin b] cos x.     (U15)

Thus D_cap is monotone in x; its direction depends only on the sign of the
bracketed coefficient.

On the vertex branch,

    2 R_* sin x >= 1,

one obtains

    D_vert(x,b)
      = sqrt(2) m [
          (3 cos b-sin b)/2 * cos x
          +(cos b-sin b)/2 * sin x
          -R_*(cos b-sin b)].                    (U16)

Both coefficients of cos x and sin x are positive on |b|<=1/6.  Therefore

    d^2 D_vert / dx^2 < 0

for 0<=x<pi/2.  So D_vert is concave and its minimum on any interval is at
an endpoint.

Now assume the small helper box

    |w|,|s| <= 1/6,     |eps| <= 1/4.             (U17)

Then |a|<=1/6, and the delta interval always contains 0.  Its largest
absolute value is

    x_max = 1/4+|a| <= 5/12.                      (U18)

Combining the monotonicity of (U15) with the concavity of (U16), the exact
minimum over eps is attained at one of only three scalar positions:

    x=0,
    x=x_max,
    x=x_switch,                                   (U19)

where the switch point is included only when it lies in [0,x_max] and is
defined by

    sin x_switch = 1/(2 R_*).                     (U20)

At the switch the two formulas agree.  Its value is algebraic because

    cos x_switch = sqrt(1-1/(4R_*^2)).            (U21)

Thus no subdivision in eps is needed.  Once the four helper angles are
reduced to finitely many chamber vertices, the fifth angle contributes at
most the three fixed scalar evaluations (U19).


### Fixed helper-support signs on the small box

For the candidate-source family, use the elementary exterior support bound

    U(G,theta)
      = R_* |G| - (|G.e_theta|+|G.f_theta|)/2.      (U22)

At the candidate this is exact for E,N,W,S. On the entire small helper box

    |e|,|n|,|w|,|s| <= 1/6                         (U23)

its two absolute values have fixed signs, uniformly over all four A2.1
central choices and all four W--N / S--E candidate source choices:

    E:   G_E.e_E > 0,      G_E.f_E > 0,
    N:   G_N.e_N > 0,      G_N.f_N < 0,
    W:   G_W.e_W > 0,      G_W.f_W < 0,
    S:   G_S.e_S > 0,      G_S.f_S > 0.             (U24)

Thus the helper support introduces no additional chamber walls.

A coarse hand proof is enough. Throughout (U23),

    cos(1/6)>49/50,
    cos(1/3)>9/10,
    |sin theta|<=1/6,
    |sin(theta_i-theta_j)|<=1/3,
    |tan n|<1/5.                                    (U25)

The candidate constants satisfy

    1/3 < r < 3/8,      m > 4/5.                    (U26)

Every balance scale lambda in (U1) is at least cos(1/3)>9/10. Hence

    alpha=lambda sec n > 9/10,
    18/25 < beta=lambda(1+tan n) < 6/5.             (U27)

Whenever a cardinal W/S weight contains a transverse term, its size is at
most

    cos(1/6)+sin(1/6) < 7/6.                        (U28)

For E, if S--E is sourced by E then

    G_E.f_E = r-beta sin e
      > 1/3-(6/5)(1/6) > 0.

If S supplies the source axis instead, then

    G_E.e_E
      = beta cos e + r sin(e-s)
      > (18/25)(49/50)-(3/8)(1/3) > 0,

    G_E.f_E
      = -beta sin e + r cos(e-s)
      > -(6/5)(1/6)+(1/3)(9/10) > 0.

The remaining E projection is plainly positive.

For N, source N gives the signs immediately. With source W,

    G_N.e_N = alpha+r sin(w-n)
      > 9/10-(3/8)(1/3) > 0,

while

    G_N.f_N = -r cos(w-n) < 0.

For W the primary-frame component is always positive. The transverse
component has the main term -m; the worst possible positive correction is
at most

    (7/6)(1/6)+(3/8)(1/3),

which is strictly below 4/5<m. Thus G_W.f_W<0. The S calculation is the
reflected one: its transverse component has main term +m and the same total
error bound, so G_S.f_S>0. This proves (U24).

Consequently, after the diagonal-angle reduction (U12)--(U21), the only
nonsmooth helper chamber walls left in the unified candidate-source stress
are

    e=0,  s=0,  e=s,
    n=0,  w=0,  n=w.                                (U29)

In particular the four-angle box decomposes as a product of two elementary
six-sector arrangements; there are no hidden support-sign cases.

`the pinned independent arithmetic audit` checks only the scalar bounds
(U25)--(U28) and the positive reserve inequalities used above.


### Pair-factorized central balance on the small helper box

For the remaining small-box analysis there is a cleaner balance than (U1)--(U3):
the central force can be cancelled as the sum of two independent adjacent-pair
resultants.  This is the balance used below.

Keep the notation

    n_N=(-sin n,cos n),

and let q_W be the selected W-to-C central normal,

    q_W=(1,0)                 if W is cardinal,
    q_W=(cos w,sin w)         if W is own-primary.

Let q_S be the selected S-to-C central normal,

    q_S=(0,1)                 if S is cardinal,
    q_S=(-sin s,cos s)        if S is own-primary.

Choose the N/W central weights (alpha,gamma) by

    W cardinal:
      alpha = sec n,
      gamma = 1-tan n,

    W own:
      alpha = (cos w+sin w)/cos(w-n),
      gamma = (cos n-sin n)/cos(w-n).              (F1)

Then in both cases

    gamma q_W - alpha n_N = (1,-1).                (F2)

Indeed the cardinal row is immediate, while the own row is the solution of
the two-by-two linear system with determinant -cos(w-n).

Choose the E/S central weights (beta,delta) by

    S cardinal:
      beta=delta=1,

    S own:
      beta = 1-tan s,
      delta = sec s.                               (F3)

Then in both cases

    delta q_S - beta(1,0) = (-1,1).                (F4)

Therefore the two pair resultants cancel exactly at C:

    [gamma q_W-alpha n_N]
      +[delta q_S-beta(1,0)] = 0.                  (F5)

No W/S case split remains at the level of the central center.

On the small helper box |n|,|w|,|s|<=1/6 all weights in (F1)--(F3) are
strictly positive.  Indeed cos(w-n)>cos(1/3)>0, cos n,cos s>0, and each of
cos x+sin x, cos x-sin x, 1-tan x is positive there.  At the candidate all
four weights equal 1.

#### Exact pair decomposition of the stress defect

Keep the candidate outer multipliers r,m from (S0).  For W--N let the selected
source normal be

    n_5=(cos w,sin w)       or       (cos n,sin n),

and for S--E let

    n_6=(-sin s,cos s)      or       (-sin e,cos e).

The candidate D edges use

    n_7=(-sin w,cos w),
    n_8=( cos s,sin s).

The exterior forces are then

    G_N =  alpha n_N + r n_5,
    G_W = -gamma q_W - r n_5 + m n_7,

    G_E =  beta(1,0) + r n_6,
    G_S = -delta q_S - r n_6 + m n_8,

    G_D = -m n_7-m n_8.                            (F6)

Let U_i(G_i) denote the disk-center support bound for square i.  For E,N,W,S
we use the elementary vertex support (U22), whose signs are fixed by (U24);
for D use the exact support already reduced in (U12)--(U21).

Write H_X for the selected central threshold of helper X, and H_WN,H_SE for
the two adjacent-pair thresholds.  Since the D--W and D--S thresholds are

    1/2+h cos(eps-w),
    1/2+h cos(eps-s),      h=1/sqrt(2),

the full reverse-stress defect factors exactly as

    Phi = A(e,s) + B(n,w) + D(w,s,eps),             (F7)

where

    A(e,s)
      = beta H_E + delta H_S + r H_SE + m/2
        -U_E(G_E)-U_S(G_S),                         (F8)

    B(n,w)
      = alpha H_N + gamma H_W + r H_WN + m/2
        -U_N(G_N)-U_W(G_W),                         (F9)

    D(w,s,eps)
      = m h cos(eps-w)+m h cos(eps-s)-U_D(G_D).     (F10)

Thus all non-D terms have become genuinely two-dimensional: A depends only on
(e,s), B only on (n,w), and the sole remaining coupling is the already
one-dimensionally reducible D term.

At the candidate,

    A(0,0)=B(0,0),
    A(0,0)+B(0,0)+D(0,0,0)=0,                      (F11)

so the factorized stress remains exactly tangent to the candidate packing.

This factorization is the preferred form for the rest of the A2.1 small-box
proof.  In particular, separate helper concavity can now be proved pairwise,
with the D curvature treated as a single explicit correction.


### Fixed endpoint margin after pair factorization

The pair factorization leaves a particularly small endpoint problem.  Suppose
the helper chamber reduction sends

    e,n,w,s in {-1/6,0,1/6}.                       (F12)

For each such helper vertex, the exact diagonal minimization (U19) leaves only

    x=0,
    x=1/4+|(w+s)/2|,
    x=x_switch                                     (F13)

with the switch included only when it lies in the allowed interval.

Using the exact factorized stress (F7)--(F10), rational enclosures of the
candidate constants, and alternating Taylor bounds at the rational angles,
all noncandidate helper vertices have a substantial positive margin:

    Phi > 3/100.                                   (F14)

The actual smallest certified lower bound is greater than

    0.0300104036.

It occurs in a one-helper boundary configuration; thus the endpoint margin is
not delicate.  The all-zero helper vertex is intentionally excluded from
(F14): at x=0 it is the exact candidate equality, while nonzero diagonal
motion is already strictly positive by (Dmode).

There are 3456 fixed evaluations after accounting for whether the switch
point is present.  This is not a subdivision tree: the helper values are the
nine pair-chamber vertices and the diagonal values are exactly the three
analytic minimizers in (F13).

`the pinned independent arithmetic audit` performs these fixed exact evaluations.
The smooth-helper chamber calculus is supplied by the subsequent Pattern-10,
Pattern-14, and Pattern-26 reductions; no additional candidate-source step is
open here.


## A2.1 Pattern 10 hand lemma — W-cardinal D--W classification

Pattern 10 has W cardinal at C and D own-primary.  Use only C,W,D and the
three separators

    C -> D on e_D,       weight alpha,
    W -> C on e_x,       weight beta,
    W -> D on the tested axis, weight mu.

For the four primary directions use

    W-primary - : (alpha,beta,mu)=(1,11,8)/20,
    W-primary + : (13,1,6)/20,
    D-primary - : (1,11,8)/20,
    D-primary + : (10,1,9)/20.

For the low-d secondary directions use

    W-secondary - : (35,40,25)/100,
    W-secondary + : (35,40,25)/100,
    D-secondary - : (43,30,27)/100,
    D-secondary + : (35,40,25)/100.               (P10DW1)

The D-secondary negative row is the only retuned stress; all other rows are
the original initial weights.

Use the universal exterior far-vertex support inequality

    g.p <= R_* |g|-h_Q(g).                         (P10DW2)

For the D-sourced rows, if (u,v) are the local W-force components, weaken

    |u|+|v| >= u-v       for the negative orientation,
    |u|+|v| >= u+v       for the positive orientation.             (P10DW3)

This removes the only oblique force-sign wall.  After writing

    x=d-w,

every row is bounded below by

    Phi(w,d)=C+F_sigma(w)+G(d)+H_tau(x),            (P10DW4)

where sigma records the sign of w and tau the sign of x.  The only chamber
walls are therefore

    w=0,     d=w.

The functions are elementary combinations of sin, cos and one square root.
For example a W-primary row has square-root factors

    sqrt(beta^2+mu^2+2 beta mu eta cos w),
    sqrt(alpha^2+mu^2-2 alpha mu eta cos x),

while a W-secondary row has the same form with cos replaced by sin.
D-primary and D-secondary have one constant D support and one W square-root
factor depending only on d.

Direct differentiation, using R_*<17/10 and alternating Taylor bounds on
[-2/5,pi/4+2/5], gives strict separate concavity on every chamber.  Because
one chamber wall is the oblique edge d=w, also restrict there.  Since x=d-w
is then zero, H is constant on that edge and

    d^2/dt^2 Phi(t,t)=F''(t)+G''(t)<0,    0<=t<=2/5.

Thus the restriction to every chamber edge is concave.  The weakest certified
upper bounds for
(partial_w^2 Phi, partial_d^2 Phi) in the eight rows are

    Wp- : (-1.52,-0.34),     Wp+ : (-0.20,-0.47),
    Dp- : (-0.50,-0.004),    Dp+ : (-0.45,-0.52),
    Ws- : (-0.31,-0.21),     Ws+ : (-0.31,-0.21),
    Ds- : (-0.52,-0.24),     Ds+ : (-0.52,-0.12).   (P10DW5)

Together with the diagonal curvature just stated, each chamber minimum is
at a chamber vertex.  Across the rectangle
-2/5<=w<=2/5 the complete vertex set is

    (-2/5,0), (-2/5,dmax), (0,0), (0,dmax),
    (2/5,0), (2/5,dmax), (2/5,2/5),

with dmax=pi/4 for primary rows and dmax=1/2 for the low-d secondary rows.

The weakest lower margins, in the same row order as (P10DW5), are

    > .219, .062, .106, .244, .0059, .017, .012, .017.             (P10DW6)

Consequently no primary D--W source is possible, and neither secondary source
is possible for d<=1/2.  Hence every Pattern-10 survivor satisfies

    1/2<d<=pi/4,
    D--W in {W-secondary,D-secondary}.             (P10DW7)

An independent arithmetic audit checks only the
one-dimensional coordinate and diagonal curvature inequalities and the fixed
chamber vertices.  It contains no multidimensional subdivision.


## A2.1 Pattern 10 hand lemma — five noncandidate D-edge graphs

After (P10DW7) and the common D--S primary reductions, the possible D-edge
graphs are

    D--W in {W-secondary,D-secondary},
    D--S in {S-primary,S-secondary,D-secondary},

with S-primary only for s>=1/6.  Apart from the candidate graph
W-secondary/S-secondary, the five graphs are

    Ws/Sp,  Ws/Ds,  Ds/Sp,  Ds/Ss,  Ds/Ds.          (P10E0)

Use only C,W,D,S and weights (CW,SC,CD,DW,DS)

    Ws/Sp : (523, 10,  0,270,197)/1000,
    Ws/Ds : (379, 14, 42,279,286)/1000,
    Ds/Sp : (238, 42,167,298,255)/1000,
    Ds/Ss : (172,351,  0,233,244)/1000,
    Ds/Ds : (263,  1,  0,368,368)/1000.             (P10E1)

For every exterior force g use the universal far-vertex support bound

    g.p <= R_* |g|-(|g.e|+|g.f|)/2.                 (P10E2)

There is no need to locate a force-sign wall.  Since

    |u|+|v| >= sigma u+tau v

for arbitrary sigma,tau in {+1,-1}, weaken (P10E2) with the fixed signed
choices

    W : (+,-) in all five rows,
    S : (+,-) for Sp, (+,+) for Ss or Ds,
    D : (+,+), (+,-), (+,+), (+,+), 0

in the row order (P10E1).  The last entry is zero because in Ds/Ds the two
equal D-secondary edge weights cancel the D force exactly.  Thus all
cap/vertex and force-sign switches disappear.

Put

    Delta=d-w,     T=d-s.

On each of the rectangular sign chambers cut only by w=0 and, when needed,
s=0, direct expansion gives

    Ws/Sp:
      Phi=C+F_sigma(w)+G(s)+K(Delta)+M(s-w),

and in the other four rows

      Phi=C+F_sigma(w)+G_tau(s)+H(d)+K(Delta)+L(T). (P10E3)

Every displayed term is a one-variable combination of sin, cos and one square
root.  For example, in the retuned Ws/Ds row the only delicate square root is

    sqrt(md^2+m7^2+m8^2
         +2 md m7 sin Delta-2 m7 m8 cos Delta),

with (md,m7,m8)=(42,279,286)/1000.  The retuning keeps this norm away from
the near-cancellation of the initial stress and leaves a uniform scalar
curvature reserve.

Alternating Taylor bounds on the one-variable ranges prove separate
concavity in every chamber, except for one harmless Ws/Sp subcase.  The
weakest certified coordinate-curvature upper bounds are

    Ws/Ds : Phi_ww < -0.118, Phi_ss < -0.325, Phi_dd < -0.237,
    Ds/Sp : Phi_ww < -0.564, Phi_ss < -0.250, Phi_dd < -0.473,
    Ds/Ss : Phi_ww < -0.426, Phi_ss < -0.220, Phi_dd < -0.130,
    Ds/Ds : Phi_ww < -0.665, Phi_ss < -0.403, Phi_dd < -0.566.       (P10E4)

For Ws/Sp, the w- and d-curvatures are respectively below -0.689 and -0.295
on the two w-sign chambers.  When w>=0 the s-curvature is below -0.244.
When w<=0 one instead has the stronger monotonicity estimate

    partial_s Phi < -0.167,                         (P10E5)

so s is sent directly to 2/5.  Thus this row also reduces to fixed chamber
vertices.

The resulting weakest endpoint margins in the row order (P10E1) are

    > .02281, .01674, .08186, .00140, .06279.       (P10E6)

Hence all five graphs in (P10E0) are impossible.  Every Pattern-10 survivor
therefore has exactly

    D--W=W-secondary,     D--S=S-secondary.         (P10E7)

An independent arithmetic audit verifies only the scalar
curvature/monotonicity inequalities and the fixed chamber vertices.  It
contains no multidimensional subdivision or adaptive replay.


## A2.1 Pattern 10 candidate closure

Return to Pattern 10 after the D-edge classification and noncandidate graph
exclusions.  Thus

    E cardinal, N own, W cardinal, D own, S cardinal,
    1/2<d<=pi/4,
    D--W=W-secondary,
    D--S=S-secondary.                              (P10C0)

Use the pair-factorized stress (F7)--(F10).

### Reflected adjacent-pair envelopes

The E/S pair is exactly the pattern-12 E/S pair already treated in the R22-c
hand proof.  Hence every S--E source is bounded below by the equality
envelope

    A(e,s) >= b(s)
      := A_Sp(0,s),    s<=0,
         A_Es(0,s),    s>=0.                       (P10C1)

The N/W pair is the reflection of the pattern-13 E/S pair under

    (e,s)=(-n,-w).                                 (P10C2)

The reflected source lemma is valid on its reflected small-angle domain

    -1/6 <= w <= 2/5.

On this strip every W--N source is bounded below by

    B(n,w) >= a(w)
      := B_Ns(0,w),    -1/6<=w<=0,
         B_Wp(0,w),     0<=w<=2/5.                 (P10C3)

Thus, on w>=-1/6,

    Phi >= F10(w,s,eps):=a(w)+b(s)+D(w,s,eps).     (P10C4)

### Hand reduction of the source-independent tails

The three regions outside the reflected pair-envelope strip are removed by
source-independent C/W/D/S stresses with weights (CW,SC,CD,DW,DS)

    s<=-3/10 : (296,360,0,216,128)/1000,
    s>= 3/10 : (316,278,0,224,182)/1000,
    w<=-1/6  : (469,130,0,310, 91)/1000.            (P10C5)

The first two apply on the full -2/5<=w<=2/5, 1/2<=d<=pi/4 ranges; the
third applies on -2/5<=w<=-1/6, |s|<=3/10.

As in (P10E2), use the universal far-vertex support bound and weaken the
local absolute values with the fixed signed choices

    W:(+,-),    S:(+,+),    D:(+,+).

All three stresses have CD weight zero.  Consequently, after putting

    Delta=d-w,    T=d-s,

their lower bounds factor exactly as

    Phi=C+F_sigma(w)+G_tau(s)+K(Delta)+L(T)+M(s-w), (P10C5a)

where

    K(x)=m7(cos x+sin x),
    L(x)=m8 cos x,

and the only D-force square root is

    M(x)=-R_* sqrt(m7^2+m8^2+2 m7 m8 sin x).        (P10C5b)

Thus the only chamber walls are w=0 and s=0.  One-dimensional Taylor
enclosures give, for the negative-S tail,

    Phi_ww<-0.336,   Phi_ss<-0.306,   Phi_dd<-0.284,

for the positive-S tail,

    Phi_ww<-0.273,   Phi_ss<-0.183,   Phi_dd<-0.406,

and for the negative-W strip,

    Phi_ww<-0.595,   Phi_ss<-0.034,   Phi_dd<-0.445. (P10C5c)

Every chamber minimum is therefore a fixed vertex.  The weakest exact
endpoint margins in the three rows of (P10C5) are respectively

    > .02309, .00884, .01083.                       (P10C5d)

An independent arithmetic audit checks only
these scalar curvature inequalities and the fixed chamber vertices.  It has
no multidimensional subdivision or adaptive replay.

Hence it remains only to consider

    |s|<3/10,     -1/6<=w<=2/5.                    (P10C6)

### Scalar derivative reduction on the middle strip

The already-used E/S pair calculus gives

    b'(s)<2/5,             -2/5<s<0,
    b'(s)>1,                0<s<3/10,
    b'(s)>9/10,             0<s<2/5.              (P10C7)

By the reflection (P10C2),

    a'(w)<-9/10,           -1/6<w<0,
    a'(w)>-2/5,             0<w<2/5.              (P10C8)

For the diagonal term, the exact cap/vertex formulas give the following
bounds on the corresponding sign regions:

    D_w < 4/5,             w<0,                    (P10C9)

    D_s < -1/2,            w>=0, -3/10<s<0,        (P10C10)

    D_s > -19/20,          w>=0, 0<s<3/10,         (P10C11)

    D_w > 9/20,            w>=0, s=0.              (P10C12)

An independent arithmetic audit checks these
explicit derivative inequalities directly from the cap/vertex formulas.  It
has no packing-state search or adaptive subdivision.

Now reduce in a fixed order.

* If w<0, then by (P10C8)--(P10C9),

      partial_w F10 < -9/10+4/5 = -1/10.

  Hence increasing w to 0 strictly decreases F10.

* We may therefore assume w>=0.  If s<0, then

      partial_s F10 < 2/5-1/2 = -1/10,

  so increasing s to 0 decreases F10.  If 0<s<3/10, then

      partial_s F10 > 1-19/20 = 1/20,

  so decreasing s to 0 decreases F10.

  Thus every minimum on the middle strip has s=0.

* At s=0 and w>0,

      partial_w F10 > -2/5+9/20 = 1/20,

  so decreasing w to 0 decreases F10.

Therefore every Pattern-10 candidate minimum occurs at

    w=s=0.                                         (P10C13)

At that point the same exact diagonal identity as R22-c gives

    F10(0,0,eps)
      = 2m(d_*-1/sqrt(2))(1-cos eps) >= 0,          (P10C14)

with equality only at eps=0.

Equality in the pair envelopes would additionally require e=n=0 and equality
source axes.  But Pattern 10 has N canonically own-primary, and at n=0 the
own and cardinal central normals coincide; the cardinal-preferred rule
therefore forbids the Pattern-10 bit.  Thus the hypothetical Pattern-10
configuration cannot realize equality.

Consequently **Pattern 10 is closed by hand**.  No multidimensional replay
is a logical premise of the Pattern-10 argument.


## A2.1 Pattern 14 closure

Pattern 14 is

\[
(E_c,N_o,W_o,D_o,S_c).
\]

All initial D-edge reductions in this section use only \(C,W,D,S\), so the
A2.2 reductions remain valid although N is own-primary.

### D-edge classification

For \(w\ge0\), P17--P18 give

\[
D\!-\!W=W\text{-secondary},\qquad
d>\pi/4-1/4>1/2.
\]

For \(w<0\), the negative-W primary-axis exclusions remove W-primary and
D-primary, and the secondary low-d stress removes both remaining secondary
sources when \(d\le1/2\). Hence throughout Pattern 14

\[
1/2<d\le\pi/4,\qquad
D\!-\!W\in\{W\text{-secondary},D\text{-secondary}\}. \tag{P14-1}
\]

The high-D D--S primary-axis lemma similarly leaves

\[
D\!-\!S\in\{S\text{-primary},S\text{-secondary},D\text{-secondary}\},
\]

and

\[
D\!-\!S=S\text{-primary}\Longrightarrow 1/6<s<2/5. \tag{P14-2}
\]

The five noncandidate D-edge graphs are eliminated as follows.

- D-secondary/D-secondary and D-secondary/S-primary on negative W are the
  source-independent R22-d hand stresses.
- W-secondary/S-primary uses
  \((376,233,0,215,176)/1000\). Outside \(|d-w|\le1/10\) use
  \(|u|+|v|\ge\sqrt{u^2+v^2}\); in the middle strip use
  \(|u|+|v|\ge-u+v\). The five scalar chambers have negative coordinate
  and oblique-edge curvature; the weakest endpoint margin is \(>.00143\).
- W-secondary/D-secondary for \(w\ge-1/5\) uses
  \((407,82,0,264,247)/1000\); the part \(w\le-1/5\) is the R22-d
  hand stress. After the walls \(w=0,s=0,d=w\), the defect is separately
  concave, including the oblique wall, and its weakest endpoint is \(>.00276\).
- D-secondary/S-secondary for \(-1/5\le w\le0\) uses
  \((153,170,290,263,124)/1000\); the far part is the R22-d chamber
  stress. After the sole sign walls the scalar curvatures are negative and
  the weakest endpoint margin is \(>.02025\).

Thus the only D-edge survivor is

\[
D\!-\!W=W\text{-secondary},\qquad
D\!-\!S=S\text{-secondary}.                    \tag{P14-3}
\]

The archived files `check_A2_pattern14_Ws_Sp_hand.py` and
`check_A2_pattern14_Dedges_hand.py` at
`b51d8a88c30588e279882b8efd5441304635f527` independently audit exactly
these scalar curvature and endpoint inequalities.

### Source-independent candidate tails

For

\[
2/25\le w\le\pi/4,
\]

use the fixed stress

\[
(381,212,0,252,155)/1000.                          \tag{P14-4}
\]

With universal far-vertex support the defect separates into one-variable
terms in \(w,s,d-w,d-s,s-w\). The only walls are \(s=0\) and \(d=w\);
coordinate and wall concavity leave fixed vertices, all with margin
\(>.00957\).

For

\[
-2/3\le w\le-21/50,
\]

the three-chamber negative-tail argument has scalar endpoint margins

\[
>.01537,\qquad >.00208,\qquad >.00922,              \tag{P14-5}
\]

with the positive-S chamber using
\((436,227,47,153,137)/1000\). Hence every candidate survivor satisfies

\[
-21/50<w<2/25.                                    \tag{P14-6}
\]

### Nonnegative-W adjacent-pair closure

On \(0\le w\le2/25\), balance the N/W pair with

\[
\alpha={\cos w+\sin w\over\cos(w-n)},\qquad
\gamma={\cos n-\sin n\over\cos(w-n)}.             \tag{P14-7}
\]

For W-primary and N-secondary the one-sided n-derivatives point to \(n=0\).
For W-secondary the three chambers cut by \(n=0,n=w\) are monotone. For
N-primary, n-concavity reduces the only nonmonotone chambers to the four
scalar edges

\[
n=-3/10,\qquad n=0,\qquad n=w,\qquad n=5/12.
\]

Each edge is monotone or concave with positive endpoint reserve. Therefore
all four W--N source choices satisfy

\[
B_u(n,w)\ge B_{Wp}(0,w).                           \tag{P14-8}
\]

At \(n=0\) this is exactly the R22-c N-cardinal/W-own equality profile.
The E/S pair in Pattern 14 is cardinal/cardinal. By the extended
Pattern-12 theorem (A22-env-ES-P12+), its equality envelope is valid on the
entire needed range \(-2/5<s<2/5\), including \(s\ge1/6\). Thus the R22-c
reduced scalar monotonicity applies without any domain gap and forces

\[
w=s=0
\]

on the nonnegative candidate strip, where the diagonal identity is
nonnegative. Hence no Pattern-14 candidate has \(w\ge0\).

### Negative-W adjacent-pair reserve

On the remaining strip \(-21/50<w<0\), the four W--N source axes satisfy

\[
B_u(n,w)\ge B_*+{73\over100}(-w).                 \tag{P14-9}
\]

The only n-walls are \(n=0,n=w\). In all three chambers the reserve is
concave in n, hence reduces to the same four scalar edges

\[
-3/10,\quad w,\quad0,\quad5/12.
\]

The E/S source reduction is independent of N and of the sign of w; it sends
\(s\) to zero. On \(s=0\), the exact diagonal term loses at most

\[
{71\over100}(-w).                                  \tag{P14-10}
\]

Therefore the total reserve is

\[
\left({73\over100}-{71\over100}\right)(-w)
 ={1\over50}(-w)>0.                               \tag{P14-11}
\]

Thus Pattern 14 is impossible. This is the full Pattern-14 hand closure;
the archived Pattern-14 `_hand.py` files are arithmetic audits only.

## A2.1 Pattern 26 closure

Pattern 26 is

\[
(E_c,N_o,W_c,D_o,S_o).
\]

The E and W helpers are opposite cardinal helpers. From the normalization
cap-depth theorem (N25)--(N26),

\[
|e|+|w|<4c_0<23/50,\qquad |w|<2/5.                \tag{P26-1}
\]

The Pattern-10 D--W classification uses only \(C,W,D\), so every survivor
satisfies

\[
1/2<d\le\pi/4,qquad
D\!-\!W\in\{W\text{-secondary},D\text{-secondary}\}. \tag{P26-2}
\]

### Complete noncandidate D-edge classification

Every noncandidate graph is eliminated by a fixed finite set of scalar
chambers.  The stress tuples below are ordered
\((CW,SC,CD,DW,DS)/1000\); all are nonnegative and sum to one.

**W-secondary / S-primary.**  The pin orientation is negative for
\(s\le-1/4\) and positive for \(s\ge-27/100\):

| s-range | stress |
|---|---|
| \([-4/5,-1/4]\) | \((0,500,0,0,500)\) |
| \([-27/100,1/5]\) | \((525,1,0,272,202)\) |
| \([1/5,1/2]\) | \((388,295,0,206,111)\) |
| \([1/2,4/5]\) | \((304,428,0,161,107)\) |

For W use the global x-dominant cap support, for S its own-primary support,
and for D the far-vertex bound
\(|u|+|v|\ge\sqrt{u^2+v^2}\).  The w derivative sends each positive
orientation chamber to \(w=0\); the remaining s/d chambers are concave,
including the walls \(d-s=0,\pi/2\).

**D-secondary / S-primary.**  The negative pin orientation
\(-4/5\le s\le-1/4\) uses

\[
(70,336,122,144,328).                              \tag{P26-3}
\]

The positive orientation uses the seven fixed chambers

| s-range | w-range | stress |
|---|---|---|
| \([-27/100,1/5]\) | \([-2/5,2/5]\) | \((0,0,678,0,322)\) |
| \([1/5,7/20]\) | \([-2/5,0]\) | \((109,16,586,193,96)\) |
| \([7/20,1/2]\) | \([-2/5,-1/5]\) | \((57,195,521,168,59)\) |
| \([7/20,1/2]\) | \([-1/5,0]\) | \((83,75,574,245,23)\) |
| \([1/5,1/2]\) | \([0,2/5]\) | \((166,1,570,261,2)\) |
| \([1/2,4/5]\) | \([-2/5,0]\) | \((40,409,382,132,37)\) |
| \([1/2,4/5]\) | \([0,2/5]\) | \((98,412,338,149,3)\) |

After fixing the natural sign walls, each defect has the separated form

\[
C+F(w)+G(s)+H(d)+K(d-w)+L(d-s),
\]

and all remaining minima reduce by scalar concavity to chamber endpoints.

**W-secondary / D-primary.**

| s-range | w-range | stress |
|---|---|---|
| \([-4/5,-1/5]\) | \([-2/5,2/5]\) | \((80,530,2,45,343)\) |
| \([-1/5,1/5]\) | \([-2/5,2/5]\) | \((175,457,11,132,225)\) |
| \([1/5,1/2]\) | \([-2/5,2/5]\) | \((178,478,74,126,144)\) |
| \([1/2,13/20]\) | \([-2/5,2/5]\) | \((196,432,106,137,129)\) |
| \([13/20,4/5]\) | \([-2/5,0]\) | \((256,413,59,191,81)\) |
| \([13/20,4/5]\) | \([0,2/5]\) | \((218,430,135,118,99)\) |

**D-secondary / D-primary.**

| s-range | stress |
|---|---|
| \([-4/5,-1/5]\) | \((74,501,16,93,316)\) |
| \([-1/5,1/5]\) | \((94,512,14,118,262)\) |
| \([1/5,1/2]\) | \((111,457,159,139,134)\) |
| \([1/2,13/20]\) | \((116,422,201,146,115)\) |
| \([13/20,4/5]\) | \((86,396,286,141,91)\) |

In both primary families universal far-vertex support leaves only
one-variable functions of \(w,s,d,d-w,d-s\); the walls
\(s=0,d-s=0,d-s=\pi/2\) are handled by the same concavity argument.

**W-secondary / D-secondary.**

| s-range | stress |
|---|---|
| \([-4/5,-1/5]\) | \((304,172,13,247,264)\) |
| \([-1/5,1/5]\) | \((372,42,14,283,289)\) |
| \([1/5,1/2]\) | \((283,314,10,199,194)\) |
| \([1/2,4/5]\) | \((274,382,1,179,164)\) |

Here the w derivative is negative for \(w<0\) and positive for \(w>0\),
so \(w=0\). The remaining d dependence is monotone except for the
\(d-s=\pi/2\) wall, where concavity again reduces to endpoints.

**D-secondary / S-secondary.**

| s-range | w-range | stress |
|---|---|---|
| \([-4/5,-1/5]\) | \([-2/5,2/5]\) | \((162,355,1,234,248)\) |
| \([-1/5,1/5]\) | \([-2/5,0]\) | \((123,338,80,242,217)\) |
| \([-1/5,1/5]\) | \([0,2/5]\) | \((197,161,302,236,104)\) |
| \([1/5,1/2]\) | \([-2/5,2/5]\) | \((133,399,84,188,196)\) |
| \([1/2,4/5]\) | \([-2/5,2/5]\) | \((99,368,237,169,127)\) |

**D-secondary / D-secondary.**

| s-range | stress |
|---|---|
| \([-4/5,-1/5]\) | \((148,150,1,350,351)\) |
| \([-1/5,1/5]\) | \((198,9,2,395,396)\) |
| \([1/5,1/2]\) | \((217,0,1,391,391)\) |
| \([1/2,4/5]\) | \((107,335,192,219,147)\) |

In the last two families the exact support again factors into scalar
functions. The coordinate and relevant oblique-wall curvatures are strictly
negative on each displayed chamber, leaving only one-dimensional s-edges.

Thus every noncandidate D-edge graph is impossible and Pattern 26 reduces to

\[
D\!-\!W=W\text{-secondary},\qquad
D\!-\!S=S\text{-secondary}.                    \tag{P26-4}
\]

The archived Pattern-26 `_hand.py` files at
`b51d8a88c30588e279882b8efd5441304635f527` independently check the
displayed scalar curvatures and endpoint signs; no adaptive or
multidimensional value replay is a premise of this classification.

### Candidate tails

Two source-independent S-tail stresses work on the whole
\(-2/5\le w\le2/5\) range:

\[
s\le-1/6:\quad (360,253,0,241,146)/1000,
\]

\[
s\ge1/2:\quad (286,396,0,171,147)/1000.          \tag{P26-5}
\]

With CD weight zero the D-force norm depends only on \(s-w\); after the
walls \(w=0\) and \(d-s\in\{0,\pi/2\}\), coordinate and wall
concavity reduce to fixed vertices.

On the remaining negative-W middle strip

\[
-2/5\le w\le-1/6,qquad -1/6\le s\le1/2,
\]

use

\[
(460,154,0,303,83)/1000.                           \tag{P26-6}
\]

The defect is

\[
C+F(w)+G_{\pm}(s)+K(d-w)+L(d-s)+M(s-w),
\]

with the sole wall \(s=0\). Every coordinate curvature is negative; the
weakest fixed endpoint margin is \(>.00654\). Therefore it remains only

\[
-1/6\le w\le2/5,qquad -1/6\le s\le1/2.         \tag{P26-7}
\]

### Adjacent-pair source envelope

The N/W pair is exactly the Pattern-10 N-own/W-cardinal pair, so its equality
profile is \(a(w)\). For the E-cardinal/S-own pair, direct source-by-source
calculus gives, for every S--E source axis,

\[
A_v(e,s)\ge b(s):=
\begin{cases}
A_{Sp}(0,s),&s\le0,\\
A_{Es}(0,s),&s\ge0.
\end{cases}                                      \tag{P26-8}
\]

The only walls are \(e=0,e=s\). For \(s\le0\), all sources move to
\(e=0\) by one-sided derivatives. For \(s\ge0\), E-secondary moves to zero
and E-primary to \(e=\min(s,2/5)\); the S-secondary high-s dip is bounded by
a derivative loss \(<1/160\) against a one-dimensional reserve \(>7/100\).
S-primary is concave on \(e<0\), and on \(0<e<s\) three fixed e/s bands
reduce the minimum to \(e=0\) or \(e=\min(s,2/5)\). The tiny
\(0\le s\le1/100\) corner is radial with \(e=ts\). Thus (P26-8) is a
one-dimensional chamber proof.

Consequently

\[
F_{26}(w,s,\epsilon)=a(w)+b(s)+D(w,s,\epsilon).    \tag{P26-9}
\]

### Scalar closure

The explicit derivatives give:

- if \(w<0\), \(\partial_wF_{26}<-1/10\), so w moves to zero;
- if \(w\ge0\), \(F_{26}\) is concave in w, so only
  \(w=0\) and \(w=2/5\) remain;
- at \(w=0,s<0\), \(\partial_sF_{26}<0\), so s moves to zero;
- at \(w=0,s\ge0\), the s-curvature is negative, so only
  \(s=0,1/2\) remain.

On \(w=2/5\), the defect is strictly increasing in \(\epsilon\). At the
lower epsilon edge it is concave in s; the three endpoint values
\(s=-1/6,0,1/2\) are all \(>1/100\). The remaining
\((w,s)=(0,1/2)\) face is one-dimensional in epsilon and is also
\(>1/100\).

At \(w=s=0\),

\[
F_{26}(0,0,\epsilon)
 =2m(d_*-1/\sqrt2)(1-\cos\epsilon)\ge0.           \tag{P26-10}
\]

Thus Pattern 26 is fully closed by hand chamber calculus.


## A2.3 hand closure: Patterns 30, 28, 29, 31

The A2.3 rows all have W,D,S canonically own-primary.  Pattern 30 is the
maximal row

    E cardinal, N own, W own, D own, S own,

and Patterns 28,29,31 differ only in the E/N bits.  We first hand-reduce the
D-edge graph for Pattern 30 using only C,W,D,S; those reductions therefore
transfer to all four rows.

### Common D-edge classification

The Pattern-30 hand stresses close every noncandidate D-edge graph:

- W-secondary/S-primary:
  an independent arithmetic audit and
  an independent arithmetic audit;
- W-secondary/D-primary and D-secondary/D-primary:
  an independent arithmetic audit,
  an independent arithmetic audit;
- D-secondary/S-primary:
  an independent arithmetic audit;
- W-secondary/D-secondary and D-secondary/D-secondary:
  an independent arithmetic audit,
  an independent arithmetic audit;
- D-secondary/S-secondary:
  an independent arithmetic audit together with the universal hard-corner
  lemma an independent arithmetic audit.

After center elimination, every one of these stresses is a sum of
one-variable functions of

    w, s, d, d-w, d-s,

with only the explicitly stated sign/support walls.  Coordinate concavity or
monotonicity, plus curvature on the oblique walls when present, reduces every
minimum to fixed chamber vertices or scalar edges.  In the universal hard
D-secondary/S-secondary corner, 53 fixed rational (w,s) cells are used, one
stress per cell; each cell is separately concave in w,s,d, so only its eight
vertices remain.

Thus all four A2.3 patterns reduce to the candidate graph

    D--W=W-secondary,
    D--S=S-secondary.                              (A23C0)

### Universal candidate tails

Three hand lemmas are shared by Patterns 28,29,30,31.

First,
an independent arithmetic audit removes

    s<=-1/6,      s>=1/2.                          (A23C1)

Second,
an independent arithmetic audit removes

    w>=2/25.                                       (A23C2)

Both use zero C--D weight.  The W and S exterior forces are constant in
their own frames, while a fixed signed far-vertex bound makes the D support a
sum of one-variable terms in d-w,d-s,s-w.  Coordinate and oblique-wall
concavity leave fixed vertices.

Third, the old far-negative adaptive replay is replaced by
an independent arithmetic audit.  On

    -2/3<=w<=-21/50,
    -1/6<=s<=1/2,
     1/2<=d<=pi/4,

use

    (CW,SC,CD,DW,DS)=(400,283,0,166,151)/1000.     (A23C3)

Write

    Delta=d-w,     T=d-s.

For the D force,

    u=(166/1000) sin Delta+(151/1000) cos T,
    v=(166/1000) cos Delta-(151/1000) sin T.

On the whole box \(u>0\) and \(u>|v|\), so \(U=u\) and
\(V=|v|\) in the exact disk support.  Split by

\[
2R_*|v|\lesseqgtr\sqrt{u^2+v^2}.                  \tag{A23V0}
\]

On the cap branch the earlier separated formula is valid.  On the vertex
branch,

\[
u^2+v^2=p^2+q^2+2pq\sin(s-w).                     \tag{A23V1}
\]

Hence the only new radical is

\[
M(s-w)=-R_*\sqrt{p^2+q^2+2pq\sin(s-w)}.           \tag{A23V2}
\]

If \(v\ge0\), the vertex terms are

\[
K_+(\Delta)=p(\sin\Delta+\cos\Delta),\qquad
L_+(T)=q\cos T.                                    \tag{A23V3}
\]

If \(v\le0\), they are

\[
K_-(\Delta)=p\sin\Delta,\qquad
L_-(T)=q(\cos T+\sin T).                           \tag{A23V4}
\]

Thus every cap/vertex/sign chamber has the separated form

\[
\Phi=C+F(w)+G_\sigma(s)+K_\tau(d-w)+L_\tau(d-s)+M_\tau(s-w), \tag{A23V5}
\]

where \(M=0\) on the cap branch and is (A23V2) on the vertex branch.

The two support formulas meet with equal first derivative.  At the switch,
put \(U=u,V=|v|,Q=\sqrt{U^2+V^2}\).  Then

\[
Q=2R_*V,\qquad U=(2\rho_*+1)V,
\]

because \(R_*^2=\rho_*^2+\rho_*+1/2\).  The cap and vertex values are both
\(\rho_*U\), while the vertex gradient

\[
R_*(U,V)/Q-(1/2,1/2)=(\rho_*,0)
\]

is the cap gradient.  Therefore no hidden coordinate minimum is created at
the switch.

For the vertex radical,

\[
M''(x)
 =R_*\left(
 {pq\sin x\over Q(x)}
 +{p^2q^2\cos^2x\over Q(x)^3}
 \right),
\quad
Q(x)^2=p^2+q^2+2pq\sin x.                          \tag{A23V6}
\]

Alternating Taylor bounds on
\(19/75\le x=s-w\le7/6\), split only at \(x=2/3\), give

\[
M''(x)<3/20.                                       \tag{A23V7}
\]

On the same domain,

\[
F(w)>6/25,\qquad G_\sigma(s)>1/10,
\]

\[
p\sin(d-w)>13/100,\qquad
p(\sin(d-w)+\cos(d-w))>4/25,
\]

\[
q\cos(d-s)>2/25,\qquad
q(\cos(d-s)+\sin(d-s))>3/20.
\]

Therefore every vertex/sign chamber satisfies

\[
\Phi_{ww}<-1/5,\qquad \Phi_{ss}<-3/100.            \tag{A23V8}
\]

Together with the cap curvatures and the \(C^1\) switch, the exact defect is
separately concave in \(w\) and \(s\).  Hence it suffices to take

\[
w\in\{-2/3,-21/50\},\qquad s\in\{-1/6,0,1/2\}.
\]

The six remaining one-dimensional \(d\)-edges are split only at their scalar
support/sign switches and bounded by alternating Taylor polynomials.  The
weakest lower margin is

\[
\Phi>1/2500.                                       \tag{A23V9}
\]

Thus the exact two-branch support proves the far-negative tail, and every
A2.3 candidate survivor satisfies

    -21/50<w<2/25,
    -1/6<s<1/2.                                    (A23C5)

No multidimensional value replay occurs in the repaired far-negative tail.

### Explicit A2.3 stress data

For auditability, the fixed C/W/D/S weights used in the common A2.3 graph
classification are recorded here.  Every tuple is

    (CW,SC,CD,DW,DS)/1000.

The associated angle cells are the fixed chambers stated in the
corresponding hand reductions above; no adaptive choice is made.

#### W-secondary / S-primary signed chambers

    ("p1",(-F(2,3),F(0)),(-F(27,100),F(1,5)),1,1,-1,(322,219,0,230,229)),
    ("p2",(F(0),F(1,2)),(-F(27,100),F(1,5)),1,-1,1,(512,55,0,225,208)),
    ("p3",(F(1,2),F(13,20)),(-F(27,100),F(1,5)),1,-1,1,(531,33,0,266,170)),
    ("p4",(-F(2,3),F(0)),(F(1,5),F(1,2)),1,1,-1,(309,385,0,155,151)),
    ("p5",(F(0),F(1,2)),(F(1,5),F(1,2)),1,1,1,(427,99,0,270,204)),
    ("p6",(F(1,2),PI.hi/4),(F(1,5),F(1,2)),1,-1,1,(452,59,0,278,211)),
    ("p7a",(-F(2,3),-F(2,5)),(F(1,2),PI.hi/4),1,1,-1,(389,367,0,142,102)),
    ("p7b",(-F(2,5),-F(1,5)),(F(1,2),PI.hi/4),1,1,1,(387,366,0,185,62)),
    ("p7c",(-F(1,5),F(0)),(F(1,2),PI.hi/4),1,1,1,(322,403,0,181,94)),
    ("p8",(F(0),F(1,2)),(F(1,2),PI.hi/4),1,1,1,(324,392,0,174,110)),
    ("p9",(F(1,2),PI.hi/4),(F(1,2),PI.hi/4),1,1,1,(485,44,0,255,216)),

Two additional simple chambers use
    (CW,SC,CD,DW,DS)=(56,453,41,0,450)/1000;
    (CW,SC,CD,DW,DS)=(138,59,530,0,273)/1000.

#### W-secondary / D-primary

    ((-PI.hi/4,-F(1,5)),(108,508,10, 51,323)),
    ((-F(1,5), F(1,5)),(259,379,15,135,212)),
    (( F(1,5), F(1,2)),(295,364,54,164,123)),
    (( F(1,2),PI.hi/4),(285,383,123,143, 66)),

#### D-secondary / D-primary

    ((-F(1,5), F(1,5)),(237,410, 30,116,207)),
    (( F(1,5), F(1,2)),(204,443,106,116,131)),
    (( F(1,2),PI.hi/4),(231,392,185,116, 76)),

#### D-secondary / S-primary

    ("neg",(-PI.hi/4,-F(1,4)),-1,(38,434,63,29,436)),
    ("p1",(-F(27,100),F(1,5)),1,(88,65,233,278,336)),
    ("p2",(F(1,5),F(1,2)),1,(343,206,96,190,165)),
    ("p3",(F(1,2),PI.hi/4),1,(278,367,121,145,89)),

#### W-secondary / D-secondary

    ((-PI.hi/4,-F(1,5)),FULL,(303,157,191,163,186)),
    ((-F(1,5), F(1,5)),FULL,(365,187,106,185,157)),
    ((F(1,5),F(1,2)),(-F(2,3),-F(2,5)),(391,246,77,146,140)),
    ((F(1,5),F(1,2)),(-F(2,5),-F(1,5)),(350,253,32,192,173)),
    ((F(1,5),F(1,2)),(-F(1,5),0),(324,228,23,222,203)),
    ((F(1,5),F(1,2)),(0,F(1,2)),(315,306,9,184,186)),
    ((F(1,5),F(1,2)),(F(1,2),PI.hi/4),(344,32,33,306,285)),
    ((F(1,2),PI.hi/4),(-F(2,3),0),(285,366,55,167,127)),
    ((F(1,2),PI.hi/4),(0,F(1,2)),(248,354,63,180,155)),
    ((F(1,2),PI.hi/4),(F(1,2),PI.hi/4),(400,110,33,257,200)),

#### D-secondary / D-secondary

    ((-PI.hi/4,-F(1,5)),(139,261,18,284,298)),
    (( F(1,5), F(1,2)),(294,265,25,201,215)),
    (( F(1,2),PI.hi/4),(294,323,61,164,158)),

#### D-secondary / S-secondary complement

    (0,0):(319,266,57,182,176),(0,3):(240,344,167,130,119),
    (1,0):(135,353,5,257,250),(1,1):(139,169,318,262,112),
    (1,2):(116,185,354,253,92),(1,3):(124,361,232,184,99),
    (2,0):(258,283,4,235,220),(2,1):(254,105,319,249,73),
    (2,2):(242,152,302,233,71),(2,3):(195,182,348,222,53),
    (3,0):(305,250,4,233,208),(3,1):(326,115,234,239,86),
    (3,2):(298,139,257,230,76),(3,3):(321,22,400,250,7),

#### Universal hard D-secondary / S-secondary corner

Each line is `(w0,w1,s0,s1; CW,SC,CD,DW,DS)`.
    (-2/3,-3/5,-1/5,-1/10; 373,248,76,168,135)
    (-2/3,-19/30,-1/10,-1/20; 428,252,61,126,133)
    (-2/3,-19/30,-1/20,0; 390,236,109,141,124)
    (-19/30,-3/5,-1/10,-1/20; 403,254,75,134,134)
    (-19/30,-3/5,-1/20,0; 415,229,68,153,135)
    (-2/3,-3/5,0,1/8; 402,198,117,150,133)
    (-2/3,-3/5,1/8,1/4; 436,185,196,110,73)
    (-2/3,-3/5,1/4,3/8; 438,328,37,73,124)
    (-2/3,-3/5,3/8,1/2; 536,366,38,29,31)
    (-3/5,-11/20,-1/5,-1/10; 307,291,59,171,172)
    (-3/5,-11/20,-1/10,0; 416,181,123,154,126)
    (-3/5,-11/20,0,1/8; 445,244,45,123,143)
    (-3/5,-11/20,1/8,1/4; 375,177,180,151,117)
    (-3/5,-11/20,1/4,3/8; 367,256,141,129,107)
    (-3/5,-11/20,3/8,1/2; 414,293,125,98,70)
    (-11/20,-1/2,-1/5,-1/10; 437,194,99,149,121)
    (-11/20,-21/40,-1/10,-1/20; 396,232,70,171,131)
    (-11/20,-21/40,-1/20,0; 434,212,45,163,146)
    (-21/40,-1/2,-1/10,-1/20; 354,238,101,161,146)
    (-21/40,-1/2,-1/20,0; 389,191,108,176,136)
    (-11/20,-1/2,0,1/8; 465,229,55,129,122)
    (-11/20,-1/2,1/8,1/4; 347,265,93,154,141)
    (-11/20,-1/2,1/4,3/8; 448,226,108,117,101)
    (-11/20,-1/2,3/8,1/2; 484,261,80,82,93)
    (-1/2,-9/20,-1/5,-1/10; 177,331,28,237,227)
    (-1/2,-9/20,-1/10,0; 405,201,58,181,155)
    (-1/2,-39/80,0,1/32; 471,211,58,138,122)
    (-1/2,-39/80,1/32,1/16; 475,178,115,131,101)
    (-39/80,-19/40,0,1/32; 417,189,125,151,118)
    (-39/80,-19/40,1/32,1/16; 403,198,103,162,134)
    (-1/2,-19/40,1/16,1/8; 368,200,122,181,129)
    (-19/40,-9/20,0,1/16; 376,230,83,163,148)
    (-19/40,-9/20,1/16,1/8; 395,223,94,160,128)
    (-1/2,-9/20,1/8,1/4; 332,238,145,161,124)
    (-1/2,-9/20,1/4,3/8; 425,218,129,134,94)
    (-1/2,-9/20,3/8,1/2; 260,321,153,149,117)
    (-9/20,-2/5,-1/5,-1/10; 124,364,14,255,243)
    (-9/20,-2/5,-1/10,0; 339,245,85,184,147)
    (-9/20,-17/40,0,1/16; 341,202,124,187,146)
    (-9/20,-17/40,1/16,1/8; 202,241,168,226,163)
    (-17/40,-2/5,0,1/16; 291,237,98,209,165)
    (-17/40,-2/5,1/16,1/8; 209,248,165,214,164)
    (-9/20,-2/5,1/8,1/4; 283,259,125,183,150)
    (-9/20,-2/5,1/4,3/8; 226,271,162,186,155)
    (-9/20,-2/5,3/8,1/2; 183,351,160,169,137)
    (-2/5,-3/10,-1/5,0; 156,269,148,250,177)
    (-2/5,-3/10,0,1/5; 145,273,186,234,162)
    (-2/5,-3/10,1/5,7/20; 199,321,149,178,153)
    (-2/5,-3/10,7/20,1/2; 119,339,209,187,146)
    (-3/10,-1/5,-1/5,0; 182,227,178,247,166)
    (-3/10,-1/5,0,1/5; 177,262,168,232,161)
    (-3/10,-1/5,1/5,7/20; 96,237,293,244,130)
    (-3/10,-1/5,7/20,1/2; 134,315,215,199,137)

#### Universal candidate tails

S-tail stresses:
    ("n1",(-F(2,3),F(2,5)),(-PI.hi/4,-F(3,10)),(1,-1),(284,344,0,147,225)),
    ("n2",(-F(2,3),F(2,5)),(-F(3,10),-F(1,6)),(1,-1),(240,373,0,135,252)),
    ("p1",(-F(2,3),-F(1,6)),(F(1,2),F(13,20)),(1,1),(365,396,0,144,95)),
    ("p2",(-F(2,3),-F(1,6)),(F(13,20),PI.hi/4),(1,1),(376,368,0,181,75)),
    ("p3",(-F(1,6),F(2,5)),(F(1,2),F(2,3)),(1,1),(284,400,0,173,143)),
    ("p4",(-F(1,6),F(2,5)),(F(2,3),PI.hi/4),(1,1),(320,411,0,155,114)),

Positive-W tail stresses:
    ((F(2,25),F(1,4)),(355,280,0,211,154)),
    ((F(1,4),F(1,2)),(307,340,0,189,164)),
    ((F(1,2),PI.hi/4),(314,349,0,172,165)),

The far-negative candidate stress is the single row

    (400,283,0,166,151)/1000,

with its exact cap/vertex repair given in (A23V0)--(A23V9).


### Pattern 30

For Pattern 30 the N/W pair is the Pattern-14 both-own pair and the E/S pair
is the Pattern-26 E-cardinal/S-own pair.

If w<0, the hand Pattern-14 reserve gives, for every W--N source,

    B_u(n,w) >= B_*+(73/100)(-w),                  (P30C1)

on the whole remaining interval -21/50<=w<=0.  The scalar hand diagonal
estimate an independent arithmetic audit gives

    partial_w D < 18/25.                           (P30C2)

Thus moving w to zero can lose at most (18/25)(-w), leaving the strict
reserve

    (73/100-18/25)(-w)=(1/100)(-w)>0.              (P30C3)

So a Pattern-30 minimum may be assumed to have w>=0.

For

    0<=w<=2/25,   -1/6<=s<=1/2,

the pair envelopes give

    Phi >= a(w)+b(s)+D(w,s,eps).                   (P30C4)

The hand scalar checker an independent arithmetic audit proves

    s<0:   b'(s)<0,       D_s<-3/5,
    s>0:   b''(s)<-12/25, D_ss<9/20,
    s=0:   a'(w)>1/10,   D_w>3/5.                 (P30C5)

Hence s moves to zero on the negative side; on the positive side the total
s-curvature is below -3/100, so a minimum lies at s=0 or s=1/2.  The latter
face is already removed by (A23C1).  At s=0 the total w derivative is
positive, so w moves to zero.  The usual identity

    Phi(0,0,eps)
      =2m(d_*-1/sqrt(2))(1-cos eps)>=0             (P30C6)

finishes the stress inequality.  Equality would force n=e=0 and equality
source axes, incompatible with the canonical N-own bit under the
cardinal-preferred rule.  Thus **Pattern 30 is closed by hand**.

### Pattern 28

Pattern 28 has N cardinal and E cardinal.  Its N/W pair is exactly the A2.2
N-cardinal/W-own pair; its E/S pair is exactly the Pattern-26
E-cardinal/S-own pair.  The same factorization

    F28(w,s,eps)=a(w)+b(s)+D(w,s,eps)              (P28C1)

holds on (A23C5).

an independent arithmetic audit gives:

- for s<0, b'(s)<0 and D_s<-1/2;
- for s>0, splitting only at s=1/10 and s=1/4 gives negative total
  s-curvature on all three chambers;
- at s=0,w>0,
      D_w>16/25,
  while the A2.2 profile satisfies
      a'(w)>-29/100.

Therefore s moves to zero and every positive w moves to zero.  On s=0,w<0,
the hand A2.2 N/W reserve is at least (73/100)(-w), while the hand A2.2
diagonal loss is at most (71/100)(-w), leaving strict reserve
(1/50)(-w).  Hence w=s=0, and the diagonal identity finishes the case.

Thus **Pattern 28 is closed by hand**.

### Pattern 29

Pattern 29 has N cardinal and E own.  The E/S pair is exactly the Pattern-14
both-own pair after reflection

    (n,w)=(-e,-s).                                 (P29C1)

The source-independent bridge checker
an independent arithmetic audit uses

    (299,308,0,197,196)/1000   on -1/6<=s<=-2/25,
    (251,433,0,160,156)/1000   on 21/50<=s<=1/2.  (P29C2)

On both bridges the D force has a dominant positive local component, but
the exact support may be on either the cap or vertex branch.  Use the exact
split (A23V0)--(A23V6).  On the vertex branch the radical depends only on
\(s-w\).  The scalar bound

\[
M''(s-w)<3/20
\]

together with the explicit positive \(F,G,K,L\) terms gives negative
\(w\)- and \(s\)-curvature on every vertex/sign chamber; the cap chambers
retain the original negative curvatures.  Since the two support branches meet
\(C^1\), only the same scalar \(d\)-edges remain.  Alternating Taylor bounds
on those edges give

\[
\Phi>1/250\quad\hbox{on the negative bridge},\qquad
\Phi>7/2000\quad\hbox{on the positive bridge}.     \tag{P29C2a}
\]  Combining (P29C2) with the universal tails gives

    -21/50<w<2/25,
    -2/25<s<21/50.                                 (P29C3)

For w<0, the A2.2 N/W reserve and (P30C2) again leave
(1/100)(-w)>0.

For w>0,
an independent arithmetic audit proves

    D_w>7/20,                                      (P29C4)

whereas the A2.2 N-cardinal/W-own profile has a'(w)>-29/100.  Thus the total
w derivative is greater than 3/50 and every minimum moves to w=0.

At w=0, use the reflected E/S hand calculus.  For s<0,
an independent arithmetic audit gives

    d/ds a(-s)<-3/40,     D_s<-3/5,                (P29C5)

so s moves to zero.

For s>0, reflection of the Pattern-14 hand negative reserve gives
+(73/100)s.  Put

    beta=-s/2,     delta=eps-s/2.

On the cap branch the beta coefficient is negative; Dcap therefore decreases
as delta increases and is minimized at eps=0.  The resulting scalar
s-edge is strictly increasing from zero.  On the negative vertex branch,
Dvert is strictly concave in delta, so only the two branch endpoints can
minimize it.  The support-switch endpoint is no lower than the cap edge; at
eps=1/2-pi/4 the remaining one-dimensional s-edge has margin greater than
1/200.  Therefore positive s also moves to zero.

Thus w=s=0.  Equality would force e=n=0, forbidden by the canonical
cardinal-preferred rule for the E-own bit.  Hence **Pattern 29 is closed by
hand**.  In particular the old large-S two-dimensional value grid is not a
logical premise.

### Pattern 31

Pattern 31 has both adjacent pairs own/own.  It inherits the common D-edge
classification, the universal tails, and both Pattern-29 bridges, so it is
confined to (P29C3).

For w<0, (P30C1)--(P30C3) move w to zero.  Assume w>=0 and reduce N/W by the
Pattern-14 positive envelope to a(w).

If s<0, an independent arithmetic audit gives the same
reflected pair derivative as (P29C5), uniformly for 0<=w<=2/25:

    d/ds a(-s)<-3/40,     D_s<-3/5.                (P31C1)

Thus s moves to zero, after which the Pattern-30 hand w derivative moves w
to zero.

If s>0, the reflected Pattern-14 negative reserve contributes
+(73/100)s.  The same checker gives

    a''(w)<-3/5,
    D_ww<1/4  on the cap branch,
    D_ww<0    on the vertex branch.                (P31C2)

Hence the total w-curvature is below -1/3.  A minimum therefore lies at
w=0 or w=2/25.  The second face is already excluded by the universal
positive-W tail (A23C2); the first face is precisely the Pattern-29
positive-s reduction above.  Thus w=s=0.

Again the diagonal identity is nonnegative and equality would force e=n=0,
contrary to the canonical own-primary bits.  Therefore **Pattern 31 is
closed by hand**.

Consequently **A2.3 is hand-complete**.  Together with the hand closures of
A2.1 and A2.2, the whole A2 elimination is now a hand proof: no
multidimensional numerical value replay is a logical premise.  The Python
files with suffix _hand.py are independent exact arithmetic checks of the
displayed one-dimensional derivative, curvature, and endpoint inequalities;
the older adaptive/fixed-grid scripts are retained only as discovery records.


## Preparatory lemma P8 — quantitative marker displacement for forced-own E/N

The cardinal-preferred rule strengthens the marker threshold substantially for
E and N because both squares have unconditional moving pins.

Define the shifted markers

    mu_E := m_E-5y/4,
    mu_N := m_N+5x/4.                              (P8a)

If E or N is canonically own-primary, then

    sign(mu_i)=sign(theta_i),
    |mu_i| > (17/192)|theta_i|.                    (P8b)

The statement is strict whenever theta_i is nonzero.  At theta_i=0 the two
central normals coincide, so the cardinal-preferred rule cannot select the
own branch.

### North, positive angle

Put n=theta_N>0, c=cos n, s=sin n.  From (ON) and O_N>=0,

    X <= (c-1-s)/2 + x s.

Since the branch is forced-own, K_N<0.  Using (KN),

    sY < cX-(1-c-s)/2
       <= s(1-s-c+2cx)/2.

Hence

    b_N+x
      > (c-1)/2-(1/2+y)s+x(1-c)
      > -(1-c)/2-(5/8)s.

Therefore

    mu_N
      > n-(5/8)(1-c)-(25/32)s
      > n[7/32-(5/16)n]
      > (17/192)n,                                 (P8N+)

using 0<=x,y<1/8, sin n<n, 1-cos n<n^2/2 and the P6 bound
n<5/12.

### North, negative angle

Write n=-v, 0<v<3/10.  The same two margin inequalities give

    b_N+x
      < (5/8)(1-c)+(5/8)sin v.

Thus

    mu_N
      < -v+(25/32)(1-c)+(25/32)sin v
      < -v[7/32-(25/64)v]
      < -(17/192)v.                                (P8N-)

(The sharper final coefficient here is 13/128.)

### East

The east formulas are the reflected versions.  For e=theta_E>0,

    b_E-y > -(5/8)(1-c)-(5/8)sin e,

so, using e<3/10,

    mu_E > e[7/32-(25/64)e] > (17/192)e.           (P8E+)

For e=-v<0,

    b_E-y < (1-c)/2+(5/8)sin v,

and the P6 bound v<5/12 gives

    mu_E < -v[7/32-(5/16)v] < -(17/192)v.          (P8E-)

This proves (P8b).

The significance is that a forced-own E/N bit now consumes marker displacement
at a uniform linear rate.  This is the quantitative form that should be used
in A2; the earlier 3/128 threshold bound remains valid but is no longer sharp
enough to drive the classification by itself.


## Preparatory lemma P9 — negative-diagonal D-secondary tail

A recurring residual family in the A2 classification has a large negative
diagonal deviation, just outside the domains of the older alternate-D
lemmas.  It can be removed by a short hand stress.

Assume

    W is canonically own-primary,
    S is south-cardinal,
    D--W separates on D's secondary axis,

and write

    w = theta_W,   s = theta_S,
    eps = theta_D-pi/4.

Suppose

    |w| <= 2/5,
    1/6 <= s <= 1/2,
    -1/3 <= eps <= -1/6.                          (P9-domain)

Then neither possible secondary-axis choice for D--S is feasible at
R^2 <= Q0.

Put

    R=sqrt(Q0),    h=1/sqrt(2),
    c0=rho0-1,     kappa=1/2-c0.

The proof uses only the selected central edges and the two D edges; E,N and
the W--N separator play no role.

### P9a. D--S also uses D-secondary

Use the three separators

    C -> W   on W's own-primary axis,
    D -> W   on D-secondary,
    D -> S   on the opposite directed D-secondary axis,

all with weight 1/3.

After applying the elementary exterior support inequality and collecting
terms, the reverse-stress gap is

    Phi_D(w,s,eps)
      = (1/3)[2-R+F(w)+G(eps-w)+H(eps-s)],         (P9D)

where

    F(w) =
      kappa(cos w+sin w),              w>=0,
      kappa cos w-(1/2)sin w,          w<=0,

    G(z) = 2h cos z - 2R sin(3pi/8+z/2),

and

    H(q) =
      2h cos q,                         q>=-pi/4,
      -2h sin q,                        q<=-pi/4.

The only chamber walls are w=0 and eps-s=-pi/4.

Each scalar piece is concave on its chamber.  For F and H this is immediate.
For G,

    G''(z)
      = -2h cos z + (R/2) sin(3pi/8+z/2).

On (P9-domain), -11/15<=z<=7/30.  Hence

    G''(z)
      < -2(7/10)(7/10) + (17/20)
      < 0.

Therefore Phi_D is concave on each chamber.  Its minimum is attained at a
chamber vertex.

### P9b. D--S uses S-secondary

Use the four separators

    S -> C   south-cardinal,
    C -> W   W own-primary,
    D -> W   D-secondary,
    D -> S   S-secondary

with respective weights

    13/40, 9/40, 9/40, 9/40.

Put a=13/40 and x=9/40.  The reverse-stress gap separates as

    Phi_S(w,s,eps)
      = C + x F(w)+x G(eps-w)+x H(eps-s)+J(s),    (P9S)

where

    C = a/2+3x-c0 a,

    F(w) =
      kappa(cos w+sin w),                    w>=0,
      kappa cos w-(1/2+c0)sin w,             w<=0,

    G(z) = 2h cos z - 2R sin(3pi/8+z/2),

    H(q) =
      h(cos q-sin q)-2R sin(pi/8-q/2),       q>=-pi/4,
      -2h sin q-2R sin(pi/8-q/2),            q<=-pi/4,

    J(s) = a cos s
           -R sqrt(a^2+x^2-2ax sin s).

Again the only chamber walls are w=0 and eps-s=-pi/4.

The functions F and G are concave as above.  For q>=-pi/4,

    H''(q)
      = -h(cos q-sin q)
        +(R/2)sin(pi/8-q/2) < 0;

the coarse bounds
cos(1/3)+sin(1/3)>6/5, h>7/10 and
sin(pi/8+5/12)<3/4 suffice.  For q<=-pi/4,

    H''(q)
      = 2h sin q +(R/2)sin(pi/8-q/2) < 0.

It remains to control J.  Put

    P=a^2+x^2=5/32,
    Q=2ax=117/800,
    Y=sqrt(P-Q sin s).

On 1/6<=s<=1/2,

    Y > 36/125,
    cos s > 7/8,

and the positive square-root curvature is bounded by

    (17/10) Q (49997/500000) / [4(36/125)^3].

This is strictly less than

    (13/40)(7/8),

the magnitude of the negative a cos s curvature.  Hence J''<0.

Thus Phi_S too is concave on each chamber.

### Fixed endpoint check

The union of the (s,eps) chamber vertices is

    (1/6,-1/3), (1/6,-1/6),
    (1/2,-1/3), (1/2,-1/6),
    (pi/4-1/3,-1/3),
    (1/2,1/2-pi/4).

Together with

    w in {-2/5,0,2/5},

there are only 18 fixed vertices per graph.

Exact rational square-root and Taylor enclosures give

    Phi_D > 1/50,
    Phi_S > 7/1000                               (P9-margin)

at every vertex.  The actual certified minima are greater than
0.02626 and 0.00784 respectively.

Therefore both D--S secondary-axis possibilities contradict R^2<=Q0
throughout (P9-domain).

\`the pinned independent arithmetic audit\` checks only the scalar curvature
inequalities and these 36 fixed endpoint evaluations.  It performs no
subdivision.


## Preparatory lemma P10 — large-N alternate D-W tail

The A2 classifier leaves a second extension of the alternate-D-W graph, on the
opposite side of the old |theta_N|<=1/6 lemma. It is also a hand
concavity lemma.

Assume N and S are cardinally separated from C and write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    1/5 <= n <= 2/5,
    |w| <= 1/5,
    1/6 <= s <= 1/2,
    -1/6 <= eps <= 0.                              (P10-domain)

Assume further that

    D--W uses D-secondary,
    D--S uses S-secondary,

while W--N may use any of its four source axes. Then R^2<=Q0 is
impossible. The E square and the central W separator are not used.

### The fixed stress

Use exactly the rational completed-square stress from the original alternate
D--W lemma:

    lambda_N,lambda_W,lambda_S,lambda_D
      = (281,233,279,207)/1000,

    mu_CN=mu_SC=949/1000,
    mu_WN=277/1000,
    mu_DW=603/1000,
    mu_DS=738/1000.                                (P10-stress)

The equal CN/SC weights cancel C. For a fixed W--N source, expanding the
completed squares leaves a smooth function F(n,w,s,eps) on (P10-domain).
There is no absolute-value chamber: n>0, s>0, and n-w>=0 throughout.

For example, for W-primary source the expansion is

    F_Wp =
      P sin s - T sin w
      + B sin(eps-s) - E sin(eps-w)
      + Q(sin n+cos n) + Q cos s
      + A cos(eps-s) + C cos(eps-w)
      + R cos(n-w) - K,                            (P10-Wp)

where

    Q=949/1000, R=277/1000,
    T=262873/562000, P=38909/31000,

    A=(41697/23000)/sqrt(2),
    B=(7749/23000)/sqrt(2),
    C=(78993/93200)/sqrt(2),
    E=(167031/466000)/sqrt(2),

and K=980542331731/840280482000. The other three source formulas are
obtained by the same direct expansion.

### Separate concavity

Direct differentiation shows that for every source choice the second
derivative in each of n,w,s,eps is strictly negative on the whole box.
Coarse rational/Taylor bounds give the following uniform upper bounds, in the
order (n,w,s,eps):

| W--N source | second-derivative upper bounds |
|---|---|
| W-primary | (-4/3,-3/5,-19/10,-4/3) |
| W-secondary | (-4/3,-3/4,-19/10,-9/5) |
| N-primary | (-9/10,-7/10,-9/5,-9/5) |
| N-secondary | (-1,-1,-9/5,-13/10) |

Thus every source stress is separately concave on the rectangular domain.
Iteratively minimizing one coordinate at a time sends a minimum to a vertex.
Only

    n in {1/5,2/5},
    w in {-1/5,1/5},
    s in {1/6,1/2},
    eps in {-1/6,0}                                (P10-vertices)

remain: 16 vertices for each source, 64 fixed evaluations total.

### Endpoint margin

Exact rational square-root and alternating Taylor enclosures give

    F_source - Q0 > 1/25                           (P10-margin)

at all 64 vertices. The actual smallest certified margin is greater than
0.04313407; it occurs for W-secondary and N-primary source at

    (n,w,s,eps)=(1/5,1/5,1/6,-1/6).

Therefore the whole large-N alternate-D-W family contradicts R^2<=Q0.

the pinned independent arithmetic audit checks the displayed curvature
bounds and the 64 fixed endpoint values. It performs no subdivision.


## Preparatory lemma P11 — W-secondary / S-secondary large-N tail

A second classifier survivor family uses W's secondary axis on D--W. This
family also has a direct hand stress proof.

Assume N and S are cardinally separated from C, while W is canonically
own-primary. Write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    1/5 <= n <= 2/5,
    0 <= w <= pi/4,
    1/6 <= s <= 2/5,
    -1/4 <= eps <= 0.                              (P11-domain)

Assume D--W uses W-secondary and D--S uses S-secondary. The W--N separator
may use any of its four source axes. Then R^2<=Q0 is impossible. E is not
used.

### Stress and central-square term

Use the chain separators C->N, S->C, C->W, W--N, D->W, D->S.
For each of the four W--N source axes choose one fixed rational
completed-square stress.  The containment weights are ordered
((\lambda_N,\lambda_W,\lambda_S,\lambda_D)), and the separator
multipliers are ordered
((\mu_{CN},\mu_{SC},\mu_{CW},\mu_{WN},\mu_{DW},\mu_{DS})):

| W--N source | containment weights /1000 | separator multipliers /1000 |
|---|---|---|
| W-primary | (273,275,246,206) | (893,803,570,180,519,465) |
| W-secondary | (415,52,300,233) | (952,952,152,561,656,638) |
| N-primary | (318,199,271,212) | (883,868,550,221,578,518) |
| N-secondary | (318,236,246,200) | (1006,815,432,240,503,429) |

All containment weights are positive and each row sums to one.

The force on C need not vanish. Since 0<=C_x,C_y<=rho0-1, write c0=rho0-1.
If the C->N, S->C, C->W multipliers are mu_N,mu_S,mu_W, then

    G_Cx = mu_W cos w,
    G_Cy = mu_S-mu_N+mu_W sin w.

Use the smooth upper bound

    G_C.p_C
      <= c0 [mu_W(cos w+sin w)+|mu_S-mu_N|].       (P11-C)

For D--W use the weaker threshold

    H_DW >= 1/2 + (1/sqrt2) cos(eps-w),             (P11-DW)

valid on the whole domain. Both weaken the stress inequality but remove the
only central max and D half-width branch switch.

### Chamber concavity

The only remaining nonsmoothness is the sign of n-w in the W--N threshold.
Split into n>=w and n<=w. On either chamber the stress is a smooth elementary
trigonometric polynomial.

For every W--N source choice, direct differentiation gives strict separate
concavity in n,w,s,eps on both chambers. Along n=w the restricted
one-variable function is also strictly concave. Exact rational/Taylor bounds
verify these signs. For transparent interval evaluation, the w-axis is
partitioned at the fixed values

    0, 1/10, 1/5, 3/10, 2/5, 1/2, 3/5, 7/10, pi/4.

This is a fixed calculus partition, not recursive subdivision. The weakest
certified second-derivative upper bound is still below -0.0824.

Thus each (n,w) chamber reaches its minimum at a chamber vertex. The union is

    (1/5,0), (1/5,1/5), (2/5,0), (2/5,2/5),
    (1/5,pi/4), (2/5,pi/4).                        (P11-NW)

Separate concavity in s and eps leaves

    s in {1/6,2/5},
    eps in {-1/4,0}.                               (P11-SE)

There are therefore 24 endpoints per source, 96 fixed evaluations total.

### Endpoint margin

Every endpoint contradicts R^2<=Q0. The smallest exact certified margin is
greater than 0.10708, attained for the N-secondary W--N source at

    (n,w,s,eps)=(1/5,0,1/6,0).

Hence the entire P11 domain is excluded.

`the pinned independent arithmetic audit` checks the fixed curvature
inequalities, equality-diagonal concavity, and 96 endpoint values using
rational square-root and alternating Taylor enclosures only. It performs no
adaptive subdivision.


## Preparatory lemma P12 — W-secondary / D-secondary large-N tail

The complementary W-secondary branch is also a hand concavity problem.

Assume N and S are cardinally separated from C, while W is canonically
own-primary. Write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    1/5 <= n <= 2/5,
    0 <= w <= 1/5,
    1/6 <= s <= 2/5,
    -1/4 <= eps <= 0.                              (P12-domain)

Assume D--W uses W-secondary and D--S uses D-secondary. The W--N separator
may use any of its four source axes. Then R^2<=Q0 is impossible. Again E is
not used.

### Fixed stresses

Use the same chain separators

    C->N,  S->C,  C->W,  W--N,  D->W,  D->S.

For each W--N source choose one fixed rational completed-square stress. The
containment weights (lambda_N,lambda_W,lambda_S,lambda_D) and separator
multipliers (mu_N,mu_S,mu_CW,mu_WN,mu_DW,mu_DS) are:

| W--N source | lambdas /1000 | multipliers /1000 |
|---|---|---|
| W-primary | (99,472,231,198) | (316,316,1193,117,939,531) |
| W-secondary | (437,15,251,297) | (0,0,43,1658,1682,950) |
| N-primary | (361,126,252,261) | (3,11,474,1337,1537,937) |
| N-secondary | (90,480,224,206) | (276,276,1241,93,969,544) |

The lambdas are positive and sum to one. Zero separator multipliers in the
W-secondary row simply mean those central inequalities are not needed.

As in P11, use the smooth central-square support upper bound

    G_C.p_C
      <= c0 [mu_CW(cos w+sin w)+|mu_S-mu_N|].      (P12-C)

For the two outer D edges use the valid weakened half-width thresholds

    H_DW >= 1/2 + h cos(eps-w),
    H_DS >= 1/2 + h cos(eps-s),                    (P12-D)

with h=1/sqrt(2). These choices leave a smooth elementary trigonometric
polynomial on the entire rectangle.

### Separate concavity

On (P12-domain),

    0 <= w <= 1/5 <= n,

so n-w>=0 everywhere. Hence there is no W--N absolute-value chamber wall.

For W-primary, N-primary, and N-secondary sources, direct differentiation
shows strict separate concavity in each of n,w,s,eps on the whole rectangle.
Exact rational/Taylor enclosures give uniform second-derivative upper bounds
at most

    -0.4177,  -0.9780,  -0.1843

respectively.

The W-secondary source is also separately concave. A single interval
evaluation in w is unnecessarily wide, so certify its w-curvature on the four
fixed intervals

    [0,1/20], [1/20,1/10], [1/10,3/20], [3/20,1/5].

On each interval the second derivative is strictly negative; the other three
coordinates are concave on the whole rectangle. This is a fixed calculus
partition, not recursive subdivision.

Therefore every source stress reaches its minimum at one of the 16 rectangle
vertices

    n in {1/5,2/5},
    w in {0,1/5},
    s in {1/6,2/5},
    eps in {-1/4,0}.                               (P12-vertices)

### Endpoint margin

Exact rational square-root and alternating Taylor enclosures give positive
margin at all 64 source/vertex combinations. The smallest certified margin is

    > 0.05294 > 1/20,

for the N-secondary source at

    (n,w,s,eps)=(1/5,0,2/5,0).

Hence the entire widened P12 domain contradicts R^2<=Q0.

`the pinned independent arithmetic audit` checks the displayed curvature signs
and the 64 fixed endpoint evaluations. It performs no adaptive subdivision.


## Preparatory lemma P13 — large-N both-D-secondary extension

The original both-D-secondary hand stress also extends across the large-N
strip needed for A2.2.

Assume N and S are cardinally separated from C and write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    1/5 <= n <= 2/5,
    0 <= w <= 1/5,
    1/6 <= s <= 2/5,
    -1/6 <= eps <= 0.                              (P13-domain)

Assume both D--W and D--S use D's secondary axis. The W--N separator may use
any of its four source axes. Then R^2<=Q0 is impossible.

### Fixed stress

Use exactly the rational completed-square stress from the existing
both-D-secondary lemma:

    lambda_N=lambda_D=1/50,
    lambda_W=lambda_S=12/25,

    mu_CN=mu_SC=3/50,
    mu_WN=1/25,
    mu_DW=43/25,
    mu_DS=17/10.                                   (P13-stress)

The central forces cancel because mu_CN=mu_SC. Since n>=w throughout the
domain, the W--N threshold has no absolute-value chamber switch.

### Separate concavity

For each of the four W--N source axes, direct differentiation gives strict
separate concavity in n,w,s on the whole rectangle.

A single interval enclosure in eps is too wide, but splitting only at
eps=-1/12 gives strict negative curvature on both fixed intervals

    [-1/6,-1/12],  [-1/12,0].

Thus the stress is separately concave throughout (P13-domain). The weakest
certified second-derivative upper bound among the four source choices is still
negative, greater in magnitude than 0.026.

Therefore each source stress reaches its minimum at one of the 16 rectangle
vertices

    n in {1/5,2/5},
    w in {0,1/5},
    s in {1/6,2/5},
    eps in {-1/6,0}.                               (P13-vertices)

### Endpoint margin

Exact rational square-root and alternating Taylor enclosures give positive
margin at all 64 source/vertex combinations. The smallest certified margin is

    > 0.18758 > 9/50,

attained for W-primary or N-primary source at

    (n,w,s,eps)=(1/5,1/5,2/5,-1/6).

Hence the whole P13 domain contradicts R^2<=Q0.

`the pinned independent arithmetic audit` checks the fixed curvature
inequalities and the 64 endpoint values. It performs no adaptive subdivision.

### Four-graph consequence for A2.2

On the common strip

    1/5 <= n <= 2/5,
    0 <= w <= 1/5,
    1/6 <= s <= 2/5,
    -1/6 <= eps <= 0,

the four possible D-edge source combinations are now all excluded by hand:

- D--W=D-secondary, D--S=S-secondary: P10;
- D--W=W-secondary, D--S=S-secondary: P11;
- D--W=W-secondary, D--S=D-secondary: P12;
- D--W=D-secondary, D--S=D-secondary: P13.

Each lemma allows every W--N source axis. Thus no further D-edge case split is
needed once an A2.2 configuration is forced into this common angle strip.


## Preparatory lemma P14 — low-N W-secondary / D-secondary bridge

The W-secondary / D-secondary graph also has a clean hand stress on the
complementary low-N strip.  This removes the artificial lower bound n>=1/5
from that graph.

Assume N and S are cardinally separated from C, while W is canonically
own-primary.  Write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    |n| <= 1/5,
    0 <= w <= 1/5,
    1/6 <= s <= 2/5,
    -1/4 <= eps <= 0.                              (P14-domain)

Assume D--W uses W-secondary and D--S uses D-secondary.  The W--N separator
may use any of its four source axes.  Then R^2<=Q0 is impossible.

### Fixed stresses and smooth weakening

Use the same six chain separators as P12:

    C->N,  S->C,  C->W,  W--N,  D->W,  D->S.

For the four W--N source choices use the following rational stresses.  The
lambda order is (N,W,S,D), and the multiplier order is
(CN,SC,CW,WN,DW,DS).

| W--N source | lambdas /1000 | multipliers /1000 |
|---|---|---|
| W-primary | (12,561,195,232) | (32,91,1543,14,1090,593) |
| W-secondary | (203,307,230,260) | (0,47,861,697,1293,745) |
| N-primary | (12,552,198,238) | (0,91,1522,40,1114,604) |
| N-secondary | (12,562,194,232) | (36,90,1542,17,1089,592) |

Again use the smooth central support upper bound from P11--P12.

There are two absolute-value half-widths which would otherwise introduce
chambers.  We simply weaken them:

    H_CN
      >= 1/2 + (cos n + sin n)/2,

    H_WN
      >= 1/2 + (cos(n-w) + sin(n-w))/2.             (P14-W)

These inequalities are valid for both signs because |sin z|>=sin z.  Thus the
stress becomes one smooth trigonometric polynomial on the whole rectangle.
The D-edge lower thresholds are the same smooth bounds as in P12.

### Separate concavity

For W-primary, W-secondary, and N-secondary source, the resulting stress is
strictly separately concave in n,w,s,eps on the whole P14 rectangle.

For N-primary, the only interval evaluation needing refinement is the
n-curvature.  It is strictly negative on the five fixed intervals

    [-1/5,-3/20], [-3/20,-1/10], [-1/10,-1/20],
    [-1/20,0], [0,1/5].

The other three coordinate curvatures are negative on the whole rectangle.
This is a fixed calculus partition, not recursive subdivision.

Therefore every source stress reaches its minimum at one of the 16 corners

    n in {-1/5,1/5},
    w in {0,1/5},
    s in {1/6,2/5},
    eps in {-1/4,0}.                               (P14-vertices)

### Endpoint margin

Exact rational square-root and alternating Taylor enclosures give positive
margin at all 64 source/vertex combinations.  The smallest certified margin is

    > 0.01587 > 3/200,

for W-primary source at

    (n,w,s,eps)=(-1/5,0,2/5,0).

Hence the entire P14 domain contradicts R^2<=Q0.

`the pinned independent arithmetic audit` checks the fixed curvature
inequalities and the 64 endpoint values.  It performs no adaptive
subdivision.


## Preparatory lemma P15 — low-N W-secondary / S-secondary bridge

The complementary low-N W-secondary graph also has a hand proof.

Assume N and S are cardinally separated from C, while W is canonically
own-primary. Write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    |n| <= 1/5,
    0 <= w <= pi/4,
    1/6 <= s <= 2/5,
    -1/4 <= eps <= 0.                              (P15-domain)

Assume D--W uses W-secondary and D--S uses S-secondary. The W--N separator
may use any of its four source axes. Then R^2<=Q0 is impossible.

Use the same six-edge completed-square stress architecture as P11 and P14,
with separate fixed rational stresses on the two half-boxes (n\ge0) and
(n\le0).  The containment weights are ordered
((\lambda_N,\lambda_W,\lambda_S,\lambda_D)), and the multipliers are
((\mu_{CN},\mu_{SC},\mu_{CW},\mu_{WN},\mu_{DW},\mu_{DS})).

For (n\ge0):

| source | containment weights /1000 | multipliers /1000 |
|---|---|---|
| W-primary | (136,361,242,261) | (431,745,869,139,685,484) |
| W-secondary | (103,267,324,306) | (41,1001,761,313,811,664) |
| N-primary | (60,326,308,306) | (0,949,894,205,806,625) |
| N-secondary | (217,325,223,235) | (694,694,668,244,613,438) |

For (n\le0):

| source | containment weights /1000 | multipliers /1000 |
|---|---|---|
| W-primary | (216,324,225,235) | (680,693,683,226,615,451) |
| W-secondary | (293,16,371,320) | (180,1144,46,854,886,777) |
| N-primary | (90,291,307,312) | (0,948,734,306,824,624) |
| N-secondary | (222,316,224,238) | (702,702,604,272,614,429) |

Again every containment row is positive and sums to one.

As before, use the smooth central support bound

    G_C.p_C <= c0[mu_CW(cos w+sin w)+|mu_SC-mu_CN|],

and the smooth lower thresholds for the D edges. On n<=0 the N and W--N
half-width signs are fixed. On n>=0 we use the valid weakened expressions
with +sin terms.

### Calculus reduction

For every source on n<=0, and for W-primary, W-secondary, and N-secondary
sources on n>=0, the stress is strictly separately concave in n,w,s,eps.
The exact checker uses only the fixed rational partitions

    n: steps of 1/20,
    w: steps of 1/20 up to pi/4.

There is one apparent exception: on n>=0 with N-primary W--N source, the
n-curvature changes sign near large w. No new stress is needed. Direct
differentiation gives the stronger monotonicity statement

    d Phi / dn > 0.20007                            (P15-mon)

throughout that whole half-box. Hence its minimum is at n=0. The remaining
three coordinates are strictly concave.

Thus every minimum is reduced to fixed box endpoints. Exact rational
square-root and alternating Taylor enclosures give

    Phi-Q0 > 0.005331 > 1/250                       (P15-margin)

at every endpoint. The worst case is W-primary source at

    (n,w,s,eps)=(0,pi/4,1/6,-1/4).

Therefore the entire P15 domain is excluded.

Together, P14 and P15 close both possible D--S secondary choices whenever
D--W uses W-secondary on the full low-N strip |n|<=1/5.

`the pinned independent arithmetic audit` checks only fixed
curvature/monotonicity inequalities and endpoint values. It performs no
adaptive subdivision.


## Preparatory lemma P16 — negative-N W-secondary tail

The opposite-cardinal cap bound leaves only a short negative-N tail beyond
P14--P15.  It too has a direct hand proof.

Assume N and S are cardinally separated from C, while W is canonically
own-primary.  Write

    n=theta_N,  w=theta_W,  s=theta_S,
    eps=theta_D-pi/4.

Suppose

    -3/10 <= n <= -1/5,
    1/6 <= s <= 2/5,
    -1/4 <= eps <= 0.                              (P16-domain)

Assume D--W uses W-secondary.  If D--S uses D-secondary assume additionally

    0 <= w <= 1/5,

while for D--S using S-secondary allow the full

    0 <= w <= pi/4.

The W--N separator may use any of its four source axes.  Then R^2<=Q0 is
impossible.

### Fixed stresses

Use the same smooth completed-square architecture as P14--P15.  For
D--S=D-secondary, the four fixed rational stresses have
(lambda_N,lambda_W,lambda_S,lambda_D) and
(mu_CN,mu_SC,mu_CW,mu_WN,mu_DW,mu_DS), respectively,

    Wp: (12,562,195,231) /1000,
        (29,92,1545,13,1088,593) /1000;

    Ws: (12,552,198,238) /1000,
        (0,92,1531,39,1113,604) /1000;

    Np: (12,553,198,237) /1000,
        (0,93,1525,36,1109,603) /1000;

    Ns: (12,562,195,231) /1000,
        (35,91,1543,18,1086,591) /1000.

For D--S=S-secondary use

    Wp: (195,334,230,241) /1000,
        (613,708,731,205,632,460) /1000;

    Ws: (213,100,366,321) /1000,
        (53,1133,288,683,869,765) /1000;

    Np: (78,310,298,314) /1000,
        (0,921,775,265,824,600) /1000;

    Ns: (222,316,224,238) /1000,
        (702,702,604,272,614,429) /1000.

All containment weights are positive and sum to one.  As before, use the
smooth central support upper bound

    G_C.p_C
      <= c0[mu_CW(cos w+sin w)+|mu_SC-mu_CN|].

Since n<0<=w, the sign of n-w is fixed for the S-secondary graph.  In the
D-secondary graph we may harmlessly use the weaker +sin half-width expression,
which removes the last absolute-value switch.

### Calculus reduction

For every source in the S-secondary graph, the resulting stress is strictly
separately concave in n,w,s,eps.  The w-curvature is checked on the fixed
intervals of length 1/20 up to pi/4.

For the D-secondary graph, W-primary, W-secondary, and N-secondary are also
strictly separately concave.  For N-primary only the n-curvature is
unnecessary: direct differentiation gives instead

    d Phi / dn > 0.0407                             (P16-mon)

throughout the whole box.  Hence that source is minimized at n=-3/10.  Its
remaining three coordinates are strictly concave.

Thus every minimum is reduced to fixed box endpoints.  Exact rational
square-root and alternating Taylor enclosures give

    Phi-Q0 > 0.01158 > 1/100.                       (P16-margin)

The worst endpoint occurs in the D-secondary graph with W-primary source at

    (n,w,s,eps)=(-3/10,0,2/5,0).

Therefore the entire P16 domain is excluded.

Finally, because N and S are opposite cardinal helpers,

    |n|+|s| < 4(rho0-1) < 23/50.

Whenever s>=1/6 this implies

    |n| < 23/50-1/6 = 22/75 < 3/10.                (P16-cap)

Consequently P14--P16 cover the entire cardinally possible negative-n range
for both W-secondary D--S choices, subject only to their displayed w-ranges.

`the pinned independent arithmetic audit` checks the fixed
curvature/monotonicity inequalities and endpoint values.  It performs no
adaptive subdivision.


## Preparatory lemma P17 — D--W primary axes are impossible for nonnegative W angle

The A2.2 source-axis coverage has a simple three-square hand proof on the
residual sign range.  Write

    phi_W=pi+w,    phi_D=pi+d,

and assume

    0 <= w <= d <= pi/4.                            (P17-domain)

Assume both W and D use their own-primary separators from C.  Then D--W
cannot separate on either square's primary axis.  Hence, by separating-axis
completeness, every D--W separation uses one of

    D-secondary,  W-secondary.                     (P17-axis)

### Three-separator stress

For a directed D--W primary normal n, put weights alpha,beta,mu on

    C->D on e_D,
    C->W on e_W,
    W->D on n.

Use the four rows

| directed normal | alpha | beta | mu |
|---|---:|---:|---:|
| +e_W | 1/20 | 1/2 | 9/20 |
| -e_W | 11/20 | 1/20 | 2/5 |
| +e_D | 1/20 | 11/20 | 2/5 |
| -e_D | 1/2 | 1/20 | 9/20 |

All weights are positive and sum to one.

Put

    kappa=1/2-(rho0-1).

Since 0<=w,d<=pi/4, the force on C points northeast, so its support is the
linear expression (rho0-1)(G_Cx+G_Cy).  Apply the elementary vertex-support
bound to W and D.  With

    delta=d-w,

every row becomes

    Phi(w,d)=C+F(w)+G(d)+H(delta),                  (P17-gap)

where

    F(w)=beta kappa(cos w+sin w),
    G(d)=alpha kappa(cos d+sin d),

and there are only two possible relative-angle functions:

    H_A(x)
      =(9/20)(cos x+sin x)
       -R sqrt(41/200+(9/200)cos x),                (P17-A)

for the +e_W and -e_D rows, and

    H_B(x)
      =(2/5)sin x
       -R sqrt(37/80-(11/25)cos x),                 (P17-B)

for the -e_W and +e_D rows.  Constants have been suppressed.

The functions F and G are plainly concave on [0,pi/4].

For H_A, write Z=41/200+(9/200)cos x.  Since
cos x>7/10,

    Z > 473/2000 > (12/25)^2.

The positive curvature produced by the negative square root is therefore less
than

    (17/10)[ (9/200)/(2(12/25))
             +(81/40000)/(8(12/25)^3) ]
      < 9/20,

whereas (9/20)(cos x+sin x) has curvature magnitude at least 9/20.
Thus H_A is strictly concave.

For H_B put P=37/80, q=11/25 and
Z=P-q cos x.  The second derivative of sqrt(Z) has the sign of

    2P cos x-q(1+cos^2 x).

If cos x>=4/5 this quantity is positive (it is increasing in cos x and
already positive at 4/5), so the square-root term only helps concavity.
If cos x<=4/5, then sin x>=3/5, cos x>7/10 and

    Z > P-(4/5)q > (33/100)^2.

Moreover the possible positive curvature is bounded by

    (17/10) q(81/10000) / [4(33/100)^3]
      = 51/1210
      < 6/25,

while the sine term has curvature magnitude at least

    (2/5)(3/5)=6/25.

Hence H_B is also strictly concave.

Therefore Phi is concave on the triangle 0<=w<=d<=pi/4.  Its minimum is at
one of the three vertices

    (w,d)=(0,0), (0,pi/4), (pi/4,pi/4).

Exact square-root arithmetic gives the following row minima:

| directed normal | certified minimum gap |
|---|---:|
| +e_W | > 0.2842 |
| -e_W | > 0.1865 |
| +e_D | > 0.1063 |
| -e_D | > 0.2842 |

Thus all four directed primary-axis possibilities are impossible.

`the pinned independent arithmetic audit` checks the two scalar curvature
bounds and the twelve fixed endpoint evaluations.  It performs no subdivision.


## Preparatory lemma P18 — near-diagonal D--W is forced W-secondary

P17 removes the primary D--W axes on the nonnegative-W branch.  The two
secondary axes can also be classified by the same three-square stress.

Assume

    0 <= w <= d <= pi/4,

with W and D both using their own-primary separators from C.  Put

    d0 := pi/4-1/4.

Then:

1. if 0<=d<=d0, neither secondary D--W axis can separate, hence W and D
   cannot be disjoint;
2. if d0<=d<=pi/4, D-secondary cannot separate.

Consequently every feasible configuration in this branch satisfies

    d > pi/4-1/4,                                  (P18-angle)

and, by P17 and separating-axis completeness,

    D--W uses W-secondary.                         (P18-axis)

### Low-diagonal strip

For 0<=d<=d0 use the same three separators as P17.  For W-secondary take

    (alpha,beta,mu)=(7/20,19/50,27/100),

and for D-secondary take

    (alpha,beta,mu)=(41/100,8/25,27/100).

In both rows the reverse-stress gap again has the form

    C+F(w)+G(d)+H(d-w),

with

    F(w)=beta kappa(cos w+sin w),
    G(d)=alpha kappa(cos d+sin d),

and

    H(x)=mu(cos x+sin x)
         -R sqrt(p^2+mu^2+2p mu sin x),            (P18-H)

where p=7/20 in the W-secondary row and p=8/25 in the D-secondary row.

The square-root curvature in (P18-H) is increasing with sin x: its derivative
has the positive factor

    (P+q sin x)^2+3(P^2-q^2),

where P=p^2+mu^2 and q=2p mu.  Since

    0<=x<=d0,     sin x < 13/25,

a single rational estimate gives square-root curvature <23/100 in both rows.
The trigonometric curvature magnitude is at least

    mu=27/100.

Thus H is strictly concave.  The whole gap is concave on
0<=w<=d<=d0, so it suffices to check

    (w,d)=(0,0),(0,d0),(d0,d0).

The certified minima are

    W-secondary gap > 3/1000,
    D-secondary gap > 1/100.                      (P18-low)

Hence no D--W separator exists on the low-diagonal strip once P17 is included.

### Near-diagonal strip

For d0<=d<=pi/4 exclude D-secondary with

    (alpha,beta,mu)=(5/8,1/8,1/4).

The relative-angle function is again (P18-H), now with p=1/8 and mu=1/4.
For 0<=x<=pi/4 its positive square-root curvature is <13/100, whereas the
trigonometric curvature magnitude is at least 1/4.  Hence the gap is concave
on the quadrilateral

    d0<=d<=pi/4,    0<=w<=d.

Its four vertices are

    (0,d0),(d0,d0),(0,pi/4),(pi/4,pi/4),

and exact evaluation gives gap >1/100 at each of them.

This proves (P18-angle)--(P18-axis).

`the pinned independent arithmetic audit` checks the scalar curvature
bounds and the ten fixed endpoint evaluations.  It performs no subdivision.


## A2.2 hand lemma — the small-s D-primary branch

Assume the A2.2 canonical bits

    N cardinal, W own, D own, S cardinal,

and the nonnegative-W small-s branch

    w>=0,    -2/5 < s < 1/6.

By P18,

    d:=theta_D > d0:=pi/4-1/4,
    d<=pi/4,
    D--W uses W-secondary.

Suppose D--S separates on D's primary axis. Then R^2<=Q0 is impossible.

The proof needs only C,D,S. The fixed D/S pins orient the D-primary separator
from D to S as -e_D: the D-to-S pin chord has angle -pi/12, while -e_D has
angle d in (d0,pi/4], so their dot product is positive.

Put

    beta=31/50,    mu=19/50,
    R=sqrt(Q0),    rho0=sqrt(Q0-1/4)-1/2,
    c0=rho0-1.

Use weight beta on S->C along the south-cardinal normal and weight mu on
D->S along -e_D.

Let t=d-s. Since d>d0 and -2/5<s<1/6,

    0<t<pi/2.

The force on C is beta e_y, hence its support is at most beta c0. The force
on D is mu e_D, hence its center support is at most mu rho0.

For S, write the force in S's own frame. Its two components are

    U=beta cos s-mu sin t,
    V=mu cos t-beta sin s.

Both are positive on the whole domain. Indeed

    U > beta(9/10)-mu > 0,

and for s>=0,

    V > mu(7/10)-beta/6 > 0,

while s<0 is easier.

Apply the elementary vertex-support inequality used in A1,

    G.p <= R|G|-(|G.e|+|G.f|)/2.

Here

    U^2+V^2
      = P-Q sin d,

with

    P=beta^2+mu^2=661/1250,
    Q=2 beta mu=589/1250.

After collecting the two separator thresholds, the reverse-stress gap is

    Phi(d,s)
      = C - R sqrt(P-Q sin d)
        + G(s) + mu cos(d-s),                       (A22-Dp)

where

    C=(beta+mu)/2-beta c0-mu rho0,

and

    G(s)= beta cos s,                    s>=0,
          beta(cos s-sin s),             s<=0.

Thus the only chamber wall is s=0.

### Separate concavity

Put

    F(d)=-R sqrt(P-Q sin d).

If u=sin d, then

    F''(d)
      = R Q [Q(1+u^2)-2Pu]
        / [4(P-Qu)^(3/2)].

Since d>d0>pi/6, u>1/2. Also P>Q, so the numerator is decreasing for
0<=u<=1 and is at most

    Q(5/4)-P = 301/5000.

Moreover

    R<17/10,
    sin d < 1/sqrt(2) < 71/100,
    sqrt(P-Q sin d) > 11/25.

Hence

    F''(d)
      < (17/10) Q (301/5000) / [4(11/25)^3]
      < (19/50)(3/8).                              (A22-Dp-curv)

On the other hand

    cos(d-s) > cos(pi/4+2/5) > 3/8.

Therefore, for fixed s,

    partial_d^2 Phi
      = F''(d)-mu cos(d-s) < 0.

For fixed d, each of the two s-pieces also has strictly negative second
derivative: G is concave and so is mu cos(d-s). Thus Phi is separately
concave on each rectangle

    [d0,pi/4] x [-2/5,0],
    [d0,pi/4] x [0,1/6].

A minimum is therefore at one of the six vertices

    d in {d0,pi/4},
    s in {-2/5,0,1/6}.

Exact rational square-root and alternating Taylor enclosures give

    Phi > 1/25

at all six vertices; the smallest certified value is greater than 0.04720,
at (d,s)=(d0,0).

Hence D-primary cannot be the D--S separator anywhere in R22-c.

`the pinned independent arithmetic audit` checks only the scalar
curvature inequalities and these six fixed endpoint values. It performs no
subdivision.


## A2.2 hand lemma — small-s D-secondary uses the existing chain stresses

Continue in the A2.2 residual

    N cardinal, W own, D own, S cardinal,
    w>=0,    -2/5 < s < 1/6,

and suppose D--S uses D-secondary. Structural lemma S3 gives

    0 <= w <= 1/5,    -1/4 < eps <= 0.

No new stress is needed. The already-committed P12/P14/P16 completed-square
stresses remain valid after enlarging their S-angle interval downward from
[1/6,2/5] to [-2/5,1/6].

Use the same three n-ranges:

    -2/5 < n <= -1/5     : P16 D-secondary stress,
    -1/5 <= n <=  1/5    : P14 stress,
     1/5 <= n <   2/5    : P12 stress.             (A22-Ds-ranges)

All four W--N source axes are already built into those stresses.

The only change in the calculus is the S interval. In all three stresses
the selected S-cardinal half-width had already been weakened to

    H_S >= 1/2 + (cos s + sin s)/2,

which is valid for both signs of s because |sin s| >= sin s. Hence the same
smooth trigonometric formulas remain valid without introducing an s=0 chamber.

### Curvature on the enlarged rectangles

On

    -1/5 <= n <= 1/5,
    0 <= w <= 1/5,
    -2/5 <= s <= 1/6,
    -1/4 <= eps <= 0,

the P14 stresses are separately concave in w,s,eps for every W--N source.
They are also concave in n except for the same N-primary row already isolated
in P14; the fixed n-partition

    -1/5,-3/20,-1/10,-1/20,0,1/20,1/10,3/20,1/5

makes its n-curvature strictly negative on every interval.

On the positive large-n strip

    1/5 <= n <= 2/5

the P12 proof is unchanged. The W-secondary row uses the same fixed w
partition

    0,1/20,1/10,3/20,1/5,

and every coordinate curvature is strictly negative.

On the negative large-n strip

    -2/5 <= n <= -1/5

the P16 D-secondary stresses remain separately concave for W-primary,
W-secondary and N-secondary source. For N-primary the n-curvature estimate
is unnecessary: throughout the enlarged rectangle

    d Phi / dn > 0.0329.                            (A22-Ds-mon)

Thus that row is minimized at n=-2/5.

These are fixed calculus partitions only; no adaptive subdivision is used.

### Endpoint margin

After the concavity/monotonicity reductions, exact rational square-root and
alternating Taylor arithmetic leaves only fixed endpoints. The smallest
certified squared-radius margin over Q0 is

    > 0.0074216 > 7/1000,

attained in the negative-n W-primary row at

    (n,w,s,eps)=(-2/5,0,-2/5,0).

Therefore D-secondary cannot separate D from S anywhere in the small-s
A2.2 residual.

The checker the pinned independent arithmetic audit verifies only the
displayed fixed curvature/monotonicity statements and endpoint values. It
reuses the P12/P14/P16 stresses exactly and performs no multidimensional
search.


## A2.2 hand lemma — uniform tangent coercivity for the S-secondary residual

Consider the last small-s A2.2 graph

    D--W = W-secondary,
    D--S = S-secondary,

and one of the four source choices which coincide with the candidate axes,

    W--N in {W-primary,N-secondary},
    S--E in {S-primary,E-secondary}.

Use the denominator-free central balance

    mu_CN = L,
    mu_CE = beta,
    mu_WC = mu_SC = 1,

where

    L = 1+sin w-cos w tan e,
    beta = cos w/cos e

for pattern 13, and set e=0 in these two coefficients for pattern 12.  Keep
the candidate outer weights r on W--N and S--E and m on D--W and D--S.

At the candidate the two patterns have the same one-sided tangent.  Put

    lambda = (1-r)/2,
    A = m d_* + r/2 - 2 s_*,
    B = s_*+t_*+1/2-m d_*-r/2.

For w>=0 the helper tangent splits exactly as

    T_0 = T_NW(n,w)+T_ES(e,s),

with

    T_NW
      = lambda n + A w
        + |n|/2 + (r/2)|n-w|,

    T_ES
      = -lambda e + B s
        + (|e|+|s|)/2 + (r/2)|e-s|.              (A22-tan)

The exact candidate constants satisfy

    r > 1/3,
    A > 3r/2,
    (3r-1)/2 < B < lambda.                         (A22-coeff)

These three inequalities imply the sharp pairwise bound

    T_NW >= r(|n|+w),
    T_ES >= r(|e|+|s|).                            (A22-pair)

For T_NW split into n<=0, 0<=n<=w, and n>=w.  For T_ES split into the
six order/sign cones cut out by e=0, s=0, e=s.  On every cone (A22-pair)
is just coefficient comparison; the only potentially tight coefficients are
exactly those displayed in (A22-coeff).

Now let eps=theta_D-pi/4 vary with |eps|<=1/4 while the helper deviations
are based at zero.  The only eps-dependent changes in the helper tangent are
the W and S coefficients,

    delta_w
      = m h [rho_*(cos eps-1)+(1-rho_*)sin eps],

    delta_s
      = m h [rho_*(1-cos eps)+(1-rho_*)sin eps],

with h=1/sqrt(2).  As in the earlier diagonal-strip estimate,

    |delta_w|, |delta_s| < 17/256.

Therefore, throughout the whole diagonal strip,

    T_eps
      >= (r-17/256)(|e|+|n|+w+|s|)
      > 1/4 (|e|+|n|+w+|s|).                      (A22-strip)

There is thus no first-order helper degeneracy anywhere on
-1/4<=eps<=0.

Finally, on the pure diagonal line e=n=w=s=0 the exact defect is

    Phi(0,0,0,0,eps)
      = 2m(d_*-h)(1-cos eps),

and d_*>h.  Hence it is strictly positive for eps!=0.

So the only zero of the tangent-plus-diagonal model is the exact candidate
tie.  This is the local coercivity input for the final R22-c / S-secondary
closure.

`the pinned independent arithmetic audit` checks only the algebraic candidate
inequalities in (A22-coeff), d_*>h, and the rational strip constant
1/3-17/256>1/4.


## A2.2 exact adjacent-pair balance for the final S-secondary graph

Continue in the last R22-c graph

    D--W = W-secondary,
    D--S = S-secondary,
    w>=0, -2/5<s<1/6, -1/4<eps<=0.

Let r and m be the exact candidate outer-edge stress weights already used in
the tangent lemma.  There is a cleaner exact central balance than the
previous coupled formula.

For the N/W pair choose

    mu_WC = sec w,
    mu_CN = 1+tan w.

Since the W-own normal is

    e_W=(-cos w,-sin w),

the force contributed to C by C--W and C--N is exactly

    -mu_WC e_W - mu_CN e_y
      = (1,tan w)-(0,1+tan w)
      = (1,-1).                                   (A22-pair-NW)

For the E/S pair, pattern 12 uses

    mu_CE=mu_SC=1,

so its C-force is exactly (-1,1).  Pattern 13 uses

    mu_CE=sec e,
    mu_SC=1+tan e,

and, because the E-own normal is e_E=(cos e,sin e), its C-force is again

    -mu_CE e_E + mu_SC e_y
      = (-1,-tan e)+(0,1+tan e)
      = (-1,1).                                   (A22-pair-ES)

Hence in both patterns the total force on C vanishes identically, not just at
the candidate.

All multipliers are positive on the A2.2 angle domains: 0<=w<=pi/4 and,
for the pattern-13 own-E branch, -5/12<e<3/10 lies strictly inside
(-pi/4,pi/4).

Now fix any W--N source normal u and S--E source normal v.  Keep weight r on
each of those two outer edges and weight m on each of D--W and D--S.  Let
U_X(G) denote the exact one-square center support at radius R_* for square X.

The outer-square force vectors are

    G_N = (1+tan w)e_y + r u,

    G_W = sec(w)e_W - r u + m(-f_W),

    G_E = mu_CE n_CE + r v,

    G_S = -mu_SC e_y - r v + m f_S,

    G_D = -m(-f_W)-m f_S,

where n_CE=e_x for pattern 12 and n_CE=e_E for pattern 13.

Split the two D-edge thresholds by assigning the W half-width m/2 to the
N/W term and the S half-width m/2 to the E/S term.  Then the exact reverse
support-stress defect factors as

    Phi(e,n,w,s,eps)
      = A_u(n,w) + B_v(e,s) + D(w,s,eps),          (A22-factor)

where

    A_u
      = mu_CN H_CN + mu_WC H_CW + r H_WN(u) + m/2
        - U_N(G_N)-U_W(G_W),

    B_v
      = mu_CE H_CE + mu_SC H_SC + r H_SE(v) + m/2
        - U_E(G_E)-U_S(G_S),

and

    D
      = m h_D(-f_W)+m h_D(f_S)-U_D(G_D).

Here h_D is D's half-width in the displayed normal and H_XY is the full
pair-separation half-width sum.

Thus all five-angle coupling has disappeared except through the single
diagonal-square term D(w,s,eps):

    A_u depends only on (n,w),
    B_v depends only on (e,s),
    D   depends only on (w,s,eps).

At the candidate, for the four equality-source choices

    u in {W-primary,N-secondary},
    v in {S-primary,E-secondary},

the three terms satisfy

    A_u=A_*,
    B_v=A_*,
    D=-2A_*,

so Phi=0, as required by the candidate self-stress.

This factorization is the working form for the final R22-c closure.  It
replaces the earlier five-variable coupled balance; no new structural
case split is introduced.


### Hand source-axis reduction for the final R22-c graph

For a fixed outer pair, all four SAT source axes have the same pair
half-width threshold.  Changing the source therefore changes only the two
one-square center supports.

For local force components ((X,Y)), put

    U=max(|X|,|Y|),   V=min(|X|,|Y|),
    q=sqrt(X^2+Y^2).

The exact disk-center support used here is the explicit two-branch function

    S(X,Y) =
      rho_* U,                         2R_* V <= q,
      R_* q-(U+V)/2,                   2R_* V >= q.       (SRC0)

The two formulas agree with equal first derivative on the switch.  Thus every
source comparison below is an elementary piecewise trigonometric function.
The only chamber walls are

    X=0, Y=0, |X|=|Y|, 2R_*V=q,

together with the corresponding walls for the other endpoint square.  No
angle subdivision is required.

#### W--N alternate sources

Let

    Delta_u(n,w)
      =[U_N+U_W]_{W-primary}-[U_N+U_W]_u.

Then (A_u-A_{Wp}=Delta_u).  Direct differentiation of (SRC0) on its
smooth chambers gives the following reductions.

For (u=W)-secondary, write
(Delta=Delta_N+Delta_W) according to the two endpoint squares.
The W term depends only on w, while

    partial_w Delta_N > 1/8.                       (SRC-Ws1)

Hence (Delta_N(n,w)geDelta_N(n,0)).  At w=0 the remaining
one-variable support formula has only one cap/vertex switch and gives

    Delta_N(n,0)>-431/1000.                        (SRC-Ws2)

The W term is decreasing and its endpoint value at (w=pi/4) satisfies

    Delta_W(w)>9/20.                               (SRC-Ws3)

Therefore

    Delta_Ws > 19/1000 > 1/100.                    (SRC-Ws4)

For (u=N)-primary split once at (w=1/5).

* On (0le wle1/5), the support walls from (SRC0) divide the
  ((n,w))-rectangle into six smooth chambers.  On each chamber
  (partial_nDelta) has at most one zero; substituting that zero using
  the switch identity (2R_*V=q), or taking a chamber endpoint, gives

      Delta_Np > 3/50.                              (SRC-Np1)

* On (1/5le wlepi/4), the same derivative formulas show

      Delta_Np(n,w) >= Delta_Np(-2/5,w),

  and the right-hand side is decreasing in w.  At the endpoint

      Delta_Np(-2/5,pi/4) > 1/50.                  (SRC-Np2)

All inequalities in (SRC-Ws1)--(SRC-Np2) follow by clearing the positive
radical denominators in (SRC0), then using
(sin xle x), (1-x^2/2lecos x), and the alternating upper
Taylor bounds on (|x|lepi/4+2/5).  The smallest reserve is the last
one, still strictly above (1/50).

Consequently

    A_Ws > A_Wp,
    A_Np > A_Wp.                                   (A22-src-NW)

Thus only W-primary and N-secondary need be retained on W--N.

#### S--E alternate sources

The same calculation is shorter on S--E.  Let the comparison quantity be
the equality-source support minus the alternate-source support.  In the
first three rows below its derivative in (s) is strictly negative on the
whole A2.2 strip, so the worst value occurs at (s=1/6).

| central pattern | alternate | comparison | (s)-derivative | remaining (e) reduction | lower margin |
|---|---|---|---:|---|---:|
| 12 | S-secondary | E-secondary | (<-7/50) | minimum at e=0 | (>3/100) |
| 12 | E-primary | S-primary | (<-3/100) | split at (e=0,1/10); middle Taylor bound | (>1/25) |
| 13 | S-secondary | E-secondary | (<-3/50) | minimum at (e=-5/12) | (>1/200) |

For the pattern-13 E-primary source compare with the **larger** of the two
equality-source supports, equivalently with the lower defect envelope.
Split only at the equality wall

    [U_E+U_S]_{S-primary}=[U_E+U_S]_{E-secondary}.

On either side, differentiation of (SRC0) shows that an interior minimum can
only lie on this wall or on (s=1/6).  Along the wall the derivative in
(e) has the sign pointing toward its endpoints.  The two endpoint
calculations and the top edge therefore leave the single worst corner

    (e,s)=(3/10,1/6),

where the support reserve is

    > 1/100.                                       (SRC-13Ep)

Thus, in both central patterns,

    B_Ss > B_Es,

and E-primary is strictly above the lower equality envelope.  Therefore it
is enough to retain

    W--N in {W-primary,N-secondary},
    S--E in {S-primary,E-secondary}.               (A22-src-final)

This is a finite hand chamber calculation from the explicit support formula
(SRC0).  An independent arithmetic audit is retained only as an
independent arithmetic check; its rational grid is not part of the proof.


### Hand reduced monotonicity once the pair envelopes are known

For the equality-source residual define

    a(w)=A_Wp(0,w),

and

    b(s)=B_Sp(0,s),    s<=0,
         B_Es(0,s),    s>=0.

The pair envelopes give

    Phi >= F(w,s,eps):=a(w)+b(s)+D(w,s,eps).

Write

    beta=(w-s)/2,
    delta=eps-(w+s)/2,
    h=1/sqrt(2).

The D term has two explicit formulas.  On the cap branch,

    D_cap
      =sqrt(2)m[(1-rho_*)cos beta+rho_* sin beta] cos delta.   (MON1)

On the vertex branch,

    D_vert
      =sqrt(2)m[
          ((3 cos beta-sin beta)/2) cos delta
          -((cos beta-sin beta)/2) sin delta
          -R_*(cos beta-sin beta)].                         (MON2)

The common A2.2 bounds, together with the graph-order constraint (w\le d), give

    -1/12 <= beta <= 3/5,
    -3/5 <= delta <= 1/5.                         (MON3)

The support condition sharpens the second interval.  On the cap branch,
(2R_*|sin delta|le1).  Since (R_*>5/3) and
(sin(31/100)>3/10),

    |delta|<31/100.                                (MON4)

On the vertex branch, (2R_*|sin delta|ge1).  Since
(R_*<17/10), (sin(1/5)<5/17), and the positive side of
(MON3) is at most (1/5),

    delta<-5/17.                                   (MON5)

Now differentiate (MON1)--(MON2), using
(partial_w beta=1/2), (partial_w delta=-1/2) and
(partial_s beta=partial_s delta=-1/2).
The elementary bounds

    cos(3/5)>4/5,    |sin beta|<3/5,
    cos(31/100)>19/20,
    sin(31/100)<31/100,

on the cap range, and

    cos(3/5)>4/5,    -sin delta>sin(5/17)>7/25,

on the vertex range, give on **both** branches

    partial_w D > 29/100,                         (MON6)

    -19/20 < partial_s D < -1/2.                  (MON7)

No support-wall case is missing: (MON1) and (MON2) have equal value and
equal first derivative on the cap/vertex switch.

The pair terms are one-dimensional.  Differentiating their explicit
SRC0 formulas gives

    a'(w)>-29/100,                                 (MON8)

    b'(s)<2/5,        -2/5<s<0,                   (MON9)
    b'(s)>1,           0<s<1/6.                   (MON10)

For (MON8), the N and W forces are x-dominant; after clearing their positive
norm denominators the possible negative numerator is bounded by
((29/100)cos^2 w).  For (MON9)--(MON10), S is on the vertex branch and
the E cap/vertex derivatives match; the respective residual numerators are
bounded using (|s|<2/5) and (s<1/6).  These are the same elementary
derivative calculations used in the two pair-envelope lemmas.

Consequently

    partial_w F >0,

    partial_s F < 2/5-1/2 = -1/10,      s<0,

    partial_s F > 1-19/20 = 1/20,       s>0.       (MON11)

Thus every minimum is forced to

    w=0, s=0.

There

    F(0,0,eps)
      =2m(d_*-1/sqrt(2))(1-cos eps)>=0,             (MON12)

with equality only at eps=0.

This is the complete reduced monotonicity argument.  The old
an independent arithmetic audit is only an arithmetic
cross-check for (MON6)--(MON10), not a proof dependency.


### Hand N/W pair envelope

For the two equality sources u in {W-primary,N-secondary}
the N and W force components are x-dominant throughout

    -2/5 <= n <= 2/5,      0 <= w <= pi/4.

Hence their one-square supports are given by (SRC0), with only the sign wall
of the transverse component and the tangent cap/vertex wall.

Fix w.  Differentiating the explicit formulas on each smooth chamber,
clearing the positive radical denominators, and using

    cos n>9/10,   |sin n|<2/5,
    cos(w-n)>1/2, R_*<17/10, rho_*<9/8,

gives, for either equality source,

    partial_n A_u < 0,       n<0,
    partial_n A_u > 0,       n>0.                 (NW1)

At a transverse sign wall the absolute-value derivative changes in the
direction prescribed by (NW1), and at a cap/vertex wall the derivatives
agree.  Thus no additional minimum is created at a wall.  Consequently

    A_u(n,w) >= A_u(0,w).                          (NW2)

At n=0 the two source formulas agree when w=0.  Their difference is
one-dimensional.  Direct differentiation gives

    d/dw [A_Ns(0,w)-A_Wp(0,w)] > 1/5              (NW3)

for 0<w<pi/4.  After multiplying by the positive square-root
denominators, (NW3) reduces to
(cos w>1/sqrt2), (sin w<1/sqrt2), and
R_*<17/10; the residual rational numerator is (>1/200).

Therefore

    A_Ns(0,w) >= A_Wp(0,w),

with equality only at w=0.  Defining

    a(w)=A_Wp(0,w),

we obtain the hand envelope

    A_u(n,w) >= a(w)
      for u in {W-primary,N-secondary}.            (A22-env-NW-done)

An independent arithmetic audit is only an arithmetic
cross-check; no box cover is used in the proof.


### Hand E/S pair envelope and closure of R22-c

For both patterns 12 and 13, the E force is x-dominant on the whole A2.2
domain.  The S force has both local components positive and is always on the
far-vertex support branch.  Thus the only support wall in the E/S calculus is
the tangent E cap/vertex switch from (SRC0).

Put

    Delta(s)=B_Sp(0,s)-B_Es(0,s).

At e=0 the two central patterns have identical pair formulas and
Delta(0)=0.  Differentiating the explicit support expressions gives

    Delta'(s)>1/20,       -2/5<s<0,
    Delta'(s)>19/100,      0<s<1/6.                (ES1)

Hence S-primary is the lower equality source at e=0 for (s<0), while
E-secondary is lower for s>0.

For E-secondary, direct differentiation in (e) gives, in both patterns,

    partial_e B_Es <0,     e<0,
    partial_e B_Es >0,     e>0.                    (ES2)

The pattern-13 own-E multipliers sec e and 1+tan e introduce no
extra wall; after clearing cos e>0, the derivative numerator has the
same sign.  Thus E-secondary is minimized at e=0.

For S-primary the same statement holds when s<=0:

    partial_e B_Sp <0,     e<0,
    partial_e B_Sp >0,     e>0.                    (ES3)

When s>0, the negative-e side still decreases toward zero.  On the
positive side split only at e=s.  The explicit derivative satisfies

    partial_e B_Sp > -9/100,      0<e<s,
    partial_e B_Sp > 0,            e>s.            (ES4)

To see the first bound, use the vertex formula for S and either branch of the
E support.  The cap and vertex derivative formulas agree at their switch;
after multiplying by the positive E-force norm, the negative part is at most
9/100 by
sin s<s<1/6, |e-s|<1/6, and R_*<17/10.

Integrating (ES4) from (0) to e<=s and using (ES1),

    B_Sp(e,s)
      >= B_Sp(0,s)-(9/100)s
      >  B_Es(0,s)+(19/100-9/100)s
      =  B_Es(0,s)+s/10.                           (ES5)

Therefore, for either equality source,

    B_v(e,s) >= b(s)
      := B_Sp(0,s),    s<=0,
         B_Es(0,s),    s>=0.                       (A22-env-ES-done)

This is the complete E/S hand envelope.  The former
an independent arithmetic audit only replays the displayed derivative
inequalities numerically and is not a proof dependency.
#### Pattern-12 cardinal/cardinal extension to \(s<2/5\)

The preceding common proof was stated only through \(s<1/6\) because the
Pattern-13 own-E derivative bound (ES4) deteriorates beyond that point.
Pattern 14, however, uses the **Pattern-12 cardinal/cardinal** E/S pair only.
For that branch the same explicit formulas have substantially more reserve.

On

\[
0<s<2/5,\qquad -2/5<e<2/5,
\]

direct differentiation of the Pattern-12 formulas, with the same exact
cap/vertex support and the same \(C^1\) switch, gives

\[
\Delta'(s)>1/5,                                    \tag{ES1+}
\]

\[
\partial_e B_{Es}<0\ (e<0),\qquad
\partial_e B_{Es}>0\ (e>0),                        \tag{ES2+}
\]

and for S-primary

\[
\partial_e B_{Sp}<0\quad(e<0),                     \tag{ES3+}
\]

\[
\partial_e B_{Sp}>-7/100\quad(0<e<s),\qquad
\partial_e B_{Sp}>0\quad(e>s).                     \tag{ES4+}
\]

These are scalar inequalities. After clearing the positive force norms,
alternating Taylor bounds on \(|e|,s\le2/5\) give the weaker rational
margins displayed above. No Pattern-13 multiplier \(\sec e\) or
\(1+\tan e\) occurs here.

Integrating (ES4+) and using (ES1+) gives, for \(0<e\le s\),

\[
\begin{aligned}
B_{Sp}(e,s)
&\ge B_{Sp}(0,s)-{7\over100}s\\
&>B_{Es}(0,s)+\left({1\over5}-{7\over100}\right)s\\
&=B_{Es}(0,s)+{13\over100}s.                       \tag{ES5+}
\end{aligned}
\]

Together with (ES2+)--(ES3+), this proves the Pattern-12-only extension

\[
\boxed{B_v(e,s)\ge B_{Es}(0,s)\qquad
       (0\le s<2/5)}                              \tag{A22-env-ES-P12+}
\]

for all four E/S source axes. The Pattern-13 own-E envelope remains
restricted to \(s<1/6\); no widened claim is made for it.

The archived exact checker `check_A2_R22c_ES_envelope.py` at
`b51d8a88c30588e279882b8efd5441304635f527` is only an arithmetic
cross-check for the original strip; the widened Pattern-12 statement above
is the hand inequality used below.


Combining (A22-env-NW-done) and (A22-env-ES-done) with the reduced
monotonicity below gives

    Phi >= a(w)+b(s)+D(w,s,eps).

The derivatives force w=s=0, and then

    Phi(0,0,eps)
      =2m(d_*-1/sqrt(2))(1-cos eps)>=0,

with equality only at eps=0.  Hence R22-c is closed for both patterns
12 and 13.


## A2.2 hand lemma — secondary D--W forces d>1/2

After the two primary D--W axes are removed, suppose

    -2/3 <= w <= 0,      0 <= d <= 1/2

and D--W separates on one of the two secondary axes.

Use the same C--W--D three-edge architecture in both cases:

    C -> D on D-primary,
    W -> C on W-primary,
    W -> D on the selected secondary axis.

For W-secondary take

    (alpha,beta,mu)=(31,44,25)/100,

and for D-secondary take

    (alpha,beta,mu)=(42,37,21)/100.                (SD1)

Put x=d-w.  In either row the C support has the single sign wall

    alpha sin d+beta sin w=0,                      (SD2)

and exactly one exterior support has the ordinary cap/vertex switch.
All force components have fixed signs away from those two walls.

On each smooth chamber direct expansion gives a function of the form

    Phi=C+F_sigma(w)+G_sigma(d)+H_tau(d-w).        (SD3)

The four F_sigma,G_sigma are positive trigonometric combinations on the
displayed angle ranges.  Differentiating the square-root term in H_tau and
using

    R_*<17/10,  cos(2/3)>3/4,
    sin(2/3)<5/8,  cos(7/6)>3/8

gives the uniform chamber curvature bounds

    W-secondary:
      partial_w^2 Phi < -17/100,
      partial_d^2 Phi <  -2/25,

    D-secondary:
      partial_w^2 Phi <  -7/50,
      partial_d^2 Phi <  -7/50.                   (SD4)

No hidden chamber minimum occurs.  Across the central sign wall (SD2), the
term `-c_0 max(0,alpha sin d+beta sin w)` turns on as the signed
quantity increases, so each relevant one-sided derivative jumps downward.
At the cap/vertex support wall the two support formulas have equal first
derivative, exactly as in the preceding W-primary lemma.  Hence both full
stress gaps are separately concave on the complete rectangle.

It remains to evaluate only the four vertices
`(w,d) in {-2/3,0} x {0,1/2}`.

For W-secondary the four lower margins, in the vertex order
((-2/3,0),(-2/3,1/2),(0,0),(0,1/2)), are

    > 3/100,  3/1000,  1/100,  3/1000.            (SD5)

For D-secondary the four lower margins are

    > 1/400,  3/1000,  1/250,  1/500.             (SD6)

These are the direct endpoint values with the exact cap/vertex support.
A separate exact fixed-cover audit gives positive reserve throughout each
rectangle as well.

The estimates use only alternating Taylor bounds at 1/2 and 2/3 and
`R_*<17/10`, `c_0<23/200`.

Therefore neither secondary source can occur when d<=1/2.  Every R22-d
survivor satisfies

    d>1/2.

This replaces the former fixed cover and predetermined 4x4 refinement in
an independent arithmetic audit.


## A2.2 hand lemma — W-primary D--W for w<0

Assume

    -2/3 <= w <= 0,      0 <= d <= pi/4,

and suppose D--W separates on W-primary.  The fixed W/D pins orient the
separator from W to D on -e_W.

Use the three separators

    C -> D on D-primary,       alpha=19/50,
    W -> C on W-primary,       beta =43/100,
    W -> D on -e_W,            mu   =19/100.

Put x=d-w and

    q(x)^2
      =(19/50)^2+(19/100)^2
        -2(19/50)(19/100) cos x.                  (WP1)

The W force is purely primary.  In the D frame the force components are

    X=19/50-(19/100)cos x,
    Y=(19/100)sin x,

so X>Y>=0 throughout the domain.

There are only two harmless support switches.

First, the exact C support is

    c_0[(19/50)cos d+(43/100)cos w
        + max(0,(19/50)sin d+(43/100)sin w)].      (WP2)

Thus the central sign wall is

    (19/50)sin d+(43/100)sin w=0.                 (WP3)

Second, the exact D-center support is the cap expression on one side of the
usual cap/vertex switch and the far-vertex expression on the other.

On every smooth chamber the stress defect has the separated form

    Phi=C+F_sigma(w)+G_sigma(d)+H_tau(d-w),        (WP4)

where sigma records the sign in (WP3), tau records the D support branch, and

    F_0(w)
      =(43/100)[(1/2-c_0)cos w-(1/2)sin w],

    F_1(w)
      =(43/100)[(1/2-c_0)cos w-(1/2+c_0)sin w],

    G_0(d)
      =(19/50)[(1/2-c_0)cos d+(1/2)sin d],

    G_1(d)
      =(19/50)(1/2-c_0)(cos d+sin d).              (WP5)

All four displayed functions are positive on their intervals, hence their
second derivatives are negative.

For the cap branch,

    H_cap''(x)
      =-(19/100)[(1/2+rho_*)cos x+(1/2)sin x]<0.  (WP6)

For the vertex branch,

    H_vert(x)
      =19/100 +(19/100)sin x-R_*q(x),

and direct differentiation gives

    H_vert''(x)<-9/100                             (WP7)

for `0<=x<=pi/4+2/3<3/2`.  Multiplying by q(x)^3 reduces (WP7) to a
sum of rational multiples of sin x, cos x and q(x)^2; the bounds
`19/100<=q<=41/100`, `R_*<17/10`, together with the alternating
Taylor bounds on [0,3/2], give the stated reserve.

The chamber joins preserve concavity.  Across (WP3), increasing either w or
d turns on the negative term
`-c_0 max(0,(19/50)sin d+(43/100)sin w)`, so the corresponding
one-sided derivative jumps downward.  At the D cap/vertex switch the two
support formulas agree with equal first derivative: writing the switch as
`2R_*Y=q` and using
`R_*^2=rho_*^2+rho_*+1/2` gives this identity directly.

Therefore Phi is separately concave in w and d on the entire rectangle,
despite the two support switches.  Its minimum is attained at one of

    (w,d) in {-2/3,0} x {0,pi/4}.

The four endpoint values satisfy

    Phi(-2/3,0)    > 9/100,
    Phi(-2/3,pi/4) > 1/125,
    Phi(0,0)       > 7/1000,
    Phi(0,pi/4)    > 7/200.                        (WP8)

These are direct alternating-Taylor evaluations at the displayed rational
angles and pi/4, using `R_*<17/10` and the defining radical bounds for
rho_*.

Hence W-primary cannot be the D--W source anywhere in R22-d.  This replaces
the former fixed `1/100` cover in
an independent arithmetic audit; that file is retained only as a sanity
check.


## A2.2 hand lemma — D-primary D--W for w<0

Assume

    -2/3 <= w <= 0,      0 <= d <= pi/4,

and suppose D--W separates on D-primary.  The fixed W/D pin chord determines
the directed normal: it is -e_D for d<pi/12 and +e_D for d>pi/12.  At
d=pi/12 the two fixed interior pins have equal projection on e_D, so a strict
D-primary separation is impossible.

### The +e_D piece: pi/12 <= d <= pi/4

Use

    W -> C on W-own primary,      weight 10/13,
    W -> D on +e_D,               weight 3/13.

Put x=d-w.  For the W center use the elementary far-vertex support bound,
not the cap/vertex minimum.  In W coordinates the force components are

    X=10/13-(3/13) cos x,
    Y=(3/13) sin x,

and satisfy X>Y>=0.  The D force is purely primary.

After cancellation the lower stress gap is

    Phi_+(w,d)=C_+ + F(w)+H(d-w),                  (DWp1)

where

    F(w)=(10/13)[(1/2-c_0)cos w-(1/2)sin w],

    H(x)=5/13 +(3/13)sin x
          -R_* sqrt(109/169-(60/169)cos x),

    C_+=1/2-(3/13)rho_*.

Since w<=0,

    F''(w)=-F(w)<0.                                (DWp2)

Write q(x)^2=109/169-(60/169)cos x.  Direct differentiation gives

    H''(x)
      = -(3/13)sin x
        -R_*[(30/169)cos x/q
              -(900/28561)sin^2 x/q^3].           (DWp3)

On

    pi/12 <= x <= pi/4+2/3 < 3/2

the elementary bounds
`q>1/2`, `R_*<17/10`, `sin x>=0`, and the usual rational
sine/cosine Taylor bounds give

    H''(x)<-7/50.                                  (DWp4)

Thus Phi_+ is separately concave in w and d.  Its minimum is at one of the
four rectangle vertices

    (w,d) in {-2/3,0} x {pi/12,pi/4}.

The four values satisfy, respectively,

    Phi_+ > 17/100,  1/100,  1/20,   2/100.        (DWp5)

Hence the +e_D orientation is impossible.

### The -e_D piece: 0 <= d <= pi/12

Use

    C -> D on D-primary,       weight 1/2,
    W -> C on W-own primary,   weight 1/20,
    W -> D on -e_D,            weight 9/20.

For the central square use the weaker but separated bound

    U_C <= c_0[(1/2)(cos d+sin d)+(1/20)cos w];

the omitted W contribution to the y-force is nonpositive because w<=0.
For W use the far-vertex support bound.  The resulting gap is

    Phi_-(w,d)=C_-+F_-(w)+G_-(d)+H_-(d-w),         (DWm1)

with

    F_-(w)=(1/20)[(1/2-c_0)cos w-(1/2)sin w],

    G_-(d)=(1/2)(1/2-c_0)(cos d+sin d),

    H_-(x)=(9/20)(cos x+sin x)
      -R_* sqrt((1/20)^2+(9/20)^2
                 +2(1/20)(9/20)cos x),

and

    C_-=1/2+(1/40)-rho_*/20.

All three scalar functions are concave on their displayed intervals.
For F_- and G_- this is immediate from the signs of sine and cosine.
For H_-, differentiating the square root gives

    H_-''(x)<-1/3                                (DWm2)

on `0<=x<=pi/12+2/3`; the bound follows already from
`cos x>1/2`, `R_*<17/10`, and the positive lower bound on the radical.

Therefore Phi_- is separately concave and its minimum is again at the four
rectangle vertices.  Their weakest value is

    Phi_->1/4.                                     (DWm3)

So the -e_D orientation is impossible as well.

Consequently D-primary is never the D--W source on R22-d.  This replaces
the former fixed `1/100` cover in
an independent arithmetic audit; that checker is retained only as a
sanity check.


## A2.2 hand lemma — S-primary D--S for s<=1/6

Keep the high-D strip

    1/2 <= d <= pi/4,      -2/5 <= s <= 1/6,

and suppose D--S separates on S-primary.  The fixed D/S pins determine the
orientation switch at s=-pi/12.

### The +e_S orientation: -pi/12 <= s <= 1/6

Use

    C -> D on D-primary,     weight 2/3,
    D -> S on +e_S,          weight 1/3.

Put t=d-s.  The D-frame force components have fixed signs, so the elementary
far-vertex support gives the lower gap

    Phi_+(d,t)
      = C_+ +(2/3)(1/2-c_0)(cos d+sin d)
        +(1/3) cos t
        -R_* sqrt(5/9-(4/9) sin t),                (SP1)

where c_0=rho_*-1 and

    C_+ = 5/6-rho_*/3.

Here

    1/3 <= t <= pi/3.

The d-dependent term is increasing on [1/2,pi/4], because
cos d-sin d>=0.  The t-dependent term is also increasing.  Indeed, if

    q(t)=sqrt(5/9-(4/9) sin t),

then

    d/dt [(1/3)cos t-R_*q(t)]
      = -(1/3)sin t + R_*(2/9) cos t/q(t).

On [1/3,pi/3],

    R_*>42/25,    cos t>=1/2,    q(t)<2/3,

so this derivative is

    > -1/3 +(42/25)(2/9)(1/2)/(2/3)
    > 1/20.                                       (SP2)

Therefore the minimum is at d=1/2,t=1/3.  At that point

    Phi_+(1/2,1/3) > 4/100.                        (SP3)

Thus the +e_S orientation is impossible.

### The -e_S orientation: -2/5 <= s <= -pi/12

Use

    S -> C on the south-cardinal normal,     weight 7/12,
    D -> S on -e_S,                          weight 5/12.

Again the force-component signs are fixed.  After the same far-vertex
support expansion the gap is

    Phi_-(s,t)
      = C_- + G(s) +(5/12)(cos t+sin t),            (SP4)

where

    C_- = 1/2-(7/12)c_0-5/24-(5/12)R_*,

    G(s)
      =(7/12)(cos s-sin s)
       -R_* sqrt(37/72-(35/72) cos s),              (SP5)

and

    1/2+pi/12 <= t <= pi/4+2/5.

Direct differentiation gives

    G''(s)<0                                       (SP6)

throughout [-2/5,-pi/12].  For example, after multiplying by the positive
cube of the square root in (SP5), the only potentially positive curvature
term is bounded by
`R_*(35/72)^2 sin^2(2/5)/4`, while the
`(7/12)(cos s-sin s)` curvature dominates it using
`cos(2/5)>9/10`, `sin(2/5)<2/5`, and `R_*<17/10`.

Also

    d^2/dt^2 [(5/12)(cos t+sin t)]
      = -(5/12)(cos t+sin t)<0.                   (SP7)

Hence Phi_- is separately concave in s and t, so its minimum is at the four
rectangle vertices.  The weakest of the four satisfies

    Phi_- > 39/100.                                (SP8)

Thus the -e_S orientation is impossible as well.

Consequently

    D--S=S-primary  =>  s>1/6

on R22-d.  This replaces the former fixed `1/50` cover in
an independent arithmetic audit; that script is now only a sanity
check.


## A2.2 hand lemma — D-primary D--S on the high-D strip

Assume the R22-d structural reductions have already given

    -2/5 <= s <= 2/5,      1/2 <= d <= pi/4,

and suppose D--S separates on D-primary.  Use only

    S -> C on the south cardinal normal,      weight 3/5,
    D -> S on -e_D,                           weight 2/5.

Put

    t=d-s,
    q(d)=sqrt(13/25-(12/25) sin d).

In the S frame the induced force is

    X=(3/5) cos s-(2/5) sin t,
    Y=(2/5) cos t-(3/5) sin s.

On the displayed domain both X and Y are positive.  Indeed, for s<=0 the
second term in Y is nonnegative, while for s>=0 one has
t<=pi/4 and hence cos t>7/10; the X estimate is even easier from
cos(2/5)>9/10 and sin t<1.  Therefore the elementary far-vertex support
bound may be used without any absolute-value chamber split.

After cancellation, the reverse-stress gap is bounded below by

    Phi(s,d)
      = C + G(s) + (2/5) cos(d-s) - R_* q(d),      (DP1)

where

    C = 1/2-(3/5)(rho_*-1)-(2/5)rho_*,

and

    G(s) =
      (3/5)(cos s-sin s),    s<=0,
      (3/5) cos s,            s>=0.                (DP2)

Thus, on either half of the s-interval,

    partial_s^2 Phi
      = -G(s) -(2/5) cos(d-s) < 0,                 (DP3)

so the minimum in s occurs at one of

    s=-2/5, 0, 2/5.

It remains to move d to its lower endpoint.  Differentiating (DP1),

    partial_d Phi
      = -(2/5) sin(d-s)
        + R_* (6/25) cos d / q(d).                 (DP4)

Use the elementary candidate bounds

    R_*>42/25,
    cos d>7/10,
    q(d)<11/20.                                    (DP5)

For the last inequality, d>=1/2 gives
sin d>23/50, hence

    q(d)^2
      < 13/25-(12/25)(23/50)
      < (11/20)^2.

Since sin(d-s)<=1, (DP4)--(DP5) give

    partial_d Phi
      > -2/5 +(42/25)(6/25)(7/10)/(11/20)
      > 1/10.                                      (DP6)

Hence d=1/2 is the unique worst d endpoint.

The three remaining scalar values are

    Phi(-2/5,1/2) > 11/100,
    Phi(0,1/2)    >  2/100,
    Phi( 2/5,1/2) >  2/100.                       (DP7)

Each follows directly from the alternating Taylor bounds
sin x > x-x^3/6 and
cos x > 1-x^2/2 on the rational angles involved, together with
42/25<R_*<17/10 and the defining radical bound for rho_*.

Therefore D-primary cannot be the D--S source anywhere on the high-D
R22-d strip.  This replaces the former two-dimensional fixed-grid check
an independent arithmetic audit; the latter is retained only as a numerical
sanity check, not as a proof dependency.


## A2.2 hand lemma — candidate graph on -1/2<=w<0

Return to R22-d after the structural D-edge reductions.  Assume

    -1/2 <= w < 0,
    |n| <= 203/1000,
    -2/5 < s < 1/6,
    1/2 <= d <= pi/4,

and

    D--W=W-secondary,
    D--S=S-secondary.

### Adjacent-pair source reduction

The S--E alternate sources are already removed by the hand source lemma
above; that argument depends only on (e,s) and is unchanged for negative w.

For W--N use the same explicit support function (SRC0).  On

    |n|<=203/1000,    -1/2<=w<=0,

split only at the equality wall between W-primary and N-secondary and at the
ordinary sign/dominance/cap walls of (SRC0).  On every smooth chamber the
difference

    max(S_Wp,S_Ns)-S_alt

has no interior minimum: its derivative points to a chamber wall, and at a
cap/vertex wall the one-sided derivatives agree.  The finite boundary
calculation gives

    max(S_Wp,S_Ns)-S_Ws > 1/25,
    max(S_Wp,S_Ns)-S_Np > 1/20.                   (NEG-src)

For W-secondary the only non-endpoint boundary is its equality wall; there
the derivative is positive toward both ends and the weakest value is
(>1/25).  For N-primary the equality wall meets the north-angle boundary
at (n=w=-203/1000); substituting the wall identity leaves a
one-variable function whose derivative is positive, with endpoint reserve
(>1/20).  Thus only

    W--N in {W-primary,N-secondary},
    S--E in {S-primary,E-secondary}               (NEG-eq-src)

remain.  No two-dimensional cover is involved.

For these four combinations the pair factorization remains

    Phi=A_u(n,w)+B_v(e,s)+D(w,s,eps).              (NEG-factor)

### Hand N/W reserve

Let

    A_*=A_Wp(0,0)=A_Ns(0,0).

For N-secondary, differentiation of the SRC0 formula shows

    partial_n A_Ns <0,    n<0,
    partial_n A_Ns >0,    n>0,

so the minimum is at n=0.  Along that line,

    d/dw A_Ns(0,w)<-73/100,    -1/2<=w<=-1/5,
    d/dw A_Ns(0,w)<-37/50,     -1/5<=w<=0.        (NEG-Ns)

For W-primary put

    G_K(n,w)=A_Wp(n,w)-A_*+K w.

On the far half-strip (-1/2le wle-1/5), take (K=73/100).
The only nonsmooth walls are (n=0), (n=w), the transverse-force sign
wall and the tangent cap/vertex wall.  On each smooth chamber the second
derivatives point toward its boundary; after using the wall identities, all
boundary functions are one-dimensional.  Their minima occur at the rational
angle endpoints, the weakest being

    n=w=-1/5,

where

    G_{73/100} > 3/50.                             (NEG-Wp-far)

On (-1/5le wle0), the same chamber calculation with
(K=37/50) has the sole zero endpoint (n=w=0); all other chamber
endpoints are positive.  Hence

    A_Wp(n,w)>=A_*+(37/50)(-w).                    (NEG-Wp-near)

Since (37/50>73/100), (NEG-Ns)--(NEG-Wp-near) give the uniform
half-strip reserve

    A_u(n,w)>=A_*+(73/100)(-w)                     (NEG-reserve)

for both equality sources.

The derivative claims above follow directly from SRC0 after clearing the
positive norm denominators.  On the present ranges one only needs

    cos(1/2)>7/8,
    |sin n|<203/1000,
    cos(n-w)>3/4,
    R_*<17/10, rho_*<9/8.

### First force s to zero

Keep

    beta=(w-s)/2,
    delta=eps-(w+s)/2.

On this half-strip

    -9/20 <= beta <= 1/5.

Use the same explicit D formulas (MON1)--(MON2).  Direct differentiation on
the cap branch and on the two signed vertex ranges gives

    -3/4 < partial_s D < -49/100.                  (NEG-Ds)

The E/S hand envelope has the slightly stronger positive-side estimate

    b'(s)>9/10,      s>0,

while for s<0 it still has

    b'(s)<2/5.

Therefore, for fixed w and eps,

    d/ds [b(s)+D(w,s,eps)] < -9/100,    s<0,
    d/ds [b(s)+D(w,s,eps)] >  3/20,    s>0.        (NEG-s)

So the unique minimum in s is at

    s=0.

### Then force w to zero

On s=0,

    -1/4 <= beta <=0,

and the cap/vertex formulas give

    partial_w D(w,0,eps)<71/100.                   (NEG-Dw)

Indeed the cap range has (|delta|<31/100); on the vertex range use
(|delta|<3/10) on the negative side and (delta<1/4) on the
positive side.  Substitution in (MON1)--(MON2) gives (NEG-Dw) directly.

Integrating from w to 0,

    D(w,0,eps)
      >=D(0,0,eps)-(71/100)(-w).                   (NEG-loss)

Combining (NEG-reserve) and (NEG-loss),

    A_u(n,w)+D(w,0,eps)
      >=A_*+D(0,0,eps)+(1/50)(-w).                 (NEG-coercive)

The E/S term at s=0 is at least b(0), and the candidate diagonal identity is

    A_*+b(0)+D(0,0,eps)
      =2m(d_*-1/sqrt(2))(1-cos eps)>=0.            (NEG-diag)

Because w<0, the reserve in (NEG-coercive) is strict.  Hence the candidate
D-edge graph is impossible throughout

    -1/2<=w<0.

This is a hand chamber/derivative proof.  The former
an independent arithmetic audit,
an independent arithmetic audit,
an independent arithmetic audit, and
an independent arithmetic audit are retained only as independent arithmetic
cross-checks.



# Proof status

This is an audited working proof, not yet a completed theorem.  The verified hand reductions should be retained, but formalization must wait on the three substantive repair tracks stated at the beginning: global foundations, exact A2.3 support branches, and direct survivor closures.  LEAN_ROADMAP.md now treats those repairs as a pre-formalization gate.
