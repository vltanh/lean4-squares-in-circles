# An aligned negative GA1 path reaches a hard owner with strict H loss

## 1. Statement and comparison scope

Put
\[
q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
\qquad K=\frac{13}{12}.
\tag{1}
\]
Work with normal signed tangents: H,A,T are positive and G,B,D,E
are negative. Magnitudes are nonnegative and sorted, all seven
points satisfy the true central exclusion, and their shifted
corner values are at most a common q with \(q_L\le q\le Q\). Their real frames
belong to one interval of length at most \(7/10\).

Suppose HG, AB and TD are aligned, and write
\[
\theta_H=\theta_G=\alpha=t+u,\qquad
\theta_A=\theta_B=u,\qquad
\theta_T=\theta_D=0,\qquad t,u\ge0.
\tag{2}
\]
Retain transverse zero witnesses, GA1, BT2, either DE2 or DE3,
and either EH0 or EH1. Let
\(\delta=\theta_E\), \(\epsilon=\alpha-\delta\).
No E-frame order is assumed. Require the radial alternative
\[
a_E\le\frac7{12}\quad\hbox{or}\quad
a_E\ge\max\{b_H,b_D\}.
\tag{3}
\]
This includes an actual true-core or outer boundary representative.
It remains valid if an original ceiling below \(q_L\) is enlarged
to \(q_L\), since the coordinates are unchanged.

**Reduction theorem.** If actual GA0 is already feasible,
[the arbitrary-frame normal hard-owner theorem](HAND_G5_NORMAL_HARD_OWNERS_ARBITRARY_FRAMES_SHARP_REDUCTION.md)
applies directly. Otherwise there is a necessary-cycle descendant
at the same ceiling with an actual GA0 witness, all the other
normal hard-owner hypotheses, and a strict H-circle loss.
Separate pre-existing losses at A or B are retained. Consequently
every system above has \(q\ge q_*\), with strict inequality if
GA0 was unavailable.

The construction preserves neighboring necessary inequalities;
it asserts nothing about omitted nonneighbor packing conditions
or G1 markers. It does not establish the alignment and order (2).

We prove the case in which GA0 is unavailable; in particular
\(t>0\). With \(W(x)=(1+\cos x+|\sin x|)/2\), the mixed
projections are
\[
\begin{array}{c|l}
DE2&a_D\cos\delta+b_D\sin\delta+b_E\\
DE3&a_D+a_E\sin\delta+b_E\cos\delta\\
EH0&a_H\cos\epsilon+b_H\sin\epsilon-b_E\\
EH1&a_H+a_E\sin\epsilon-b_E\cos\epsilon.
\end{array}
\tag{4}
\]
A retained entry is at least its corresponding width.

## 2. The unavailable hard witness forces a high H tangent

Put
\[
K_G=a_G+\tfrac12,\quad D_G=b_G+\tfrac12,\quad
X=a_A+\tfrac12,\quad Y=b_A+\tfrac12.
\]
The comparison-vector calculation in Section 4 of
[the low-GA/high-EH theorem](HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md)
uses only the two quarter projections, sorting and A's circle.
It gives
\[
q\ge X^2+Y^2>
1+K_G^2+D_G^2+2D_G\cos t+2K_G\sin t
\ge K_G^2+(D_G+1)^2.
\tag{5}
\]
For completeness, its comparison vector is
\[
X_*=1+D_G\cos t+K_G\sin t,\qquad
Y_*=K_G\cos t-D_G\sin t>0.
\]
GA1 gives \(X\ge X_*\), while GA0 failure gives
\(Y>Y_*-\tan(t/2)(X-X_*)\).
Since
\(X_*-\tan(t/2)Y_*=1+D_G+K_G\tan(t/2)>0\),
the completed-square comparison is strict. The last inequality
in (5) uses \(K_G\ge D_G\) and \(\sin t+\cos t\ge1\).
No outer-circle equality for G is used.

Equation (5) forces \(D_G<1\), since \(K_G\ge D_G\).
Thus \(b_G<1/2\), and true central exclusion gives
\(a_G\ge7/12\). Consequently
\[
D_G<\frac{82}{125},\quad b_G<\frac{39}{250},\quad
b_H\ge1-b_G>\frac{211}{250}=.844,\quad a_H<1.
\tag{6}
\]
The square reserve for D is
\(K^2+(1+82/125)^2-Q=781/2250000>0\).
For the last assertion,
\(9/4+(168/125)^2>Q\).
If \(\epsilon\le0\), either EH projection in (4) is at most
\(a_H<1\), while \(W(\epsilon)\ge1\). Therefore
\[
\epsilon>0.
\tag{7}
\]

Lower only G's primary to \(7/12\), if necessary. Its tangent
is below \(1/2\), so it becomes a sorted true flat-core point;
HG is unchanged, GA1 improves, and its circle does not increase.
No original radial-boundary status of G is required.

## 3. Bounds for the aligned primary/hard chain

Cancel G and T in the retained neighboring inequalities:
\[
\begin{aligned}
a_A-\tfrac12&\ge(\tfrac32-b_H)\cos t+K\sin t,\\
b_A+b_B&\ge1,\\
a_B\cos u-b_B\sin u+b_D&\ge1+W(u).
\end{aligned}
\tag{8}
\]
All sorted circles give \(b_i<.9\), \(a_i<1.415\).
The first line implies \(a_A\ge2-b_H>1.1\):
for \(D=\tfrac32-b_H<3/2\),
\[
K\sin t-D(1-\cos t)
=\sin t\{K-D\tan(t/2)\}\ge0
\]
because \(\tan(t/2)<3/8\). The B composite gives the same
primary bound. Their actual circles and AB now imply
\[
a_A,a_B>1.1,\quad .335<b_A,b_B<.665,\quad a_A,a_B<1.294,
\quad b_H,b_D>.706,\quad a_H,a_D<1.1.
\tag{9}
\]
The relevant square reserves are
\[
(1.165)^2-(Q-1.6^2)=\frac{13}{8000},\qquad
(1.794)^2-\{Q-(.835)^2\}=\frac{61}{10^6}.
\]
The endpoint tangent bound follows from \(b_H+a_A\ge2\)
and its B counterpart. A primary at least 1.1 and tangent
greater than .7 would have corner square greater than 4.

We next prove
\[
\alpha=t+u<\frac{11}{50}.
\tag{10}
\]
Set
\[
C(x)=1+\tfrac35\cos x+K\sin x,\qquad
P(x)=\sqrt{Q-C(x)^2},
\]
\[
L(x)=\cos x\sqrt{Q-(3/5+\cos x)^2}
                 -\sin x(3/5+\cos x).
\tag{11}
\]
The actual transverse corners satisfy \(Y_A\le P(t)\),
\(Y_B\le L(u)\). Both caps decrease on their feasible domains.
Since \(Y_A>.835\), one has \(t<1/5\): at \(x=1/5\),
\[
1+\tfrac35(1-x^2/2)+K(x-x^3/6)-1.794
=\frac{83}{9000}>0.
\tag{12}
\]

On \(0\le x\le1/5\) the entire primary cap satisfies
\[
P''(x)<-\frac75,\qquad P(0)<1.165,\qquad -P'(0)>1.487.
\tag{13}
\]
Here is an exact proof of its curvature. Put
\(M=(3/5)^2+K^2\), \(w=\sqrt{Q-C^2}\).
The identity \((C-1)^2+(C')^2=M\) gives
\[
P''=\frac{N(C)}{w^3},\qquad
N(C)=C(C-1)(Q-C^2)-Q\{M-(C-1)^2\},
\]
\[
N'(C)=(4C-3)(Q-C^2)>0.
\]
Thus \(N(C)\le N(\sqrt Q)=-Q\{M-(\sqrt Q-1)^2\}\).
Use \(\sqrt Q<1.979\), \(w<1.165\), and
\[
Q\{M-(.979)^2\}-\frac75(1.165)^3
=\frac{577531681}{15000000000}>0.
\]
The derivative bound in (13) follows from
\((26/15)/(233/200)-1487/1000=587/699000>0\).

The hard cap L is convex by
[the full feasible cap lemma](HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md),
and
\[
L(0)<1.165,\qquad L(11/50)<.825.
\tag{14}
\]
For a rational verification put \(r=11/50\),
\(c_-=1-r^2/2+r^4/24-r^6/720\),
\(c_+=1-r^2/2+r^4/24\), \(s_-=r-r^3/6\). Then
\[
\begin{aligned}
(1.197)^2-\{Q-(.6+c_-)^2\}
&=\frac{83755313462694863226721}
 {126562500000000000000000000}>0,\\
.825-\{1.197c_+-s_-(.6+c_-)\}
&=\frac{6339186306307691}{8437500000000000000}>0.
\end{aligned}
\]
If \(\alpha\ge11/50\), then \(u\ge11/50-t\).
The convex chord for L and (13) give
\[
\begin{aligned}
2\le Y_A+Y_B
&\le P(t)+L(11/50-t)\\
&<1.99+(\tfrac{17}{11}-1.487)t-\tfrac7{10}t^2\\
&<1.99+\tfrac3{50}t-\tfrac7{10}t^2\\
&\le1.99+\frac{(3/50)^2}{14/5}
=2-\frac{61}{7000},
\end{aligned}
\]
a contradiction. This proves (10).

We also need the endpoint-primary sum
\[
a_H+a_D<1.998-.718\sin\alpha<2.
\tag{15}
\]
Indeed the first line of (8) has \(D<.794\), \(t<.2\),
so \(b_H+a_A>2+\sin t\), since
\(\tan(.1)<.101\) and \(K-(.794)(.101)>1\).
The B composite gives \(b_D+a_B>2+.835\sin u\).
The common A/B circle bound therefore yields
\[
b_H+b_D>5-2\sqrt{Q-1}+.835\sin\alpha.
\]
Use \(\sqrt{Q-1}<1.708\) and the tangent line at zero of
\(2\sqrt{Q-(1.292+.4175z)^2}-1\), with \(z=\sin\alpha\).
The needed bounds are
\[
\sqrt{Q-(1.292)^2}<1.499,\qquad
\frac{.835(1.292)}{1.499}>.718.
\]
Their positive reserves are \(665/10^6\) after squaring
and a direct positive rational comparison, respectively.

## 4. The E alternative supplies an actual EH1 witness

A core E is impossible. The four exact core-demand comparisons
in Section 3 of
[the aligned mixed-owner theorem](HAND_G5_ALIGNED_CHAIN_ALL_MIXED_OWNERS_SHARP_REDUCTION.md)
use only (4), true-core bounds and the common coordinate bounds.
For either sign of each error they give
\(a_H+a_D\ge2-\sin(\alpha/2)\). This contradicts (15), because
\[
2-\sin(\alpha/2)-\{1.998-.718\sin\alpha\}
=.002+\{1.436\cos(\alpha/2)-1\}\sin(\alpha/2)>0.
\]
Thus the second alternative in (3) holds. By (7),
\(\epsilon>0\), and the exact difference
\[
P_{EH1}-P_{EH0}
=(a_H+b_E)(1-\cos\epsilon)+(a_E-b_H)\sin\epsilon\ge0
\tag{16}
\]
supplies EH1. If \(\delta\ge0\), the analogous DE comparison
supplies DE3; its exact formula and sorting argument are
Section 4 of the same cited note. If \(\delta<0\), retain
its original DE owner for now.

## 5. A whole-domain H-circle rate while GA0 is unavailable

Hold A fixed and vary its positive GA tilt x. Put
\[
P_A=a_A-\tfrac12,\quad
D(x)=P_A\sec x-K\tan x,\quad
b_H(x)=\tfrac32-D(x).
\tag{17}
\]
These are the aligned HG and GA1 contact equations for
\[
a_G=\frac7{12},\qquad b_G=D(x)-\frac12.
\tag{18}
\]
Their derivatives are
\[
D'=D\tan x-K,\qquad b_H'=K-D\tan x.
\tag{19}
\]
While GA0 is unavailable, its contact difference is
\[
P_{GA0}-W(x)
=\sin x\{K\cos x-D(x)\sin x-Y_A\}.
\]
Consequently A's actual circle gives the intrinsic bound
\[
\mathcal R(D,x):=1+D^2+K^2+2D\cos x+2K\sin x<Q.
\tag{20}
\]
As H's tangent is never increased, \(D>3/5\). Moreover
\[
D<d_*:=\sqrt{Q-K^2}-1<\frac{82}{125},\qquad x<.09.
\tag{21}
\]
For the first bound compare (20) to x=0; its x derivative
is \(2(K\cos x-D\sin x)>0\). For the second, monotonicity
in D and the lower Taylor bound give
\(\mathcal R(3/5,.09)-Q>283963/36000000>0\).

Let \(q_H\le q\) be H's own retained circle ceiling, and
put H on this circle as its tangent decreases. Its primary
gain per unit decrease of x has magnitude
\[
\mathcal A(D,x)=
\frac{(2-D)(K-D\tan x)}{\sqrt{q_H-(2-D)^2}}>1.
\tag{22}
\]
To prove the strict estimate, it suffices to show
\(F(D,x):=(2-D)^2\{1+(K-D\tan x)^2\}>Q\).
For fixed D, F decreases with x. Its minimum is therefore
on the intrinsic upper curve \(\mathcal R(D,x)=Q\), where
\[
\frac{dx}{dD}=-\frac{D+\cos x}{K\cos x-D\sin x}.
\]
Throughout that curve,
\[
\begin{gathered}
\tfrac{168}{125}<2-D<\tfrac75,\quad
1<K-D\tan x\le K,\quad K\cos x-D\sin x>1,\\
\sec^2x<\tfrac{101}{100},\qquad D+\cos x<\tfrac{83}{50}.
\end{gathered}
\tag{23}
\]
Use \(\tan(.09)<.091\). Two explicit reserves are
\[
K(1-.09^2/2)-\tfrac23(.09)-1=\frac{4547}{240000},
\quad
(1-.09^2/2)^2-\frac{100}{101}
=\frac{73422661}{40400000000}.
\]
Differentiating F along the curve, and discarding negative
terms, now gives
\[
\frac d{dD}F(D,x(D))
<-4\frac{168}{125}
+2(\tfrac75)^2K\frac23\frac{101}{100}\frac{83}{50}
=-\frac{708029}{1125000}<0.
\]
Its least value is at \(D=d_*,x=0\), where
\[
F(d_*,0)>
(\tfrac{168}{125})^2(1+K^2)
=Q+\frac{667}{62500}>Q.
\tag{24}
\]
This proves (22) without dividing the angle domain.

## 6. E not below D: move H and G to an actual hard witness

Assume \(\delta\ge0\). Then \(0<\epsilon<.22\).
At x=t, (8) gives \(b_H\ge b_H(t)\) in (17).
Lower H's tangent to that contact value along its own actual
circle, and use (18). H's primary increases, EH1 is preserved,
and HG and GA1 become equalities. G's new tangent is at least
its previous one, so GA0 remains unavailable. Its new flat-core
corner is below \(q_L\), by \(K^2+(82/125)^2<q_L\).

Decrease x, moving the aligned H/G frame toward the fixed A/B
frame with H on that same circle and G given by (18).
All other points and frames stay fixed. Stop at the first
actual GA0 witness, or at x=0, where GA0 and GA1 coincide.
Before the stop, (20)--(22) apply, and
\[
b_H>.844,\qquad a_H<1.
\tag{25}
\]
All changing frames stay in their original convex hull.

At a possible EH1 boundary put
\(P_H=a_H-\tfrac12>.344\),
\(X_E=a_E+\tfrac12\), \(Y_E=b_E+\tfrac12\).
Contact gives
\[
-X_E\sin\epsilon+Y_E\cos\epsilon=P_H-\sin\epsilon.
\]
The competing angular derivative is
\[
\mathcal U_E
=(a_E-\tfrac12)\cos\epsilon+(b_E+\tfrac12)\sin\epsilon
=X_E\cos\epsilon+Y_E\sin\epsilon-\cos\epsilon.
\]
The actual E circle therefore gives
\[
\mathcal U_E
\le\sqrt{Q-(P_H-\sin\epsilon)^2}-\cos\epsilon
<\sqrt{Q-(.344-.22)^2}-(1-.22^2/2)<1.
\tag{26}
\]
The final square reserve is
\[
(2-.22^2/2)^2-\{Q-(.344-.22)^2\}
=\frac{89041}{25000000}>0.
\]
Sorting and (25) supply \(P_H>.344\). This is an
active-contact bound, not an unrestricted E-circle bound.

At every possible first boundary of EH1 feasibility its
x-derivative is \(-\mathcal A+\mathcal U_E<0\).
Decreasing x therefore cannot lose EH1; after any positive
movement its margin is strict. The path cannot meet
\(\epsilon=0\) while GA0 is unavailable, since EH1 would
require \(a_H-b_E\ge1\), contradicting (25).
No derivative across the width cusp is used.

The stop is reached with positive movement. Lower H's primary
by a sufficiently small amount. Strict EH1 slack permits it;
aligned HG depends only on H's tangent. Sorting is strict
after the positive tangent decrease, and the true exclusion
is strict since \(b_H>.844\). This records strict H-circle
loss while A and B remain unchanged.

The descendant has actual GA0 and BT2, all normal signs,
retained zero and mixed witnesses, true-core constraints,
and the original span ceiling. The E alternative (3) persists,
since H's tangent decreased. The normal hard-owner theorem
gives \(q\ge q_*\); its equality conclusion excludes this
strict H loss at \(q=q_*\).

## 7. A primary E below D reaches D or a zero-tangent boundary

Suppose \(\delta<0\), with EH1 available by Section 4.
First suppose DE3 is available. Keep H,A,B,D and their frames
fixed, and minimize E's corner over
\(\delta_{\rm old}\le\delta\le0\) with the two primary mixed
inequalities. The outside-E calculation in Section 3 of
[the E-order note](HAND_G5_E_ORDER_FROM_ALIGNED_NON_E_CHAIN.md)
uses only \(\alpha<.22\), \(a_H+a_D<2-.718\sin\alpha\),
sorting and these two inequalities. Equation (15) supplies
its inputs, so every feasible outside state satisfies
\[
a_E>\frac{1.15082}{1.11}>1.
\tag{27}
\]
Sorting and true central exclusion are strict throughout
the outside portion of this compact relaxation.

A minimizer with \(\delta<0,b_E>0\) cannot have only one active
mixed contact: a primary or tangent contraction lowers its
corner. With two active contacts, the exact derivative in
Section 4 of the cited note is
\[
\frac{q_E'}2
=-\frac{A\sin\delta+B\cos\epsilon}{\sin\alpha}<0
\]
as E moves toward D. Its positivity proof uses only
\(a_E>b_E\), the actual frame spread and \(\alpha>0\).
Thus a minimum is at \(\delta=0\) or at
\(b_E=0,\delta<0\). No hard-owner endpoint theorem from
that note is invoked here.

At \(\delta=0\), raise E's primary to its q-circle value.
DE3 is independent of that primary and EH1 improves because
\(\epsilon=\alpha>0\). E is outer, hence (3) holds, and
Section 6 applies with H,A,B,D unchanged.

At the other boundary write \(\delta=-z<0,b_E=0\).
Equation (27) gives \(a_E>1\), and DE3 gives
\[
a_D\ge\tfrac12+\tfrac12\cos z+(a_E+\tfrac12)\sin z.
\]
Together with \(a_D<1.1\), this forces \(z<2/25\):
the lower Taylor bound at \(2/25\), with \(a_E>1\),
already exceeds 1.1. Actual DE2 is now strictly feasible:
\[
\begin{aligned}
a_D\cos z-b_D\sin z-W(z)
&\ge\sin z\{a_E\cos z-b_D-W(z)\tan(z/2)\}\\
&>\sin z\{.9968-.9-(1.04)(.041)\}\\
&=\frac{677}{12500}\sin z>0.
\end{aligned}
\tag{28}
\]
Here \(\tan(.04)<.041\) and \(W(z)<1.04\).
Raise E's primary to \(a_0(q)=\sqrt{q-1/4}-1/2\);
DE2 is unaffected and EH1 improves. This is the
zero-tangent boundary treated next.

## 8. A rotated E below D uses the DE2 contact descent

If DE2 was the original retained witness, use the contact
curve from Section 6 of
[the aligned mixed-owner theorem](HAND_G5_ALIGNED_CHAIN_ALL_MIXED_OWNERS_SHARP_REDUCTION.md):
\[
b(z)=\tfrac12-(a_D-\tfrac12)\cos z
                    +(b_D+\tfrac12)\sin z,\qquad \delta=-z.
\tag{29}
\]
At the original frame lower E's tangent on its q-circle to
\(\max\{0,b(z)\}\). DE2 stays feasible and EH1 improves.
Then decrease z until \(z=0\) or \(b(z)=0\).
The exact proof in that section uses only
\(\alpha<.22\), \(b_D>.706\), \(a_D<1.1\), \(q\le Q\),
and \(\alpha+z\le.7\), all proved here. In its notation,
\[
\frac{J'(z)}{\cos(\alpha+z)}
<-\frac{19}{75000}-\frac z{250}-\frac{16z^2}{15}<0.
\tag{30}
\]
Thus EH1 strictly improves. The q-circle path stays outside
the true core and sorted; a diagonal E is also immediately
incompatible with EH1 and \(a_H<1\), since
\(\sin\epsilon<\cos\epsilon\).
At \(z=0\), DE3 is available, E is outer, and Section 6 applies.

At zero tangent with \(z>0\), including the boundary from
Section 7, the retained DE2 condition is
\[
(a_D-\tfrac12)\cos z-(b_D+\tfrac12)\sin z\ge\tfrac12.
\tag{31}
\]
It forces \(a_D>1\). Section 7 of the same cited note
performs a D/T move using only (31), \(a_B>1.1\),
\(b_D>.706\), \(q_L\le q\le Q\), and the BT2 composite.
None of these inputs uses the GA owner. For clarity, put
\[
Y_D=b_D+\tfrac12,\qquad Y_0=\sqrt{q-\tfrac94}.
\]
The published positive-cap rate gives
\(z<2/25\) and \(Y_0-Y_D>(7/5)z\).
Move D down to E's frame and set
\[
a_D'=1,\quad b_D'=Y_0-\tfrac12,\qquad
a_T'=\tfrac7{12},\quad b_T'=1-b_D',\quad
\theta_T'=\theta_D'.
\]
The new T is true core with corner below \(q_L\).
B's actual circle and \(a_B>1.1\) give the derivative bound
\[
\left|\frac d{ds}\{(a_B-\tfrac12)\cos s
                   -(b_B+\tfrac12)\sin s\}\right|<\frac43.
\]
Hence its new BT2 composite, at \(u+z\), has strict reserve
greater than \(z/15\). A small decrease of B's primary retains
its tangent, AB, sorting and true exclusion and records a
strict B loss.

H,A,G,E and their frames were fixed. All new frames lie
within the old H/E interval. The three zero edges remain
aligned and ordered, E agrees with D, and DE3 is an equality.
The new total span is at most .7; Section 3 applies afresh
to give \(<.22\). E is outer and its primary exceeds both
endpoint tangents. Every input of Section 6 is now present,
so that section finishes the GA0 conversion with strict H loss.

## 9. Completion and original equality bookkeeping

If GA0 was available initially, apply the normal hard-owner
theorem to the original system. Otherwise Sections 2--4
give the uniform cuts and actual EH1. Section 6 handles
E not below D; Sections 7--8 move E, or E and the aligned
D/T pair at a zero-tangent boundary, until Section 6 applies.

Every construction preserves the actual shared neighboring
inequalities and frame-span ceiling. A and B are unchanged
apart from the explicit optional B contraction, so earlier
strict losses remain. Every genuinely unconverted case
ends with positive H/G movement and strict H-circle loss.
The normal hard-owner theorem then gives \(q\ge q_*\),
and its equality conclusion rules out \(q=q_*\).
No reconstructed H, D or E is identified with its predecessor.

The theorem removes negative GA1 from the stated aligned,
ordered GA1/BT2 class, including both mixed-owner choices,
arbitrary E placement and (3). Arbitrary original zero
alignment, non-E order, positive GA1 error and a simultaneous
BT3 alternative remain outside this theorem's scope.

All numerical constants are exact rationals. The proof uses
analytic cap curvature, one intrinsic boundary-curve derivative,
and exact Taylor reserves. No state or angle mesh, numerical
optimizer premise, Lean compilation or CI result is used.
