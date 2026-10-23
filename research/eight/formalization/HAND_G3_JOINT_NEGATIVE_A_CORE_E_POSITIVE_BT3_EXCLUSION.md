# Joint negative A and core E with positive BT3 and actual TD0

## 1. Exact coefficient input and geometric scope

Put \(Q=9789/2500\), \(R=\sqrt Q\), \(h=.7\), and
\(K=13/12\). All decimals denote exact rational numbers.
This note gives the whole-angle reduction for the four
one-negative-A, one-negative-E systems of Section 1 of
[the joint-negative TD2 theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_TD2_EXCLUSION.md),
now with **BT3 at error \(z>0\) and actual TD0 at an arbitrary
error**. H,G,B,D remain sorted outer states with signs
positive, negative, negative, negative; A,E are flat core;
T has arbitrary sign and radial kind. Either HG0 or HG2 is
allowed. All remaining errors have arbitrary signs, and
both total variations are less than h.

For each fixed z the proof uses positive weights k,m,c and
\(\eta\ge0\), satisfying
\[
 c=m(\cos z+\eta\sin z),\qquad
 .65\le k\le .751,\qquad k\le m\le c,\qquad .7\le c\le1.4,
\tag{1}
\]
\[
 c\ge1\ \Longrightarrow\ z\le .3\text{ and }k\le .6692,
 \qquad z\ge .15\ \Longrightarrow\ c\le1.2.
\tag{2}
\]
Define
\[
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\qquad
 C_z=1+2\cos z+(.5+1.5\eta-\sigma)\sin z,
\]
\[
 D(c)=\begin{cases}(1+c)/\sqrt2,&c\ge1,\\
                    \sqrt{1+c^2},&c\le1,
       \end{cases}
\]
\[
 \mathcal B_0(z)=2k+6+mC_z
       -R\{2\sqrt{1+k^2}+\sqrt{1+m^2}+D(c)\}.
\tag{3}
\]
The scalar input consists of precisely
\[
              \mathcal B_0(z)+V_{k,1}(z)>0,
              \qquad \mathcal B_0(z)+F_k(z)>0.
\tag{4}
\]
Here F,V are the functions from
[the common-gain theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_COMMON_GAIN.md).
The scalar companion
[for positive BT3](HAND_G3_JOINT_NEGATIVE_A_CORE_E_POSITIVE_BT3_SCALAR_CERTIFICATES.md)
is the input for (1)--(4). The argument below is a general
implication from these explicit scalar hypotheses; it does
not differentiate the weight family or its tilt.

**Concentration conclusion.** Under (1)--(4), every one of
the four one-primary systems is impossible. The varying
secant at D is included throughout, even when its negative
E angle is arbitrarily close to h.

## 2. The weighted baseline

Let the negative A and E primary errors be \(-r\) and
\(-s\), with \(S=r+s\le h\). The actual entry bounds are
\(r<.25\) for GA3, \(r<.38\) for AB2, and \(s<.25\)
for EH1; a negative DE3 needs only \(s<h\).

Use weight \(\sec r\) on the A primary, \(\sec s\) on the
E primary, weight 1 on their other actual edges, and
\[
                              HG:k,\qquad BT:m,\qquad TD:c.
\tag{5}
\]
The secants cancel the two flat-core tangents exactly, as
in Section 2 of the joint-negative TD2 theorem. The only
changed core calculation is T:
\[
 m\sin z\,a_T+(c-m\cos z)y_T
      =m\sin z(a_T+\eta y_T)\le m\sigma\sin z.
\tag{6}
\]
Thus the zero-negative-angle baseline is exactly (3).
The A gain is \(F_k(r)\) for GA3 and \(F_m(r)\ge F_k(r)\)
for AB2. The E gain is \(F_k(s)\) for EH1 and the exact
sorted-D secant gain \(L_c(s)\ge F_k(s)\) for DE3. The
last comparison uses only \(c\ge k\); its full and diagonal
branches are proved in Section 2 of the TD2 theorem.
All four systems therefore have the common lower baseline
\[
                          \mathcal B_0(z)+F_k(r)+F_k(s).
\tag{7}
\]

The ordinary H,G,B pairs are exactly those in that theorem:
\((k,\lambda_H)\), \((k,\lambda_G)\), and the ordered
\((m,\lambda_B)\), where each \(\lambda\) is 1 or its
incident negative-primary secant. The actual-primary cuts
give \(\lambda_G,\lambda_H,\lambda_B<1.078\). Their
ratios are at least 1/2, and their larger-to-smaller ratios
are less than 1.7. For B with m the larger coefficient,
use \(m\le1.4\) and \(\lambda_B\ge1\); otherwise use
\(m\ge k\ge.65\).

## 3. The exact D block in both E alternatives

If E retains DE3, put \(q=\sec s\). The remaining TD0
argument t has the exact increment
\[
 \Delta(q,c;t)=c\{W(t)-1\}+S(q,c)
                         -S(q+c\sin t,c\cos t).
\tag{8}
\]
Here S denotes the sorted outer-circle support. Section 1 of
[the secant-D single-angle comparison](HAND_G3_SECANT_D_SINGLE_ANGLE_COMPARISON.md)
applies on the ranges (1), \(1\le q\le\sec h<1.308\), and
gives
\[
 \Delta(q,c;t)\ge
 \begin{cases}
 -.545\max(q,c)t,&t\ge0,\\
 V_{k,1}(-t),&t\le0.
 \end{cases}
\tag{9}
\]
This retains the exact sorted support at zero and includes
all of its intrinsic support transitions.

If E retains EH1, both TD0 and DE2 remain at D. For \(c<1\)
the zero support \(S(1,c)\) is the full-circle value,
because \(.7\le c\le1\). Its ordinary pair is \((c,1)\),
so the usual U,V,\(\Psi\) concentration applies. Its pure
negative term dominates \(V_{k,1}\), by monotonicity in
the smaller coefficient.

For \(c\ge1\), (2) gives \(k\le .6692\). The enlarged
[two-angle sorted-D envelope](HAND_G3_SORTED_D_TWO_ANGLE_ENVELOPE_TO_SEVEN_FIFTHS.md)
supplies the separately concave lower block
\[
                             -.65P_D+V_{k,1}(N_D).
\tag{10}
\]
It is valid for every signed allocation at D and every
\(1\le c\le1.4\). The zero support is still the exact
diagonal value \((1+c)c_0\).

Introduce the following positive cost, with z and hence c
held fixed:
\[
 \Lambda_z(S)=
 \begin{cases}
 .545\sec S,&c<1,\\
 \max\{.65,.545c,.545\sec S\},&c\ge1.
 \end{cases}
\tag{11}
\]
At c=1 use the second branch. Every ordinary larger coefficient is at
most \(\max(c,\sec S)\), because \(m\le c\) and each
incident negative angle is at most S. Equations (9)--(10)
and the universal \(U_{p,q}(t)\ge-.545qt\) therefore show
that every positive alternative is at least
\(-\Lambda_z(S)t\). Uniformly,
\[
                         \Lambda_z(S)\le .763<.9.
\tag{12}
\]
For fixed z, \(\Lambda_z\) is increasing and convex in S.
As a function of \(x=\tan S\), it is the maximum of
constants and \(.545\sqrt{1+x^2}\), and is again convex.

## 4. Complete angle concentration and canonical negative blocks

Deleting \(-r,-s,z\) leaves
\[
              P\le h-z,\qquad N\le h-S,\qquad N-P=z-S.
\tag{13}
\]
Separate concavity gives the same intrinsic alternatives
as in Section 3 of the joint-negative TD2 theorem: pure
positive or negative terms, ordinary same-block terms,
and separated terms at \(P=h-z,N=h-S\). The sorted D
block (10) is already separated; a singleton from (9) may
be enlarged to the same form. This does not introduce an
extra ordinary D same-block term.

Every negative term dominates one of
\[
                       V_{k,1}(d),\quad V_{k,\sec r}(d),
                                      \quad V_{k,\sec s}(d).
\tag{14}
\]
For H,G this is immediate. For B, use exactly the two
comparisons from Section 4 of the TD2 theorem: when
\(m\le\lambda_B\), increase the smaller coefficient from
k to m; when \(m\ge\lambda_B\), the universal endpoint
chord gives \(V_B(d)\ge(87/70)\lambda_Bd\), while the
canonical tangent is below \(1.19\lambda_Bd\).
For D use (9), (10), or the \((c,1)\) comparison above.

Ordinary same-block terms reduce to pure terms. The
comparison \(\Psi(P,N)\ge V(N-P)\) for \(P\le N\)
requires \((q/p)\sin N\le1\). For an incident secant
\(\sec\xi\), it follows from
\[
       \sec\xi\sin(h-S)\le\sin h<.645<k.
\]
When B has larger coefficient m, use
\(m\sin h\le1.4(.645)<1\). For the ordinary D pair
\((c,1)\), use \(\sin h<c\). The other same-block
comparison, \(\Psi(P,N)\ge U(P-N)\) for \(N\le P\),
requires only \(q/p\le1.7\), already checked in Section 2.

For a pure positive term, (12), the common-gain
subadditivity, and \(F'_k>.9\) give
\[
 \mathcal B_0+F_k(r)+F_k(s)-\Lambda_z(S)(S-z)
                   \ge\mathcal B_0+F_k(z)>0
                         \qquad(S\ge z).
\tag{15}
\]
For a pure negative term, the common-gain allocation lemma
and (14) reduce the value to
\[
 \mathcal B_0+F_k(S)
           +\min\{V_{k,1}(z-S),V_{k,\sec S}(z-S)\}.
\tag{16}
\]
Its minimum is at S=0 or S=z, so (4) excludes it.
For \(z\ge.15\) this is the stated common-gain endpoint
lemma. For \(z\le.15\) its proof applies to every k in
(1): Section 4 of that note proves \(F''_k<0\) on this
small interval for all such k, and the unaffected V is
concave. The affected V is always strictly concave after
the substitution \(x=\tan S\).

Thus only separated positive and negative terms remain.

## 5. The endpoint lemma with an increasing convex penalty

We record precisely the extension needed for those terms.
Fix \(t=h\), k in (1), and \(P\ge0\), and put
\(g(S)=P\Lambda_z(S)\) for \(0\le S\le h\). Then
\[
 \begin{split}
 &F_k(S)+\min\{V_{k,1}(h-S),V_{k,\sec S}(h-S)\}-g(S)\\
 &\hspace{10mm}\ge
   \min\{V_{k,1}(h)-g(0),F_k(h)-g(h)\}.
 \end{split}
\tag{17}
\]
For the affected term, the exact substitution \(x=\tan S\)
leaves, up to a constant,
\[
 (K+\sin h)x
       -R\sqrt{(x+k\cos h)^2+(1-k\sin h)^2}.
\]
This is concave, and \(g(\arctan x)\) is convex by the
last observation after (12). Their difference is concave,
so its minimum is at an endpoint.

For the unaffected term let
\(f(S)=F_k(S)+V_{k,1}(h-S)\). The common-gain theorem
proves \(f'''(S)>.788\) and \(f'(h)<0\). Thus \(f'\)
is convex. At any interior point where \(f'(S)\ge0\), its
derivative satisfies the strict secant-to-right bound
\[
                     f''(S)\le\frac{f'(h)-f'(S)}{h-S}<0.
\tag{18}
\]
On each smooth part of g, we have \(g'\ge0,g''\ge0\).
Where \((f-g)'\ge0\), necessarily \(f'\ge g'\ge0\),
and hence \((f-g)''<0\) by (18). Its derivative therefore
cannot cross from nonpositive to positive. At a corner of
g its derivative can only jump down, since g is convex.
Thus \(f-g\) also has its minimum at an endpoint. The
one-sided endpoint values agree across every corner, proving
(17) on the whole interval.

## 6. The separated alternatives are strictly positive

Put \(P=h-z\). The common-gain allocation lemma, applied
at \(d=h-S\), and the cost (11) bound any separated
alternative below by
\[
 \mathcal B_0+F_k(S)
 +\min\{V_{k,1}(h-S),V_{k,\sec S}(h-S)\}
                              -P\Lambda_z(S).
\tag{19}
\]
At fixed S the cost is independent of the allocation of
r and s, so the allocation lemma applies directly.
Equation (17) leaves only
\[
 \mathcal B_0+F_k(h)-P\Lambda_z(h),\qquad
 \mathcal B_0+V_{k,1}(h)-P\Lambda_z(0).
\tag{20}
\]
The first is positive by (12), \(F'_k>.9\), and the second
scalar inequality in (4).

For the second, use the following elementary chord bounds:
\[
 V_{k,1}(h)-V_{k,1}(z)>
 \begin{cases}
 .8(h-z),&0\le z\le .15,\\
 .75(h-z),&0\le z\le .3,\\
 .64(h-z),&0\le z\le h.
 \end{cases}
\tag{21}
\]
At z=h read the last bound as equality zero. The last line
follows from \(V'_{.65,1}(h)>.64\), concavity in its
argument, and the positive derivative
\[
 \partial_kV'_{k,1}(d)
       =\frac{R\cos d(1-k\sin d)}
                    {(1+k^2-2k\sin d)^{3/2}}>0.
\]
The first line is proved in Section 7 of the joint-negative
TD2 theorem. For the middle line, its same bounds give
\(V_{.65,1}(h)>.611\), while direct rational bounds give
\[
 \begin{split}
 V_{.65,1}(.3)
 &<.9554-1+1.9788(1.1927-1.0189)\\
 &=.29931544<.3.
 \end{split}
\tag{22}
\]
Here \(\cos(.3)<.9554\), \(\sin(.3)<.2956\),
\(\sqrt{1+.65^2}<1.1927\), and
\(\sqrt{1+.65^2-1.3\sin(.3)}>1.0189\); the latter two
follow by squaring. Concavity therefore bounds the chord
from every \(z\le .3\) below by
\((.611-.3)/.4>.75\). Monotonicity of \(V'\) in k extends
both chord bounds to every k in (1).

If \(c<1\), then \(\Lambda_z(0)=.545<.64\).
If \(c\ge1\) and \(z\le .15\), then
\(\Lambda_z(0)\le.763<.8\). In the remaining case,
(2) gives \(z\le .3,c\le1.2\), so
\(\Lambda_z(0)\le.654<.75\). Thus in every case the
second expression in (20) is at least
\(\mathcal B_0+V_{k,1}(z)>0\), by (4).

All concentrated alternatives are positive, contradicting
the weighted necessary inequalities. This proves the
concentration conclusion of Section 1, with every negative
angle split and every support transition included.

## 7. Joining arbitrary negative A and E totals

The local negative-A transports and the mixed-negative and
paired-negative E transports used in Section 8 of the TD2
theorem do not depend on which T owner is retained. They
therefore apply here with the actual BT3 and TD0 witnesses
unchanged. They preserve all four outer anchors and both
variation bounds. Genuine negative-primary entry gives the
flat sides and cuts stated in Section 2; a zero E endpoint
is excluded by the retained high-GA reflection theorem.

Every descendant whose two selected primary totals remain
negative reaches one of the four one-primary systems just
excluded. A same-state secondary reselection that makes
one total nonnegative belongs to the corresponding
nonnegative-total branch: if E becomes nonnegative while A
remains negative, use
[the positive-BT negative-A theorem with nonnegative E](HAND_G3_NEGATIVE_A_POSITIVE_BT3_WITH_NONNEGATIVE_E_TOTAL_EXCLUSION.md).
If A becomes nonnegative while E remains negative, first
finish the E-only transport and use the
[negative-DE theorem with nonnegative A](HAND_G3_NEGATIVE_DE3_POSITIVE_BT3_WITH_NONNEGATIVE_A_TOTAL_EXCLUSION.md)
or the
[negative-EH theorem with nonnegative A](HAND_G3_NEGATIVE_EH1_POSITIVE_BT3_WITH_NONNEGATIVE_A_TOTAL_EXCLUSION.md).
If both totals become nonnegative, use
[the positive-BT theorem with both totals nonnegative](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
All these reselections concern actual feasible projections
at the current state. No frame order, nonneighbor packing
assumption, or additional marker hypothesis is introduced.
