# Joint negative A and core E are impossible with BT2 and positive TD2

## 1. The full remaining BT2 scope

Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=.7,
 \qquad K=\frac{13}{12}.
\tag{1}
\]
Work with the actual G0--G2 boundary-neighbor cycle, or a
necessary descendant covered by
[the boundary-neighbor transport theorem](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
H,G,B,D are sorted outer Q states, with tangent signs
positive, negative, negative, negative. Retain BT2, TD2 at
error \(z>0\), and either actual HG owner 0 or 2. Every
other error may have either sign; the whole positive and
negative variations are each less than h.

**Theorem.** Such a system is impossible if its selected
A-primary total is negative and its selected E-primary total
is negative, with E on the true core. Both A and E may
initially retain two primaries. T has arbitrary sign and
radial kind. No order of the real frames is assumed.

The proof first treats the following four actual one-primary
systems, then gives the finite transport join in Section 8:

| A primary and actual secondary | E primary and actual secondary |
|---|---|
| GA3 at \(-r\), AB0 | DE3 at \(-s\), EH0 |
| GA3 at \(-r\), AB0 | EH1 at \(-s\), DE2 |
| AB2 at \(-r\), GA2 | DE3 at \(-s\), EH0 |
| AB2 at \(-r\), GA2 | EH1 at \(-s\), DE2 |

At this stage A and E are flat core, so
\(a_A=a_E=7/12\). The genuine-primary entry bounds are
\[
 \begin{array}{ll}
 0\le r<.25&\text{for GA3},\\
 0\le r<.38&\text{for AB2},\\
 0\le s<.25&\text{for EH1},\\
 0\le s<h&\text{for DE3},
 \end{array}
 \qquad r+s<h.
\tag{2}
\]
Allowing zero endpoints only enlarges this scalar domain.
All decimals in this note denote exact rationals.

The two analytic ingredients proved separately are
[the common-gain theorem](HAND_G3_JOINT_NEGATIVE_A_CORE_E_COMMON_GAIN.md)
and [the scalar certificates](HAND_G3_JOINT_NEGATIVE_A_CORE_E_SCALAR_CERTIFICATES.md).
Their certificates are explicit rational polynomial identities
and coefficient-norm bounds on whole intervals.

## 2. One common scale cancels both core tangents

Take the coefficient families k,c from (4)--(5) of the scalar
certificate note, set \(\eta=.303\), and put
\[
 m=c(\cos z+\eta\sin z),\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\qquad
 W(t)=\frac{1+\cos t+\sin t}{2}\quad(0\le t\le h).
\tag{3}
\]
Give both nonprimary A/E edges weight 1. Give the negative
A primary weight \(\sec r\) and the negative E primary
weight \(\sec s\). The remaining weights are
\[
                         HG:k,\qquad BT:m,\qquad TD:c.
\tag{4}
\]
Every weight multiplies the retained actual witness.

For negative GA3 the A contribution is
\(-a_A\tan r-y_A\); for negative AB2 it is
\(-a_A\tan r+y_A\). The opposite A edge cancels the signed
tangent exactly. At E the same calculation cancels its
signed tangent and leaves \(-a_E\tan s\). The T force is
\[
 c\sin z\,a_T+(c\cos z-m)y_T
      =c\sin z(a_T-\eta y_T)\le c\sigma\sin z.
\tag{5}
\]
The bound follows from the actual shifted corner in the
radius-R disk and holds for either T sign and radial kind.

Write
\[
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2}
\]
for the complete-circle support, and retain the sorted D
support. At zero remaining angular arguments the H,G,B
coefficient pairs are respectively
\[
 (\lambda_H,k),\quad(\lambda_G,k),\quad(m,\lambda_B),
\tag{6}
\]
where \(\lambda_G=\sec r\) in the GA case and 1 otherwise,
\(\lambda_B=\sec r\) in the AB case and 1 otherwise,
and \(\lambda_H=\sec s\) in the EH case and 1 otherwise.
The D pair is \((\lambda_D,c)\), with \(\lambda_D=\sec s\)
in the DE case and 1 otherwise.

Let \(B_0(z)\) be (2) of the scalar certificate note. It is
the exact zero-negative-angle baseline after the corner
half-shifts have been collected. In particular, its sorted-D
term is \(D(c)=(1+c)/\sqrt2\) for \(c\ge1\), and
\(D(c)=\sqrt{1+c^2}\) for \(c\le1\).

The exact A gain is \(F_k(r)\) in the GA case and
\(F_m(r)\) in the AB case, where
\[
 F_k(t)=\sec t+K\tan t-R\sqrt{\sec^2t+k^2}
                                      -1+R\sqrt{1+k^2}.
\tag{7}
\]
Since \(m\ge k\), \(F_m(r)\ge F_k(r)\). Indeed the
derivative, in \(w=\sec r\), of the non-tangent part is
\(1-Rw/\sqrt{w^2+m^2}\), which increases with m; both
gains vanish at r=0.

The exact E gain in the EH case is \(F_k(s)\). For DE define
\[
 \mathcal D_c(w)=
 \begin{cases}\sqrt{w^2+c^2},&w\ge c,\\
               (w+c)/\sqrt2,&w\le c.
 \end{cases}
\]
Its exact gain is
\[
 L_c(s)=w-1+K\tan s
                 -R\{\mathcal D_c(w)-\mathcal D_c(1)\},
                 \qquad w=\sec s.
\tag{8}
\]
This dominates \(F_k(s)\). On its full-circle branch,
\(c\ge k\) makes the derivative in w at least
\(1-Rw/\sqrt{w^2+k^2}\). On the diagonal branch its
derivative is \(1-R/\sqrt2\), again larger, since
\(w\ge1>k\). The branches and their first derivatives agree
at w=c, and both gains start at zero.

Thus all four one-primary systems have the common lower
baseline
\[
                         B_0(z)+F_k(r)+F_k(s).
\tag{9}
\]
No new projection has been asserted by collecting these
weighted identities.

## 3. Whole-angle concentration at fixed r,s,z

Put \(S=r+s\). For an ordered pair \(p\le q\), define
\[
 \begin{split}
 N_{p,q}(d)&=\sqrt{p^2+q^2+2pq\sin d},\\
 U_{p,q}(d)&=p(\cos d+\sin d-1)
                          -R\{N_{p,q}(d)-N_{p,q}(0)\},\\
 V_{p,q}(d)&=q(\cos d-1)
                          -R\{N_{p,q}(-d)-N_{p,q}(0)\},\\
 \Psi_{p,q}(P,N)&=p(\cos P+\sin P-1)+q(\cos N-1)\\
                &\hspace{13mm}-R\{N_{p,q}(P-N)-N_{p,q}(0)\}.
 \end{split}
\tag{10}
\]
The actual ordered pairs are
\[
                    (k,\lambda_H),\quad(k,\lambda_G),\quad
               (\min(m,\lambda_B),\max(m,\lambda_B)).
\tag{11}
\]
Every one has ratio \(p/q\ge1/2\). Consequently U,V are
concave on \([0,h]\), and \(\Psi\) is separately concave,
by Section 3 of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md).
If E retains EH1, its remaining DE2 argument contributes
the sorted-D minorants
\[
 U_D(d)=-d_0d,\qquad V_D(d)=V_{k,1}(d),\qquad
                         d_0=R/\sqrt2-1<.4.
\tag{12}
\]
The hypotheses of that D comparison are \(k\le c\le2\)
and \(.5\le k\le .85\), all supplied by the scalar note.
If E retains DE3, both D arguments have already been fixed,
and there is no D angular block.

Delete the three fixed arguments \(-r,-s,z\) from the
algebraic angular vector. The remaining variations satisfy
\[
             P\le h-z,\qquad N\le h-S,
                         \qquad N-P=z-S.
\tag{13}
\]
The concentration proof of Section 3 of
[the negative-A concentration theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
applies without change: singleton blocks may be enlarged by
allowing their zero argument to vary, and separate concavity
first concentrates each sign in a single block. The
remaining common variation parameter also has a concave
objective. Its intrinsic endpoints leave precisely:

* a pure \(V_i(z-S)\) if \(S\le z\);
* a pure \(U_i(S-z)\) if \(S\ge z\);
* a same-block \(\Psi_i(h-z,h-S)\);
* a separated \(U_i(h-z)+V_j(h-S)\).

The D terms from (12) are allowed where present. A necessary
cycle must make the common baseline (9), plus at least one
of these alternatives, nonpositive. This is an enlargement
of the angular optimization; no concentration of the actual
configuration is assumed.

## 4. Every negative block has one of three canonical forms

For H and G, a negative term already has the form
\[
                V_{k,1}(d),\qquad V_{k,\sec r}(d),
                               \qquad V_{k,\sec s}(d).
\tag{14}
\]
The same is true of D by (12). For B write \(q_A=\lambda_B\).
If \(m\le q_A\), increasing the smaller coefficient from k
to m increases V, so
\[
                         V_{m,q_A}(d)\ge V_{k,q_A}(d).
\tag{15}
\]
Here is the whole-interval sign check: differentiation in
the smaller coefficient is nonnegative whenever
\(\sin d\le2pq/(p^2+q^2)\). Along this comparison,
\(p\ge.65\), \(q\le\sec(.38)<1.078\), so that condition
holds for every \(d\le h\).

If \(m\ge q_A\), the universal endpoint bound from
[the scalar-envelope theorem](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
and concavity give
\[
 V_{q_A,m}(d)\ge\frac{.87}{h}q_A d
       >1.19q_A d\ge V_{k,q_A}(d)\qquad(d>0).
\tag{16}
\]
The last step uses concavity and
\[
 V'_{k,q_A}(0)=\frac{Rkq_A}{\sqrt{k^2+q_A^2}}
               \le q_A\frac{R(.751)}{\sqrt{1+.751^2}}<1.19q_A.
\]
At d=0 the same conclusion holds with equality. Thus (14)
is exhaustive for pointwise lower bounds on negative terms.

For a positive term, the same scalar-envelope theorem gives
\[
 U_i(d)\ge-.545M d,
 \qquad
 M=\begin{cases}m,&0\le z\le .15,\\1.078,&.15\le z\le h.
 \end{cases}
\tag{17}
\]
All larger coefficients are at most M, by Section 2 of the
scalar note. The D term also satisfies (17), since \(d_0<.4\).
In particular
\[
                    .545M\le .7521<.9.
\tag{18}
\]

## 5. Same-block alternatives reduce to pure terms

Section 6 of the negative-A concentration theorem proves
\[
 \begin{split}
 \Psi(P,N)&\ge V(N-P)
       &&\text{if }P\le N,\ (q/p)\sin N\le1,\\
 \Psi(P,N)&\ge U(P-N)
       &&\text{if }N\le P,\ q/p\le1.7.
 \end{split}
\tag{19}
\]
All the hypotheses hold here at \(P=h-z,N=h-S\).
For an H or G pair whose secant is \(\sec\xi\),
\(0\le\xi\le S\), and
\[
       \sec\xi\sin(h-S)\le\sec\xi\sin(h-\xi)
                      =\sin h-\cos h\tan\xi<.645<k.
\tag{20}
\]
For B with \(m\le q_A\), the same argument applies with
the smaller coefficient m at least k. For B with \(m\ge q_A\),
its ratio is at most 1.38, so its ratio times \(\sin N\)
is less than \(1.38(.645)<1\).

For the other comparison, H/G have
\(q/p\le1.078/.65<1.7\). The B ratio is at most 1.38
when its larger coefficient is m on the low interval; in
all other cases it is at most \(1.078/.65<1.7\).
Thus every same-block term reduces to one of the pure
alternatives already listed in Section 3.

## 6. Merging both negative angles removes the pure alternatives

The common-gain theorem proves, on \(r+s+d\le h\),
\[
 \begin{split}
 F_k(r)+F_k(s)&\ge F_k(S),\\
 F_k(r)+F_k(s)+V_{k,\sec r}(d)
 &\ge F_k(S)+\min\{V_{k,1}(d),V_{k,\sec S}(d)\},
 \end{split}
\tag{21}
\]
with the analogous inequality for the secant of s. Its
proof makes the allocation function strictly concave using
the full-domain bounds
\[
 F''_k(r)+F''_k(s)<-.008-1.1(h-r-s),\qquad
 (V_{k,\sec r}(d))_{rr}\le .78d.
\tag{22}
\]
Thus this step includes every split of the two negative
angles, including simultaneous nonzero values.

If \(S\ge z\), equations (17), (18), and \(F'_k>.9\)
give
\[
 \begin{split}
 B_0+F_k(r)+F_k(s)+U_i(S-z)
 &\ge B_0+F_k(S)-.545M(S-z)\\
 &\ge B_0+F_k(z)>0.
 \end{split}
\tag{23}
\]
The last inequality is the second scalar certificate.

If \(S\le z\), replace the negative block using (14), then
apply (21) with \(d=z-S\). Section 6 of the common-gain
theorem proves the complete endpoint reduction
\[
 F_k(S)+\min\{V_{k,1}(z-S),V_{k,\sec S}(z-S)\}
                  \ge\min\{V_{k,1}(z),F_k(z)\}.
\tag{24}
\]
Its hypotheses are exactly the two coefficient intervals:
\(k=.65\) for \(z\le .15\), and \(.65\le k\le .751\)
for \(z\ge .15\). Both resulting scalar endpoints are
strictly positive after adding \(B_0\). This excludes every
pure negative alternative, and Section 5 also excludes every
same-block alternative.

## 7. Separated positive and negative blocks

Let \(P=h-z\), \(N=h-S\). Combining (17), (21), and the
endpoint reduction (24) with total argument h gives
\[
 \begin{split}
 &B_0+F_k(r)+F_k(s)+U_i(P)+V_j(N)\\
 &\hspace{12mm}\ge B_0-.545MP+\min\{V_{k,1}(h),F_k(h)\}.
 \end{split}
\tag{25}
\]
For the F endpoint, \(F'_k>.9\) and (18) give
\[
 B_0-.545MP+F_k(h)\ge B_0+F_k(z)>0.
\tag{26}
\]

For the V endpoint on \(z\ge .15\), concavity and the
monotonicity of \(V'_{k,1}(h)\) in k give
\[
 V_{k,1}(h)-V_{k,1}(z)>.64P.
\tag{27}
\]
The endpoint bound \(V'_{.65,1}(h)>.64\) is proved in
Section 4 of the negative-A concentration theorem. Directly,
\(V'=-\sin d+Rk\cos d/\sqrt{1+k^2-2k\sin d}\); its
derivative in k is positive since \(1-k\sin d>0\).
As \(.545(1.078)=.58751<.64\), this endpoint in (25) is
at least \(B_0+V_{k,1}(z)>0\).

On \(z\le .15\), k=.65. A useful larger chord reserve is
\[
             V_{.65,1}(h)-V_{.65,1}(z)>.8(h-z).
\tag{28}
\]
To verify it exactly, the coarse bounds
\[
 \cos h>.7648,\ R>1.9787,\ \sqrt{1+.65^2}>1.1926,
 \quad \sqrt{1+.65^2-1.3\sin h}<.7649
\]
give
\[
 V_{.65,1}(h)>.7648-1+1.9787(1.1926-.7649)
                         =.61108999>.611.
\]
Also concavity and \(V'_{.65,1}(0)<1.08\) give
\(V_{.65,1}(.15)<.162\). The chord from .15 to h therefore
has slope greater than \((.611-.162)/.55>.8\).
Concavity makes every chord from \(z\le .15\) to h at least
as steep, proving (28). Since \(.545M\le .7521<.8\), this
last endpoint in (25) is again strictly positive by the
first scalar certificate.

Every concentrated alternative is now positive. This
contradicts the necessary nonpositive value from Section 3
and proves the four one-primary exclusions.

## 8. The finite join from arbitrary negative primary totals

Start with the theorem's original arbitrary negative A and E
totals. Apply
[the negative-sum A transport](HAND_G3_MIXED_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_ONE.md)
and its
[same-state primary entry alternatives](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md).
They change only A and preserve BT2, TD2, z, E, the four outer
anchors, and both variation bounds. If a same-state secondary
reselection leaves a nonnegative A-primary total, Section 5 of
[the paired-negative E transport](HAND_G3_PAIRED_NEGATIVE_CORE_E_COMPLETE_TRANSPORT.md)
already excludes the system. Otherwise there is one negative
A primary with an actual secondary on its other edge.
Selecting that secondary whenever available either exits to
the covered zero A total, or leaves genuine flat-core A with
the appropriate bound in (2).

Next use Sections 2--4 of the paired-negative E transport and
[the mixed-negative E transport](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
They change only E and retain all the resulting A/T data and
variation bounds. A same-state secondary reselection leaving
a nonnegative E-primary total is covered by
[the core-E nonnegative-total theorem for every A](HAND_G3_CORE_E_NONNEGATIVE_PRIMARY_TOTAL_ALL_A_EXCLUSION.md).
The E-zero endpoint is excluded by the retained high GA and
the boundary-neighbor reflection theorem. The remaining
endpoint has one negative E primary and an actual secondary.

If the primary is DE3, its actual EH0 witness gives
\[
 b_E\le\sqrt{a_H^2+b_H^2}-1\le a_0-1<.415<1/2,
 \qquad a_0=\sqrt{Q-1/4}-1/2.
\]
Thus its true core is flat. If the primary is EH1, select
actual EH0 whenever it is feasible; this exits to the covered
zero E total. Otherwise the genuine negative-EH entry theorem
gives flat E, \(b_E<39/250\), and \(s<1/4\). Consequently
the resulting necessary cycle satisfies exactly one of the
four systems in Section 1, all excluded above.

The boundary-neighbor transport theorem supplies the scope
of every necessary descendant used here. The proof needs
only the retained neighboring inequalities, the canonical
corner constraints, and the preserved variation bounds.

This closes the negative-A, negative-core-E, positive-TD2
region. Together with the all-A/E nonpositive-TD2 theorem,
the TD0 join in Section 6 of the paired-negative E transport,
the complete outer-E BT2 theorem, and the nonnegative-A/E
total exclusions, it excludes every high-GA boundary cycle
retaining BT2 and either TD0 or TD2.
