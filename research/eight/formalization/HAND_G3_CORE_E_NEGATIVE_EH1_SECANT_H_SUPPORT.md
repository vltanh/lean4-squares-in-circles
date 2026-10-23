# The negative EH1 secant support and all E owners at small positive A total

## 1. Fixed family and statement

Use
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad k=\frac{39}{50},\quad l=\frac{63}{50},\quad c=\frac95,
 \quad L=\frac{103}{100}.
\tag{1}
\]
The fixed sorted outer Q anchors H, G, B and D have tangent signs
positive, negative, negative and negative. E is nonpositive.
A and T may have either tangent sign and either canonical radial
kind, with their retained sorted circle constraints.
Retain BT2 and either HG owner. The A edges have either the
secondary pair GA2/AB0, a single nonnegative primary GA3 or AB2,
or both primaries with nonnegative signed total
\[
                              0\le a\le\frac16.
\tag{2}
\]
When an A edge is secondary its error is arbitrary; for two
primaries their individual signs are arbitrary. TD is either
TD0 at any error or TD2 at a nonpositive error. Assume the
captured variation domain
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{3}
\]

The principal support lemma below handles flat-core E with a
negative EH1 error of magnitude at most 1/4, and either a
secondary DE2 at any error or a nonpositive primary DE3.
Section 5 combines this lemma with the existing E comparisons
to exclude **every DE2/3--EH0/1 owner and error choice** in the
A/TD regime (2), with either radial kind of E and no frame order.

This is a proof about the consecutive necessary inequalities.
Its use after an E-only reduction needs no fresh G1 premise.
All decimals below are exact rationals.

## 2. A uniformly charged H block with a small secant coefficient

Write the full shifted-circle support as
\[
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2}.
\tag{4}
\]
For
\[
 1\le q\le\bar q:=\frac{1033}{1000},\qquad -h\le v\le h,
\]
put
\[
 \begin{split}
 N_q(v)&=\sqrt{k^2+q^2+2kq\sin v},\\
 \Phi_q(v)&=k\{\cos v+\max(0,\sin v)-1\}
                     -R\{N_q(v)-N_q(0)\}+Lv.
 \end{split}
\tag{5}
\]
Then
\[
                              \Phi_q(v)\ge0.
\tag{6}
\]
For HG2 this is precisely the charged increment of
\[
                    kW(v)+q-\overline S(q+k\sin v,k\cos v)
\tag{7}
\]
from its value at v=0, where
\(W(v)=(1+\cos v+|\sin v|)/2\).
For HG0 the H force is already \((q,k)\), so no H angular
increment is needed.

### 2.1 Concavity on the two sign intervals

The uniform derivative estimates in Section 3 of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
apply because \(1/2<k/q<1\). With \(C_q=-RN_q''\), they give
\[
 \frac{C_q(0)}k<.762,\qquad
 \frac{C_q'(0)}k<.921,
 \qquad
 C_q(v)\le
 \begin{cases}
 C_q(0),&v\le0,\\
 C_q(0)+vC_q'(0),&v\ge0.
 \end{cases}
\tag{8}
\]
For negative v, these imply
\(\Phi_q''(v)<k(.762-\cos h)<0\), since
\(.7648-.762=7/2500>0\).
For positive v, it suffices that
\(\cos v+\sin v-.762-.921v>0\). This last function is
concave on \([0,h]\), and its endpoint lower bounds are
\[
                         .238>0,\qquad
                  1.409-.762-.921h=\frac{23}{10000}>0.
\tag{9}
\]
Thus \(\Phi_q\) is strictly concave separately on each sign
interval. Its minimum is among \(-h,0,h\).

### 2.2 The intrinsic endpoints remain nonnegative

At q=1, the exact corner comparisons in Section 3.1 of
[the low-angle four-circle stress](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md)
give
\[
                         \Phi_1(h)>.075533,\qquad
                         \Phi_1(-h)>.007.
\tag{10}
\]
For the negative endpoint the cited two-variable corner puts
the coefficient 1 on the negative cosine term; replacing it
by k<1 only increases that corner value.

The q derivative of (5) is
\[
 \partial_q\Phi_q(v)
 =-R\left\{\frac{q+k\sin v}{N_q(v)}-
                         \frac q{N_q(0)}\right\}.
\tag{11}
\]
The first ratio increases with v, since its derivative is
\[
              \frac{k^2\cos v\,(k+q\sin v)}{N_q(v)^3}>0.
\tag{12}
\]
For its sign, the whole-domain lower bound is
\[
                    k-\bar q(.645)=\frac{22743}{200000}>0.
\]
Consequently \(\Phi_q(-h)\ge\Phi_1(-h)>0\).
At the positive endpoint, both ratios in (11) belong to [0,1],
so its possible loss is less than \(1.978788(\bar q-1)\).
The positive corner therefore retains the exact reserve
\[
 \Phi_q(h)>.075533-1.978788(.033)
                         =\frac{2558249}{250000000}>0.
\tag{13}
\]
Finally \(\Phi_q(0)=0\) for all q. Concavity proves (6).

## 3. The net EH gain pays the whole angular charge

Suppose E is flat, \(a_E=7/12\), and EH1 has error \(-s\),
\(0\le s\le1/4\). Put \(q=\sec s\). It lies in the range
of Section 2 because
\[
                \bar q C_6(1/4)-1=\frac{2614487}{2949120000}>0.
\tag{14}
\]
Give that actual EH1 inequality multiplier q. Its projection is
\[
                   qP_{EH1}=q a_H-\frac7{12}\tan s-b_E.
\tag{15}
\]
The E tangent cancels with either unchanged DE2 or secant-weighted
negative DE3, whose E tangent coefficient is +1. Compared with
reference EH demand q, the demand and the primary term in (15)
give the exact gain
\[
                q(W(s)-1)+\frac7{12}\tan s
                       =\frac{13}{12}\tan s-\frac12(q-1).
\tag{16}
\]
The H baseline changes by
\[
 [q-\overline S(q,k)]-[1-\overline S(1,k)]
      =\frac32(q-1)-R\{\sqrt{q^2+k^2}-\sqrt{1+k^2}\}.
\tag{17}
\]
For HG2, (6) bounds its remaining H angular increment by zero;
for HG0 the H block is already this baseline. The net gain is
therefore
\[
 H(s)=K\tan s+(q-1)
         -R\{\sqrt{q^2+k^2}-\sqrt{1+k^2}\},
                  \qquad K=\frac{13}{12}.
\tag{18}
\]

Throughout \(1\le q\le\bar q\),
\[
                  \frac{Rq}{\sqrt{q^2+k^2}}<\frac{79}{50}=1.58.
\tag{19}
\]
The ratio increases in q, and its endpoint square reserve is
\[
 \left(\frac{79}{50}\right)^2(\bar q^2+k^2)-Q\bar q^2
                         =\frac{2748157}{625000000}>0.
\tag{20}
\]
Integrating (19) in (18) gives
\[
                     H(s)\ge g_H(s):=K\tan s-\frac{29}{50}(\sec s-1).
\tag{21}
\]
This lower bound pays the full charge with reserve:
\[
                         H(s)\ge\left(L+\frac1{625}\right)s.
\tag{22}
\]

Here is a whole-interval verification of the last claim. The
second derivative of \(g_H\) has numerator
\(2K\sin s-(29/50)(1+\sin^2s)\). For \(s\le1/4\) it is
at most
\[
                          2K(1/4)-\frac{29}{50}=-\frac{23}{600}<0.
\tag{23}
\]
Thus \(g_H(s)-Ls\) is concave and vanishes at zero. At the
other endpoint its positive-cosine multiple has the exact bound
\[
\begin{split}
 &\cos(1/4)\{g_H(1/4)-L/4\}\\
 &\quad=K\sin(1/4)+(29/50-L/4)\cos(1/4)-29/50\\
 &\quad\ge KS_7(1/4)+(29/50-L/4)C_6(1/4)-29/50\\
 &\quad=\frac{6133843}{12386304000}>\frac1{2500}.
\end{split}
\tag{24}
\]
Its reserve above \(1/2500\) is
\(5896607/61931520000\). Since cosine is at most one,
concavity supplies \(g_H(s)-Ls\ge s/625\), proving (22).

## 4. A single negative EH, or both negative E primaries

Keep the A/TD regime (2). Suppose first that E is flat and EH1
has error \(-s_H\), with \(s_H\le1/4\), while DE2 is retained
at an arbitrary error. The G/B charged blocks and the actual
sorted D block are unchanged from the low-angle stress. Replace
only the H estimate by Section 2, and use the gain (22).

If instead DE3 is selected with error \(-s_D\le0\), also give
it multiplier \(\sec s_D\). Section 3 of
[the secant-D support proof](HAND_G3_CORE_E_NEGATIVE_DE3_SECANT_D_SUPPORT.md)
applies with \(c=9/5\). Its net gain is
\[
 D(s_D)=\frac{13}{12}\tan s_D
             -(c_0-\tfrac12)(\sec s_D-1)
                    \ge\left(\frac{21}{20}+\frac1{390}\right)s_D.
\tag{25}
\]
The support and gain arguments there use EH0 only to establish
that E is flat at entry. Flatness is an explicit hypothesis
here. Its secant DE projection has E coefficient +1 and (15)
has coefficient -1, so the same D support and both baseline
gains apply simultaneously. H and D are different circles.

Let w be the magnitude of a selected nonpositive TD2 error,
or zero for TD0. The pointwise secant TD comparison has gain
at least \(.9cw=1.62w\), as in Section 6 of the secant-D proof.
Delete the designated A arguments, EH, DE when primary, and
TD when owner 2. Their virtual signed sum is
\[
                             s_H+s_D+w-a,
\tag{26}
\]
with absent \(s_D=0\). Positive and negative variation remain
at most h. The unchanged low-A baseline estimate is
\[
                         B_0+La+l j(a)>\frac{49}{15000},
\tag{27}
\]
where \(j(a)=W(a)-1-S(\sin a,1-\cos a)\). The signed
A-combination proof justifies the same term for opposite signs
of its two primary errors.

Combining the independent charged blocks, (22), (25), and the
TD gain makes the actual positive stress strictly greater than
\[
                \frac{49}{15000}
                   +\frac{s_H}{625}+\frac{22}{975}s_D
                   +\frac{59}{100}w>0.
\tag{28}
\]
Feasibility requires demand minus projection to be nonpositive.
This excludes both stated negative-E patterns.

## 5. Complete E-owner coverage in the small positive-A regime

Now allow either radial kind for nonpositive E and arbitrary
errors and owners DE2/3 and EH0/1, retaining exactly the other
conditions of Section 1. The resulting necessary system is
impossible.

For outer E this is already Section 4 of
[the outer-E witness comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md),
in its second fixed regime. For core E, a single nonnegative
primary or two primaries with nonnegative signed total is
excluded by Section 7 of
[the signed E-primary stress](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md).
If both owners are secondary, use the low-A TD0 proof and its
nonpositive-TD2 comparison directly.

The remaining negative-total cases have the following finite
reduction. A genuine negative EH1 error, meaning that EH0 is
not feasible, forces E flat and \(s_H<1/4\), by Section 2 of
[the mixed-negative E reduction](HAND_G3_MIXED_NEGATIVE_E_PRIMARY_ERRORS_REDUCTION.md).
Any core E with an actual EH0 witness is also flat. A single
negative DE3 with EH0 is excluded by the secant-D proof, while
a single genuine negative EH1 with DE2 is excluded by Section 4
above. If both primaries have nonpositive errors, select EH0
when available; otherwise the genuine EH cut gives exactly the
simultaneous case of Section 4.

For opposite signs and negative total, the two local paths in
the mixed-negative E reduction retain D/H and every A/T datum.
Negative DE/positive EH reaches a single negative DE with actual
EH0. Positive DE/genuine negative EH reaches a single negative
EH with aligned DE2. If EH0 was already feasible in the latter
case, select it and retain the single positive DE primary,
which is covered by the signed E stress. The paths keep E core,
preserve the signed sum, reduce both variations, and leave (2)
unchanged. The already established necessary-system contradictions
therefore apply at every endpoint.

This completes all E owner and error choices at small nonnegative
A total. The explicit remaining A/TD scope boundaries are
\(a>1/6\) and positive TD2; this theorem makes no assertion
about those classes.
