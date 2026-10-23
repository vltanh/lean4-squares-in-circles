# A genuine negative EH1 and a nonpositive TD2 with nonnegative A total

## 1. Scope

Use the fixed-original-witness G0--G2 necessary system at
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 h=\frac7{10},\quad L=\frac16,\quad u=\frac14.
\tag{1}
\]
The sorted outer states H, G, B and D have tangent signs
positive, negative, negative and negative. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},\quad
 BT=2,\quad TD=2,\quad DE=2,\quad EH=1.
\tag{2}
\]
The TD2 and EH1 errors are respectively \(-t\) and \(-s\), with
\[
 t\ge0,\qquad 0\le s\le u,\qquad
                    a_E=\frac7{12},\quad 0\le b_E\le\frac{39}{250}.
\tag{3}
\]
These are the genuine negative-EH entry conditions whenever
an actual EH0 cannot already be chosen.

At A allow no primary, a single nonnegative primary, or both
GA3 and AB2 with nonnegative signed total a. Secondary A
arguments remain arbitrary. A and T have either sign and
either canonical radial kind. Assume the actual adjacent
inequalities and the captured variation conditions
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{4}
\]

There is no such necessary system. For \(0\le a\le L\), this
already follows from
[the all-E fixed secant-H theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md).
We prove the remaining range \(L\le a\le h\).
No frame-order hypothesis is used.

## 2. Exact cancellation and two negative angles

Choose the fixed coefficients
\[
 k=\frac{717}{1000},\qquad l=\frac{457}{500},\qquad
 c=\frac{1193}{1000},\qquad
 \gamma=\frac{18247}{20000},\qquad
 \lambda=\gamma c=1.08843355.
\tag{5}
\]
Give the original seven inequalities the multipliers
\[
                         (k,l,l,c,c\sec t,1,1).
\tag{6}
\]
The pointwise secant comparison from Section 2 of
[the positive-A negative-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md)
cancels T's signed tangent. Its gain over the algebraic
zero-error TD0 projection is
\[
 c\{(a_T+\tfrac12)\tan t+(\tfrac12-b_D)(\sec t-1)\}
                           \ge\gamma c\,t=\lambda t.
\tag{7}
\]
The unconditional bounds used here are
\(a_T>447/800\), \(b_D<.9\), and
\(\tan(t/2)<183/500\) for \(t\le h\).
In particular the T sign is not restricted.
The reference TD0 projection in this calculation is only
part of a weighted force identity; it is not asserted to be
an original separating witness.

Give both E edges weight one. The fixed true-core E and
its small tangent give the same exact charge as in Section 2 of
[the small negative-EH theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SMALL_ERROR_EXCLUSION.md):
\[
 g(s)=K\sin s-\beta(1-\cos s),\qquad
             K=\frac{13}{12},\quad \beta=\frac{82}{125}.
\tag{8}
\]
That force calculation is valid on all of \([0,u]\):
the E residual has coefficient \(1-\cos s\ge0\).
It also removes the EH rotation from the H norm.

The selected A arguments contribute \(l j(a)\), where
\[
 j(a)=
 \begin{cases}
 \frac12(\cos a-1)+(\frac12-a_0)\sin a,&a\le a_{\rm ax},\\
 \sin a-2R\sin(a/2),&a\ge a_{\rm ax},
 \end{cases}
 \quad a_0=\sqrt{Q-\frac14}-\frac12,\quad a_{\rm ax}>\frac12.
\tag{9}
\]
For two A primaries, this is
[the signed combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
All remaining reference forces are the old three ordinary
norm blocks and the one-angle D support with the TD argument
zero.

Put
\[
                              w=s+t.
\tag{10}
\]
The actual negative variation gives \(w\le h\).
After the selected A arguments, TD and EH are deleted from the
algebraic angular vector, the remaining masses satisfy
\[
                  P\le h-a,\qquad N\le h-w,\qquad N-P=a-w.
\tag{11}
\]
For two signed A primaries, the removed positive variation is
at least a; removing any negative A variation only enlarges
(11).

At fixed w, the charge \(g(s)+\lambda(w-s)\) decreases in s,
because
\[
          g'(s)\le K<\lambda,\qquad
                \lambda-K=\frac{306013}{60000000}>0.
\tag{12}
\]
Thus it is at least
\[
 J(w)=
 \begin{cases}
 g(w),&0\le w\le u,\\
 g(u)+\lambda(w-u),&u\le w\le h.
 \end{cases}
\tag{13}
\]
This replaces s by its largest permitted value \(\min(w,u)\)
inside a scalar relaxation. No geometric E or T transport is
needed. The function J is concave separately on the two
displayed intervals. Its upward derivative jump at u will
be kept as an intrinsic endpoint.

## 3. Ordinary norm support and the baseline

Write
\[
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2},\qquad
 c_0=\sqrt{Q/2}-\frac12,\qquad d_0=c_0-\frac12<.4.
\]
The three ordered pairs are
\[
                         H=(k,1),\qquad G=(k,l),\qquad B=(l,c).
\tag{14}
\]
Every pair has smaller-to-larger ratio strictly greater than
\(2/3\). Define
\[
\begin{split}
 N_i(x)&=\sqrt{p_i^2+q_i^2+2p_iq_i\sin x},\\
 U_i(x)&=p_i(\cos x+\sin x-1)-R\{N_i(x)-N_i(0)\},\\
 V_i(x)&=q_i(\cos x-1)-R\{N_i(-x)-N_i(0)\},\\
 \Psi_i(P,N)&=p_i(\cos P+\sin P-1)+q_i(\cos N-1)
                         -R\{N_i(P-N)-N_i(0)\}.
\end{split}
\tag{15}
\]
The exact D support at zero is diagonal, since \(c>1\).
The baseline is
\[
\begin{split}
 B_0={}&k+2l+2c+2-\overline S(1,k)-\overline S(l,k)
                      -\overline S(c,l)-(1+c)c_0\\
                              &>-.02093.
\end{split}
\tag{16}
\]
Its explicit radical enclosure is given in Section 7.

The actual DE2/D force is \((\cos d,c+\sin d)\).
The D minorant from Section 4 of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
therefore gives
\[
                  U_D(P)+V_H(N),\qquad U_D(P)=-d_0P.
\tag{17}
\]
Its hypotheses \(k\le.85\), \(k\le c\le2\) hold.
The true zero-angle support stays in (16).

Separate concavity in the ordinary blocks first concentrates
the negative variation, then the positive variation, then
their common total. As in the cited theorem, missing angular
arguments are permitted as virtual zeros. Equations (11)
therefore leave pure U or V terms, same-block terms
\(\Psi_i(h-a,h-w)\), and separated U/V terms at those masses.
The linear positive D term is included; its negative term
is already \(V_H\).

## 4. Removing saturation on either side of the excess

For the fixed pairs (14),
\[
                         V_i'(x)>.767\qquad(0\le x\le h).
\tag{18}
\]
Concavity reduces this to \(x=h\). The exact formula is
\[
 V_i'(h)=-q_i\sin h+\frac{Rp_iq_i\cos h}{N_i(-h)}.
\]
The rational enclosures of Section 7 give lower bounds
greater than .768188, .806704, and 1.017506 for H, G, and B.

We also use the established whole-interval inequalities
\[
 U_i(x)\ge-.545q_i x,\qquad
 U_i'(x)>-.64q_i\quad(0\le x\le h-L).
\tag{19}
\]
The derivative estimate is Section 4 of
[the negative-DE concentration theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_ANGLE_CONCENTRATION.md).
Its proof uses only \(p_i/q_i\in[1/2,1]\); the coefficients
need not belong to that theorem's later parameter family.
Both inequalities also hold for \(U_D\), since \(d_0<.4\).

Let \(P=h-a\), \(N=h-w\). If \(N\ge P\), the separated
increment is at least
\[
 U_i(P)+V_j(N)
 \ge V_j(N-P)+\{.767-.545c\}P
 =V_j(N-P)+.116815P.
\tag{20}
\]
If \(N\le P\), both P and N are at most \(h-L=8/15\).
Integrating the derivative estimate in (19) instead gives
\[
 U_i(P)+V_j(N)
 \ge U_i(P-N)+\{.767-.64c\}N
 =U_i(P-N)+.00348N.
\tag{21}
\]
These comparisons allow the linear \(U_D\), as well as
coincident scalar indices. They do not assert a new
original same-block witness.

Every ordinary same-block term also dominates its pure term.
For \(P\le N\), direct subtraction gives
\[
 \frac{\Psi_i(P,N)-V_i(N-P)}{p_i}
 =(1-r\cos N)(\cos P-1)+(1-r\sin N)\sin P,\quad r=q_i/p_i.
\tag{22}
\]
This decreases with r. At \(r=3/2\) both terms are
nonnegative because \((3/2)\cos h>1\) and
\((3/2)\sin h<1\).
For \(N\le P\),
\[
 \frac{\Psi_i(P,N)-U_i(P-N)}{p_i}
 =(\phi(P)-r)(1-\cos N)+\phi'(P)\sin N,\quad
 \phi(x)=\cos x+\sin x.
\tag{23}
\]
The right side decreases with P. At \(P=h\), use
\(\phi(h)>1.409\), \(\phi'(h)>.12\), and
\(\tan(N/2)<.366\). It is at least
\[
             \{(1.409-1.5)(.366)+.12\}\sin N\ge0.
\]
The separate D minorant is already covered by (20)--(21).

Thus every feasible necessary system would require one of
the following stresses to be nonpositive:
\[
\begin{array}{ll}
 B_0+l j(a)+J(w)+V_i(a-w),&0\le w\le a,\quad i=H,G,B,\\
 B_0+l j(a)+J(w)+U_i(w-a),&a\le w\le h,\quad i=H,G,B,D.
\end{array}
\tag{24}
\]

## 5. The intrinsic combined-angle endpoints

For fixed a, every expression in (24) is concave in w on
each interval cut by a and u. This uses concavity of U and V,
linearity of \(U_D\), and the two concave pieces of J.
The only w values to check are therefore
\[
                                0,\qquad a,\qquad u,\qquad h.
\tag{25}
\]
The cut at u is retained; global concavity across its upward
derivative jump is not used.

We next reduce the a intervals. The standard A-support bounds
are
\[
           j''<.02,\qquad j'<-.69.
\tag{26}
\]
They hold on both smooth support branches, with the matching
first derivative at \(a_{\rm ax}\). We also have the sharper
lower derivative bound
\[
                                j'>-1.1.
\tag{27}
\]
On the axis branch,
\(|j'|\le\sqrt{1/4+.915^2}<1.05\).
On the full-circle branch \(j''<0\), so its smallest
derivative occurs at h, and
\[
            j'(h)=\cos h-R\cos(h/2)
               >C_6(h)-1.978787508\,C_4(h/2)>-1.1.
\]
Here \(S_n,C_n\) are alternating Taylor polynomials.

The ordinary norm curvature bounds give
\[
 V_i''<-.0648q_i,\qquad
 U_i''<-.1p_i\quad(0\le x\le h-L).
\tag{28}
\]
The first follows from \(\cos h>.7648\) and
\(-RN_i''(0)<.7q_i\); the second is the usual positive-angle
curvature bound, using
\(\phi(x)-.762-.921x>.1\) on \([0,h-L]\).

Consequently every a-dependent ordinary U or V function
in (25) is strictly concave:
\[
 .02l-.0648q_i\le-.0409472,\qquad
 .02l-.1p_i\le-.05342.
\tag{29}
\]
At \(w=a\le u\), the function \(l j(a)+g(a)\) is also
strictly concave, since its second derivative is at most
\[
                  .02l-\beta\frac{31}{32}=-.61722.
\tag{30}
\]
At \(w=a\ge u\), it is instead increasing:
\[
                 l j'(a)+\lambda>
                      \lambda-1.1l=.08303355>0.
\tag{31}
\]

For clarity the linear D terms are handled separately.
When \(w=u\) or h is fixed and \(a\le w\),
\[
 \frac d{da}\{l j(a)-d_0(w-a)\}
                      =l j'(a)+d_0<-.23066<0.
\tag{32}
\]
Their minimum is the right endpoint \(a=w\), where the
increment is zero. No concavity of j alone is asserted.

It remains to check precisely these endpoints:

* \(w=0\), \(a=L,h\), for each of the three V pairs;
* \(w=a\), \(a=L,u\), with no ordinary increment;
* \(w=u\), \(a=L\), for each ordinary U pair, and \(a=h\)
  for each V pair;
* \(w=h\), \(a=L\), for each ordinary U pair, and \(a=h\)
  with no increment.

There are eighteen scalar values. All are positive below.

## 6. The explicit endpoint scalar formulas

Use the exact constants (5), the exact baseline (16), and
the functions (8)--(9), (15). Define, for \(i=H,G,B\),
\[
\begin{split}
 I_i&=B_0+l j(L)+V_i(L),\\
 II_i&=B_0+l j(h)+V_i(h),\\
 III_i&=B_0+l j(L)+g(u)+U_i(u-L),\\
 IV_i&=B_0+l j(h)+g(u)+V_i(h-u),\\
 V_i^*&=B_0+l j(L)+g(u)+\lambda(h-u)+U_i(h-L).
\end{split}
\tag{33}
\]
The three zero-increment endpoints are
\[
\begin{split}
 Z_L&=B_0+l j(L)+g(L),\\
 Z_u&=B_0+l j(u)+g(u),\\
 Z_h&=B_0+l j(h)+g(u)+\lambda(h-u).
\end{split}
\tag{34}
\]

The following are strict exact lower bounds:

| Pair | \(I_i\) | \(II_i\) | \(III_i\) | \(IV_i\) | \(V_i^*\) |
|---|---:|---:|---:|---:|---:|
| H | .01964 | .00695 | .04471 | .04332 | .30762 |
| G | .01470 | .00494 | .04775 | .03594 | .32563 |
| B | .06608 | .19252 | .03738 | .16538 | .25192 |

The remaining three bounds are
\[
                    Z_L>.00468,\qquad Z_u>.00566,\qquad Z_h>.0649.
\tag{35}
\]
Section 7 gives the complete rational data proving these
comparisons.

## 7. Rational Taylor and radical certificates

Use
\[
\begin{gathered}
 R_-=1.978787507<R<\overline R=1.978787508,\\
 c_0<.899214066,\qquad a_0-\tfrac12<.914576.
\end{gathered}
\tag{36}
\]
All follow by positive squaring. With \(S_{11}\le\sin\le S_9\)
and \(C_{10}\le\cos\), direct rational substitution gives
\[
\begin{gathered}
 j(L)>-.15866,\qquad j(u)>-.24182,\qquad j(h)>-.71283,\\
 g(L)>.17063,\qquad g(u)>.24762.
\end{gathered}
\tag{37}
\]
For the first two j bounds use its exact axis formula;
for the third use
\(S_{11}(h)-2\overline R S_9(h/2)\).

Here are rational norm enclosures for the fixed pairs (14).
The first two columns bound \(N_i(0)\) below and above;
the other columns are upper bounds.

| Pair | \(N_i(0)\) lower | \(N_i(0)\) upper | \(N_i(-L)\) upper | \(N_i(-h)\) upper |
|---|---:|---:|---:|---:|
| H | 1.230483 | 1.230484 | 1.129688 | .768298 |
| G | 1.161673 | 1.161674 | 1.063979 | .710722 |
| B | 1.502878 | 1.502879 | 1.377265 | .923977 |

| Pair | \(N_i(u-L)\) upper | \(N_i(-(h-u))\) upper | \(N_i(h-L)\) upper |
|---|---:|---:|---:|
| H | 1.278066 | .943584 | 1.497714 |
| G | 1.207718 | .882830 | 1.419804 |
| B | 1.562104 | 1.144584 | 1.835044 |

Every entry is verified by squaring positive quantities.
For a positive argument x the sufficient upper comparison is
\[
             n_+^2>p_i^2+q_i^2+2p_iq_i S_9(x).
\]
For a negative argument \(-x\), it is
\[
             n_-^2>p_i^2+q_i^2-2p_iq_i S_{11}(x).
\tag{38}
\]
The zero-argument enclosures compare to \(p_i^2+q_i^2\).

Using the three zero-norm upper bounds and (36) in (16)
gives the explicit lower value
\[
 B_0>
 k+2l+2c+2+\frac{1+2k+2l+c}{2}
 -\overline R(1.230484+1.161674+1.502879)
 -(1+c)(.899214066)>-.02093.
\tag{39}
\]
For a negative increment, use
\[
 V_i(x)\ge q_i\{C_{10}(x)-1\}
                        +R_-\{n_{0,-}-n_{-x,+}\}.
\]
For a positive increment, use
\[
 U_i(x)\ge p_i\{C_{10}(x)+S_{11}(x)-1\}
                        -\overline R\{n_{x,+}-n_{0,-}\}.
\tag{40}
\]
The brackets have their stated positive signs at every
nonzero argument in the tables. Substitution of (37)--(40)
in (33)--(34) gives every printed bound in Section 6.

For (18), use the same \(N_i(-h)\) upper bounds with
\[
            -q_iS_9(h)+\frac{R_-p_iq_i C_6(h)}{n_{-h,+}}.
\tag{41}
\]
They are respectively greater than .768188, .806704, and
1.017506, hence greater than .767.

These are fixed intrinsic endpoint comparisons following
the whole-domain concavity argument. No sampled state or
angle partition is used.

## 8. Completion

Every normalized angle system in (11) is bounded below by
(24). Its two intrinsic w cuts, followed by the a comparisons
of Section 5, reduce to the eighteen values (33)--(34).
All are strictly positive by Sections 6--7. This contradicts
the nonpositive weighted stress required by the actual
separating inequalities.

Together with the fixed small-a theorem, this excludes the
entire single genuine negative-EH1 branch with DE2, nonnegative
A-primary total, and nonpositive TD2. Combining it with
[the remaining-error EH theorem](HAND_G3_CORE_E_NEGATIVE_EH1_REMAINING_ERROR_EXCLUSION.md),
its small-error companion, and
[the arbitrary-TD0 extension](HAND_G3_CORE_E_NEGATIVE_EH1_NONNEGATIVE_A_TD0_EXCLUSION.md)
covers both TD owners at every error in this single-EH class.

The result retains BT2 and the secondary DE2 witness. It does
not assert a negative A-primary total or simultaneous negative
E primaries.
