# E above A forces F above B: a complete rational table

Retain the entire [Cb882 original-nine predicate](CB882_WHOLE_DOMAIN.md),
with all independent physical frames and all original pair conditions.
Assume the upward A/E inset order

\[
                         y_E-y_A\ge g_A+g_E.
\]

Then

\[
                         y_F-y_B\ge g_B+g_F.             \tag{1}
\]

The [whole-parent G-order theorem](CB882_G_ABOVE_D.md) and the
[B/F inset theorem](CB882_BF_VERTICAL.md) have already proved
y_G-y_D>=g_D+g_G and that the two vertical B/F orders are exhaustive.
It therefore suffices to exclude the closed contrary alternative

\[
                         y_B-y_F\ge g_B+g_F.             \tag{2}
\]

The complete arithmetic is printed in two appendices:

* [All 129 literal rational rows, in two contexts](CB882_E_UP_F_DOWN_ROWS.md).
* [All 44 bound deductions and the one final contradiction](CB882_E_UP_F_DOWN_CERTIFICATES.md).

There is no angle subdivision or selection of a C/D physical axis.
The single contrary domain (2) passes through the first set of bounds
to the final contradictory row sum. The appendices print every used
coefficient, positive integer weight, and rational reserve. The proof
requires only the continuous inequalities cited below and this finite
rational arithmetic.

## 1. Original variables and the initial context

Number A through I by i=0 through 8. Use these 54 real variables:

\[
 \begin{aligned}
 z_{2i}&=x_i,& z_{2i+1}&=y_i,\\
 z_{18+3i}&=a_i,&z_{19+3i}&=b_i,&z_{20+3i}&=d_i=|b_i|,\\
 z_{45+i}&=g_i=1/(4h_i),& h_i&=(a_i+d_i)/2.
 \end{aligned}                                         \tag{3}
\]

Here (a_i,b_i),(-b_i,a_i) are the actual orthonormal sides of original
i. In particular a_i^2+b_i^2=1 and a_i>=|b_i|. Write
w_i=tan(theta_i/2), with a(w)=(1-w^2)/(1+w^2) and
b(w)=2w/(1+w^2).

The first table context, C000, prints an interval for every coordinate
and every frame component. Its center and w intervals are the closed
enlargements of the whole-parent bounds in
[the whole-domain chapter](CB882_WHOLE_DOMAIN.md), Sections 1--2,
and [the geometric localization](CB882_GEOMETRIC_REDUCTION.md).
In particular the latter proves

\[
 x_A<-23/16,\quad x_B<-7/16,\quad x_C<57/80,\quad
 y_B<743/1920,\quad x_H<-1/40,\quad y_B-y_H>203/240.
\]

The last two height bounds give y_H<-881/1920. The whole-parent
A-height bound y_A<1/4 is proved in Section 1 of
[the endpoint-routing chapter](CB882_E_DOWN_ROUTING.md), before
either E order is chosen. The remaining initial bounds are printed
with their derivations in the whole-domain chapter. Thus C000
contains every hypothetical original satisfying (2).

The a,b,d intervals follow from the rational frame formulas. More
explicitly, for a w interval [l,u], let m be zero when l<=0<=u and
otherwise min(|l|,|u|), and put M=max(|l|,|u|). The halfwidth bounds
used in both contexts are exactly

\[
 H=\frac{a(m)+b(m)}2,\qquad
 U=\begin{cases}
 (a(M)+b(M))/2,&M<2/5,\\
 707107/1000000,&M\ge2/5.
 \end{cases}
\]

The last rational number exceeds 1/sqrt(2), since
707107^2-500000000000=309449>0. The g interval is
[1/(4U),1/(4H)]. These are enclosures of the same original frame,
not independent physical choices.

## 2. Why every printed row is necessary

Every row in the appendices means

\[
                         \sum_{q=0}^{53}c_qz_q\le t.     \tag{4}
\]

Only its nonzero coefficients are printed: an entry `q:c` means
c_q=c. The row label gives its geometric source. The index within
the row name only distinguishes literal rows in that context.

The continuous proofs of the row families are as follows.

| Printed family | Proof of validity |
|---|---|
| Coordinate and frame bounds | The context intervals and the preceding section |
| Frame chord, canonical frame, absolute component, width bound, inset tangent and secant | [Physical-frame rows](CB882_PHYSICAL_FRAME_ROWS.md), Section 1 |
| Original corner, original center, exact Q tangent | Physical-frame rows, Section 2 |
| Actual link, center cone, CD inset, CD height, BH cone and inset, H/I order | The unchanged original caller and its actual contained insets |
| C-slant | [Complete nonpositive-D C-slant proof](00100_C_SLANT_LOWER_COMPLEMENT.md) |
| Long span and unary inset transfers | Whole-domain chapter, Sections 2 and 4; geometric localization, Section 1 |
| A unary bound | [Endpoint-inset theorem](00100_ENDPOINT_INSETS_ARE_VERTICAL.md), Section 1 |
| Physical two-square cap | [Foundation](FOUNDATION.md), Part B |
| A/E, D/G and B/F vertical inset rows | The height hypotheses preceding (2) |
| Pair distance and frame-distance secants | Whole-domain chapter, Sections 3--4, and [frame-coupled pair rows](FRAME_COUPLED_PAIR_ROWS.md) |
| Width-mismatch distance | Physical-frame rows, Section 6 |

The rational radius ceiling in the ordinary corner rows is exactly
83103850693/40000000000, whose square exceeds Q=1105/256 by
4436580249/1600000000000000000000. The exact Q-tangent rows instead
use normals of squared norm 1105 and right side 1105/16.

Positive rescaling of a necessary inequality preserves its validity.
The literal row coefficients already include any such rescaling.
All row proofs are valid on their entire printed context intervals,
including boundaries. They require neither a chosen C/D side normal
nor an additional original-coordinate separation.

## 3. Verification rule for each positive row sum

In one context let z_q lie in the printed interval [l_q,u_q]. For a
listed positive integer weight lambda_j on each used row, put

\[
 A_q=\sum_j\lambda_jc_{jq},\qquad B=\sum_j\lambda_jt_j.
\]

Then the weighted rows imply A dot z<=B. For any coefficient vector
v define its exact box minimum by

\[
 L(v)=\sum_{v_q\ge0}v_ql_q+\sum_{v_q<0}v_qu_q.
                                                               \tag{5}
\]

Thus v dot z>=L(v), with no sign restriction on v.

A bound-deduction line `(k,s,b)` has s in {-1,1} and asserts
s z_k<=s b. To check it, form

\[
 v=A-10^6s e_k,\qquad
 \mathcal R=10^6s b-(B-L(v)).                              \tag{6}
\]

The table prints a nonnegative rational lower bound for this reserve.
Indeed 10^6s z_k<=B-L(v)<=10^6s b, proving the deduction.
All 44 deductions use the original C000 box in (5); none uses an
earlier deduction from the same batch.

For the final contradiction no coordinate is subtracted. The check is
simply

\[
                            L(A)-B>0.                    \tag{7}
\]

The weighted rows would then require both A dot z<=B and
A dot z>=L(A)>B.

## 4. The sole transition and final contradiction

Context C000 supplies deductions D000 through D043. Intersecting
the corresponding coordinate bounds with C000 gives the coordinate
intervals printed in C001. The new signed frame-component bounds
give the w intervals of C001 because b(w) is strictly increasing
on [-5/12,5/12]. The following four exact comparisons justify every
nontrivial endpoint in that transition; negative lower endpoints
also use b(-w)=-b(w).

| w | Component upper bound t | b(w)-t |
|---|---|---|
| 2285/32768 | 69391/500000 | 4555066841/539481524500000 |
| 441/16384 | 53783/1000000 | 2964098329/268629937000000 |
| 13573/32768 | 707107/1000000 | 2041236629/1257968153000000 |
| -2265/65536 | -6907/100000 | 12965577547/430009752100000 |

The unchanged original A lower endpoint and D sign restriction are
retained. All a,b,d,g intervals in C001 then follow from these w
intervals by the same formulas used for C000. No assumption about a
new physical frame is made at this transition.

Finally, the sole terminal line C001.X combines its 18 literal rows
with the printed positive integer weights. Its reserve in (7) is
at least

\[
                         \frac{5047119761}{250000}>0.
\]

This contradicts every original in C001, while all hypothetical
originals satisfying (2) were proved to reach C001. Thus (2) is
empty. The exhaustive B/F inset alternatives prove (1) throughout
the E-up part of the whole Cb882 caller.

Together with the [E-down middle-height theorem](CB882_E_DOWN_F_ABOVE_B.md),
this proves y_F-y_B>=g_B+g_F on the whole Cb882 caller, since the
endpoint-inset theorem covers both A/E height orders. This is a
whole-parent height reduction; the remaining F-above-B configurations
still require exclusion.
