# Proving the sharp guard by rational row sums

This chapter gives a finite-certificate rule for entering the
[enlarged sharp terminal](CB882_ENLARGED_SHARP_TERMINAL.md). It allows
the relative-coordinate inequalities of that guard to be proved
directly from necessary rows. Individual coordinate intervals need
not imply those relative-coordinate inequalities by themselves.

No whole-domain cover is asserted here. Each application must print
its input intervals, necessary rows, positive weights and reserves,
and must occur in a separately established complete case tree.

## 1. A rational certificate for a linear target

Let the original physical variables satisfy a finite family of
necessary inequalities

\[
 c_j\cdot z\le b_j,
 \qquad L_q\le z_q\le U_q.
\]

For any rational vector t define

\[
 \ell(t)=\sum_{t_q\ge0}t_qL_q+\sum_{t_q<0}t_qU_q.
\]

Then t dot z>=ell(t). Let nonnegative rational weights lambda_j
have sums A=sum_j lambda_j c_j and B=sum_j lambda_j b_j.
For a target v dot z<=r and a positive rational M, suppose

\[
               Mr-B+\ell(A-Mv)\ge0.                    \tag{1}
\]

The weighted necessary rows imply

\[
 Mv\cdot z\le B-(A-Mv)\cdot z
                  \le B-\ell(A-Mv)\le Mr.
\]

Dividing by M proves the target. This calculation permits signed
entries in A, v and A-Mv. It retains every residual coefficient;
no numerical near-zero coefficient may be discarded without paying
for it in ell.

The finite tables may take M=10^6 and positive integer weights.
All targets in one context use that context's same original box and
rows. One target is never needed to justify the residual estimate
of another target in that context.

There is a simpler certificate when the box itself implies the target:

\[
 u(v)=\sum_{v_q\ge0}v_qU_q+\sum_{v_q<0}v_qL_q\le r.    \tag{2}
\]

Both (1) and (2) are finite rational comparisons. A displayed
nonnegative lower bound for (1), or the exact upper value u(v) in
(2), supplies its arithmetic check.

## 2. Exactly ten targets complete the enlarged guard

Retain the full original Cb882 caller. Number A,...,I by i=0,...,8
and write z_(2i)=x_i, z_(2i+1)=y_i. The remaining variables may be
the original frame components and inset halfwidths used in
[the physical-row chapter](CB882_PHYSICAL_FRAME_ROWS.md).

Assume the parameter intervals already imply

\[
 0\le\beta_A\le1/20,\qquad -1/20\le\beta_D\le0,
 \qquad |\beta_P|\le1/10\quad(P=B,I,E,F,G).             \tag{3}
\]

For rational half-angle intervals this check is rational: the function
b(w)=2w/(1+w^2) is increasing on [-5/12,5/12], so its two endpoint
values bound beta, and the larger endpoint magnitude bounds |beta|.
The original A and D signs must also be retained.

Suppose the upward endpoint inset orders are available:

\[
 y_E-y_A\ge g_A+g_E,\qquad y_G-y_D\ge g_D+g_G.          \tag{4}
\]

These imply the two strict height inequalities in the enlarged guard,
because every actual inset halfwidth is positive. No strict numerical
certificate for those heights is required.

The following ten closed targets give precisely the remaining
coordinate part of that guard:

| Target | Sparse left side v dot z | Right side r | Geometric meaning |
|---|---|---|---|
| BI horizontal order | z_2-z_16 | 0 | x_B<=x_I |
| ID horizontal order | z_16-z_6 | 0 | x_I<=x_D |
| IB lower height | z_3-z_17 | 1/20 | y_I-y_B>=-1/20 |
| IB upper height | z_17-z_3 | 1/2 | y_I-y_B<=1/2 |
| DI upper height | z_7-z_17 | 1/10 | y_D-y_I<=1/10 |
| DI lower height | z_17-z_7 | 1/10 | y_D-y_I>=-1/10 |
| AE lower horizontal gap | z_0-z_8 | -1/3 | x_E-x_A>=1/3 |
| AE upper horizontal gap | z_8-z_0 | 2/3 | x_E-x_A<=2/3 |
| GD lower horizontal gap | z_12-z_6 | -1/3 | x_D-x_G>=1/3 |
| GD upper horizontal gap | z_6-z_12 | 2/3 | x_D-x_G<=2/3 |

The original actual AB link already gives x_B-x_A>=h_A+h_B>0.
The two original actual EFG links give their required horizontal
gaps. Thus (3), (4), the ten targets and the unchanged original
physical hypotheses imply every line of the enlarged terminal's
guard. That theorem forces the aligned equality configuration;
its retained original BC link and strict weak CD bit contradict
that configuration. The entire context is therefore excluded.

The same ten targets also apply to the
[uniform one-tenth terminal](CB882_UNIFORM_SHARP_TERMINAL.md). In
that version, replace (3) by abs(beta_P)<=1/10 for all seven
loaded originals, retaining beta_A>=0 and beta_D<=0. Every other
hypothesis and every target stays the same. The terminal record
must identify which proved orientation guard it uses.

## 3. What a terminal record must contain

Each use of this rule must give exactly one certificate for every
target in the preceding table, together with the parameter intervals
establishing (3) and the inherited endpoint orders (4). A weighted
certificate must identify the target vector and right side as well
as all its positive row weights. Checking a positive reserve for an
unidentified linear functional would not establish the guard.

If coordinate or parameter bounds were first contracted, the guard
certificate uses the resulting context's necessary rows and box.
Those contractions must have their own preceding certificates.
Their validity cannot be inferred from the eventual sharp-terminal
conclusion.

This rule also permits replacing a completely specified subtree by
a sharp terminal when its root context meets these requirements.
Every sibling of that subtree remains in the cover. Such replacement
does not turn any other pending or unproved case into a closed case.
