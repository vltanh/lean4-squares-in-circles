# Aligned-owner endpoints of a strictly weak CD separator

Retain the original physical squares C,D in the normalized 001/00
caller. Write their canonical frames as
u_P=(alpha_P,beta_P), v_P=(-beta_P,alpha_P), where
alpha_P>0, alpha_P^2+beta_P^2=1, and
h_P=(alpha_P+|beta_P|)/2. The strictly weak CD bit means

\[
                        x_D-x_C<h_C+h_D.                 \tag{1}
\]

Suppose the selected physical separator is the positive primary
axis of C. Its necessary inequality is

\[
 (c_D-c_C)\mathbin{\cdot}u_C
 \ge \frac{1+|u_C\mathbin{\cdot}u_D|
                    +|u_C\mathbin{\cdot}v_D|}{2}.        \tag{2}
\]

Then beta_C cannot vanish. Indeed, beta_C=0 gives alpha_C=1,
u_C=(1,0), and h_C=1/2. Substituting into (2) gives

\[
 x_D-x_C\ge\frac{1+\alpha_D+|\beta_D|}{2}=h_C+h_D,
\]

contradicting (1). This argument allows contact in the physical
separator and uses the strict weak bit only in (1).

In a rational frame-interval cover, the rule therefore closes any
cell whose retained separator is +u_C and whose entire C interval
is the singleton w_C=0. A cell merely containing zero is not closed
by this rule. The conclusion uses neither an H-order assumption nor
any condition on the other seven originals.

The same observation covers every aligned-owner endpoint of the
three-case CD-axis union. Put d=x_D-x_C and v=y_D-y_C. The
selected CD cone gives 0<v<=d. If the selected owner O is aligned,
its primary and secondary normals are (1,0) and (0,1), and the
support threshold on either is h_C+h_D. Thus the complete endpoint
table is

| Retained separator | Required singleton | Necessary separation | Contradiction |
|---|---|---|---|
| +u_C | w_C=0 | d>=h_C+h_D | d<h_C+h_D |
| +v_C | w_C=0 | v>=h_C+h_D | v<=d<h_C+h_D |
| +v_D | w_D=0 | v>=h_C+h_D | v<=d<h_C+h_D |

Only the selected owner's angle must vanish. The other original's
frame remains independent. The rule also applies to +u_D when that
axis is retained in a larger physical-axis union. It requires no
radius hypothesis and therefore also applies in a closed-Q cover
that retains the strict weak CD condition.
