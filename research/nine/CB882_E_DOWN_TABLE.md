# A seven-terminal rational exclusion of E below A

**Theorem.** In the complete original Cb882 caller,

\[
                         y_E-y_A\ge g_A+g_E.
\]

The endpoint-inset theorem makes the A/E inset separation vertical.
We exclude its downward alternative. The argument uses the seven
terminal row sums printed below and in the linked appendices. There
are no unprinted angle subdivisions, omitted frame signs, numerical
feasibility premises, or local-neighborhood hypotheses.

All nine original physical squares and their independent frames are
retained. The radius hypothesis is the closed Q-disk, where
Q=1105/256. Set

\[
 r_0=83103850693/40000000000,\qquad \rho=91/60.
\]

The rational inequality r_0^2>Q makes r_0 an outward radius ceiling.
The strict bounds in the parent chapters may all be weakened to the
closed inequalities used in this table.

## 1. Caller, variables, and the complete seven-case cover

Use the original normalization and whole-parent deductions of
[the geometric reduction](CB882_GEOMETRIC_REDUCTION.md), including
x_H<-1/40 and y_B-y_H>203/240. The
[G-order theorem](CB882_G_ABOVE_D.md) gives
y_G-y_D>=g_D+g_G. Assume for contradiction
y_A-y_E>=g_A+g_E. The
[E-down height and axis theorem](CB882_E_DOWN_ROUTING.md) applies.
The [E-down B/F theorem](CB882_E_DOWN_F_ABOVE_B.md), whose separate
endpoint argument does not use this table, gives
y_F-y_B>=g_B+g_F.

Index A,...,I by i=0,...,8. The 54 variables z_q are

\[
 z_{2i}=x_i,\quad z_{2i+1}=y_i,\quad
 z_{18+3i}=a_i,\quad z_{19+3i}=b_i,\quad z_{20+3i}=d_i,
 \quad z_{45+i}=g_i.
\]

Here u_i=(a_i,b_i), v_i=(-b_i,a_i), d_i=|b_i|,
h_i=(a_i+d_i)/2, g_i=1/(4h_i), and
w_i=tan(theta_i/2). Thus d_i in this chapter is an absolute frame
component, not a center gap. Define

\[
 a(w)=(1-w^2)/(1+w^2),\qquad b(w)=2w/(1+w^2).
\]

The initial closed intervals, before the selected AE axis is imposed,
are as follows. All are whole-parent bounds or the consequences of
E below A in the cited routing theorem. The H-height ceiling is
743/1920-203/240=-881/1920.

| Original | x | y | w |
|---|---|---|---|
| A | [-91/60,-23/16] | [-1/3,1/4] | [0,1/10] |
| B | [-31/60,-7/16] | [-67/120,743/1920] | [-1/24,1/24] |
| C | [29/60,57/80] | [-91/60,-77/120] | [-5/12,5/12] |
| D | [4/3,91/60] | [-91/60,91/60] | [-5/12,0] |
| E | [-7/5,-29/60] | [-91/60,-3/5] | [-5/12,5/12] |
| F | [-31/60,31/60] | [-91/60,91/60] | [-5/12,5/12] |
| G | [29/60,91/60] | [-91/60,91/60] | [-5/12,5/12] |
| H | [-91/60,-1/40] | [-91/60,-881/1920] | [-5/12,5/12] |
| I | [-91/60,91/60] | [-91/60,91/60] | [-5/12,5/12] |

Write Delta=c_E-c_A. The complete three-case AE cover is

| AE case | Actual normal toward E | Additional sign |
|---|---|---|
| A-secondary | -v_A | Already w_A>=0 |
| E-secondary | -v_E | Either sign of w_E |
| E-primary | +u_E | w_E<=0 |

The physical inequality in each case is n dot Delta>=R_AE.
For either secondary case, the complete C-slant routing gives the
following three original CD possibilities, directed from C toward D:
+u_C with w_C>=0; +v_C with w_C<=0; or +v_D. These are the
three CD owner-axis cases already proved exhaustive in
[the whole-domain chapter](CB882_WHOLE_DOMAIN.md). The E-primary
case will close without a CD choice. Consequently the seven cases
in Section 4 cover the entire downward A/E alternative.

## 2. Literal rows and their mathematical sources

The [row appendix](CB882_E_DOWN_ROWS.md) prints every row used in
any certificate, including its complete sparse rational coefficients
and right side. Each means c dot z<=B. A row ID such as C003.R1442
has meaning only in the indicated context; its number is an identifier,
not a reference to an external list or program.

Each context starts by printing all center, frame-parameter and
54-variable intervals. For a parameter interval [l,u], let m=0
when it contains zero and otherwise m=min(|l|,|u|); let
M=max(|l|,|u|). The displayed frame intervals are

\[
 [a(M),a(m)],\qquad [b(l),b(u)],\qquad [b(m),b(M)].
\]

For h use H=(a(m)+b(m))/2 and

\[
 U=\begin{cases}(a(M)+b(M))/2,&M<2/5,\\
                 707107/1000000,&M\ge2/5.
    \end{cases}
\]

These contain every physical halfwidth: on the canonical interval
h increases with |w|, and (707107/1000000)^2>1/2. The g interval
is [1/(4U),1/(4H)]. The physical canonical inequality a>=d is
retained even in the harmless rational tails beyond the canonical
parameter endpoints.

The labels in the row appendix refer to these explicit families:

| Family label | Proved necessary row |
|---|---|
| bound upper/lower | The displayed interval bound on z_q |
| frame chord/tangent; canonical frame; abs positive/negative/exact | Equations (1)--(4) of [physical frame rows](CB882_PHYSICAL_FRAME_ROWS.md) |
| width lower/upper; inset tangent/secant | H<=h<=U and equation (5) of that chapter; the tangent label supplies h_0 |
| corner; center; exact Q tangent | Equations (6)--(7) of that chapter; the label supplies the normal and actual corner signs |
| actual i j | x_i-x_j+h_i+h_j<=0 for AB, BC, EF or FG |
| cone i j s | x_i-x_j+s(y_j-y_i)<=0 for AB, BC, CD, EF or FG |
| proxy i j ax s | s(c_i-c_j)_ax+g_i+g_j<=0 for the indicated proved inset order |
| sat; frame sat | The four signed-product upper planes for the indicated actual owner-axis choice, against R^- or 1 plus either signed beta difference times k; [physical frame rows](CB882_PHYSICAL_FRAME_ROWS.md), Sections 3--4 |
| frame distance | Square secants against 1 plus either signed beta difference times 2k; [frame-coupled pair rows](FRAME_COUPLED_PAIR_ROWS.md) |
| width mismatch distance | Equation (14) of [physical frame rows](CB882_PHYSICAL_FRAME_ROWS.md) |
| actual square incircle | Equations (11)--(13) of that chapter, including every indicated signed-product upper-plane choice |
| pair cap | 46(s c_i,ax-h_i)+(27/2)(s c_j,ax-h_j)<=211/4, the original two-square cap in the whole-domain chapter |
| incircle inset | The secant rule described immediately below |

In a frame-distance or selected-axis row the rational k is

\[
 k=\max\left(0,\min_{t\in\{l_i,u_i\},\,v\in\{l_j,u_j\}}
              \frac{1+tv-|t-v|}{2(1-tv)}\right),
\]

as proved in the frame-coupled chapter. The threshold R^- is the
maximum of 1 and the minimum of the four endpoint values

\[
 \frac{1+a(t)a(v)+b(t)b(v)+|a(t)b(v)-b(t)a(v)|}{2},
\]

with the value 1 also included in the minimum when the two parameter
intervals overlap. This is the whole-domain pair-support bound.

For `incircle inset i j`, set g_0=1/(4U_i). The actual inset of i
contains the closed aligned square of halfwidth g_0. Hence the
original radius-1/2 incircle of j has center at distance at least
1/2 from that smaller square. For Delta=c_j-c_i this says

\[
 \sum_{ax=0}^1\bigl(\max\{|\Delta_{ax}|-g_0,0\}\bigr)^2
                       \ge1/4.
\]

On each displayed difference interval [L,U], replace the convex
summand f by its upper secant
[(f(U)-f(L))/(U-L)]z+f(L)-L(f(U)-f(L))/(U-L).
At L=U use the constant f(L). Adding the two upper secants gives
the printed necessary linear inequality.

The remaining named geometric rows, written before normalization,
are as follows. Their sources are the whole-domain reduction,
the inner-frame and endpoint-inset chapters, and the E-down routing
chapter already cited.

| Label | Inequality |
|---|---|
| CD inset | x_C-x_D+g_C+g_D<=0 |
| CD v | y_C-y_D<=-2/3 |
| BH down cone s | y_H-y_B+s(x_H-x_B)<=0 |
| BH down inset | y_H-y_B+g_B+g_H<=0 |
| HI x order | x_H-x_I<=0 |
| C slant | 7x_C/8+y_C<=-7/32 |
| long span | x_A-x_D+h_A+2h_B+g_D<=-1 |
| left cap load | -46x_C-(27/2)x_G+46h_C+(27/2)h_G<=-27/4 |
| A unary | -x_A-rho a_A<=0; endpoint-inset chapter, Section 1, equation (6) |
| D unary inset | x_D-g_D<=17/16 |
| C unary inset transfer | x_C+g_C<=17/16 |
| B unary inset transfer | x_B+h_B<=1/16 |
| A unary inset transfer | x_A+h_A+2h_B<=1/16 |
| A signed height inset reserve | y_A-g_A<=-1/4 |

There is also a conditional `CD C primary span frame` row. It is
used only after selecting +u_C and w_C>=0. If w_C^+ is the upper
endpoint of C's parameter interval, put
k_C^-=(a(w_C^+)-b(w_C^+))/2 and h_C^+=U_C. The proved positive-C
primary span bound in the whole-domain chapter is

\[
 x_C-x_D+g_C+\frac{a_D}{2}
                 +\frac{\max(0,k_C^-)}{2h_C^+}d_D\le0.
\]

All printed rows are divided by the positive rational
max(1,max_q |c_q|), where c_q are their unnormalized left-side
coefficients. This normalization changes neither validity nor sign.
It explains the rational coefficients in the literal appendix; the
row sums always use those printed normalized rows.

## 3. How to check a bound deduction or a terminal sum

The [certificate appendix](CB882_E_DOWN_CERTIFICATES.md) gives
positive integer row weights. Let their weighted sum be

\[
                            A\cdot z\le B.
\]

For any rational vector t, the displayed context box
z_q in [L_q,U_q] gives the exact lower bound

\[
 \mathcal L(t)=\sum_{t_q\ge0}t_qL_q+\sum_{t_q<0}t_qU_q.
\]

A terminal certificate checks \mathcal L(A)-B>0. This contradicts
the weighted sum. The appendix prints a positive rational lower
bound for this reserve at each of the seven terminals.

A bound deduction is printed as (k,s,b), where s is -1 or +1.
It asserts s z_k<=s b. Subtract s*10^6 from component k of A
to form t. The required rational comparison is

\[
                10^6 s b-\bigl(B-\mathcal L(t)\bigr)\ge0.
\]

Indeed 10^6 s z_k<=B-t dot z<=B-\mathcal L(t).
Every deduction in a context uses that same context's original
box and rows. Deduction lines are simultaneous, so their order in
the appendix is immaterial.

After a bound context, intersect each center interval with all its
deduced bounds. For a beta variable b_i, let [p,q] be its resulting
interval. A printed narrower w interval [l',u'] is valid whenever
its changed lower endpoint satisfies b(l')<=p and its changed upper
endpoint satisfies b(u')>=q. Unchanged endpoints are inherited.
Monotonicity of b(w) on [-5/12,5/12] proves this rule; all these
comparisons are rational. The actual printed endpoints are multiples
of 1/65536, but that grid is not a premise of the rule. Recompute
the frame and g bounds by Section 2. A CD sign condition is an
additional intersection with [0,infinity) or (-infinity,0].

## 4. Complete context and terminal table

Every context below has its full input box printed in the row
appendix. `After C` means the simultaneous contractions from C,
followed by the indicated additional condition. An omitted new
condition means all previous conditions are inherited. All three
roots also carry E below A and G above D. The B/F upper order is
a proved consequence of E below A, and is added where indicated.

| Context | Input | Additional condition | Result |
|---|---|---|---|
| C000 | Initial box | AE A-secondary | 37 bound deductions |
| C001 | After C000 | F above B | 22 bound deductions |
| C002 | After C001 | CD +u_C, w_C>=0 | Contradiction |
| C003 | After C001 | CD +v_C, w_C<=0 | 38 bound deductions |
| C004 | After C003 | None | Contradiction |
| C005 | After C001 | CD +v_D | 38 bound deductions |
| C006 | After C005 | None | Contradiction |
| C007 | Initial box | AE E-secondary | 37 bound deductions |
| C008 | After C007 | F above B | 21 bound deductions |
| C009 | After C008 | CD +u_C, w_C>=0 | Contradiction |
| C010 | After C008 | CD +v_C, w_C<=0 | 39 bound deductions |
| C011 | After C010 | None | Contradiction |
| C012 | After C008 | CD +v_D | 39 bound deductions |
| C013 | After C012 | None | Contradiction |
| C014 | Initial box | AE E-primary, w_E<=0 | 37 bound deductions |
| C015 | After C014 | F above B | Contradiction |

Thus the A-secondary branch closes at C002,C004,C006; the
E-secondary branch closes at C009,C011,C013; and the E-primary
branch closes at C015. There are nine bound contexts containing
308 deductions, seven contradiction contexts, 1111 literal rows,
and 5833 positive integer weight occurrences. Every appendix row
is used by at least one of these sums.

The physical AE and CD covers were established before the table;
the table's seven terminals exhaust them. Therefore E below A is
impossible in the original Cb882 caller. The vertical endpoint-inset
theorem now yields E above A, as asserted.

The proof data are the displayed rational boxes, rows, weights and
finite cover. Computation was used to find and check these numbers;
neither a search program nor its feasibility verdict is a premise.
