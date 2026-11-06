# F lies above B throughout the nonnegative-A, nonpositive-D caller

Retain the normalized original-nine 001/00 caller: all independent
physical frames, all original pairs and corners in the closed disk
Q=1105/256, actual AB, BC, EF, FG, strictly weak CD, the five
selected center cones, and y_D-y_C>2/3. Suppose A's canonical tilt
is nonnegative and D's is nonpositive. Then

\[
                       \boxed{y_F-y_B\ge g_B+g_F}.       \tag{1}
\]

There is no H-order or alternate-chain escape hypothesis. In
particular this theorem applies to the original C887, Cd402, and
Cb882 callers. The original H and I remain unrestricted physical
squares; the finite row sums below involve only A through G.

The [endpoint-inset theorem](00100_ENDPOINT_INSETS_ARE_VERTICAL.md)
covers both A/E vertical orders. On E-down, the
[endpoint bound](CB882_E_DOWN_ENDPOINT.md) and
[middle-height proof](CB882_E_DOWN_F_ABOVE_B.md) already give (1).
Those arguments use no H row; their dependencies are recorded in
[the transfer-scope audit](00100_REMAINING_ORIGINAL_TRANSFER_SCOPE.md).
It remains to consider E-up. The
[G-order theorem](CB882_G_ABOVE_D.md) and
[B/F inset theorem](CB882_BF_VERTICAL.md) reduce its contrary to

\[
 y_E-y_A\ge g_A+g_E,\qquad
 y_G-y_D\ge g_D+g_G,\qquad
 y_B-y_F\ge g_B+g_F.                                    \tag{2}
\]

The entire domain (2) is excluded by these literal rational appendices:

* [103 necessary rows in two contexts](00100_C_E_UP_F_DOWN_ROWS.md).
* [36 simultaneous bound deductions and one contradiction](00100_C_E_UP_F_DOWN_CERTIFICATES.md).

There is no angle subdivision or chosen C/D physical side normal.
Every coefficient, positive integer weight, and reserve is printed.
The argument consists of the continuous inequalities below and the
displayed rational arithmetic.

## 1. Variables and the initial context

Number A through I by 0 through 8. To retain the common variable
numbering of the physical-row chapters, use

\[
 z_{2i}=x_i,\quad z_{2i+1}=y_i,\quad
 z_{18+3i}=a_i,\quad z_{19+3i}=b_i,\quad
 z_{20+3i}=d_i=|b_i|,\quad z_{45+i}=g_i,
 \qquad h_i=(a_i+d_i)/2.                                \tag{3}
\]

The actual orthonormal frame is (a_i,b_i),(-b_i,a_i), with
a_i>=|b_i| and a_i^2+b_i^2=1. Put w_i=tan(theta_i/2), so

\[
 a(w)=\frac{1-w^2}{1+w^2},\qquad
 b(w)=\frac{2w}{1+w^2}.
\]

The C000 table prints all initial intervals. The main-chain span,
center bounds, and inner-frame theorem give

\[
\begin{gathered}
 -\rho<x_A<-23/16,\quad -31/60<x_B<-7/16,\quad
 29/60<x_C<57/80,\quad 4/3<x_D<\rho,\\
 x_E<-29/60,\quad |x_F|<31/60,\quad x_G>29/60,
 \qquad \rho=91/60.
\end{gathered}
\]

The relevant inputs are the
[inner-frame theorem](00100_INNER_FRAME_AND_DOWNWARD_CONE.md),
[endpoint-inset theorem, Section 1](00100_ENDPOINT_INSETS_ARE_VERTICAL.md),
and [geometric reduction, Section 1](CB882_GEOMETRIC_REDUCTION.md).
Only their main-chain statements are used here. The complete
[nonpositive-D C-slant proof](00100_C_SLANT_LOWER_COMPLEMENT.md)
gives y_C+(7/8)x_C<-7/32, hence y_C<-77/120; its combination
with BC gives y_B<743/1920. The
[left-cap theorem](CD402_H_ABOVE_B.md) gives |y_A|<1/4 and
x_E+g_E>-15/16. No B/H cone, inset order, or contracted H bound
is among these inputs.

The initial frame intervals are
w_A in [0,1/10], w_B in [-1/24,1/24],
w_D in [-5/12,0], and [-5/12,5/12] for every other original.
They are closed outer enclosures of the original canonical frames;
the actual relation a_i>=|b_i| remains necessary throughout.
H and I have only their universal boxes, and their coordinates have
zero coefficient in every printed row and every deduction.

Here are exact rules for all component boxes in both contexts. For
w in [l,u], set m=0 if l<=0<=u and otherwise
m=min(|l|,|u|), and M=max(|l|,|u|). The a,b,d intervals are
[a(M),a(m)], [b(l),b(u)], and [b(m),b(M)]. Set

\[
 H=\frac{a(m)+b(m)}2,\qquad
 U=\begin{cases}(a(M)+b(M))/2,&M<2/5,\\
 707107/1000000,&M\ge2/5.
 \end{cases}
\]

Then g is in [1/(4U),1/(4H)]. The rational upper bound exceeds
1/sqrt(2), since 707107^2-500000000000=309449>0.
These are enclosures of each unchanged original frame.

## 2. Necessary rows

A sparse row with entries `q:c` and right side t means
sum(c z_q)<=t, with unlisted coefficients zero. Row identifiers
distinguish literal inequalities only within their stated context.

| Printed family | Mathematical source |
|---|---|
| Bounds, frame chord, canonical frame, absolute component, width, inset tangent and secant | The context intervals and [physical-frame rows](CB882_PHYSICAL_FRAME_ROWS.md), Section 1 |
| Original corner and center, exact Q tangent | Physical-frame rows, Section 2 |
| Actual link, center cone, CD inset and height | The retained original caller and its original aligned insets |
| C-slant | The complete nonpositive-D C-slant theorem |
| Long span, C upper width, unary inset transfers | Main-chain span and geometric reduction, Section 1 |
| A unary | Endpoint-inset theorem, Section 1, equation (6) |
| Physical pair cap | [Foundation](FOUNDATION.md), Part B |
| A/E, D/G, B/F vertical inset rows | The three hypotheses (2) |
| Universal left cap for E | The left-cap theorem, conclusion (L) |
| Width-mismatch distance | Physical-frame rows, Section 6 |

For clarity, the C upper-width row is x_C-h_C<=r_+-2.
The CD insets and x_D+h_D<=sqrt(Q) give
x_C+g_C<=x_D-g_D<=sqrt(Q)-(h_D+g_D)<=sqrt(Q)-1.
Subtract h_C+g_C>=1 to obtain the stated row.
Here r_+=83103850693/40000000000 is the rational radius ceiling
used for ordinary corner rows. Its square exceeds Q by
4436580249/1600000000000000000000. Exact Q-tangent rows use
normal squared norm 1105 and right side 1105/16.

Positive normalization of any necessary row preserves validity.
The printed coefficients already include it. Each row is valid on
its entire context box, with no restriction on a physical pair's
actual separating owner or side axis.

## 3. Checking the simultaneous deductions

For a context with bounds z_q in [l_q,u_q], let a positive weighted
sum of its literal rows be A dot z<=B. Define the box minimum

\[
 \mathcal L(v)=\sum_{v_q\ge0}v_q l_q+
                   \sum_{v_q<0}v_q u_q.                 \tag{4}
\]

A deduction `(k,s,b)`, s in {-1,1}, asserts s z_k<=s b. Its
printed reserve is a nonnegative lower bound for

\[
 10^6s b-\left(B-\mathcal L(A-10^6s e_k)\right).         \tag{5}
\]

The row sum and the original box then imply
\(10^6s z_k\le B-\mathcal L(A-10^6s e_k)\le10^6s b\).
All 36 deductions in C000 use the same C000 box. No deduction
within that batch uses another deduction from the batch.

For the terminal sum, the strictly positive reserve is

\[
                         \mathcal L(A)-B>0.              \tag{6}
\]

This is incompatible with A dot z<=B.

## 4. The single transition and contradiction

Intersecting C000 with deductions D000 through D035 gives the
center intervals printed in C001. Since b(w) is strictly increasing
on [-5/12,5/12], the following positive differences certify every
changed frame endpoint; negative lower endpoints also use
b(-w)=-b(w).

| w | Component upper bound t | b(w)-t |
|---|---|---|
| 2285/32768 | 69391/500000 | 4555066841/539481524500000 |
| 441/16384 | 53783/1000000 | 2964098329/268629937000000 |
| 13573/32768 | 707107/1000000 | 2041236629/1257968153000000 |
| -73/2048 | -35609/500000 | 40731497/2099816500000 |

The original A lower endpoint is retained. H and I are unchanged.
The other component intervals of C001 follow from the formulas in
Section 1. This is an outer enclosure of the same original frames,
not a choice of new orientations.

The terminal C001.X combines its thirteen displayed rows with the
printed positive integer weights. Its reserve in (6) is at least

\[
                         \frac{1053924491}{25000}>0.
\]

Every original satisfying (2) reaches C001, so the contrary is
empty. The exhaustive B/F vertical alternatives give (1) on E-up.
The previously proved E-down implication completes (1) throughout
the stated nonnegative-A, nonpositive-D caller. The configurations
with F above B still require a separate exclusion.
