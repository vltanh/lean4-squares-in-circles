# Rational rows retaining each original physical frame

This chapter proves continuous necessary inequalities for the complete
[Cb882 parent](CB882_WHOLE_DOMAIN.md). They retain the same original
frame variables in the corner, projection, and pair constraints. They
are suitable for a finite rational table; a search run alone is not a
proof that such a table covers its caller.

For each original P write

\[
 u_P=(a_P,b_P),\qquad v_P=(-b_P,a_P),\qquad
 d_P=|b_P|,\qquad h_P=(a_P+d_P)/2,\qquad g_P=1/(4h_P).
\]

The physical equations are a_P^2+b_P^2=1 and a_P>=d_P>=0.
The letters d_P here denote absolute frame components, not center
coordinates or distances. Every inequality below is valid for the
original physical values; no independently chosen replacement frame
is assumed.

## 1. A rational enclosure of one original frame

Put

\[
 a(w)=\frac{1-w^2}{1+w^2},\qquad
 b(w)=\frac{2w}{1+w^2},\qquad w=\tan(\theta/2).
\]

Let the original parameter lie in a rational interval [l,u] contained
in [-5/12,5/12]. Write m=0 if the interval contains zero, otherwise
the smaller endpoint magnitude, and M for the larger endpoint
magnitude. Monotonicity gives

\[
 a(M)\le a_P\le a(m),\qquad b(l)\le b_P\le b(u),
 \qquad b(m)\le d_P\le b(M).                              \tag{1}
\]

The canonical restriction a_P>=d_P remains in force even when the
rational parameter interval slightly exceeds the physical canonical
range. With a_l=a(l), b_l=b(l), and corresponding upper-endpoint
notation, the chord inequality is

\[
 (a_l+a_u)a_P+(b_l+b_u)b_P
                 \ge1+a_la_u+b_lb_u.                    \tag{2}
\]

Indeed the vector on its left points along the midpoint of the arc;
its scalar product with a point of that arc is minimized at an
endpoint. The arc length here is less than pi. For every rational
w_0, unit-vector Cauchy--Schwarz also gives the tangent inequality

\[
                       a(w_0)a_P+b(w_0)b_P\le1.          \tag{3}
\]

The same physical frame also lies on the unit-circle arc in the
absolute coordinates (a_P,d_P), with absolute half-angle in [m,M].
Applying the identical chord and tangent arguments gives

\[
 (a(m)+a(M))a_P+(b(m)+b(M))d_P
                 \ge1+a(m)a(M)+b(m)b(M),                 \tag{2a}
\]
\[
                       a(w_0)a_P+b(w_0)d_P\le1.          \tag{3a}
\]

These retain the relation between alpha and absolute beta even when
the signed angle interval crosses zero. They introduce no new frame;
a_P^2+d_P^2=1 holds for the same original square. The rational
interval [m,M] may be slightly larger than the physical canonical
interval, just as in (2).

The lower bounds d_P>=b_P and d_P>=-b_P are always valid.
When l>=0, d_P=b_P; when u<=0, d_P=-b_P. If l<0<u,
convexity of absolute value gives its upper secant

\[
 d_P\le m_b b_P+c_b,
 \quad m_b=\frac{|b(u)|-|b(l)|}{b(u)-b(l)},
 \quad c_b=|b(l)|-m_b b(l).                              \tag{4}
\]

Let [H,U] be any proved interval for h_P with H>0. For every
positive rational h_0, convexity of 1/(4h) gives

\[
 g_P\ge\frac1{2h_0}-\frac{h_P}{4h_0^2},
 \qquad
 g_P\le\frac{H+U-h_P}{4HU}.                             \tag{5}
\]

The second inequality is the secant on [H,U]. It is also valid when
H=U. The variable bounds 1/(4U)<=g_P<=1/(4H) follow directly.
Thus (1)--(5) are rational linear necessary inequalities in
(a_P,b_P,d_P,g_P).

## 2. Original-corner halfplanes

For any rational unit vector n=(n_x,n_y), every physical corner obeys

\[
 n\cdot c_P+
 \frac{\sigma n_x+\tau n_y}{2}a_P+
 \frac{\sigma n_y-\tau n_x}{2}b_P\le r_0
 \qquad(\sigma,\tau\in\{-1,1\}),                         \tag{6}
\]

where r_0 is the rational radius ceiling in the whole-domain chapter.
This is the scalar product of n with the actual corner
c_P+(sigma u_P+tau v_P)/2. Likewise n dot c_P<=rho.

Certain rational normals give exact Q-circle halfplanes without a
radius ceiling. If n_x^2+n_y^2=1105, then the right side of (6) can
be replaced by 1105/16. Indeed

\[
 |n|\sqrt Q=\sqrt{1105}\,\frac{\sqrt{1105}}{16}
                         =\frac{1105}{16}.              \tag{7}
\]

The integer pairs (31,12), (32,9), (33,4), (24,23), their coordinate
interchanges, and all independent coordinate signs have this property.
All four actual corner choices are retained for every such normal.

## 3. Two upper planes for a signed product

Suppose k in [a,b] and z in [L,U]. The two linear forms

\[
 P_0=bz+Lk-bL,\qquad P_1=az+Uk-aU                      \tag{8}
\]

both satisfy kz<=P_e. Their exact nonnegative remainders are

\[
 P_0-kz=(b-k)(z-L),\qquad P_1-kz=(k-a)(U-z).
\]

There is no sign restriction on k or z. To bound a signed term
m k Delta, take z=m Delta and compute [L,U] by sorting the two
products m Delta^- and m Delta^+. In particular a negative m is
absorbed before taking the upper plane. Multiplying a pre-existing
upper bound by a negative scalar would not give this rule.

For a sum of several such products, choose either upper plane for
each term and add them. Every resulting linear form is an upper
bound on the original sum. Interval endpoints may coincide; (8)
remains valid in that case.

## 4. A selected physical side axis

Let Delta=c_T-c_P. A selected separating side axis owned by one
of the two originals O in {P,T} is one of the signed forms

\[
 \sigma(a_O\Delta_x+b_O\Delta_y),\qquad
 \sigma(-b_O\Delta_x+a_O\Delta_y).                       \tag{9}
\]

Physical separation requires this form to be at least R_PT,
the common support threshold of P,T. The whole-domain chapter
supplies rational lower bounds R^-_PT and the stronger bounds
1+k_PT(b_P-b_T), 1-k_PT(b_P-b_T).

Each form in (9) has two product terms. Section 3 supplies four
linear upper bounds, and every one must be at least each applicable
lower threshold. These are simultaneous necessary inequalities;
they do not select an additional physical axis.

If two selected links P to T and T to X use the same owned side
normal with the same direction, their exact inequalities add to

\[
                 n\cdot(c_X-c_P)\ge R^-_{PT}+R^-_{TX}.  \tag{10}
\]

Applying the same four upper-plane choices directly to this endpoint
difference gives further necessary rows. The ownership condition
means the very same original frame occurs in both links. A reversed
selected normal is handled by reversing that link's ordered endpoints
before using (10).

## 5. The incircle of one original against the actual other square

For an ordered pair P,T define the physical coordinates

\[
 U=a_P\Delta_x+b_P\Delta_y,\qquad
 V=-b_P\Delta_x+a_P\Delta_y,
 \qquad \Delta=c_T-c_P.
\]

The squared distance from c_T to the closed physical square P is

\[
 \phi(U)+\phi(V),\qquad
 \phi(z)=\bigl(\max\{|z|-1/2,0\}\bigr)^2.
\]

The open radius-1/2 incircle of T is contained in its open interior.
Disjoint original interiors therefore imply

\[
                        \phi(U)+\phi(V)\ge1/4.          \tag{11}
\]

This remains true when the two physical boundaries touch.

Obtain a rational interval for each product in U,V by taking the
minimum and maximum of its four endpoint products. Addition gives
intervals [L_U,U_U], [L_V,U_V] containing the actual U,V. The
function phi is convex. Its endpoint secant on a nondegenerate
interval [L,U] is

\[
 \phi(z)\le mz+c,\qquad
 m=\frac{\phi(U)-\phi(L)}{U-L},\qquad c=\phi(L)-mL.      \tag{12}
\]

On a point interval use m=0,c=phi(L). Write m_U,c_U and
m_V,c_V for these two secants. Equations (11)--(12) give

\[
 m_U a_P\Delta_x+m_U b_P\Delta_y
       -m_V b_P\Delta_x+m_V a_P\Delta_y+c_U+c_V\ge1/4. \tag{13}
\]

Apply Section 3 to the four signed product terms in (13). Every
one of the at most sixteen resulting upper linear forms, plus
c_U+c_V, must be at least 1/4. Zero coefficients may be omitted.
If both slopes vanish and c_U+c_V<1/4, the entire interval cell
is contradictory. These conclusions include negative secant slopes,
signed original angles, and degenerate product intervals.

## 6. Width differences and squared-distance secants

Section 2 of the [G-order proof](CB882_G_ABOVE_D.md) proves

\[
                 |c_T-c_P|\ge1+|h_T-h_P|.
\]

On a center-difference interval Delta_x in [L_x,U_x],
Delta_y in [L_y,U_y], put

\[
 S=(L_x+U_x)\Delta_x-L_xU_x
     +(L_y+U_y)\Delta_y-L_yU_y.
\]

The elementary square secants give S>=|c_T-c_P|^2.
Consequently both linear necessary inequalities

\[
 S\ge1+(a_T+d_T)-(a_P+d_P),\qquad
 S\ge1-(a_T+d_T)+(a_P+d_P)                               \tag{14}
\]

hold simultaneously. They follow by dropping the nonnegative square
of |h_T-h_P| and using 2|h_T-h_P|>=2(h_T-h_P) and
2|h_T-h_P|>=-2(h_T-h_P).
These rows retain the same widths used in every original corner and
actual projection link.

All constructions in this chapter have rational coefficients whenever
the interval endpoints and chosen directions are rational. Their
validity is pointwise on the entire stated intervals. The finite-cover
bookkeeping and exact nonnegative row sums must be supplied separately
for any claimed exclusion of an original domain.
