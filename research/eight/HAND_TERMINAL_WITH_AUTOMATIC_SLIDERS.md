# The sharp hand terminal with automatic slider bounds

**Table-free successor.**
[The whole-domain terminal proof](formalization/HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md)
proves this same \(S\le1/1000\) sharp-radius conclusion, its automatic
original-center sliders, and its equality implications with no numerical
rectangle or derivative table. Its explicit linear reserve is \(S/500\),
and it retains the nonnegative actual family defect in place of a
quantitative reduced-curvature estimate. The earlier arithmetic below is
not an input to that proof.

## Theorem and effect on the remaining gates

The two projected-slider bounds need not be separate global capture
hypotheses. They follow from the central core and containment after a
minor enlargement of the terminal rectangle. With this enlargement,
the exact square-completion terminal is valid for \(S\le1/1000\).

More precisely, consider seven exterior unit squares, each avoiding the
open disk of radius 1/12 about the origin, and contained in a centered
disk of squared radius \(r\le9789/2500\). Give them the candidate
roles \((H,G,A,B,T,D,E)\) and canonical quarter offsets
\((-1,-1,0,0,1,1,2)\). Normalize A's actual frame to zero and G's
actual frame to t. Assume

\[
 \frac1{10}\le t\le\frac4{25},\qquad S\le\frac1{1000},
\tag{1}
\]

where S is the sum of the five aligned-edge frame differences in
`HAND_EXACT_CENTER_SQUARE_COMPLETION.md`. Suppose the seven actual
separators have any of that note's 32 allowed owner assignments.
Then

\[
 r\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2+
 \sum_{i=A,B,D,E,H}\mu_i
 \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac{10293}{5000000}S\ge q_*.
\tag{2}
\]

The weights, actual corner offsets and actual center forces are exactly
those of the completed square-completion theorem. Thus the global
candidate hand gate needs the named owners, the tilt interval and
\(S\le1/1000\). It does not also need to capture the signed tangents
or slider coordinates. Coarse tangent exclusions may still help prove
the remaining pair budget, but are optional tools for that budget.

The theorem applies directly to original exterior centers as well as
radially deformed boundary centers. Its proof uses no search and no
new varying-domain arithmetic table.

## 1. Uniform primary-coordinate bounds for every exterior square

In a canonical square frame write its center as \((a,-ua)\), with
\(a\ge0\) and \(|u|\le1\). Put \(b=|u|a\le a\).
The distance from the origin to the square is

\[
 \sqrt{(a-1/2)_+^2+(b-1/2)_+^2}.
\tag{3}
\]

Since the square avoids the open radius-1/12 disk, this distance is
at least 1/12. It is at most \(\sqrt2(a-1/2)_+\), so

\[
 a\ge\frac12+\frac{\sqrt2}{24}>\frac{447}{800}=.55875.
\tag{4}
\]

For the strict numerical bound it suffices that
\(\sqrt2>141/100\), whose squared reserve is \(119/10000>0\).
This argument includes both boundary curves and every original center
between them; it does not assume a boundary equality.

The farthest square corner has squared norm
\((a+1/2)^2+(b+1/2)^2\). Therefore containment gives

\[
 a\le\sqrt{9789/2500-1/4}-1/2<\frac{283}{200}=1.415.
\tag{5}
\]

The final inequality is verified by squaring: at a=1.415 the corner
expression with b=0 exceeds \(9789/2500\) by \(13/8000>0\).
Also, the radius-1/2 disk about any square's center is inside the
square. Since the containing radius is less than 2, every actual
center has norm less than 3/2.

## 2. The automatic enlarged rectangle

The A-to-T path in the aligned-edge tree gives
\(|\theta_T|\le S\). The canonical quarter offset of T is one,
so its center is the rotation through \(\theta_T\) of
\((u_Ta_T,a_T)\). Consequently

\[
 |(p_T)_y-a_T|\le |p_T|\,|\theta_T|\le\frac32 S.
\tag{6}
\]

Equations (1), (4) and (5) imply that the actual transverse projection
\(Z=(p_T)_y\) lies in the strict interior of

\[
 \boxed{\frac{557}{1000}\le Z\le\frac{1417}{1000}.}
\tag{7}
\]

The lower and upper reserves are greater than 1/4000 and 1/2000,
respectively.

G's actual frame is t and its canonical quarter offset is minus one,
so its f_t coordinate is exactly \(-a_G\), regardless of the sign
or size of its signed tangent. For the stationary comparison anchor
\(p_H^0=(h_1+1/2)e_t+(h_2+1/2)f_t\), define

\[
 \eta=(p_G-p_H^0-e_t)\cdot f_t=-a_G-h_2-1/2.
\tag{8}
\]

The completed stationary hand calculation gives
\(-29/20<h_2<-7/5\) throughout the t interval in (1). Thus (4)--(5)
put \(\eta\) in the strict interior of

\[
 \boxed{-\frac{103}{200}\le\eta\le\frac{49}{125}.}
\tag{9}
\]

The lower bound is \(-1.415+1.4-.5=-.515\); the upper bound is
less than \(-.55875+1.45-.5=.39125<.392\).
No tangent-sign or radial-kind restriction has been used.

## 3. The nine owner reserves on the enlarged rectangle

Let \(w=4209/5000=.8418\), the strict upper bound for every edge
weight in the broad terminal. The hand owner table in
`HUMAN_BROAD_TERMINAL_ARITHMETIC.md` proves the following nine old
reserves, before rounding them to a common minimum:

\[
 (.01869,.34656,.3112575,.3984975,.0641425,.03072,
   .021785,.0345425,.0521875).
\tag{10}
\]

Only four change when its old rectangle
\(Z\in[.58,1.4]\), \(\eta\in[-.5,.37]\) is replaced by (7)--(9).
The exact smooth coefficients are already displayed in that hand
table, so no new differentiation is needed:

| Reserve | Change to its lower bound | New strict lower bound |
|---|---|---|
| V1 | None | .0186900 |
| V2 | None | .3465600 |
| V3 | None | .3112575 |
| V4 | None | .3984975 |
| V5 | Subtract .017w for the upper T endpoint | .0498319 |
| V6 | Subtract .023w for the lower T endpoint | .0113586 |
| V7 | None | .0217850 |
| V8 | Subtract .022w for the upper G endpoint | .0160229 |
| V9 | Subtract .015w for the lower G endpoint | .0395605 |

For example, the varying T coefficient is \(-\beta(Z+J)\).
Its two cusp reserves are \(\beta(1/2-Z-J)\) and
\(\beta(1/2+Z+J)\), which explain V5 and V6. The varying G
coefficient is \(-\omega/2+N-\omega\eta\). At the new lower
endpoint it is \(N+.015\omega\), and at the new upper endpoint
its lower cusp reserve is \(N-.392\omega\); these give V9 and V8.
The other owner choices are bounded by the same nine reserves.

Hence every one of the 32 allowed owner assignments has first-order
angular reserve strictly greater than

\[
 \rho S,\qquad \rho=\frac{56793}{5000000}=.0113586.
\tag{11}
\]

The maximum-edge-weight bound is strict, so using w in the four
subtractions is conservative. All entries in the table are fixed
rational arithmetic.

## 4. The exact square-completion remainder still costs less than 9.3S²

Use the exact force identities, completion of the five center squares,
five force-norm trigonometric terms and support/offset cancellations in
`HAND_EXACT_CENTER_SQUARE_COMPLETION.md`, Sections 2--4. None of those
identities depends on the size of the slider rectangle. Its quadratic
remainder constant is unchanged:

\[
 C_2=\frac{26453303561590200213}{2850910772000000000}
 <\frac{232}{25}.
\tag{12}
\]

Only its slider cubic estimate needs updating. The actual center
bound gives \(|X_T|,|Z|,|U_G|,|V_G|\le3/2\).
For the T force,

\[
 F_T\cdot p_T=\beta X_T(\cos u-\cos v)
               +\beta Z(\sin u-\sin v).
\tag{13}
\]

With \(|u|,|v|\le S_C\), the cosine difference has magnitude at
most \(S_C^2/2\), and the remainder after the sine linear term
has magnitude at most \((|u|^3+|v|^3)/6\). Thus (13) loses at
most \(3\beta S_C^2/4+\beta S_C^3/2\).
The G estimate remains \(3\omega S_H^2/4+\omega S_H^3/4\), or
zero for its other owner. Since \(S_C+S_H=S\), the combined slider
loss is bounded by

\[
 \frac{3w}{4}S^2+\frac w2 S^3.
\tag{14}
\]

The old cubic coefficient used \(7w/15\) in its slider term.
Replacing that term by \(w/2\) adds exactly \(w/30\), giving

\[
 C_3=\frac{25398850783}{17277200000}+\frac w{30}
 =\frac{5176729803}{3455440000}<\frac32.
\tag{15}
\]

The strict reserve in the last comparison is
\(6430197/3455440000\). For \(S\le1/1000\), (12) and (15) yield

\[
 C_2S^2+C_3S^3<\left(\frac{232}{25}+\frac3{2000}\right)S^2
 <\frac{93}{10}S^2.
\tag{16}
\]

The enlarged comparison sliders need not themselves define a packing.
Their two reference forces vanish, and all selected reference contact
equalities depend only on their fixed longitudinal coordinates.
The square-completion proof uses their transverse projections for the
first derivative, and the actual center bound for the remainder.
It requires no reference-slider containment or center proximity.

## 5. Sharpness and equality

The completed-square identity, the stationary-family lower bound and
(11), (16) give

\[
 r\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2+\mathcal C
       +(\rho-9.3S)S.
\tag{17}
\]

For \(S\le1/1000\),

\[
 \rho-9.3S\ge\frac{56793}{5000000}-\frac{93}{10000}
 =\frac{10293}{5000000}>0,
\]

which proves (2). Equality forces \(t=t_*\), \(S=0\), and all
five completed center squares to vanish. At zero errors these are
exactly the squared displacements of A,B,D,E,H from their stationary
anchors. The original-center equality pullback and complete
five-parameter classification therefore apply as before. No additional
equality cases arise from enlarging a comparison rectangle.

## 6. Consequence for a full-SAT capture budget

The cyclic argument in `CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md`
remains valid if the five aligned-edge charges are increased from
\(1/50\) to \(1/25\), while keeping
\(\varepsilon=19/10^6\). It first gives
\(S<4\varepsilon/(1/25)=.0019<.004\). The same hand Taylor bound
\(h(d)\ge.49d\) then gives

\[
 S<\frac{\varepsilon}{(1/25)(49/100)}
 =\frac{19}{19600}<\frac1{1000}.
\tag{18}
\]

Thus an appropriate full-SAT budget plus the tilt bound suffices for
the unrestricted candidate terminal, with automatic sliders. The
whole-domain pair inequalities supplying that budget and tilt are
still an active gate; this note does not assume them proved.
