# The sharp owner-frame terminal at S <= 3/200

## 1. Complete conditional theorem

Consider the actual seven exterior squares with the candidate roles,
core avoidance and containing squared radius `r0 <= Q0=9789/2500`.
Assume the G/T tangent cuts and all intended original signed owner sets.
Select any originally feasible aligned witness on each edge. Let d0 be
the physical frame of the selected ED owner, and put

\[
 \tau=\theta_H-d_0,\qquad
 S=|\theta_B-\theta_A|+|\theta_T-\theta_B|
  +|\theta_D-\theta_T|+|\theta_E-\theta_D|
  +|\theta_H-\theta_G|.
\]

Assume `1/10 <= tau <= 4/25` and `S <= 3/200`.

**Theorem.** The original squares satisfy `r0 >= q_*`. More precisely,
with the stationary weights at `(q_*,u(q_*,tau),tau)`,

\[
\boxed{
 r_0\ge q_*+\mu_H M(q_*,\tau)
 +\sum_{i=A,B,D,E,H}\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac{S}{5000}\ge q_*.}
\tag{1}
\]

The actual forces and offsets are those in Section 2 of
`HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md`.
They use the actual ED-owner frame and preserve every originally selected
witness. All 32 aligned-owner assignments and all ties are included.

The stationary existence theorem proves `M(q_*,tau)>=0`, with its unique
zero at `tau=t_*`. Thus equality forces `S=0`, the unique stationary tilt,
and the five stationary anchors. The full five-parameter equality-family
theorem, including its converse, then applies to the unchanged original
centers. This is not an assertion of isolated-pose uniqueness.

The earlier candidate cuts and the `S<=3/200` capture remain hypotheses.
No preceding contraction to `S<=1/1000` is used. All decimals below are
exact rationals, and no interval subdivision is used.

## 2. One additional stationary strip

Use the notation and proved bounds of
`HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md` and
`HAND_STATIONARY_POSITION_AND_SLIDER_BOUNDS.md`. Write `h=tan(tau)` in
this section only, and retain the positive radical definitions

\[
 r=\sqrt{q-u^2},\quad l=2-u,\quad U=\sqrt{q-l^2},\quad V=3-U,
\]
\[
 Y=\sqrt{q-V^2},\quad v=2-Y,\quad w=\sqrt{q-v^2},
\]
\[
 c=(1+h^2)^{-1/2},\quad s=hc,\quad
 a=s+cu/r,\quad p=lV/(UY),\quad b=p(c+sv/w),
\]
\[
 k_1=2-c(r-1)+su,\quad k_2=1+cv-s(w-1),\quad
 F=k_1^2+k_2^2-q.
\]

On `3.9154<=q<=3.9156`, `.1<=h<=.164`, the earlier theorem gives
`.895<u(q,tau)<1-.6h`, `F_u=0`, and strict position convexity. We improve
only its lower side:

\[
                 \boxed{1-.7h<u(q,\arctan h)<1-.6h.}             \tag{2}
\]

### 2.1 Whole-rectangle derivative estimates

On `.895<=u<=.94`, the existing primitive bounds give

\[
\begin{gathered}
1.741<r<1.765,\quad1.641<U<1.671,\quad1.329<V<1.359,\\
1.438<Y<1.467,\quad .533<v<.562,\quad1.897<w<1.906,\\
.9868<c<.9951,\quad .0995<s<.162,
\end{gathered}
\]
\[
.574<p<.637,\quad .599<a<.700,\quad .582<b<.665,
\quad1.327<k_1<1.422,\quad1.379<k_2<1.470.
\tag{3}
\]

The existing proof already establishes `F_uu>6.6` and `F_ut<5.5` on
this whole rectangle. The same exact derivative formulas give

\[
                         F_{uu}<8.7,\qquad F_{ut}>4.2.           \tag{4}
\]

For explicit rational checks, put
`Z=q/(l U^2)+p q/(Y V^2)`. Then

\[
 Z<\frac{3.9156}{1.06(1.641)^2}
       +\frac{.637(3.9156)}{1.438(1.329)^2}<2.354.
\]

Substitution into the exact formula for F_uu gives the upper bound

\[
2\left[.700^2+.665^2+rac{1.422(.9951)(3.9156)}{1.741^3}
 +1.470\left\{.637(2.354)\left(.9951+rac{.162(.562)}{1.897}\right)
              +\frac{.162(.637)^2(3.9156)}{1.897^3}\right\}\right]<8.7.
\]

The corresponding lower substitution in F_ut is

\[
2\left[
 \{.0995(.741)+.9868(.895)\}(.599)
 +1.327\left(.9868-rac{.162(.94)}{1.741}\right)
 +.938(.582)
 -1.470(.637)\left(-.0995+rac{.9951(.562)}{1.897}\right)
 \right]>4.2.
\]

All factors being bounded have their displayed signs. These are single
rational comparisons over (3), not evaluations on a mesh.

### 2.2 An affine comparison curve and one pivot

For `.1<=h<=.15`, set `u0(h)=1-.7h`; its range is contained in
`[.895,.93]`. With q fixed let `f(h)=F_u(q,u0(h),arctan(h))`.
The chain rule and (4) give

\[
 -2<-.7(8.7)+\frac{4.2}{1+.15^2}<f'(h)
 < -.7(6.6)+\frac{5.5}{1+.1^2}<.83.
\tag{5}
\]

At the single pivot `h=.12,u0=.916`, repeated positive squaring gives,
uniformly in the whole q interval,

\[
\begin{gathered}
1.7539509685<r<1.7540079818,\quad
1.6553984414<U<1.6554588488,\\
1.4517047387<Y<1.4518295674,\quad
1.9012554553<w<1.9013440449,\\
.9928768384<c<.9928768385.
\end{gathered}
\]

In particular the defining formulas imply
`a<.637675`, `b>.6229251`, `k1<1.360556569`, and `k2>1.436874890`.
Thus

\[
 f(.12)<2\{1.360556569(.637675)-1.436874890(.6229251)\}
       =-\frac{1717032775229}{31250000000000}<-.054.
\tag{6}
\]

Integrate the lower bound in (5) to the left and its upper bound to
the right. This gives `f(h)<-.054+2(.02)<0` for `h<=.12`, and
`f(h)<-.054+.83(.03)<0` for `h>=.12`. Position convexity therefore puts
the stationary root above u0 throughout `[.1,.15]`.
For `.15<=h<=.164`, the already proved lower bound `.895<u` suffices,
because `1-.7h<=.895`. This proves (2) without a subdivision certificate.

## 3. The stationary flux and the free sliders

In the following sections h again denotes the HG error, as in the
owner-frame identity; write `z=tan(tau)` for the stationary tangent.
Let the positive normalized stationary edge weights be
`alpha,beta,delta,epsilon,omega`. The five circle masses sum to one.
The earlier whole-domain bounds give

\[
2/3<\omega<.8,\quad .69<\beta<.78,\quad
\alpha<.526,\quad \delta,\epsilon<.87,
\]
\[
 K_A=\alpha r/c<.942,\quad K_B=\beta l<.862,
 \quad K_D=\delta V=\beta Y<1.183,
 \quad K_H=\epsilon k_1<1.238,
\tag{7}
\]

and `1.4<k2<1.45`. Put

\[
 C=K_Ac-\omega s=\omega\{cu+s(r-1)\},
 \qquad \Delta=r-U.
\tag{8}
\]

The force identity `alpha=omega(s+cu/r)` proves (8) directly.
We need the uniform flux ratio

\[
                         \boxed{1<C/\beta<21/20.}    \tag{9}
\]

Indeed, writing `w0=1-u`, (2) gives `.6z<w0<.7z`. Since
`Delta=4w0/(r+U)`, equations (3) imply

\[
 1+.417z<r/U<1+.505z,
 \qquad1+1.041z<u+zr<1+1.165z.
\]

The coefficients follow from the strict rational comparisons
`2.4/(3.436*1.671)>.417` and `2.8/(3.382*1.641)<.505`.
The exact ratio is

\[
 \frac C\beta=(2-u)\frac rU\left(1-rac z{u+zr}\right).
\]

Its lower bound exceeds one because

\[
 (1+.6z)(1+.417z)(1+.041z)-(1+1.041z)
 =.017z+.291897z^2+.0102582z^3>0.
\]

For the upper bound, clearing `1+1.165z` leaves

\[
 \frac{21}{20}(1+1.165z)
 -(1+.7z)(1+.505z)(1+.165z)
 =.05-.14675z-.552325z^2-.0583275z^3>0.
\]

The right side decreases and its value at `.164` is
`67627421649/6250000000000>0`. This proves (9).
A second useful bound follows immediately from (2),(3):

\[
               .9868<C/\omega<1+.165(.164)<1.028.    \tag{10}
\]

The actual G/T tangent cuts give

\[
 7/12\le a_G,a_T<1.396,\qquad0\le b_G,b_T<.797.
\tag{11}
\]

For the transverse bound, `b>=.797` and `b/a<=.8` contradict containment,
because `(.797/.8+.5)^2+(.797+.5)^2-Q0=85969/16000000>0`.
These are actual own-frame coordinates, not nearby comparison sliders.

## 4. Every original first-order reserve

Differentiate the generic exact scalar identity (6) in
`HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md`, retaining the
same owner indicators a,b,d,j,g and actual coordinates (11).
The two reserves on each intrinsic owner alternative are:

\[
\begin{array}{c|c}
\text{alternative}&\text{the two cusp reserves}\\ \hline
 AB,\ a=0&K_B-C,\quad\alpha+C-K_B\\
 AB,\ a=1&\omega s,\quad\alpha-\omega s\\
 TB,\ b=1&K_B-C,\quad\beta+C-K_B\\
 TB,\ b=0\text{ or }DT,\ d=1
   &C-\beta(a_T-1/2),\quad\beta(a_T+1/2)-C\\
 DT,\ d=0&K_D-C,\quad\beta+C-K_D\\
 ED,\ j=0&\epsilon c,\quad\delta-\epsilon c\\
 ED,\ j=1&K_D-C,\quad\delta+C-K_D\\
 HG,\ g=0&C-\omega(a_G-1/2),\quad\omega(a_G+1/2)-C\\
 HG,\ g=1&K_H-C,\quad\omega+C-K_H.
\end{array}
\tag{12}
\]

There are no omitted owners or tie conventions in this list.

### The two small AB/TB reserves

Using `beta=omega*a*U/l`, the exact simplification is

\[
 K_B-C=\omega\{s-a\Delta\}.
\]

Here `0<Delta<.124`, `cu/r<.54`, `a=s+cu/r`, and `s>.0995`.
Consequently

\[
 K_B-C>rac23\{.876(.0995)-.124(.54)\}
                     =\boxed{3367/250000}.           \tag{13}
\]

The other AB reserve is
`alpha+C-KB=alpha(1+Delta)-omega s > omega cu/r`, much larger than .03.
The other T-owned TB reserve is likewise greater than
`beta-omega s>.69-.8(.162)>.03`.

### All remaining alternatives

Equation (9) and (11) give for both free T reserves the lower bound

\[
 \beta\min\{1-.896,\ 13/12-21/20\}
                     =\beta/30>.023.
\tag{14}
\]

The two anchored DT reserves exceed
`.69(1.438-1.05)` and `.69(2-1.467)`, respectively.
For E-owned ED the second reserve exceeds
`.69(1.438/1.359+1-1.467)`; the first is the same anchored reserve.
Both B-owned AB reserves exceed .03 by (3),(7).
For free G use (10): both reserves exceed .03.
For anchored H, use `K_H/omega=k2` and (10); both exceed .2.

D-owned ED has the separately proved small reserve

\[
 \delta-\epsilon c=\epsilon s v/w
                >.69(.0995)(.533)/1.906>.019,        \tag{15}
\]

while its other reserve `epsilon c` is larger.
Thus every ordinary alternative in (12) has reserve greater than .023;
only (13) and the D-owned ED alternative need special remainder bounds.

## 5. One simultaneous error estimate without an E-norm loss

Use the exact owner-frame identity (6) cited above with these stationary
weights. The E force is constant at fixed tau. The actual free squares
are written in their own frames as in that identity, so their scalar
terms depend only on their own incident errors.

On `S<=.015` and `.1<=tau<=.16`, all mixed arguments lie in
`[.085,.175]`. The four varying norm terms have each Hessian entry
bounded by

\[
 .942(.175)+1.238(.015)<.185.
\]

The KB, KD, KH error blocks are disjoint; they are not all added.
Aligned support curvature is below `.87(1+.015/2)<.877`, mixed GA
curvature is below .8, and the free G/T curvature is below
`.8(.797+1.396(.015))<.655`, on separate diagonals. Therefore an ordinary
smooth Hessian row is bounded by `2.52`, giving Taylor coefficient 1.26.

For A-owned AB, its x1 row has no slider term and is bounded by

\[
 .942(.175)+.862(.015)+.526(1+.015/2)+.8
                    =1.507725<1.766.
\]

For T-owned TB, the x2 row also has no slider term, since its own T
projection is fixed on that edge. Its bound is

\[
 .942(.175)+.862(.015)+.78(1+.015/2)+.8
                    =1.76363<1.766.
\]

Both small-reserve rows therefore have Taylor coefficient `.883`.
If D owns ED, x4 appears in neither a norm term, mixed GA term nor a
slider term. Its entire row is bounded by

\[
 .87(1+.015/2)+.87(.175)<1.03,
\]

giving coefficient `.515`. This includes its mixed HE contribution.

The symmetric-Hessian inequality
`|sum H_ij x_i x_j| <= S sum B_i |x_i|` gives all these estimates
simultaneously, with only one shared S. Restoring each sine cusp costs
at most `(.87/12)S^2` per unit error.

For the two smallest reserves the resulting per-unit margin is greater
than

\[
 \frac{3367}{250000}-.883\frac3{200}
                  -\frac{.87}{12}\left(\frac3{200}\right)^2
 =\frac{3307}{16000000}>\frac1{5000}.                \tag{16}
\]

The ordinary and D-owned ED comparisons are, respectively,

\[
 .023-1.26\frac3{200}
       -\frac{.87}{12}\left(\frac3{200}\right)^2
       =\frac{65339}{16000000}>\frac1{5000},
\]
\[
 .019-.515\frac3{200}
       -\frac{.87}{12}\left(\frac3{200}\right)^2
       =\frac{180139}{16000000}>\frac1{5000}.
\]

All loss terms increase with S, so these endpoint comparisons prove
that the entire angular correction is at least `S/5000` on the full
domain, with zero correction at S=0.

## 6. Exact center completion, sharpness and equality

For each actual selected signed gap `g_e>=0`, positivity of the weights
and normalization of the circle masses give

\[
 r_0\ge\sum_{i=A,B,D,E,H}\mu_i|p_i+o_i|^2
                              -\sum_e\lambda_e g_e.
\]

Complete the five squares exactly:

\[
 \mu_i|p_i+o_i|^2+F_i\cdot p_i
 =\mu_i\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
              -F_i\cdot o_i-\frac{|F_i|^2}{4\mu_i}.
\]

At zero errors the stationary geometry has scalar value
`q_*+mu_H M(q_*,tau)`, exactly as in the earlier sharp terminal.
This reference is the same two-frame geometry; only its relation to the
actual error coordinates has changed. Section 5 supplies its complete
nonzero-error correction, proving (1).

All terms after q_* in (1) are nonnegative. At equality, `S=0`,
`M(q_*,tau)=0`, and all five completed center squares vanish. The unique
zero of the stationary family defect gives `tau=t_*`. Since S=0, the
ED-owner frame is now the common A/B/T/D/E frame and H/G share the other
frame: the five anchors are exactly the existing stationary anchors.
The unchanged weak slider and central-square constraints therefore give
the complete five-parameter equality family and its converse.

This proves the full sharp terminal on the larger mismatch interval in
the exact frame delivered by the new tilt-capture theorem. It does not
prove the earlier unrestricted G3--G5 capture hypotheses. No numerical
row table, angle mesh, native computation, Lean compilation or CI run is
used as a proof premise.
