# A low side original forces a high central floor with wide inner mains

November 2, 2026. Computer-assisted discovery, a complete exact
four-variable table, and the physical hand reduction below. No Lean or CI.

## 1. The complete original-square statement

Put

\[
 Q=1105/256,\qquad l=29/60,\quad u=13/12,\quad\rho=91/60.
\]

Retain four original unit squares A,B,C,D in horizontal center-cone
order inside the closed Q-disk. Their outer projection links A--B and
C--D are actual. The middle may be actual or weak, and both inner frames
remain independent. Let S,F be two further distinct original units with

\[
 l\le x_S<u,\qquad y_C<y_S<3/5,
\]

\[
 0\le x_F\le l,\qquad y_F>\max(y_B,y_C).
                                                        \tag{1}
\]

All six original squares are pairwise interior-disjoint.

**Theorem.**

\[
                             y_F-h_F>1/10.               \tag{2}
\]

Horizontal reflection gives the left-side version. Vertical reflection
gives the corresponding lower-side whole-ceiling version. The side
containing S need not be full. No selected outsider cone chain, short
link, or third outsider is assumed.

## 2. Move the two originals into a bounded horizontal range and height order

Write \(g_M=1/(4h_M)\), \(\eta_M=h_M+g_M-1\), and
\(V=\eta_B+\eta_C\). The accepted outer-actual theorem gives

\[
 1/2\le h_B,h_C<13/20,\quad g_B,g_C>5/13,
 \quad V<1/30,
\]

\[
 g_C+\eta_B-1/60<x_C<61/60-h_C,\qquad y_C>-6/5.
                                                        \tag{3}
\]

The last bound follows directly from the outer cone and endpoint
resource, as proved without a selected short-chain premise in
`WEAK_MIDDLE_BOTH_WEAK_COMMON_REDUCTIONS.md`, Section 1.

Before any further narrowing, (1),(3) imply
\(|x_S-x_C|<93/130<4/5\); the reverse horizontal order has the still
smaller bound \(1/30\). The original half-unit disks therefore give
\(y_S-y_C>3/5\), because S is above C. Thus

\[
                              -3/5<y_S<3/5.             \tag{4}
\]

The right endpoint contains the fixed aligned rectangle centered at
\((3/2,0)\), of horizontal halfwidth \(217/480\) and vertical
halfheight

\[
                    c_*+(32/9)V,\qquad c_*=4421/12000.
                                                        \tag{5}
\]

Indeed \(|x_D-3/2|<1/60\), \(g_D>15/32\), and the accepted endpoint
reserve is \(g_D-|y_D|\ge c_*+(32/9)V\).

S's original radius-one-half disk must avoid this rectangle. Using
(4) and the weaker vertical halfheight \(221/600<c_*\) gives

\[
 x_S<503/480-\sqrt{1/4-(3/5-221/600)^2}<49/80.        \tag{6}
\]

The positive-root comparison in the final step has squared reserve
\(38839/5760000\). The first step follows from the squared distance
from S's center to the rectangle. Its horizontal term must be positive,
so no assumed horizontal center order is hidden in this calculation.

The independently certified theorem
`WIDE_MAIN_UPPER_CENTRAL_HEIGHT_HAND_TABLE.md` gives \(y_F>-7/40\).
If F were at or below S, the original disk centers would satisfy

\[
 |x_F-x_S|<49/80,\qquad |y_F-y_S|<3/5+7/40=31/40,
\]

contradicting

\[
 1-(49/80)^2-(31/40)^2=31/1280>0.
\]

Consequently

\[
                             y_F>y_S.                    \tag{7}
\]

This establishes the required vertical order from the full hypotheses,
without a low-floor assumption on either original.

## 3. A monotone original-pair bound removes the main position

Use the complete original-pair clearance K from (3) of the companion
upper-central-height manuscript. In particular its support lower bound
\(\sigma\ge1\) retains both original chiralities and all four owners.

For a folded owner with components \(a\ge b>0\), compare its shallow
and steep expressions at a horizontal gap D:

\[
 \frac{\sigma-aD}{b}-\frac{\sigma-bD}{a}
       =\frac{(a-b)[\sigma-(a+b)D]}{ab}.              \tag{8}
\]

If \(D<1/\sqrt2\), this is nonnegative. At b=0 the shallow owner is
impossible because \(D<1\). Thus throughout that range only the two
steep owners are needed to realize the same K. Their slopes in D lie
in [-1,0]. The minimum of these affine functions is consequently
nonincreasing and 1-Lipschitz. It follows that

\[
                         z+K(C,S,|x_S-z|)
\]

is nondecreasing as a function of z on any interval where the gaps are
below \(1/\sqrt2\).

After (6), every z between \(g_C-1/60\) and the actual \(x_C\)
has \(|x_S-z|<1/4\). For the forward horizontal order the upper
bound is

\[
 49/80-5/13+1/60=763/3120<1/4;
\]

for the reverse order it is below 1/30. Thus (8) applies on that full
interval, including every possible location of the original C.

The endpoint diagonal bound and the individual endpoint resource give
two cone lower bounds for that same original C:

\[
 y_C\ge x_C-129/80,
\qquad y_C\ge x_C-197/120+(32/9)V.                  \tag{9}
\]

The second follows from
\(y_D\ge-1/8+(32/9)V\), \(x_D<\rho\), and the original C--D
cone comparison. The first is the accepted endpoint diagonal bound
\(|x_D|+|y_D|<129/80\), which requires only actual outer links.

Set \(h=h_C\), \(g=1/(4h)\), \(\eta=h+g-1\), and \(x=x_S\).
Since \(V\ge\eta\), \(x_C>g-1/60\), and S is above C, adding
the original C/S clearance to (9) and using the monotonicity just proved
gives the necessary lower height bound

\[
 y_S\ge L:=\max\{-129/80,-197/120+(32/9)\eta\}
          +g-1/60+K(C,S,x-g+1/60).                  \tag{10}
\]

This is the point where the B frame and both main positions are
eliminated. Their contributions have been removed only in a necessary
direction. The original C and S frames are still live in K.

## 4. A low F floor supplies the opposite bound, retaining both original frames

Suppose contrary to (2) that \(y_F-h_F\le1/10\).
Equations (1),(6) imply \(0\le x_S-x_F\le x_S=x\).
The original S/F separation, monotonicity of K in its horizontal gap,
and (7) therefore give

\[
 y_S\le H:=\min\{3/5,1/10+h_F-K(S,F,x)\}.          \tag{11}
\]

Both original S,F frames remain independent in (10)--(11). In particular
F has not been replaced by its inset, and the original support gain
between differently oriented S and F is retained.

If \(L>H\), the original configuration is already impossible.
Otherwise \(y_S\in[L,H]\). Retain the original S and the endpoint
rectangle (5), weakening its vertical halfheight to

\[
 c=c_*+(32/9)\eta,\qquad E=503/480-x,
 \quad W=\max(|L|,|H|)-c.
\]

Write S's folded components as \(a_S\ge b_S\ge0\), and
\(h_S=(a_S+b_S)/2\). The separating-axis theorem for this rectangle
and the original S requires

\[
 T:=\max\{E-h_S,\ W-h_S,
                 a_SE+b_SW-1/2,\ b_SE+a_SW-1/2\}\ge0.       \tag{12}
\]

The first two expressions include both rectangle coordinate owners.
The last two bound all signs and both chiralities of the original S
owners, whose support on their own unit normals is 1/2. Specifically,
the actual adjusted vertical displacement is \(|y_S|-c\le W\),
and the adjusted horizontal displacement is E. Every coefficient used
with W is nonnegative. Thus the maximum in (12) is an upper bound for
the complete physical owner union. Negative W is permitted and is kept
with its correct sign.

## 5. Four parameters, three exact terminal rules

The complete remaining closed root is

\[
 (h_C,t_S,t_F,x_S)\in
 [1/2,13/20]\times[0,1]^2\times[29/60,49/80],         \tag{13}
\]

where \(t=b/a\) parameterizes each independent original folded frame.
Every original counterexample must satisfy simultaneously

\[
                  \eta\le1/30,\qquad L\le H,\qquad T\ge0.
                                                        \tag{14}
\]

`low_side_floor_candidate.json` is a complete binary midpoint cover of
(13), with 44,055 nodes, 22,028 strict leaves, and maximum depth 26.
Its exact terminal conclusions are:

| Strict contradiction | Number of leaves |
|---|---:|
| \(\eta>1/30\) | 0 |
| \(L>H\) | 20,325 |
| \(T<0\) | 1,703 |
| Total | 22,028 |

`verify_low_side_floor.py` reconstructs (10)--(12) and the complete
literal rational root. It imports only the already reviewed exact shape
and physical-clearance helpers, never the numerical producer. Lower
bounds L are rounded downward, upper bounds H upward, and W uses the
endpoints of that resulting containing height interval. The original
axis expressions are evaluated with directed integer interval products,
including negative W. Every exact leaf therefore contradicts at least
one necessary condition in (14).

The complete exact replay passed with least reserve

\[
                       91211994366279/92233720368547758080>0.
\]

Certificate SHA-256:
`a92bed3c0804b76bcd92679da11826ce2ab1ad0fe57ee1dabb5b7088f222a2d3`.
Checker SHA-256:
`cea3a6f8abf3f70f599d7159333e2fbb41c4b2f9352bcf90c9a511fae90b997b`.
The exact report and four rejected changed-root, illegal-axis,
missing-child, and false-terminal controls are saved beside the source.

The root includes all equality faces and zero slopes. The tree has no
unresolved frontier. Since every original counterexample to (2) would
belong to (13) and satisfy (14), the complete cover rules it out. This
proves (2) on the full six-original hypotheses (1). It is a reusable
caller lemma, not by itself a new whole-mask closure.
