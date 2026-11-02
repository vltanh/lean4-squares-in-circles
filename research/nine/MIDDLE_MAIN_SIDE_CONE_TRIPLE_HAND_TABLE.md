# A middle-height main forces a high side cone triple

November 2, 2026. Both complete finite roots have passed independent exact
replay. The low-right table has 19,387 leaves; the low-floor table has
2,821,264 leaves. The latter uses the original lower-side consequence
y1>-17/50. Final assembly and code-review records are listed below.
Numerical optimization and floating subdivision were discovery only.
No Lean, Lake, or CI.

Put

\[
 Q=1105/256,\quad l=29/60,\quad u=13/12,\quad G=15/31,
 \quad A=503/480,\quad B=937/480,
\]
\[
 c_*=4421/12000,\qquad K=80669/93000,\qquad J=23/150.
\]

## 1. Complete original-square statement

Retain four original physical squares in an actual horizontal projection
chain whose consecutive centers also form a horizontal cone chain.
Retain three distinct original outsiders L,P,R forming a horizontal cone
chain with both links weak. All independent frames, original corner
constraints, and physical pair predicates remain in force. Suppose the
common upper routing has been made, and

\[
 x_L\le-l,  x_R\ge l,  y_P>\max(y_1,y_2),  y_L>y_1,  y_R>y_2,
 \qquad y_1\ge-7/20.
\tag{1}
\]

For the low-floor conclusion additionally suppose that y1>=-17/50.
The original lower full-side unit supplies this stronger premise by the
complete 74-row theorem `LOWER_SIDE_MAIN_SEVENTEEN_FIFTIETHS_HAND_TABLE.md`.
The low-right conclusion uses only y1>=-7/20 as in (1).

The two conclusions are

\[
                       y_P-h_P>1/10,\qquad y_R>3/5.
\tag{2}
\]

The established common cone-three routing supplies
`|xP|<23/60`, and every outsider has `|x|<u`. The accepted inner-main height band `|y2|<139/120` and the
same-half-plane physical clearance greater than 97/100 give
`yR>-139/120+97/100=-113/600`. The proof retains
the original P frame simultaneously on both short links. Neither remaining outsider is replaced. In the full-side-middle caller,
one is the original lower side unit that supplies y1>=-17/50; the other
original square remains unrestricted. Both conclusions concern the same
retained original units inside the original nine.

### 1.1. A short bad-floor center cut

In the low-floor branch, xP>-1/5. The original L has
`yL>y1+97/100>=31/50>3/5`. If xP<=-1/5, P lies in its main's half-plane,
so the original own-half central clearance gives
`yP>y1+59/60>=19/30>3/5`.
A high central original with bad floor and a high left-side original has
xP>-1/5 by the two-disk convex-arc argument in Section 2 of
`ACTUAL_FOUR_131_BOTH_SIDE_UPPER_CLOSED_HAND_PROOF.md`. That argument
uses only these two original units, their contained radius-one-half disks,
and the universal center bound rho; it has no occupancy or cap premise.
The evaluator intersects its necessary x interval with the closed bound
x>=-1/5, retaining the strict boundary outward.

## 2. The shared endpoint resource, including the main tilt

Write `e=h1-1/2`, `U=h0+h3-1`, `S=|y0|+|y3|`. Summing the actual
main gaps and using the universal center bound gives

\[
                  0\le e<1/60,\qquad U+2e<1/30.
\tag{3}
\]

For either endpoint write X=|xE|, Y=|yE|. Since X>Y, an actual
outward-quadrant corner always implies
`Q>=(X+kE)^2+(Y+hE)^2`: if its offsets are `(hE,kE)`, compare the
two squared norms. Sum these two synthetic corner vectors and apply the
vector triangle inequality. The result is

\[
4Q\ge (4+2e-73U/1000)^2+(1+U+S)^2.
\]

Here the accepted endpoint bound
`h+sqrt(1/2-h^2)>=1-(73/1000)(h-1/2)` is used. It follows that

\[
                 S+(37/50)U+(64/9)e\le1/8.
\tag{4}
\]

Indeed, if the left side is at least `1/8`, the second squared quantity
is at least `9/8+(13/50)U-(64/9)e`, which is positive by (3). Subtracting
`4Q` from the resulting sum gives exactly

\[
 U/1000+(2e-73U/1000)^2+((13/50)U-(64/9)e)^2.
\]

This is nonnegative and forces `U=e=0` if equality can hold; the original
inequality then gives `S<=1/8`. This proves (4), including its boundary.

For the two original outer endpoints define their actual symmetric inset
heights `c0=g0-|y0|` and `c3=g3-|y3|`. The accepted individual endpoint
bound gives `ci>=c_*`, and plainly `ci<=1/2`. Also

\[
\begin{aligned}
 c_0+c_3
 &\ge {1\over1+U}-1/8+(37/50)U+(64/9)e\\
 &\ge K+(64/9)e.
\end{aligned}
\tag{5}
\]

The first inequality uses `g0+g3>=1/(h0+h3)`. The function
`1/(1+U)-1/8+(37/50)U` decreases on `[0,1/30]`: its derivative is at
most `-900/961+37/50<0`. Its value at `1/30` is exactly `K`.

Use `c0`, the actual left endpoint inset height, as one live variable in
`[c_*,1/2]`. The left endpoint contains the reflected rectangle
`[-B,-A] x [-c0,c0]`; the right endpoint contains

\[
 [A,B]\times[-c_R,c_R],\qquad
 c_R:=\max\{c_*,K-c_0+(64/9)e_{\rm need}\}.
\tag{6}
\]

In the low-right proof take `e_need=0`. In the low-floor proof it is the
necessary main-tilt lower bound derived below. Every rectangle is contained
in its original endpoint. No endpoint frame is reset.

## 3. Main clearances retaining the original outsider chirality

For a folded outsider frame put

\[
 a=(1+t^2)^{-1/2},\quad b=ta,\quad
 h=(a+b)/2,\quad k=(a-b)/2,\quad 0\le t\le1,
\]

with signed side directions `(a,s*b),(-s*b,a)`, `s in {-1,1}`.
For a unit to the right and above the left inner main, define

\[
 r_-(h,a,b,\delta)=\min\{h,(1/2+\delta b)/a\},
\]
\[
 r_+(h,a,b,\delta)=\min\{h,(1/2+\delta a)/b\}.
\tag{7}
\]

A quotient with `b=0` is omitted. These are the exact necessary
outward/upward owned-axis alternatives after the inward axes are bounded
by the vertical alternative.

For the original P, write `x=xP`. Its horizontal gap from M1 is positive.
The correlated actual-four x-band and `h1+g1>=1` give

\[
 D_P<x+31/60,\qquad g_1-D_P\ge -x-1/60=: \delta_P.
\tag{8}
\]

The inward margin `g1+D_P` exceeds `G+1/10>1/2>=kP`, so an inward
side axis cannot improve vertical separation. A nonpositive vertical
component is impossible because `D_P-g1<2/5<1/2`, while horizontal
coordinate separation is impossible because `hP>=1/2`. Thus

\[
                   y_P-y_1\ge g_1+r_{s_P}(P,\delta_P).
\tag{9}
\]

For the original L write `Z=-xL`. Its correlated inset margin satisfies

\[
 g_1-|x_L-x_1|\ge\delta_L:=\min(59/60-Z,Z-1/60),
\]
\[
 |x_L-x_1|<D_L^{\rm main}:=\max(Z-l,31/60-Z).
\tag{10}
\]

If `Z>=8/15`, L is to the left of M1 and its inward margin exceeds
`G+8/15-31/60>1/2`. Use (7) with reflected chirality `-sL` and
`deltaL`. For `Z<8/15`, retain both possible absolute component orders:

\[
              r_L=\min\{h_L,(1/2+\delta_L b_L)/a_L,
                                 (1/2+\delta_L a_L)/b_L\}.
\tag{11}
\]

This includes either sign of the small horizontal gap. The same
nonpositive-vertical and horizontal-axis exclusions follow from
`D-g1<=1/10<1/2`. Consequently `yL-y1>=g1+rL`.

In both (9) and (11), the proof also retains the independent center-distance
bound from the physical near-aligned main:

\[
 |c_F-c_1|\ge\max\{1,h_F+12/25\}.
\tag{12}
\]

This is the accepted actual-four estimate from Section 2 of
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_FULL_SIDE_MAIN_HEIGHT_HAND_PROOF.md`.
Combining (12) with (8) or (10) and `g1>G` strengthens the main clearance
used in the table to

\[
 C_F=\max\left\{G+r_F,
       \sqrt{\max(1,h_F+12/25)^2-(D_F^{\rm main})^2}\right\}.
\tag{13}
\]

All radicands in (13) are positive on the stated roots. The base height
bounds are `yP>=-7/20+CP` and `yL>=-7/20+CL`.

### 3.1. Eliminate the main tilt in the low-floor branch

For orientation, the weaker y1>=-7/20 premise already gives the bound
below. Section 3.5 records the stronger exact formula actually used with
y1>=-17/50. Since `g1=1/[2(1+2e)]>=1/2-e`, (9) and `y1>=-7/20` give
`yP>=3/20-e+rP`. Under `yP<=hP+1/10`, necessarily

\[
        e\ge e_{\rm need}:=\max\{0,1/20+r_P-h_P\}.
\tag{14}
\]

Equations (3), (5), and (14) give the necessary inequalities
`e_need<=1/60` and `K-c0+(64/9)e_need<=1/2`, and justify the stronger
right endpoint rectangle (6). The same actual P chirality supplies both
its clearance and its tilt lower bound.

The accepted `COUPLED_CONE_INSET_LOSS_HAND_PROOF.md` gives one further
necessary low-floor condition:

\[
                              x+g_P\ge J.
\tag{15}
\]

For `x<0`, the opposite inequality would force P's whole floor above
`1/10+13/4960`; for `x>=0`, (15) is automatic from `gP>7/20>J`.
The table retains the equality in (15) as an outward relaxation.

### 3.2. A circular endpoint resource

There is a useful second lower bound on the right inset height. The same
synthetic outward corner gives, for each original endpoint i,

\[
 X_i+k_i\le\sqrt{Q-(h_i+g_i-c_i)^2}
                  \le\sqrt{Q-(1-c_i)^2}.
\]

Summing and using the actual span, the affine lower bound on `hi+ki`, and
`U<1/30`, proves

\[
 \sqrt{Q-(1-c_0)^2}+\sqrt{Q-(1-c_3)^2}
                   \ge4-73/30000+2e.
\tag{16}
\]

Consequently, with `H=4-73/30000+2e_need` and
`v=H-sqrt(Q-(1-c0)^2)>0`, an original configuration requires
`Q-v^2>=0` and

\[
                            c_3\ge1-\sqrt{Q-v^2}.
\tag{17}
\]

The table takes the maximum of (6) and (17). If the radicand is negative,
the corresponding physical branch is impossible. The universal bound
`c3<=1/2` is also retained. For the low-right proof set `e_need=0`.

### 3.3. The universal two-square caps bound the same main tilt

The universal physical two-square cap in
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`
applies to the two original pairs `(M0,L)` and `(M3,R)`. Put
`A0=-x0-h0`, `A3=x3-h3`, and `C=451/810`. It gives

\[
 46A_0+(27/2)(Z-h_L)\le211/4,
 \qquad46A_3+(27/2)(X-h_R)\le211/4.
\]

The actual main chain gives `A0+A3>=2+2e`, while each `Ai<61/60`.
Thus each opposite `Ai>59/60+2e`. The two individual caps and their
sum consequently imply

\[
 e\le e_{\rm cap}:=\min\left\{1/60,
 {27\over184}(C-Z+h_L),
 {27\over184}(C-X+h_R),
 {27\over184}(1-Z-X+h_L+h_R)\right\}.
\tag{18a}
\]

A negative upper bound already excludes the branch. This resource uses
only the original physical pairs and actual main chain. It requires no
shoulder-height premise, central floor, or actual selected short edge,
and it does not depend on the joint five-square cap.

The cap from the opposite side also gives the two adaptive load bounds

\[
 A_0\ge B_L+2e,\quad B_L:=\max\{59/60,157/184+(27/92)(X-h_R)\},
\]
\[
 A_3\ge B_R+2e,\quad B_R:=\max\{59/60,157/184+(27/92)(Z-h_L)\}.
\tag{18b}
\]

Put `J_E=29927/30000`. Every original endpoint has `hE+kE>=J_E`
by the affine bound of Section 2 and `hE-1/2<=1/30`. Its synthetic
outward corner therefore gives

\[
               Q\ge(A_i+J_E)^2+(1-c_i)^2.
\tag{18c}
\]

Use (18b)–(18c) on the left to strengthen the necessary upper bound on e:

\[
 e\le {\sqrt{Q-(1-c_0)^2}-J_E-B_L\over2}.
\tag{18d}
\]

For the left endpoint, the actual live height also gives `g0>=c0` and
`h0<=1/(4c0)`. Therefore the constant JE in (18d) may be strengthened to

\[
 J_L(c_0)=H+\sqrt{1/2-H^2},\qquad H=\min\{8/15,1/(4c_0)\}.
\tag{18f}
\]

This follows because `h+sqrt(1/2-h^2)` decreases for `h>=1/2`.
The evaluator uses this stronger left value. On an interval it uses the
lower endpoint of c0 to obtain an upper H, then rounds JL downward.

The evaluator takes the minimum of (18a) and (18d); a negative result
excludes the branch. On the right, (18b) and `e>=e_need` give the additional
inset lower bound

\[
 c_3\ge1-\sqrt{Q-(B_R+2e_{\rm need}+J_E)^2}.
\tag{18e}
\]

A negative radicand is itself impossible. These inequalities retain the
same actual endpoint and opposite original shoulder in each cap. They
are the adaptive load consequences of the universal two-square caps,
without assuming a selected actual short edge.

### 3.3a. Accepted orientation tolls preserve the shoulder frame

The independently checked universal pair refinements
`UNIVERSAL_PHYSICAL_PAIR_SHOULDER_TILT_TOLL.md` and
`UNIVERSAL_PHYSICAL_PAIR_CURVED_TILT_TOLL.md` strengthen each pair cap by
adding

\[
 \tau_B=\max\{2b_B,\;6b_B-(27/2)(1-a_B)\}
\]

to its left side. Both theorems retain every original physical owner and
both independent frames, without any shoulder height premise. Define

\[
 \psi_B=h_B-{2\over27}\tau_B
 =\min\{a_B/2+19b_B/54,\;1-a_B/2+b_B/18\}.
\tag{18g}
\]

Every cap-derived resource in (18a), (18b), (18d), and (18e) is therefore
strengthened by replacing its shoulder hL,hR with psiL,psiR. For example,

\[
 e\le {27\over184}(1-Z-X+\psi_L+\psi_R),\qquad
 B_L=\max\{59/60,157/184+(27/92)(X-\psi_R)\}.
\]

The evaluator computes psi directly, preserving this cancellation.
The curved expression increases with folded slope t. The linear expression
has its unique maximum at t=19/27, of value sqrt(1090)/54.
Thus a valid interval upper for psi is the smaller of the curved
right-endpoint upper and the linear maximum over the two endpoints and
this one critical point when present. Every use of psi in these resources
needs only such an upper bound.

### 3.4. Feed the proved high R back into the main clearance

The proof order is **low-right first, low-floor second**. Thus, in the
low-floor branch, the already independently proved consequence `yR>3/5`
is available. This is an acyclic use of the two complete roots.

Fix the original R chirality. If `X+hR>A`, horizontal separation from
its endpoint rectangle is impossible. A downward normal is impossible
as well: `yR+c3>3/5+c_*>kR`. Explicitly, its adjusted projection is
strictly below either
`aR*hR-bR*(yR+c3)=1/2+bR*(kR-yR-c3)<=1/2`, or
`bR*hR-aR*(yR+c3)=1/2-aR*(kR+yR+c3)<1/2`.
Strict horizontal overlap already makes the actual projection strictly
less than the first bound, including the boundary bR=0.
The inward normals are already dominated by the vertical alternative.
Therefore, with the outward/upward reach

\[
 r_R=\begin{cases}
 \min\{h_R,(1/2+(X-A)b_R)/a_R\},&s_R=+1,\\
 \min\{h_R,(1/2+(X-A)a_R)/b_R\},&s_R=-1,
 \end{cases}
\]

one has `yR>=c3+rR`. Its original corner ceiling gives
`c3<=UR(X,sR)-rR`. Combining this with (5) yields the necessary upper
bound

\[
 e\le e^{\rm up}:=\min\left\{1/60,
 {9\over64}\bigl(U_R(X,s_R)-r_R-K+c_0\bigr)\right\}.
\tag{18}
\]

If its upper bound is negative, this R chirality branch is impossible.
When horizontal overlap is not established on an interval box, simply
use `e_up=e_cap`. In all cases also take the minimum with `e_cap`
from (18a). Otherwise (18) strengthens the contained main inset to

\[
                         g_1\ge {1\over2+4e^{\rm up}}.
\tag{19}
\]

Replace G by this lower bound in the first term of (13), for **both** P
and L; their correlated margins (8),(10) are unchanged. Also impose
`e_need<=e_up`. The P and L clearances must now be computed within the
same R-chirality branch: maximize over L only after fixing both P and R,
then maximize over R and P. The original P, L, R frames and the original
main tilt remain jointly constrained. No eighth live parameter or assumed
main orientation is introduced.

For R's height lower bound in this second proof, use
`max(3/5,cR+rR)` when horizontal overlap is established, and `3/5`
otherwise. This retains all equality faces through non-strict outward
bounds.

### 3.5. Retain the exact main support and the same endpoint load

The left endpoint corner in (18c), with the sharper value JL, also gives

\[
 A_0\le A_{0}^{\max}(c_0):=
 \min\{61/60,\sqrt{Q-(1-c_0)^2}-J_L(c_0)\}.
\tag{19a}
\]

The actual chain places the same original M1 in the interval
`h1-A0<=x1<=-l-e`. Thus replace (8) and (10) by the stronger necessary
bounds

\[
 D_P\le x+A_0^{\max}-1/2-e,\qquad
 g_1-D_P\ge1-A_0^{\max}-x+q(e),
\]
\[
 D_L^{\rm main}\le
 \max\{Z-l,A_0^{\max}-1/2-Z\}-e,
\]
\[
 g_1-D_L^{\rm main}\ge
 \min\{59/60-Z,Z+1-A_0^{\max}\}+q(e),
 \qquad q(e)={2e^2\over1+2e}.
\tag{19b}
\]

Here `h1+g1=1+q(e)`, and q increases for e>=0. First compute rP with
the unchanged nonnegative remainder discarded, using
`deltaP=1-A0max-x`. Using the stronger main-height premise y1>=-17/50, the bad-floor inequality gives
`g1<=T:=hP+11/25-rP`. If T<=0 the physical branch is impossible;
otherwise the evaluator strengthens (14) to

\[
 e\ge e_{\rm need}:=\max\{0,1/(4T)-1/2\}.
\tag{19c}
\]

It then uses this lower bound in the subtracted e terms and in q(e) of
(19b). This order is acyclic: the first rP and (19c) do not assume the
subsequently improved clearance. All right endpoint resources still use
this same proved lower bound for the one original main tilt.

There is also no need to round the main's physical support down to
`hF+12/25`. The original two-frame proof underlying (12) gives, for
both independent chiralities,

\[
 |c_F-c_1|\ge
 \max\{1,1/2+h_F a_1-k_F b_1\}.
\]

For a proved upper bound `e<=e_up`, put
`H=1/2+e_up` and `K1=sqrt(1/2-H^2)`. Since
`hF-kF=bF` and `hF+kF=aF`, the expression at that endpoint is

\[
 \sigma_F^{\min}
 =\max\{1,1/2+b_F H+a_F K_1\}.
\tag{19d}
\]

This is a lower bound: its derivative in H is
`bF-aF*H/K1<=0`. For fixed H it increases with the outsider's folded
angle beta, because the derivative is
`H*cos(beta)-K1*sin(beta)>=0` on `[0,pi/4]`. The exact evaluator
therefore computes (19d) at the lower endpoint of the outsider slope
interval, and at the upper endpoint of the allowed main tilt.
It uses this support in the distance term of (13), with the smaller
horizontal-gap bounds from (19b). The inset term uses the improved
margin (19b) and `g1>=1/(2+4e_up)`. P and L retain the same eNeed,
e_up, original M1, and original left endpoint throughout. In the low-floor
evaluator their base height is -17/50, while the independent low-right
evaluator retains the weaker -7/20 base.

### 3.6. Cancel the bad floor in the necessary main-owned reach

The main/P vertical inset separator is impossible in the bad-floor
branch: it would give
`yP-y1>=g1+hP>hP+11/25`, whereas the caller and bad floor give the reverse
non-strict bound. All other excluded main/inset alternatives in Section 3
remain excluded. Consequently the indicated outward tilted original P
axis is necessary. The exact identities
`aP*hP=1/2+bP*kP` and `bP*hP=1/2-aP*kP` cancel hP from its inequality:

\[
 \begin{array}{ll}
 s_P=-1:&t_P(k_P-\delta_P)\ge g_1-11/25,\\
 s_P=+1:&-k_P-\delta_P\ge t_P(g_1-11/25).
 \end{array}
\tag{19e}
\]

For negative chirality this strengthens the upper bound T in (19c) to
`11/25+tP*(kP-deltaP)`. For positive chirality and tP>0 it strengthens
T to `11/25-(kP+deltaP)/tP`. The latter quotient is bounded outward;
when its denominator interval meets zero the weaker bound is retained.
The division-free inequalities (19e) are always checked. The exact tP=0
limit is impossible in either chart on this root, since deltaP>=-2/5,
kP=1/2, and g1>11/25.

After e_up is known within one P/R chirality branch, put
`gmin=1/(2+4e_up)`. Equations (19b) and (19e) give a further necessary
lower bound on that same xP:

\[
 x_P\ge
 \begin{cases}
 1-A_0^{\max}+q(e_{\rm need})-k_P+(g_{\min}-11/25)/t_P,&s_P=-1,\\
 1-A_0^{\max}+q(e_{\rm need})+k_P+t_P(g_{\min}-11/25),&s_P=+1.
 \end{cases}
\tag{19f}
\]

The exact evaluator intersects its x interval with an outward lower bound
from (19f) before forming the two physical short-link intervals in that
same chart. This does not change any prior upper bound used for eNeed,
e_up, or the original main gap: those use x's upper endpoint, which is
unchanged. Every possible original configuration remains in the narrower
necessary interval. An empty intersection excludes only that chirality.

## 4. Original endpoint separators and corner height caps

Consider an outsider with reflected horizontal coordinate X in `[l,u]`,
above a known base height `Y>=v`, next to an endpoint rectangle. When c is
any proved lower bound for that endpoint's actual symmetric inset height,
its inset halfwidth satisfies `gE>=c`. Its center bound therefore gives
`xE-gE<=rho-c`. The contained rectangle can consequently be strengthened
to

`[A(c),B] x [-c,c]`, where `A(c)=min(A,rho-c)`.

In all expressions below, A may be replaced by this A(c); the endpoint-union
evaluator does so. The separate high-R feedback in Section 3.4 retains
the weaker fixed A, which is also valid. The farther boundary B stays unchanged. For an
interval lower bound on c, the resulting A(c) is an upper bound for the
actual inner edge, so this rectangle remains physically contained.
 For signed chirality s define

\[
 q_+(s)=c+
 \begin{cases}
 \min\{h,(1/2+(X-A)b)/a\},&s=+1,\\
 \min\{h,(1/2+(X-A)a)/b\},&s=-1,
 \end{cases}
\tag{20}
\]

again omitting a zero denominator. Put `q_-(s)=q_+(-s)`.
If `X+h<=A`, horizontal coordinate separation is possible and no new
height bound is imposed. Otherwise every separator gives

\[
                         Y\ge q_+(s)\quad\hbox{or}\quad Y\le-q_-(s).
\tag{21}
\]

Indeed, the two vertical coordinate alternatives and the one
outward/upward or outward/downward original side normal give (20)–(21).
An inward horizontal normal uses the farther rectangle boundary B;
`B-X>=B-u>1/2>=k` makes its quotient at least h, so it is already covered
by the vertical alternative. This proves the complete signed owner union.

Only if `v+q_-(s)>0` is the second branch removed. The new lower bound is
then `max(v,q_+(s))`; otherwise the base v is retained. In interval rows,
both tests `X+h>A` and `v+q_-(s)>0` are made with strict outward lower
bounds. A box crossing a branch boundary keeps the weaker bound. Thus
neither a touching equality nor an unknown endpoint-normal sign is lost.

The original four corner offsets are

`(h,-s*k), (s*k,h), (-h,s*k), (-s*k,-h)`.

For a horizontal center coordinate z let `U(z,s)` be the minimum of
`rho=91/60` and the four values `sqrt(Q-(z+dx)^2)-dy` from these
corners. This is a necessary upper center-height bound. The left cap is
`UL(Z,-sL)`, because horizontal reflection reverses chirality. Every
radicand is positive on the roots; the evaluator nevertheless rejects
an impossible negative-radicand branch explicitly.

For L, feed (21) with base `-7/20+CL`, rectangle height `c0`, reflected
frame `-sL`. For R, use base `-113/600`, rectangle height (6), frame `sR`.
Write the resulting lower bounds as `Llo,Rlo`, and their corner caps as
`Lhi,Rhi`.

## 5. The two physical short-link tests keep one shared P frame

For two original frames i,j the sum of supports on any owned side normal
is

\[
 \sigma_{ij}={1+|a_i a_j+s_i s_j b_i b_j|
                    +|s_i b_i a_j-s_j a_i b_j|\over2}\ge1.
\tag{22}
\]

For a cone displacement `(D,V)`, `D>0`, `|V|<=D`, it suffices to consider
all four positive-horizontal owner normals

`(ai,si*bi), (bi,-si*ai), (aj,sj*bj), (bj,-sj*aj)`.

To check completeness without assuming a strict weak edge, the negative
of a near-horizontal normal has projection at most `(-a+b)D<=0`. The
negative of the other normal, if positive, is dominated by the positive
near-horizontal one: their projection difference is
`(a+b)D-(a-b)sV>=2bD>=0`. Their physical support sum is identical.

Put `DL=x+Z`, `DR=X-x`. The closed weak-link and inset cone conditions are

\[
 g_L+g_P\le D_L\le h_L+h_P,\qquad
 g_P+g_R\le D_R\le h_P+h_R.
\tag{23}
\]

For each fixed `sP`, its lower height is `Plo=-7/20+CP`. In the low-floor
branch set `Phi=hP+1/10`; in the low-right branch set `Phi=UP(x,sP)`
and additionally replace `Rhi` by `min(Rhi,3/5)`.

The two actual signed vertical gaps belong to

\[
 [\max(-D_L,Plo-Lhi),\min(D_L,Phi-Llo)],
\]
\[
 [\max(-D_R,Rlo-Phi),\min(D_R,Rhi-Plo)].
\tag{24}
\]

Each interval must be nonempty. The maximum of `nx D+ny V` on one such
interval is attained at its upper endpoint if `ny>=0`, and at its lower
endpoint otherwise. Take the maximum over the four owner normals and
subtract (22). Each pair requires this result to be nonnegative, as well
as its height-interval widths and `Lhi-Llo` or `Rhi-Rlo`.

For a fixed original P sign, take the maximum over the two L signs of the
left minimum of necessary margins, and similarly the maximum over the
two R signs. Take the minimum of these two results and `Phi-Plo`; in the
low-floor branch also include the two necessary main-tilt margins after
(14). Finally maximize over `sP`. Its value must be nonnegative.
The same signed P frame occurs in both pair tests and in (14). Allowing
different vertical centers in the two interval tests only enlarges the
original configuration set.

### 5.1. Eliminate the same P height across both owner choices

The low-floor evaluator additionally enumerates the four left and four
right owner normals **jointly**, inside one original chirality chart.
For a left normal `(a,b)` and a right normal `(c,d)`, their physical
inequalities require

\[
 b y_P\ge A_L:=\sigma_{LP}-aD_L+bY_L^*,\qquad
 -d y_P\ge A_R:=\sigma_{PR}-cD_R-dY_R^*,
\tag{25}
\]

where `YL*=Llo` for `b>=0` and `Lhi` otherwise; `YR*=Rhi` for `d>=0`
and `Rlo` otherwise. These endpoint choices only decrease the respective
right sides, so both inequalities remain necessary.

If b,d have the same sign, multiply them by `|d|,|b|` and add. The one
original P height cancels, leaving the division-free necessary inequality

\[
                           |d|A_L+|b|A_R\le0.
\tag{26}
\]

The same implication remains valid when either component vanishes. For
opposite signs the evaluator uses only the original two separate interval
projection tests. For each of the 16 owner pairs it takes the minimum of
the two individual necessary margins and, when applicable, the negative
of the left side of (26); then it maximizes over the 16 choices. This
replaces the weaker independent maxima over physical owner axes. It adds
no owner hypothesis, no vertical-order hypothesis, and no new live variable.
All products, including negative values of AL or AR, are enclosed with
ordinary signed outward interval arithmetic.

### 5.2. Preserve the shared horizontal coordinate as well

For the same-sign case of (26), write b=sB,d=sD with B,D>=0.
The evaluator additionally expands that very same weighted expression as

\[
 D\sigma_{LP}+B\sigma_{PR}-DaZ-BcX+(Bc-Da)x_P
                        +sBD(Y_L^*-Y_R^*).
\tag{27}
\]

This keeps the one original xP before interval evaluation. When both
links choose the identical P-owned axis, the code recognizes that owner
identity and also adds the two original separator inequalities directly:

\[
       a(Z+X)+b(Y_R^*-Y_L^*)\ge\sigma_{LP}+\sigma_{PR}.
\tag{28}
\]

This remains valid when b=0, and eliminates both coordinates of the same
original P. The owner identity is checked by its discrete owner indices,
not by numerical equality of interval endpoints.

For every owner pair the evaluator also multiplies the left separator
by c>=0 and the right separator by a>=0, obtaining

\[
 ac(Z+X)+(cb-ad)y_P-cbY_L^*+adY_R^*
                      -c\sigma_{LP}-a\sigma_{PR}\ge0.
\tag{28a}
\]

This eliminates the same xP for either vertical-sign relation. The endpoint
choices YL*,YR* remain those of (25); the full one P-height interval is
enclosed against the possibly signed coefficient cb-ad. The inequality
also holds when a or c vanishes. It is checked in every one of the same
16 physical owner charts.

### 5.3. Necessary interval contraction preserves root coverage

Before evaluating a low-floor leaf, the verifier makes three finite
intersection sweeps using (15), the x>=-1/5 cut, both sides of (23), and
these cap-derived necessary inequalities:

\[
 Z\le C+\psi_L,\quad X\le C+\psi_R,\quad
 Z+X\le1+\psi_L+\psi_R,
\]
\[
 X\le\psi_R+{92\over27}(A_0^{\max}-157/184).
\tag{29}
\]

For example, DL>=gL+gP gives x>=gL+gP-Z and
Z>=gL+gP-x; DR<=hP+hR gives x>=X-hP-hR and
X<=x+hP+hR. Each new interval endpoint is rounded outward using the
other current endpoints. Every physical point in the original box
therefore remains in each successive intersection. A strict lower>upper
comparison certifies emptiness; equality is always retained.

Inside each fixed chirality chart, one further necessary propagation
uses the four physical owner alternatives themselves. For a signed
height-gap interval E, an owner (nx,ny) with nx>0 requires

\[
                     D\ge(\sigma-nyE)/nx.
\tag{30}
\]

Take an outward lower bound for each quotient and then the minimum over
all four original owners. If nx=0, retain its vertical alternative unless
its entire projection falls strictly short of sigma. This produces lower
bounds qLP,qPR on the two actual horizontal gaps. Intersect the same
xP interval with `[qLP-Zhi, Xhi-qPR]`, then evaluate the original two
pair tests and the joint owner constraints on that necessary intersection.
An empty intersection excludes only the corresponding signed chart.

Collect the intervals of all chirality charts whose necessary margins
have not become strictly negative, and take their union hull. Every
physical original configuration lies in that hull. The evaluator may
repeat the complete low-floor calculation on this smaller xP interval
at most three times. This finite propagation lets its smaller upper xP
bound feed back into the same main tilt lower bound and endpoint
resources. No convergence, fixed-point claim, or unverified numerical
optimization is used.

The tree still splits and covers its original root boxes. These finite
contractions are used only inside the independently reconstructed leaf
test and do not alter tree coverage. No iteration convergence or numerical
fixed point is assumed.

### 5.4. The zero-tilt collar is excluded by hand

In the low-floor branch, tP>1/27 even under the weaker y1>=-7/20.
For negative chirality, (19e), kP<=1/2, and deltaP>=-2/5 give, if
tP<=1/27,
`g1<=9/20+(9/10)/27=29/60<15/31`, a contradiction with margin 1/1860.
For positive chirality on that interval,
`kP>=13/sqrt(730)>2/5>=-deltaP`, contradicting the second inequality
in (19e), whose right side is nonnegative. The squared reserve in the
last radical comparison is `169/730-4/25=261/3650>0`.
Thus the remaining low-floor root may start at tP=1/27, retaining this
already excluded boundary outward.

## 6. Exact roots and independent acceptance

The root order is `(tL,tP,tR,Z,xP,xR,c0)`.

| Contrary conclusion | Complete closed root |
|---|---|
| `yP-hP<=1/10` | `[0,1] x [1/27,1] x [0,1] x [l,u] x [-23/60,23/60] x [l,u] x [c_*,1/2]` |
| `yR<=3/5` | `[0,1]^3 x [l,u] x [-23/60,23/60] x [l,49/80] x [c_*,1/2]` |

For the second root, `-113/600<yR<=3/5` implies `|yR|<=3/5`.
The radius-one-half disk of R avoids the fixed endpoint rectangle with
height `221/600`, so

`xR <= A-sqrt(1/4-(3/5-221/600)^2) <49/80`.

The last positive-root comparison has exact squared reserve
`38839/5760000`; it includes `yR=3/5`.

`discover_middle_main_side_triple.cpp` is an untrusted floating discovery
producer. No floating value is used for acceptance. The original root
boxes, all midpoint splits, and every signed physical alternative are
reconstructed in the separate exact checkers.

| Complete exclusion | Nodes | Leaves | Maximum depth | Independent arithmetic |
| --- | ---: | ---: | ---: | --- |
| Low right, yR<=3/5 | 38,773 | 19,387 | 28 | Directed 80-bit integer dyadics and integer square roots |
| Low whole floor, yP-hP<=1/10 | 5,642,527 | 2,821,264 | 52 | Directed 48-bit integer dyadics, checked signed 128-bit intermediate arithmetic, and integer-only square roots |

For low right, `verify_middle_main_side_triple.py` independently
reconstructed all leaves. The least exact exclusion reserve was

\[
 {6602649188058974793\over604462909807314587353088}>10^{-5}.
\]

The report is `middle_main_low_right_final_exact_replay.json`. Its
certificate SHA256 is
`723b5864033f3b12cb260dd54685b0c139685a6cefbceec7d187054b96fdfcd9`.

For low floor, the separate standard-library checker
`verify_middle_main_low_floor_exact.cpp` reconstructed the complete root
from rational dyadic cell indices. Rounded interval endpoints never
define the partition. It checked every one of the 2,821,264 leaves,
including every finite contraction and all original owner alternatives.
The least exact exclusion reserve was

\[
                    {360606\over281474976710656}>10^{-9}.
\]

There is no unfinished frontier. The report is
`middle_main_low_floor_cpp_replay.json`. The canonical certificate is
`middle_main_low_floor_candidate.json`, with SHA256
`faf9cc6967ce02412024f0fe90db6298931d0c243bce6cf345ad78dda2785a9c`.
For publication, the lossless archive
`middle_main_low_floor_candidate.json.gz` contains exactly that canonical
JSON. Its SHA256 is
`ad5275e67b28a15d86cea564cd6221149a9c7cf7e4470dfe4762c296e4f8e76e`.
From the `computer_assisted` directory, expand it before invoking either
unchanged checker:

```sh
gzip -dc middle_main_low_floor_candidate.json.gz > middle_main_low_floor_candidate.json
```

The archive contains every tree event; it is only a storage encoding.
The C++ checker source SHA256 is
`96ac00e7069e20dcbf39dfb6e092349773300edc3689549f791f32c6c557bd00`.

The C++ implementation was ported from the independently written Python
mathematical evaluator; it imports neither the floating producer nor its
interval arithmetic. Its integer kernel, root parser, tree accounting,
and formula parity receive separate review. Four damaged controls are
rejected by that checker; four additional short controls are rejected by
the Python checker. The frozen Python checker SHA256 is
`c1e26b7c6184c2636c3eb66c1f267b076f84b852a9c7fe39e6c26e7a2029fe29`.
The optional `verify_middle_main_side_triple_parallel.py` partitions the
same root into disjoint exact subtrees only for scheduling that unchanged
80-bit evaluator; it changes no mathematical acceptance rule.

The physical ranges of a,k decrease and b,h increase on each folded-slope
interval. All radicals are enclosed by integer square roots, every
quotient has an explicitly controlled denominator, and all signed
products are rounded outward. Each strict negative leaf proves that its
whole original box contains no configuration satisfying the stated
physical hypotheses. The finite hand collar in Section 5.4 supplies the
excluded tP range below 1/27.

The low-floor proof consumes the separately proved low-right consequence
in the acyclic order of Section 3.4. Together these exact covers prove
both conclusions (2) under their stated main-height premises. Their
original-nine use is fully assembled in
`ACTUAL_FOUR_221_FULL_SIDE_MIDDLE_ASSEMBLY.md`. No fixed A.2 count is
changed by this scalar theorem alone.
