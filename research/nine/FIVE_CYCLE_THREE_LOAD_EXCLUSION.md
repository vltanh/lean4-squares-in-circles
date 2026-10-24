# A positive five-cycle cannot have three loaded bodies

**Status: complete hand exclusion; root and separate independent full hand audits
passed.** This source excludes the entire three-load C5 orbit,
including both side-normal and diagonal transmitter widths. It retains
every physical circle mask, all actual shared-side means and all four
additional physical squares.

Assume throughout
\[
             R_*:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The selected positive component is exactly
\[
                         T-U-B-C-V-T,
\tag{2}
\]
where precisely T,B,C carry positive total circle load. U,V are unloaded
degree-two transmitters. Use the existing strict point normals and the
compatible diagonal-avoidance choice, made before the certificate.

**Theorem.** The component (2) is impossible. No secondary minimization,
completion-square motion or assumption of a common frame is needed.
The theorem concerns the exact degree-two cycle component; additional
positive edges at its vertices are outside its scope.

## 1. Proper concurrences, physical order and the channel endpoint lemma

`FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md` excludes parallel
pair forces at T. B and C each have a boundary neighbor and likewise
have nonparallel forces. The proper-concurrence theorem and exact
transmission calculation in `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md`,
Sections1--3, therefore apply to all three loads. Their concurrence
points form a strictly convex triangle containing the origin. Its
TB and CT edges have physical transmitter reserves
\[
                           w\in\{1,\sqrt2\};
\tag{3}
\]
its BC edge is the actual direct boundary contact.

The positive radial concurrence directions and the physical boundary
center directions have the same circular order. Indeed each physical
circle corner lies within20 degrees of its center, the corresponding
center intervals are disjoint, and a positive circle resultant lies
between its physical circle corners. Thus the three consecutive center
arcs corresponding to the triangle edges have positive lengths with
sum2pi. We retain the physical corners whose individual weights are
zero as well.

We use the following whole-channel consequence, already proved with
all masks and means in `FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md`,
Sections1--2. Its proof uses only the two loaded endpoints, their proper
concurrences, and the fact that the origin is on the inward side of
their contracted force edge. It does not require four loads.

**Channel endpoint lemma.** Normalize either channel horizontally,
with its loaded endpoints X on the left and Y on the right, and put
its actual applications at
\[
                     P_X=(l,h),\qquad P_Y=(l+w,h),\qquad h>0.
\tag{4}
\]
The vertical axis points away from the origin. The endpoint centers
satisfy
\[
 c_X=(-X_0,Y_X),\quad c_Y=(Y_0,Y_Y),\qquad
 X_0,Y_0>0,\quad Y_X,Y_Y\ge0.
\tag{5}
\]
Their consecutive center arc across the channel is the upper minor
arc, of length
\[
 \gamma=\pi-\delta_X-\delta_Y,
 \qquad
 \delta_X=\arctan(Y_X/X_0),\quad
 \delta_Y=\arctan(Y_Y/Y_0).
\tag{6}
\]

Here is the precise all-mask content behind that lemma. The horizontal
center gap is w+H_X(e_x)+H_Y(e_x)>=2, while every boundary center has
norm less than91/60; consequently their horizontal signs oppose.
Each endpoint concurrence has height h and is a positive multiple of
its circle resultant, so that resultant has positive vertical component.
For an oblique left endpoint, its rightmost application is a vertex P
and its inward axes are (-a,b),(-b,-a). If its center were on or below
the horizontal axis, a>b and h<=(a-b)/2. The center has strictly positive
dot product with (-b,-a), so every farthest corner includes that step;
its vertical coordinate is h-a or h+b-a, both strictly negative.
That contradicts its positive vertical circle resultant. For an aligned
endpoint a strictly negative center height also makes every farthest
corner negative; height zero and two opposite-height circle corners
remain allowed. Reflection gives the right endpoint. This argument
does not put a radial two-corner concurrence inside its square and
does not fix any side mean.

Finally, the upper minor center arc in (6) corresponds to the force
edge: both endpoint concurrences have height h>0 and the origin is
strictly below their edge, and their order agrees with the disjoint
center intervals. The third loaded center is on the other arc. This
identifies the actual consecutive angle used in the global sum.

## 2. A uniform target angle for every transmitter

Set
\[
                 \theta=\arccos\frac9{25},\qquad
                 \beta=\frac\theta2.
\tag{7}
\]
Thus 0<beta<pi/4 and
\[
                        \cos\beta=\frac{\sqrt{17}}5.
\tag{8}
\]
Every boundary center has the strengthened radial lower bound
\[
                         |c|>\frac{19}{15}.
\tag{9}
\]
Indeed |c|>=R-1/sqrt(2), and sqrt(2)<17/12 gives
\[
 R-1/\sqrt2\ge\frac{79}{40}-\frac1{\sqrt2}
              >\frac{79}{40}-\frac{17}{24}=\frac{19}{15}.
\]
We will prove for **each** of the two possible reserves in (3) that
\[
                              \gamma<\pi-\beta.
\tag{10}
\]

### 2.1. A side-normal channel

When w=1, the actual endpoint means lie within1/sqrt(2) of their
respective centers. Therefore
\[
                         |c_Y-c_X|\le1+\sqrt2.
\tag{11}
\]
If gamma>=pi-beta, (8)--(9) imply
\[
 \begin{split}
 |c_Y-c_X|^2
 &=(|c_Y|-|c_X|)^2+2|c_X||c_Y|(1-\cos\gamma)\\
 &>\frac{722}{225}\left(1+\frac{\sqrt{17}}5\right)
  >\frac{65702}{11250}.
 \end{split}
\tag{12}
\]
The last comparison uses sqrt(17)>41/10. But
\[
 (1+\sqrt2)^2<\frac{583}{100}<\frac{65702}{11250},
\tag{13}
\]
where sqrt(2)<283/200 gives the first bound and the second has exact
margin229/22500. This contradicts (11), proving (10) for the entire
side-normal channel, with arbitrary endpoint frames and transverse means.

## 3. A strict concavity fact for aligned boundary centers

For fixed R in (1), let a globally axis-aligned boundary square have
center in the first quadrant at angle delta in [0,pi/4]. Write its
radius as r(delta), and its horizontal coordinate as x_R(delta). The
actual farthest-corner equation is
\[
 R^2=r^2+r(\cos\delta+\sin\delta)+\frac12,
 \qquad x_R(\delta)=r(\delta)\cos\delta.
\tag{14}
\]

**Lemma 3.1.** On [0,pi/4], x_R is strictly decreasing and strictly
concave.

*Proof.* Put c=cos(delta), s=sin(delta), t=c+s, u=c-s and D=2r+t.
Here r>1 by (9), c>0, 1<=t<=sqrt(2), and 0<=u<=1.
Differentiating (14) gives
\[
       r'=-\frac{ru}{D},\qquad
       x_R'=-\frac{r(1+2rs)}D<0.
\tag{15}
\]
A second differentiation, with no estimates yet, gives
\[
 x_R''=-\frac{2r}{D^3}E,
 \quad
 E=4r^3c+4r^2+rt(u^2+2s^2)-(r+t)u.
\tag{16}
\]
For verification one may first put N=r(1+2rs). Then
D'=ut/D and
\[
 \frac{D}{2r}(N'D-ND')
       =rcD^2-u\bigl(r+t+4r^2s+3rst\bigr)=E.
\]
Using c^2+s^2=1 gives exactly the expansion (16).
All terms except the last in E are nonnegative, and
\[
                 E\ge4r^2-r-\sqrt2>3-\sqrt2>0.
\]
Thus x_R''<0, proving strict concavity, including the one-sided
endpoint derivatives. `square`

Concavity and monotonicity in particular imply, whenever a,b>=0 and
a+b<=beta,
\[
                 x_R(a)+x_R(b)\ge x_R(0)+x_R(\beta).
\tag{17}
\]
For a+b>0, apply the concave chord inequality separately at a and b
on [0,a+b] and add; then use decrease from a+b to beta. The zero-sum
endpoint follows directly from monotonicity.

## 4. The complete diagonal channel has the same angle bound

When w=sqrt(2), the existing compatible diagonal avoidance makes both
actual transmitter endpoints relative-interior points of loaded sides.
Both endpoint frames are therefore parallel to the channel axes. Their
horizontal center separation is exactly
\[
                           X_0+Y_0=1+\sqrt2.
\tag{18}
\]
This does not prescribe either endpoint's transverse position or its
physical circle-corner weights.

Assume gamma>=pi-beta. Equation (6) then gives
\[
                         \delta_X+\delta_Y\le\beta.
\tag{19}
\]
Since each center is in its upper horizontal quadrant, reflection of
the left endpoint reduces both actual horizontal magnitudes to the
function in (14). Lemma3.1 therefore implies
\[
                     X_0+Y_0\ge x_R(0)+x_R(\beta).
\tag{20}
\]
The right side has the following uniform lower bounds:
\[
 x_R(0)=\sqrt{R^2-1/4}-\frac12>\frac75,
 \qquad
 x_R(\beta)=r(\beta)\frac{\sqrt{17}}5
      >\frac{19}{15}\frac{41}{50}=\frac{779}{750}.
\tag{21}
\]
For the first use R_*^2-1/4=5841/1600>(19/10)^2.
For the second use (8)--(9) and sqrt(17)>41/10. Hence
\[
             X_0+Y_0>\frac{1829}{750}
                     >\frac{17}{7}>1+\sqrt2.
\tag{22}
\]
The rational comparison has margin53/5250, and sqrt(2)<10/7 gives
the last one. This contradicts (18). Thus (10) also holds for every
diagonal channel, including either aligned endpoint at zero center
height and every physical two-corner weight split.

## 5. The complete three-load angle sum is impossible

The direct boundary contact BC has minor center-angle gap strictly
less than theta. As in `FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md`, Section3,
this follows from center distance at most sqrt(2) and both center
radii greater than5/4:
\[
 \cos(\text{minor gap})
 =1-\frac{|c_B-c_C|^2-(|c_B|-|c_C|)^2}{2|c_B||c_C|}
 >\frac9{25}.
\tag{23}
\]
The actual angular-neighbor contact theorem identifies this minor arc
with the consecutive BC arc in the three-load order from Section1.
The other two consecutive arcs are exactly the two outward channel
arcs treated in Sections2--4. Their full circular sum would therefore
satisfy
\[
        2\pi=\gamma_{TB}+\gamma_{BC}+\gamma_{CT}
               <(\pi-\beta)+\theta+(\pi-\beta)=2\pi,
\tag{24}
\]
a contradiction because 2beta=theta.

This argument covers every pair of reserves in {1,sqrt(2)}, without
assuming common endpoint frames in the side-normal case. In particular
it closes both complete residual pairs(1,1) and(1,sqrt(2)) and also
independently excludes the double-diagonal pair after the nonparallel
T reduction. The earlier double-diagonal theorem remains valid but is
not an additional premise of this angle-sum exit.

## 6. Scope

The parallel-T source supplies the one necessary initial case split;
the nonparallel proper-concurrence lemma expressly permits T to have
two unloaded neighbors. No boundary-neighbor premise is silently
applied at T. Physical two-corner concurrences may remain outside their
bodies: only their positive radial factor and proper contact directions
enter the endpoint half-plane proof.

All shared-side means, individual zero circle weights, zero-weight
physical contacts and all four completion squares are retained. The
whole three-load C5 component is excluded directly, including R at
both endpoints of (1). With `FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md`, this
closes the entire C5 graph branch of C1.5.b0; the separate house and
four-load fan graph branches are not covered by this theorem.

No numerical diagnosis, Lean compilation, CI, post-stress normal
selection or deletion of a positive chord is used.
