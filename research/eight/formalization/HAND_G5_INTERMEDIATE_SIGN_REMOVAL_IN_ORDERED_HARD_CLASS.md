# G and T need no transverse-sign entry assumption in the ordered hard class

## 1. The local wrong-sign transport

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad q_L\le q\le Q.
\tag{1}
\]
Retain the H--G--A system
\[
\begin{aligned}
 b_H+a_G\sin h-y_G\cos h&\ge W(h),\\
 y_G+a_A\cos(\Theta+h)-b_A\sin(\Theta+h)&\ge W(\Theta+h),
\end{aligned}
\tag{2}
\]
with positive H,A signs, a genuinely wrong G sign y_G>0,
sorted actual q-circles, and
\[
 \Theta\ge0,\qquad 0<h\le\Theta+h\le7/10,
 \qquad b_H<9/10,\qquad b_A\ge67/200.
\tag{3}
\]
Assume A satisfies the wrong-sign cap of
`HAND_G5_AB_ALIGNMENT_WITH_ARBITRARY_INTERMEDIATE_SIGNS.md`.
In particular `a_A>197/250`, and its primary satisfies the
true core. The cap is necessary for every pair (2), so this
adds no assumption to a feasible pair in the stated domain.

**Wrong-sign transport.** At the same q, keeping H fixed
and A's tangent and frame fixed, the necessary system has
a descendant with G transverse coordinate zero and positive
HG error. The new G frame is between H and its old frame.
All changed points remain sorted and satisfy the true core.
A's corner value can be made strictly less than q. A separate
strict circle loss at the other middle point is unchanged.

This is a local necessary-system construction. It makes no
claim that unretained nonneighbor constraints survive. Its
reflected form applies to a wrong-sign T in BT2/TD2, with
B,D replacing A,H. No sign of E is used in this reflection.

## 2. Optimize G after the actual-q primary lift

Lift A's primary to its actual q-circle while keeping b=b_A
fixed. Introduce
\[
 Y=b+\tfrac12,\qquad P=\sqrt{q-Y^2}-1,
\]
\[
 V(z)=P\cos z-Y\sin z,\qquad
 U(z)=P\sin z+Y\cos z,\qquad z=\Theta+h.
\tag{4}
\]
This lift preserves (2), sorting and the true core. The cap
bound gives P>0; the lower bound on b gives
\[
 P<p_0:=397/500,\qquad Y\ge167/200,
\tag{5}
\]
because
`(897/500)^2+(167/200)^2-Q=61/1000000>0`.
Also U>0 throughout `0<=z<=.7`.

The second inequality of (2) requires
`y_G>=1/2-V(z)`. Choose the smallest allowed nonnegative
transverse coordinate and the largest compatible primary:
\[
 y_G'=\max\{0,1/2-V(z)\},\qquad
 a_G'=\sqrt{q-(y_G'+1/2)^2}-1/2.
\tag{6}
\]
This decreases G's transverse coordinate and increases
its primary, so HG0 improves because h>0. Sorting follows
from the original sorted G circle. A sorted point on the
q-circle has primary at least `sqrt(q/2)-1/2>7/12`, so the
true core also holds.

If V(z)>=1/2, (6) already gives the required G-zero state
at the same positive error. Suppose henceforth V(z)<1/2.
Put
\[
 Z=1-V,\qquad w=\sqrt{q-Z^2},\qquad T=w-U.
\tag{7}
\]
Then GA0 is active and the optimized HG0 demand is
\[
 H(h):=\tfrac12+\cos h+\sin h
          -\cos h\,V(\Theta+h)-\sin h\,w(\Theta+h)
          \le b_H.
\tag{8}
\]
The exact derivative and circle identities are
\[
 H'(h)=\cos h-T\left(\cos h+\frac{Z\sin h}{w}\right),
\tag{9}
\]
\[
 U^2=q-2P-1-V^2,\qquad
 w^2-U^2=2(P+V),\qquad
 T=\frac{2(P+V)}{w+U}.
\tag{10}
\]
We prove H'>0 on the whole feasible wrong-sign arc V<=1/2.
If T<=0 this follows immediately. Otherwise P+V>0, so
`-p_0<V<=1/2`. It suffices to prove
\[
                 E:=T\left(1+\frac{(1-V)\tan h}{w}\right)<1.
\tag{11}
\]

## 3. A monotone envelope retaining the containing radius

At fixed V, increasing P increases T, since U decreases.
For T>0, increasing q decreases T:
\[
 T_P=1/U>0,\qquad
 T_q=\frac1{2w}-\frac1{2U}<0.
\tag{12}
\]
The factor `(1-V)/w` also decreases with q. Consequently,
after any nonnegative bound for tan h independent of P,q,
the largest expression in (11) is bounded by setting
\[
                            P=p_0,\qquad q=q_L.
\tag{13}
\]
For the positive-V bound below, `(P-V)/Y` likewise increases
with P and decreases with q. All these comparisons keep
their roots positive on the enlarged domain, because
\[
 Y_0^2:=q_L-(1+p_0)^2=\frac{174241}{250000}
        >\left(\frac{417}{500}\right)^2
        >\left(\frac56\right)^2.
\tag{14}
\]
At (13), both w and U are at least Y_0 for
`-p_0<=V<=1/2`. Thus no root-domain extension is implicit
in the envelope argument.

### 3.1 The intrinsic branch 0<=V<=1/2

Since h<=z and V>=0,
\[
 \tan h\le\tan z
     =\frac{P-V\sec z}{Y}\le\frac{P-V}{Y}.
\tag{15}
\]
At the envelope (13), the two circle arcs w(V),U(V) are
concave. Positive squaring at their endpoints gives
\[
\begin{array}{c|cc}
 V&w&U\\ \hline
 0&>1707/1000&>1152/1000\\
 1/2&>1914/1000&>1037/1000.
\end{array}
\tag{16}
\]
Their chords and (14) therefore imply
\[
                w+U>57/20,\quad
                w>17/10+(2/5)V,\quad Y_0>417/500.
\tag{17}
\]
Use (10),(15)--(17) in (11). It is enough to show
\[
 \frac{2(p_0+V)}{57/20}
 \left\{1+\frac{(1-V)(p_0-V)}
                 {(417/500)(17/10+(2/5)V)}\right\}<1.
\tag{18}
\]
After multiplication by the positive denominator, the
difference from one is the explicit cubic
\[
 D_+(V)=\frac{1320979}{2500000}
        -\frac{360539}{312500}V
        +\frac{833}{625}V^2-2V^3.
\tag{19}
\]
The maximum of its derivative, by completing its square,
is `-4020307/4687500<0`. Thus it decreases on this entire
branch and
\[
                         D_+(1/2)=86823/2500000>0.
\tag{20}
\]
This proves (11) for V>=0.

### 3.2 The intrinsic branch -p_0<V<=0

Now use `tan h<=13/15`. At the envelope (13), put
`y=p_0+V`, so `0<y<=p_0` and `Z=1+p_0-y`.
Concavity of the two circle arcs gives the chord bounds
\[
                  w+U>5/3+(3/2)y,\qquad
                  w>5/6+(11/10)y.
\tag{21}
\]
At y=0 both roots equal Y_0>5/6. At y=p_0, the first
row of (16) proves (21), with the exact endpoint reserves
\[
 \frac{2859}{1000}-\left(\frac53+\frac32p_0\right)=\frac1{750},
\]
\[
 \frac{1707}{1000}-\left(\frac56+\frac{11}{10}p_0\right)=\frac1{3750}.
\tag{22}
\]
Consequently it is enough for (11) that
\[
 \frac{2y}{5/3+(3/2)y}
 \left\{1+\frac{(13/15)(1+p_0-y)}{5/6+(11/10)y}\right\}<1.
\tag{23}
\]
Its cleared difference is
\[
 D_-(y)=\frac{25}{18}-\frac{12697}{7500}y+\frac{71}{60}y^2
\]
\[
 \hspace{11mm}=\frac{71}{60}
                 \left(y-\frac{12697}{17750}\right)^2
                  +\frac{625733573}{798750000}>0.
\tag{24}
\]
This proves (11) for V<=0, and therefore H'>0 throughout
the whole wrong-sign arc. The two branches are selected by
the exact sign of V; there is no angular partition or sampled
minimum in this argument.

## 4. Reach G zero, retaining a strict middle-circle loss

Suppose the optimized starting point has V<1/2. Decrease h
while keeping H and the lifted A fixed. Since V'=-U<0,
V increases, G's transverse coordinate in (6) decreases,
and its q-circle primary increases. Sorting and the true
core persist. Equation (9), proved positive above, means
that H(h) strictly decreases, so HG0 stays feasible with
strict slack after any positive movement.

This path must reach V=1/2 before h=0. Otherwise (8) at
zero would give `b_H>=3/2-V(Theta)>=1`, contradicting
b_H<.9. The same contradiction excludes an endpoint at
both V=1/2 and h=0. Hence the reached G-zero endpoint has
\[
                  h'>0,\qquad V(\Theta+h')=1/2,
\tag{25}
\]
and strict HG0 slack. Its frame is between H and the old G
frame, so the original real-frame spread has not increased.

If the optimized starting point instead has V>=1/2, set
G's transverse coordinate to zero immediately. Its original
transverse coordinate was strictly positive, so decreasing
it and increasing its primary makes HG0 strictly slack.
The same positive h is retained.

In either case this strict slack preserves a strict A-circle
loss after the temporary lift. If V>1/2, decrease A's
primary a sufficiently small positive amount, keeping V>=1/2.
If V=1/2, make the same small primary decrease and decrease
h continuously to retain V=1/2. The derivative `V_h=-U<0`
makes this possible, and h remains positive. The strict HG0
slack persists by continuity. Sorting and the primary core
condition are strict before this small change, so they persist
as well. G remains on its q-circle with transverse zero.

Thus any genuinely wrong input sign supplies a strict loss
at its middle circle, even if no earlier loss was present.
Any earlier strict loss there is recreated, and a loss at
the other middle point is unchanged. This proves the local
transport including all its strictness assertions.

## 5. Remove both intermediate sign assumptions after AB alignment

Consider the ordered hard-owner class of
`HAND_G5_ALL_OUTER_SIGNS_ORDERED_SHARP_REDUCTION.md`, retaining
its H,A,B,D,E normal signs, its sorted circles and true core,
its frame order and spread, and its original owner list, but
allow arbitrary signed transverse coordinates at G and T.
For original candidates, the global zero-owner sign theorem
restricts a wrong sign to HG0 or TD2. The original global
quarter-owner sign facts can supply the retained H,A,B,D
signs separately; they are not assumed for the comparison
intermediates created below.

**Ordered hard-class theorem without G/T sign hypotheses.**
Every such candidate has q>=q_*. At equality G and T already
have their normal weak signs in the original candidate, its
three original zero frame differences vanish, and its original
five anchors are the stationary anchors. For an original
packing, the full weak five-parameter equality family and
converse follow as in the existing ordered theorem.

Use the stationary enclosure
\[
 q_L<q_*<Q_1:=1957767069/500000000<Q.
\tag{26}
\]
A q>Q_1 proves the strict bound directly. A q<q_L may first
be enlarged to q_L without changing its original centers.
It therefore suffices to use (1), and no enlargement occurs
in an equality argument.

First apply
`HAND_G5_AB_ALIGNMENT_WITH_ARBITRARY_INTERMEDIATE_SIGNS.md`.
This derives, before any use of the middle tangents,
\[
                              b_A+b_B=1
\tag{27}
\]
at a common frame between D and H. It retains the actual
H,D,E data and both mixed constraints. Both wrong signs
may be present at this stage; their exact cap realizations
still have those strict signs. All earlier A/B losses are
retained separately.

Choose a middle tangent at least 1/2 as the large side.
If its intermediate sign is normal, use precisely the local
alternatives in Section 3 of the existing all-outer-sign
theorem: align an already aligned, canceling, positive
noncanceling, or small-transverse negative side; retain a
negative noncanceling side if its tangent is greater than
1/2. These are local comparisons and do not use the other
intermediate's sign.

If the large side has a wrong sign, Sections 1--4 apply,
since its tangent is at least 1/2. They give a positive-error
G/T-zero state with a strict middle-circle loss. Regard zero
as the normal weak transverse sign and apply Section 5 of
`HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md`.
Its direct positive-error transport aligns the pair. That
note's Section 4 retains the strict loss through its primary
lift: lifting a point below q makes its hard projection
strictly greater than 1/2, so the endpoint comparison is
strict and recreates the loss.

In every alternative the large middle primary exceeds 1.1.
For an aligned pair this follows from the aligned composite
and b_outer<.9. For a retained negative noncanceling pair
its core cap has
\[
 D_-(e)=1+(1/2-b_{\rm outer})\sec e+(13/12)\tan e>3/5,
\]
which gives the same primary bound at its nonnegative hard
tilt. Its actual circle then gives b_large<.665, because
`1.6^2+1.165^2>Q`. By (27),
\[
                         .335<b_{\rm small}\le.5.
\tag{28}
\]

If the small side has a wrong sign, apply Sections 1--4
again, now using (28). This gives a normal weak sign at a
positive outer error, retains the same circle ceiling, and
creates a strict small-middle loss. If its sign was already
normal, retain its previous comparison unchanged. H,D,E,
their frames and their mixed inequalities have not changed
in either case. Both-sided wrong signs have therefore been
handled without assuming either one absent.

## 6. Join the existing sharp normal-sign reduction

The output of Section 5 is exactly the input used in Section 4
of `HAND_G5_ALL_OUTER_SIGNS_ORDERED_SHARP_REDUCTION.md`:
the large side is aligned or retains one large-transverse
negative noncanceling composite; the small tangent satisfies
(28); and the small side has a normal signed intermediate
or its previously retained normal-owner cap. The new G/T-zero
state satisfies the actual positive HG0/TD2 inequalities, so
it is also an allowed input for that section.

That section aligns the small side. A positive noncanceling
side uses the same continuous boundary comparison as before.
Its active G/T-zero endpoint is excluded either by the
ordinary G-zero theorem, if the large side has aligned, or
by the mixed G-zero/negative domain and stress, if the large
side retains a negative error. Those endpoint exclusions
allow signed E, so local reflection of the T side is valid.
An inherited middle-circle loss survives the positive
primary lift by the strict argument cited above.

The resulting necessary five-anchor system is therefore
exactly (15) of that all-outer-sign note: the unchanged H,D,E
data, the common A/B tangent sum, and either two aligned
composites or one remaining large negative noncanceling
composite. Its Sections 5--6 prove q>=q_* and retain both
separate middle-circle losses to the final positive masses.
This use of its proof requires no reconstruction of an
original packing or unretained nonneighbor inequalities.

Suppose q=q_*. Any originally wrong G/T sign was still
strictly wrong in its exact AB cap realization and therefore
created a strict middle-circle loss in Section 4. The
subsequent positive-error transport and sharp terminal
retain that loss, contradicting equality. Hence the
original G and T already had their normal weak signs.

Apply `HAND_G5_ALL_OUTER_SIGNS_ORDERED_SHARP_REDUCTION.md`
afresh to the original candidate. Its hypotheses now all
hold on those original centers, so it gives the three
original zero differences and the unique original stationary
anchors, together with the full equality-family conclusion
for an original packing. No equality identification is made
only through a transformed descendant.

The G and T transverse-sign entry conditions have thus been
removed from the ordered hard-owner class, for either sign
of either outer frame error and either original AB owner.
The specified hard/mixed owners and frame order remain
separate global-entry questions. All new scalar comparisons
are the continuous monotonicity (9)--(12), the explicit
cubic (19), the completed square (24), and the AB cap proof
in the companion note. No angle mesh, state cover, numerical
oracle, Lean compilation or CI is a premise.
