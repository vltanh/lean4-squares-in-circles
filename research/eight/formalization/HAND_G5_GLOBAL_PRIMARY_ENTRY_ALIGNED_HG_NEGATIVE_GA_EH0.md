# An aligned HG negative-primary endpoint with EH0 reaches the hard class

## 1. Scope: arbitrary AB and TD, and arbitrary T sign

Put
\[
 q_L=19577/5000,\qquad Q=9789/2500,\qquad
 h=7/10,\qquad K=13/12.
\tag{1}
\]
Retain a necessary seven-cycle at a common actual ceiling
\(q_L\le q\le Q\), with sorted shifted corners, true central
exclusion and real frame spread at most h. H,A are nonnegative,
B,D,E are nonpositive, G is nonpositive, and **T has arbitrary
signed tangent**. Assume the actual retained witnesses
\[
 HG\in\{0,2\},\quad GA1,\quad AB\in\{0,2\},\quad BT2,
 \quad TD\in\{0,2\},\quad DE\in\{2,3\},\quad EH0,
\tag{2}
\]
and only the alignment and order
\[
                   \theta_H=\theta_G>\theta_A.
\tag{3}
\]
Neither AB nor TD is assumed aligned. No order involving
B,T,D,E is assumed. For necessary cycles apart from original
candidates, retain the original zero-owner implication
\(TD0\Longrightarrow y_T>0\). Finally retain the usual E
radial alternative
\[
               a_E\le7/12\quad\hbox{or}\quad
               a_E\ge\max\{b_H,b_D\}.
\tag{4}
\]
Every original true-core or outer boundary E satisfies (4).

**Theorem.** There is a necessary descendant at the same q
with actual GA0 and BT2 and every hypothesis of the
[arbitrary-sign hard-owner sharp theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md).
If GA0 was unavailable initially, the descendant has a strict
H-circle loss. A,B,T,D,E, including all their frames, remain
identical. All existing losses at these five points persist.
Consequently this entire class has \(q\ge q_*\), and an
initially unavailable GA0 gives \(q>q_*\).

The local H/G construction in Sections 2--6 does not use BT2
or any other B/T/D constraint. It remains valid with an actual
BT3 witness retained, or with any unchanged opposite-side
data. BT2 is used only for the final sharp-theorem application
in Section 7. Thus the local reduction can also be used before
a separate conversion on the opposite primary side.

The same theorem holds with EH1 in place of EH0 if its actual
positive error satisfies
\[
                        0<\theta_H-\theta_E\le11/50.
\tag{5}
\]
This latter restriction is unnecessary for EH0. Section 5 proves
EH0 preservation on the full original interval \((0,h]\).

This note removes the AB/TD alignment, their frame orders, and
the T-sign hypotheses from the EH0 part of the earlier
[aligned negative-GA theorem](HAND_G5_ALIGNED_NEGATIVE_GA1_TO_HARD_OWNER.md).
It does not assert (5) for an arbitrary EH1 input.

## 2. The original exceptional primary supplies all local cuts

If GA0 is available, apply the hard-owner theorem directly.
Assume it is unavailable and put
\[
 t=\theta_H-\theta_A>0,\qquad
 D_G=b_G+1/2,\qquad X_A=a_A+1/2,\quad Y_A=b_A+1/2.
\]
The exact comparison-vector calculation for genuine negative
GA1 gives
\[
 q>1+(a_G+1/2)^2+D_G^2
       +2D_G\cos t+2(a_G+1/2)\sin t.
\tag{6}
\]
This uses the actual GA1 inequality and the unavailable GA0
inequality, not an outer-circle equality at either point.
Its full derivation is Section 2 of the cited aligned theorem.
Sorting and (6) give \(b_G<1/2\); true-core avoidance then gives
\(a_G\ge7/12\). Lower only G's primary to \(7/12\).
HG at alignment is unchanged, GA1 improves, and G stays on
or outside the true core with a smaller circle.

The same comparison, now with K, gives
\[
 D_G<82/125,\qquad b_G<39/250,
 \qquad b_H\ge1-b_G>211/250=.844,\qquad a_H<1.
\tag{7}
\]
The positive square reserves are
\[
 K^2+(1+82/125)^2-Q=781/2250000,
 \qquad 9/4+(168/125)^2-Q>0.
\]
Both EH0 and EH1 have projection at most \(a_H<1\) when
their error is nonpositive. Thus the actual retained EH
error is necessarily positive:
\[
                         \epsilon=\theta_H-\theta_E>0.
\tag{8}
\]
Only the unchanged actual EH inequality and E's nonpositive
sign are used in this conclusion.

## 3. Contact normalization changes H and G only

Keep A fixed and use x for the changing positive tilt
\(\theta_H-\theta_A=\theta_G-\theta_A\). Define
\[
 P=a_A-1/2,\qquad
 D(x)=P\sec x-K\tan x,\qquad
 b_G(x)=D(x)-1/2,\qquad b_H(x)=3/2-D(x).
\tag{9}
\]
These are the exact aligned HG and GA1 contact equations.
Their derivatives are
\[
 D'=D\tan x-K,
 \qquad r(x):=b_H'(x)=K-D\tan x.
\tag{10}
\]
At x=t, the retained GA1 inequality gives \(D(t)\ge D_G\),
and aligned HG gives \(b_H\ge b_H(t)\).

Before reusing the exceptional comparison at this new contact,
its sorting and circle eligibility can be checked with coarse
bounds alone. Since \(P<.915\), \(t\le h\), and
\(\tan(t/2)<3/8\), one has \(P\tan(t/2)<K\). Hence
\[
 D(t)-P=\frac{P(1-\cos t)-K\sin t}{\cos t}<0,
 \qquad \frac12\le D_G\le D(t)<.915.
\tag{9a}
\]
The new G therefore has \(0\le b_G<.415<7/12\), is on
the true flat core, and its circle is below
\(K^2+.915^2=723901/360000<q_L\). Its comparison-vector
component is strictly positive already from
\[
 K\cos t-D(t)\sin t
 >(13/12)(.7648)-(.915)(.6443)>.23.
\tag{9b}
\]
Thus the comparison is eligible before any of the sharper
cuts below are derived; there is no sorting or circle assumption
being inferred from an ineligible application of that comparison.

Use H's own original corner value \(q_H\le q\). Lower H's
tangent to \(b_H(t)\), increasing its primary along that
same circle, and set G by (9). GA1 and HG become equalities.
Increasing G's tangent cannot create GA0, whose projection
decreases with that tangent. Thus the exceptional comparison
remains applicable throughout this normalization.

Here are the bounds that also justify the normalization.
While GA0 is unavailable, the contact equations and A's
actual circle imply
\[
 \mathcal R(D,x):=1+D^2+K^2+2D\cos x+2K\sin x<Q.
\tag{11}
\]
Also \(D>3/5\), since H's tangent is only decreased from
an original value below .9. The function in (11) increases
with x on the domain in question. Positive squaring and
the lower Taylor bounds consequently give
\[
 D<d_*:=\sqrt{Q-K^2}-1<82/125,
 \qquad 0<x<9/100,
 \qquad 1<r(x)\le K.
\tag{12}
\]
For the tilt cut,
\(\mathcal R(3/5,9/100)-Q>283963/36000000\).
For the lower r bound use
\(D<2/3\) and \(\tan(.09)<.091\).
In particular
\[
 .844<b_H<.9,\quad b_H\le a_H<1,
 \qquad .1<b_G<.156<7/12,
 \qquad K^2+D^2<q_L.
\tag{13}
\]
Thus G is strictly sorted, on the true flat core, and strictly
inside the actual q-circle. H stays sorted and strictly outside
the true core; lowering its tangent improves sorting.

For EH1, normalization increases its projection because it
increases H's primary. For EH0, at its fixed error \(\epsilon\),
the derivative of its projection with respect to H's tangent is
\[
 -\frac{b_H+1/2}{a_H+1/2}\cos\epsilon+\sin\epsilon<0.
\tag{14}
\]
Indeed (13) makes the ratio greater than \(112/125=.896\),
whereas \(\tan\epsilon\le\tan h<.843\). Therefore lowering
H's tangent also improves EH0, on the entire allowed interval.

## 4. H's primary gains faster than one along the exceptional contact

Now decrease x, with H on its retained \(q_H\)-circle and
G given by (9). The magnitude of H's primary derivative is
\[
 \mathcal A(D,x):=-a_H'(x)
   =\frac{(2-D)(K-D\tan x)}{\sqrt{q_H-(2-D)^2}}>1.
\tag{15}
\]
For completeness, the whole-domain verification is recorded
here. It is enough to prove
\[
 F(D,x)=(2-D)^2\{1+(K-D\tan x)^2\}>Q.
\tag{16}
\]
At fixed D, F decreases with x. Its minimum on (11) is
therefore on the intrinsic upper curve \(\mathcal R(D,x)=Q\),
where
\[
 \frac{dx}{dD}=-\frac{D+\cos x}{K\cos x-D\sin x}.
\]
On that curve, (12) gives
\[
 \frac{168}{125}<2-D<\frac75,\quad
 1<K-D\tan x\le K,\quad K\cos x-D\sin x>1,
\]
\[
 \sec^2x<101/100,\qquad D+\cos x<83/50.
\]
The two elementary reserves used here are
\[
 K(1-.09^2/2)-(2/3)(.09)-1=4547/240000,
\]
\[
 (1-.09^2/2)^2-100/101=73422661/40400000000.
\]
Differentiation along the upper curve, dropping negative
terms, gives
\[
 \frac{d}{dD}F(D,x(D))
 <-4\frac{168}{125}
  +2(7/5)^2K(2/3)(101/100)(83/50)
 =-708029/1125000<0.
\tag{17}
\]
Its smallest value is at \((d_*,0)\), and
\[
 F(d_*,0)>(168/125)^2(1+K^2)
                       =Q+667/62500>Q.
\tag{18}
\]
This proves (15) at every point before GA0 becomes feasible.
It uses no AB, BT, TD or DE condition.

## 5. Full-interval EH0 preservation with a uniform reserve

Write H's shifted corner as
\[
 X=a_H+1/2,\qquad Y=b_H+1/2,
 \qquad Y\le X<3/2,
\]
and let \(\epsilon(x)=\theta_A+x-\theta_E\).
On its positive-error portion, the actual EH0 slack is
\[
 L_0(x)=a_H(x)\cos\epsilon(x)
              +b_H(x)\sin\epsilon(x)-b_E-W(\epsilon(x)).
\tag{19}
\]
Using \(a_H'=-rY/X\), its exact derivative divided by the
positive cosine is
\[
 \frac{L_0'}{\cos\epsilon}
  =Y-1-rY/X+\tau(r-X+1),\qquad \tau=\tan\epsilon.
\tag{20}
\]
Here \(\tau<.843<Y/X\). Since r>1, the coefficient of r
in (20) is negative; hence
\[
 \begin{split}
 \frac{L_0'}{\cos\epsilon}
 &<Y-1-Y/X+\tau(2-X)\\
 &=Y(X-1)/X-1+\tau(2-X)\\
 &\le X-2+\tau(2-X)
 =-(2-X)(1-\tau).
 \end{split}
\tag{21}
\]
Sorting was used only in the non-strict third line. Therefore
\[
 L_0'<-(2-X)(\cos\epsilon-\sin\epsilon)
 <-\tfrac12(\cos h-\sin h)<-3/50.
\tag{22}
\]
The last rational comparison follows from
\(\cos h>.7648\), \(\sin h<.6443\).

Thus decreasing x increases the actual EH0 slack by more
than \((3/50)\) times the movement, **for every positive
EH0 error up to h**. No E-circle equality, E radial kind,
mixed-owner conversion, or other alignment has entered this
calculation. Every weak original EH0 contact is covered.

## 6. The short EH1 alternative

For EH1 assume (5). Normalization improved it, and decreasing
x only decreases its error, so the same upper bound holds
throughout. At a possible active EH1 boundary, put
\(X_E=a_E+1/2\), \(Y_E=b_E+1/2\), \(P_H=a_H-1/2>.344\).
Its contact identity is
\[
 -X_E\sin\epsilon+Y_E\cos\epsilon=P_H-\sin\epsilon.
\]
The opposing angular derivative is
\[
 \mathcal U_E=(a_E-1/2)\cos\epsilon+(b_E+1/2)\sin\epsilon
            =X_E\cos\epsilon+Y_E\sin\epsilon-\cos\epsilon.
\]
One use of E's actual circle gives
\[
 \mathcal U_E
 \le\sqrt{Q-(P_H-\sin\epsilon)^2}-\cos\epsilon
 <\sqrt{Q-(.344-.22)^2}-(1-.22^2/2)<1.
\tag{23}
\]
The last positive square reserve is
\[
 (2-.22^2/2)^2-\{Q-(.344-.22)^2\}
                         =89041/25000000>0.
\]
At every possible first feasibility boundary, the slack's
x-derivative is \(-\mathcal A+\mathcal U_E<0\), by (15).
Decreasing x consequently preserves EH1 and makes an initial
contact strict. The same first-boundary argument prevents any
later return to zero slack. This argument is independent of
E's radial kind and all AB/TD data.

## 7. The hard endpoint and original equality

Stop at the first actual GA0 witness, or at x=0 where GA0
and GA1 coincide. All preceding cuts hold while GA0 is
unavailable. The path cannot reach \(\epsilon=0\) first:
either actual EH witness would then require
\(a_H-b_E\ge1\), contrary to \(a_H<1\).
The bounds (12)--(13) exclude every circle, tangent, sorting
and core boundary before the stop. The path therefore reaches
the specified endpoint after positive movement.

The aligned H/G frame moves toward the fixed A frame, so
the full real frame interval never expands. HG remains aligned
and retains both transverse witnesses. The GA negative
variation and EH positive variation each decrease by the
movement. All other actual errors and witnesses remain
unchanged. H's tangent decreases, so (4) persists.

At the stop EH has strict slack by (22) or Section 6. Decrease
H's primary by a sufficiently small positive amount. HG uses
only its tangent, and EH tolerates the small decrease. H is
strictly sorted after its positive tangent decrease, and its
true-core exclusion is strict because \(b_H>.844\).
This records a strict H-circle loss at the original q.

The descendant has actual GA0 and BT2, all three zero owners
in their original transverse sets, the original mixed-owner
sets, and the E alternative (4). G is normal and T retains its
original arbitrary sign. The zero-owner implications needed by
the arbitrary-sign hard theorem are retained: G is negative,
and any TD0 implication was never changed. That theorem now
gives \(q\ge q_*\). At \(q=q_*\) it requires each of its
five anchors, including H, to have the stationary circle value.
The strict H loss contradicts this. Hence a genuinely exceptional
negative GA1 in the present class satisfies \(q>q_*\).

If the original ceiling was below \(q_L\), enlarge it to
\(q_L\) without changing centers and apply the same conclusion;
this contradicts \(q_L<q_*\). If GA0 was originally available,
apply the hard theorem directly to the original states for its
complete equality characterization. No transported H is
identified with its ancestor.

Only H and G were changed. In particular this theorem makes
no assumption about a hidden AB/TD alignment, the T sign, the
E frame relative to D, or the sign of the H/D span. Its remaining
EH1 input (5) is explicit. Every calculation is on a whole
continuous domain with the displayed rational reserves.
