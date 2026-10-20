# Direct D/T/E entry after the first aligned negative primary conversion

## 1. Local theorem with E's original sign

Put
\[
 q_L=19577/5000,\quad Q=9789/2500,\quad
 h=7/10,\quad K=13/12,\qquad q_L\le q\le Q.
\tag{1}
\]
Retain sorted true-core states at the same actual circle
ceiling q, with all real frames in an interval of length
at most h. H,A are nonnegative, B,D,E are nonpositive,
G is negative, and T is nonnegative. Retain actual
\[
 HG,AB,TD\in\{0,2\},\quad GA0,\quad BT3,
                  \quad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
Assume
\[
 \theta_T=\theta_D<\theta_B,
 \qquad b_H>.844,\quad a_H<1,
 \qquad \alpha=\theta_H-\theta_D<.21.
\tag{3}
\]
Let E be on its true-core boundary or its actual outer
q-circle. There is no order assumption involving E, no
EH-error bound, and no AB alignment assumption. H and D
need not be outer at q. In particular no H or D primary
lift is part of this theorem.

**Direct second-primary theorem.** There is a necessary
descendant at the same q with actual BT2, the other owner
sets in (2), and the radial hypothesis required by the
arbitrary-sign hard-owner theorem. H,G,A,B, including all
their coordinates and frames, stay identical. If BT2 was
unavailable initially, the descendant can be chosen with a
strict D-circle loss. Every preexisting H-circle loss persists.

Consequently this class satisfies q>=q_*, and an initially
unavailable BT2 gives q>q_*. The construction below keeps
E nonpositive throughout. It does not apply a reflected
EH theorem after changing E's sign.

If BT2 is already actual, select it and apply the hard-owner
theorem directly. The rest of the proof concerns its genuinely
unavailable case.

## 2. The E-independent negative-primary contact

The local negative-primary comparison on D/T/B is the
reversed counterpart of the H/G/A comparison in Sections
2--4 of
[the aligned negative-GA local theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_HG_NEGATIVE_GA_EH0.md).
This invocation uses no E state or E witness. Write
\[
                      u=\theta_B-\theta_D>0.
\]
Actual negative BT3 and unavailable BT2, together with
aligned TD, give
\[
 0<u<.09,\quad .1<b_T<.156,
 \qquad b_D>.844,\qquad a_D<1,
                       \qquad a_T\ge7/12.
\tag{4}
\]
Lower T's primary to 7/12. It improves its negative BT3
witness and does not affect aligned TD. Put
\[
 P=a_B-1/2,\qquad
 Z(u)=P\sec u-K\tan u,
 \qquad b_T(u)=Z(u)-1/2,\qquad b_D(u)=3/2-Z(u).
\tag{5}
\]
These are exactly BT3 and aligned TD at contact. At the
initial u, increase T's tangent to the value in (5) and
decrease D's tangent to the value in (5), moving D on its
own initial circle q_D<=q. The same eligibility check as in
the cited local theorem gives
\[
 \tfrac12\le Z<.915,
 \quad K^2+Z^2<q_L
\]
before the sharper exceptional comparison is reapplied.
Thus the contact normalization is sorted, on the true flat
core at T, and contained. Increasing T's tangent cannot
create BT2, whose projection decreases with that tangent.
The sharper contact bounds are therefore valid throughout:
\[
 \begin{gathered}
 .6<Z<\sqrt{Q-K^2}-1<.656,\qquad 0<u<.09,\\
 r:=b_D'(u)=K-Z\tan u>1,
 \qquad .844<b_D<.9,\quad b_D\le a_D<1,\\
 \mathcal A:=-a_D'(u)
       =\frac{(2-Z)(K-Z\tan u)}
                   {\sqrt{q_D-(2-Z)^2}}>1.
 \end{gathered}
\tag{6}
\]
The last strict inequality is exactly the E-independent
circle calculation in Sections 3--4 of the cited theorem.

Normalization preserves either original DE owner at every
signed error d in [-h,h]. For DE3 it increases D's primary,
whose coefficient is one. For DE2 its projection is
\[
                     a_D\cos d+b_D\sin d+b_E.
\tag{7}
\]
Its derivative with respect to D's tangent on D's own
circle is
\[
 -\frac{b_D+1/2}{a_D+1/2}\cos d+\sin d<0,
\tag{8}
\]
because the ratio exceeds .896 while tan h<.843. Thus
decreasing D's tangent improves (7) for either sign of d.
No other witness involving H,G,A,B or E changes in this
normalization. All subsequent motion keeps (5), D's own
circle, and its strict bounds (6), until BT2 first becomes
actual or u=0.

Finally, either actual EH owner and a_H<1 imply
\[
                          p=\theta_H-\theta_E>0.
\tag{9}
\]
At a nonpositive EH error its projection is at most a_H,
whereas the required width is at least one. This observation
also prevents any of the later paths from reaching p=0
while retaining an actual EH witness.

## 3. If E is below D, move E alone to D

Suppose first that n=theta_D-theta_E>0. Increase E's frame
toward D, with movement parameter tau, so that
\[
                  n_\tau=n-\tau,\qquad p_\tau=p-\tau.
\tag{10}
\]
Keep H,D,T and every other point fixed. On E's radial
arc write a=a(b) and v=-a'(b). The actual core and outer
arcs, including their flat/curved junction, satisfy
\[
 0\le v\le1,\qquad
 b-va=\frac{1-v}{2}\ \text{on curved core},
 \qquad b-va=-\frac{1-v}{2}\ \text{on outer}.
\tag{11}
\]
On the flat core a=7/12 and v=0. As b decreases, sorting
improves; the outer corner stays at q and the core corner
does not increase.

Initially keep b fixed until EH contact requires a decrease.
The negative-DE2 and negative-DE3 margins both increase at
fixed b: their respective angular derivatives are
\[
 C_D(n)=(a_D-1/2)\sin n+(b_D+1/2)\cos n>1.249,
\tag{12}
\]
\[
                  (a+1/2)\cos n+(b-1/2)\sin n>0.
\tag{13}
\]
For (12), the lower bound .344 sin n+1.344 cos n is
concave and its two endpoint values on [0,h] exceed 1.249:
\[
 1.344>1.249,
 \qquad .344(.6442)+1.344(.7648)=1.249496>1.249.
\tag{14}
\]
For (13), use a>1/2, b>=0 and tan n<1.

### 3.1 Retaining EH0

At an active EH0 contact set
\[
 C_H(p)=(b_H-1/2)\cos p-(a_H-1/2)\sin p,
 \qquad \beta_0=\max\{C_H(p),0\}<.4.
\tag{15}
\]
Decrease b at rate db/dtau=-beta_0 while contact is active.
If C_H<=0, keeping b fixed improves EH0 instead, and the
path leaves contact. This defines a continuous feasible
piecewise contact path. At contact,
\[
 b=(a_H-1/2)\cos p+(b_H-1/2)\sin p-1/2
                         <\sqrt{.5^2+.4^2}-1/2<.141.
\tag{16}
\]
Thus a core contact lies on its flat part.

The DE2 derivative on that contact is C_D-beta_0>.849.
The DE3 derivative is
\[
 (a+1/2-\beta_0)\cos n
                      +(b-1/2-v\beta_0)\sin n.
\tag{17}
\]
On the flat core it is bounded below by
\[
 (K-.4)\cos h-.5\sin h
             >(K-.4)(.7648)-.5(.6443)>.2.
\tag{18}
\]
On the outer arc a>.899 and v<=1, so it is bounded below by
\[
                   .999\cos h-.9\sin h
                         >.999(.7648)-.9(.6443)>.18.
\tag{19}
\]
Both actual negative DE owners are therefore preserved,
including at every weak original contact.

### 3.2 Retaining EH1

At EH1 contact the required tangent decrease is
\[
 \beta_1=\frac{db}{dp}
       =\frac{(a-1/2)\cos p+(b+1/2)\sin p}
                         {\cos p+v\sin p}>0.
\tag{20}
\]
The denominator is positive on the entire interval. A core
contact must be flat: a_H<1 and a<=7/12 give
\[
 b+1/2<\frac{.5+(1/12)\sin h}{\cos h}
             <\frac{.5+(1/12)(.6443)}{.7648}<.725.
\tag{21}
\]
Consequently
\[
              \beta_1<1/12+.725(.843)<.695
                  \quad\text{on the core}.
\tag{22}
\]
On the outer circle put X=a+1/2, Y=b+1/2 and
Z_E=X cos p+Y sin p. Then (20) becomes
\[
                       \beta_1=X\{1-\cos p/Z_E\}.
\]
Since X<1.915 and Z_E<=sqrt Q<1.9788,
\[
         \beta_1<1.915\{1-.7648/1.9788\}<1.175.
\tag{23}
\]
Therefore the DE2 derivative C_D-beta_1 is strictly
positive for both radial kinds.

For DE3 the exact radial identity of Section 4 in
[the outside DE3 transport](HAND_G5_GLOBAL_PRIMARY_ENTRY_LONG_EH_OUTSIDE_TRANSPORT.md)
applies on the entire positive n,p domain; its identity
does not require that p>.22. For completeness, with
x=tan n and y=tan p, its derivative multiplied by the
positive factor (1+vy)/cos n is
\[
             1-\frac{1-v}{2}(x+y)+(b-va)(x-y)-vxy.
\tag{24}
\]
On the outer arc this is 1-x{1-v+vy}>=1-x>0;
on curved core it is 1-y{1-v+vx}>=1-y>0;
on flat core it is
1-(1/2-b)x-(1/2+b)y>=1-max{x,y}>0.
Thus DE3 also remains actual on every contact segment.

### 3.3 The endpoint is actual DE alignment

Neither radial kind has an unexplained stopping boundary.
Sorting improves, the contact denominators stay positive,
and the flat/curved core derivatives join. A zero tangent
b=0 is impossible before or at DE alignment: for n>=0
the actual DE2 projection is
\[
                       a_D\cos n-b_D\sin n<1,
\]
and the actual DE3 projection is a_D-a sin n<1. Their
required widths are at least one. The strict a_D<1 bound
includes n=0.

If p<=n, this otherwise feasible path would reach p=0
before or at DE alignment, contradicting (9). Hence that
case cannot occur. Otherwise the path reaches DE alignment
with
\[
                  p_{\rm end}=p-n=\alpha>0,
                         \qquad 0<\alpha<.21.
\tag{25}
\]
This also proves H>D for the feasible E-below-D case;
it was not assumed. The E frame has moved within its
original E/D interval, and its radial kind is unchanged.

## 4. If E is above D, advance D/T until alignment or BT2

Now suppose d=theta_E-theta_D>0. Equation (9) and (3)
give
\[
                           0<d<\alpha<.21.
\tag{26}
\]
Keep E and H fixed. Decrease u in (5), so aligned D/T
move toward the fixed B frame. Both u and d decrease by
the same amount. H/G/A/B and both E witnesses other than
DE remain unchanged.

For the actual positive-error DE2 margin
\[
 L_2(u)=a_D\cos d+b_D\sin d+b_E-W(d),
\]
the added constant b_E does not change the derivative
calculation of the local EH0 theorem. With
X_D=a_D+1/2, Y_D=b_D+1/2 and tau_d=tan d,
\[
 \frac{L_2'}{\cos d}
       =Y_D-1-rY_D/X_D+\tau_d(r-X_D+1)
       <-(2-X_D)(1-\tau_d).
\tag{27}
\]
Thus L_2'<-.06, on the full allowed positive-error
interval and in particular on (26).

For the actual DE3 margin,
\[
 \begin{split}
 L_3(u)&=a_D+a_E\sin d+b_E\cos d-W(d),\\
 L_3'(u)&=-\mathcal A+(a_E-1/2)\cos d
                                      +(1/2-b_E)\sin d.
 \end{split}
\tag{28}
\]
Containment gives a_E<1.415 and b_E>=0. The positive
combination .915 cos d+.5 sin d increases on [0,.21].
Using the elementary Taylor upper bounds,
\[
 \begin{split}
 (a_E-1/2)\cos d+(1/2-b_E)\sin d
   &<.915C_4(.21)+.5S_5(.21)\\
   &=.99912834759<1.
 \end{split}
\tag{29}
\]
Together with \(\mathcal A>1\), this makes L_3'<0 with
a uniform strict reserve. Decreasing u therefore preserves
either actual DE owner and makes its initial contact strict.

Stop at the first actual BT2, or at d=0. If BT2 appears
first, the positive movement has made DE slack strict.
Decrease D's primary by a small positive amount. Aligned
TD is unchanged; DE tolerates the decrease. D is strictly
sorted after its tangent decrease and remains far outside
the true core. This supplies a strict D-circle loss and
completes the local theorem in this alternative.

If DE aligns first while BT2 is still unavailable, retain
that actual alignment and proceed to the next section.
If the two events occur simultaneously, the preceding
strict-DE-slack argument already completes the proof.

## 5. At DE alignment, move D/T/E together

This section includes an initially aligned DE pair and the
aligned endpoints of Sections 3--4. The actual DE contact
at alignment has the same expression for both owners:
\[
                             a_D+b_E\ge1.
\tag{30}
\]
Lower E's tangent, on its same radial arc, to
\[
                             b_E=1-a_D.
\tag{31}
\]
The lower tangent increases E's primary and improves either
positive-error EH projection. It preserves (30) until contact.
By (6), throughout the remaining construction
\[
                        0<b_E<.156.
\tag{32}
\]
Thus a core E is flat and an outer E is strictly sorted.

Continue decreasing u in (5). Keep E's frame equal to D's
frame and keep (31), on its same actual radial arc. If tau
denotes the forward frame movement, then
\[
 \frac{da_D}{d\tau}=\mathcal A>1,
 \quad \frac{db_E}{d\tau}=-\mathcal A,
 \quad \frac{da_E}{d\tau}=v\mathcal A,
 \quad p=\theta_H-\theta_D>0,
 \quad\frac{dp}{d\tau}=-1.
\tag{33}
\]
Both actual DE owners remain aligned contact. The remaining
positive EH error starts below .21 and only decreases.

For EH0, its exact slack derivative is
\[
                 \frac{dL_{EH0}}{d\tau}
                       =\mathcal A-C_H(p)>1-.4=.6.
\tag{34}
\]
For EH1, its exact slack derivative is
\[
 \frac{dL_{EH1}}{d\tau}
    =(\cos p+v\sin p)(\mathcal A-\beta_1).
\tag{35}
\]
The small tangent (32) gives a better whole-domain bound
on beta_1 than was needed in Section 3. On the flat core,
\[
                  \beta_1<1/12+.656(.224)<.231<1.
\tag{36}
\]
On the outer circle use Y_E=b_E+1/2<.656 and
X_E=sqrt(q-Y_E^2). The working radius band gives
\[
 X_E>1.866,\qquad X_E<1.915,
 \qquad v=Y_E/X_E<.352,\qquad \tan p<.224.
\tag{37}
\]
The formula in (20) now simplifies to
\[
 \beta_1=X_E-1+
                  \frac{v\tan p}{1+v\tan p}
       <.915+.352(.224)=.993848<1.
\tag{38}
\]
Thus (35) is strictly positive. Both possible original
EH witnesses acquire strict slack during every positive
segment of this coupled motion.

All non-angular boundaries are excluded by (6),(32),(37).
In particular b_E cannot reach zero while BT2 is unavailable,
since that would give a_D=1. Neither can p reach zero, by
(9). Therefore the path reaches actual BT2 before either
obstruction, or at u=0 where BT2 and BT3 coincide. BT2 was
unavailable at the start of this coupled phase, so its
movement is positive. At its endpoint EH has strict slack.

Record a strict D-circle loss as follows. Lower D's primary
by a sufficiently small positive epsilon and increase E's
tangent by epsilon, staying on E's same radial arc. Equation
(30) remains equality. Strict EH slack tolerates the small
change in E; aligned TD is unchanged. D has become strictly
sorted during its positive frame movement and tangent
decrease, so its small primary decrease is eligible and
keeps its true-core avoidance. An outer E remains on q;
a core E remains flat and has circle below q_L, even after
this small increase. Thus the loss is at the same original q.

## 6. All necessary data and the sharp equality consequence

H,G,A,B and all of their frames have stayed identical.
No initial H-circle loss was spent or repaired. T remains
positive on the true flat core; D remains negative. Both
TD witnesses are actual at its retained alignment. The new
BT2 is an actual feasible witness, selected only when its
feasibility was established. The DE owner changes only if
one elects to select the identical aligned witness; otherwise
the original owner itself was retained. The same original
EH owner was retained throughout.

Every frame movement lies between original frames. The
E-only segment is inside the original E/D interval. D/T
always move toward fixed B; after DE alignment, E follows
inside that same interval. Hence the full real-frame range
never expands. All circle ceilings are the same actual q.
For a boundary-neighbor input, the continuous actual
neighbor separations and the two-square band preserve its
cyclic order and winding, as in
[the boundary-neighbor transport bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
The local inequalities above themselves use only the stated
necessary witnesses, radial arcs and frame interval.
E always stays on its core or outer radial arc, so
\[
            a_E\le7/12\quad\text{or}\quad
            a_E\ge\sqrt{q/2}-1/2\ge\max\{b_H,b_D\}.
\tag{39}
\]
This is exactly the radial alternative used by the sharp
hard-owner theorem. The usual zero-owner sign implications
hold because G is negative and T is positive.

The descendant has actual GA0 and BT2 with all hypotheses
of
[the arbitrary-sign hard-owner sharp theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md).
It gives q>=q_*. In the genuinely unavailable-BT2 case,
Sections 4--5 recorded a strict D-anchor loss. At q=q_*
the hard theorem requires that anchor to have the stationary
circle value, a contradiction. Thus q>q_* in that case.
No transported intermediate or anchor is identified with
its original ancestor, and no G/T circle loss is substituted
for this D-anchor argument.

## 7. Complete application to two genuine aligned negative primaries

Start with the actual both-negative aligned input of
[the stronger original-data span theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SHORT_SPAN.md),
with q_L<=q<=Q, E on its actual core or outer q boundary,
and the original DE/EH owner sets. That theorem gives
H-D<.21 before any state changes.

Use the first-side assembly in Section 5 of
[the original both-negative span note](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SPAN.md).
Its eligible lifts are justified because HG and TD are
aligned. The E-only preparation reaches actual EH0 or
short positive EH1, and the subsequent H/G path reaches
actual GA0 with strict H-circle loss. It changes neither
B,T nor D's frame, so genuine negative BT3 and aligned TD
remain. Its H-frame movement decreases H-D, so the .21
span survives. Its endpoint still has b_H>.844,a_H<1:
the exceptional contact bound is Z<=sqrt(Q-K^2)-1<.656
even at the first GA0 endpoint, and the final small primary
decrease preserves a_H<1.

All hypotheses of the direct theorem in Section 1 are now
present. Apply it without reflecting E. It reaches actual
GA0/BT2 at the same q, preserves the strict H loss, and
also records a strict D loss. Therefore every such original
two-genuine-primary cycle has q>q_*.

For an original ceiling below q_L, first use the original
fixed-witness boundary reduction at the enlarged actual
working ceiling q_L. Its anchors and E radial alternatives
then have precisely the stated same-radius eligibility.
An eligible two-genuine aligned endpoint at that radius is
impossible, since q_L<q_*. Merely enlarging an already
constructed descendant's ceiling is not being used to
manufacture an outer radial equality.

This completes the both-genuine aligned negative-primary
branch. The local theorem deliberately retains the near-H
hypotheses in (3). An arbitrary one-negative-BT input with
GA0 is not claimed to satisfy those hypotheses merely
because GA0 is actual.
