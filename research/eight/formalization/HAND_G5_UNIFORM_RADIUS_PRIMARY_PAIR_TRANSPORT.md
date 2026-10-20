# Positive primary-pair transport at the original radius

## 1. The same-radius statement

Put
\[
 q_L=\frac{19577}{5000},\qquad
 Q_1=\frac{1957767069}{500000000},\qquad
 Q=\frac{9789}{2500},\qquad h=\frac7{10}.
\tag{1}
\]
Fix one actual ceiling
\[
                         q_L\le q\le Q_1<Q.
\tag{2}
\]
All outer circles constructed below have squared radius q.
Write
\[
 R_q=\sqrt q,\quad c_q=\sqrt{q/2}-\frac12,\quad
 a_q=\sqrt{q-\frac14}-\frac12,\quad
 A_q=a_q+\frac12,\quad d_q=a_q-\frac12=A_q-1.
\tag{3}
\]

A boundary-neighbor cycle at q means the geometric domain
of the [boundary-domain bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md),
with every outer Q boundary replaced by the outer q boundary.
In particular its seven actual squares are contained at q,
avoid the open radius-\(1/12\) disk, have one-winding cyclic
order and quarter word 0101011, and retain actual weak
neighboring witnesses. Their real frames have spread below h,
and both captured variations are below h. The only radial
states are the true core and the outer q circle.

Suppose B,D are sorted outer q states with negative signed
tangents, and retain actual BT3 and TD2. Put
\[
 u=d_{BT},\qquad v=d_{TD},\qquad t=u+v>0,
 \qquad |u|,|v|<h,\quad t<h.
\tag{4}
\]
The intermediate T can have either sign and either radial kind.

**Uniform-radius pair theorem.** Replacing only T gives an
actual boundary-neighbor cycle at the same q with either
\[
 \begin{array}{c|cc}
 &BT&TD\\ \hline
 u'=0&2&2\text{ at }t\\
 v'=0&3\text{ at }t&0.
 \end{array}
\tag{5}
\]
The endpoint T is on the outer q circle. The six other actual
states, all their coordinates and frames, and every other
retained witness are unchanged. The T-frame stays in the
original global interval. If u,v are nonnegative, both
variations are unchanged. If one is negative, each variation
decreases by its absolute value, and the endpoint aligns
that negative primary. The signed sum t is always unchanged.

There is no high-GA, selected A/E-total, or T-sign hypothesis.
At t=0 with u,v nonnegative, both errors already vanish and
the corresponding secondary witnesses are actual ties.

Sections 3--5 give the uniform verification of the two
existing transport proofs. Section 6 reflects the result
to HG0/GA1 and completes their same-radius finite join.
Section 7 states exactly what this preserves for equality.
All decimals and coefficient bounds are exact rationals.

## 2. The same-radius geometric domain and the auxiliary diagonal contradiction

The two-square central-band proof uses only containment at
an upper ceiling Q, true-core avoidance and actual pairwise
separation. It therefore applies directly at every q in (2).
Every two contained disjoint squares have smaller center
angle greater than \(19/25\). During any continuous motion
retaining those conditions, a neighboring gap cannot cross
zero. At a directly constructed endpoint, positive gaps
and their unchanged sum instead verify winding one directly.

The sole global exclusion used by the same-sign transport
is that a feasible T diagonal cannot occur. This also holds
for a boundary-neighbor cycle at q. Here is a precise way
to use the already proved Q-boundary theorem without
identifying the two radial boundaries.

Suppose such a q-cycle had a T diagonal. Regard its actual
squares as contained at Q, choose its already retained weak
axis on every neighboring pair, and apply the fixed-axis
radial-boundary reduction from Section 1 of
[the exterior-frame theorem](../HAND_EXTERIOR_FRAME_CONCENTRATION.md).
That reduction needs only the seven neighboring inequalities;
it preserves all actual frames, center rays, cyclic order
and the chosen weak witnesses. Radial rays also preserve
the signed ratio \(|y_i|/a_i\), including a diagonal tie.
The resulting core-or-Q-boundary cycle is therefore in the
domain of the boundary bridge, with the same quarter word
and a T diagonal. The
[nearest-axis tie theorem](HAND_G3_GLOBAL_NEAREST_AXIS_TIE_LOCATIONS.md)
excludes it. This proves the required diagonal restriction
for the original q-cycle as well.

This is only an auxiliary contradiction. None of the actual
comparison states in (5) is taken from that Q reduction,
and no anchor of the same-radius construction is enlarged.
Nor is a Q-boundary marker evaluated as though it were a
marker on the outer q circle. The variation bounds needed
after each transport are verified directly below.

## 3. Explicit bounds uniform in the actual radius

On (2) the following bounds hold:
\[
 \frac{899}{1000}<c_q<\frac9{10},\qquad
 \frac{19}{10}<A_q<\frac{383}{200}<2,\qquad
 \frac9{10}<d_q<\frac{183}{200}.
\tag{6}
\]
The lower bounds follow by positive squaring at q_L; the
upper bounds follow at Q. Useful exact reserves are
\[
 \begin{split}
 q_L/2-(1399/1000)^2&=\frac{499}{10^6}>0,\\
 q_L-1/4-(19/10)^2&=\frac{277}{5000}>0,\\
 (383/200)^2+1/4-Q&=\frac{13}{8000}>0,\\
 2(7/5)^2-Q&=\frac{11}{2500}>0.
 \end{split}
\tag{7}
\]
In particular \(a_q<283/200<3/2\) and \(c_q>3/4\).
The actual sorted B,D anchors give
\[
 c_q\le a_B\le a_q,
 \qquad 0\le b_D\le c_q,
 \qquad \frac38<a_B-\frac12<\frac{183}{200}.
\tag{8}
\]
All angular bounds are independent of the radius:
\[
 \cos x>\frac34,\quad |\sin x|<\frac{13}{20},\quad
 |\tan x|<1\quad(|x|\le h),
\]
\[
 1\le\sin x+\cos x<\frac{10}{7}\quad(0\le x\le h).
\tag{9}
\]

The strict norm reserves needed by the two contact branches
remain positive at the lower endpoint:
\[
 \begin{split}
 q_L-(183/200)^2-(7/4)^2&=\frac{627}{40000}>0,\\
 q_L-(59/56)^2-(5/3)^2&=\frac{487031}{17640000}>0,\\
 q_L-9/4-1&=\frac{3327}{5000}>0.
 \end{split}
\tag{10}
\]
Thus every use of the outer radius as a lower numerical
bound in the existing proofs has a displayed uniform
replacement. Uses as an upper bound are valid because
q<Q<4. Exact circle equations retain q itself throughout.

## 4. Two nonnegative primary errors

Use the proof in
[the positive-pair endpoint theorem](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
with its exact circle radius changed from Q to q, and
its symbols \(c,a_0,A,d\) changed to (3).
The following verification includes every radius-dependent step.

For \(u,v\ge0\), raising \(a_T\) at fixed signed tangent
and frame to
\[
                    a(y)=\sqrt{q-(|y|+1/2)^2}-1/2
\tag{11}
\]
improves both actual primary inequalities. Sorting, core
avoidance and containment at q are preserved. The gap
argument in Section 2 preserves cyclic order along this
radial entry. The final state is an actual outer q state.

On that circle the two exact projections are
\[
 a_B+a(y)\sin u-y\cos u\ge W(u),\qquad
 a(y)\sin v+y\cos v+b_D\ge W(v).
\tag{12}
\]
Their respective y derivatives are negative and positive,
since \(|a'(y)|\le1\) and (9) holds. Increasing y to
the largest value allowed by the first inequality gives
a unique BT contact or the positive diagonal.
The lower diagonal is never a BT contact:
\[
 a_B-\frac12+(c_q-\frac12)(\sin u+\cos u)>0.
\tag{13}
\]
The contact root increases with u by the exact derivative
\((a(y)-1/2)\cos u+(y+1/2)\sin u>0\).
At u=0 it is \(y=a_B-1\), strictly between the diagonals
by (6)--(8). Thus the two contact arcs and the possible
positive-diagonal arc have exactly the intrinsic order
used by the original proof.

Put \(P=a_B-1/2\), \(S=\sin t\), \(C=\cos t\).
The exact required opposite endpoint coordinates are
\[
 \begin{split}
 \mathcal D_+(u)&=\frac12-PC+(S+C)\cos u+S\sin u
                      -S\sqrt{q-(\sin u-P)^2},\\
 \mathcal D_-(u)&=\frac12-PC+(S+C)\cos u
                      -S\sqrt{q-(\sin u+\cos u-P)^2}.
 \end{split}
\tag{14}
\]
Their differentiated identities remain exact with q.
Equations (8)--(10) give respectively \(M_+>7/4\) and
\(M_->5/3\). Using q<4, their strict concavity bounds
are unchanged:
\[
 \mathcal D_+''< -\frac{301577}{6860000}<0,
 \qquad
 \mathcal D_-''< -\frac{471}{2500}<0.
\tag{15}
\]
The upper-diagonal demand
\(1/2-(c_q-1/2)(\sin(t-u)+\cos(t-u))\) increases with u.
Hence exactly the four intrinsic candidate types in the
original theorem remain: the two alignments, the unique
zero-tangent contact, and the first positive diagonal.

Every feasible candidate is an actual q-cycle. In fact its
two gaps, with
\(\beta_B=\arctan(b_B/a_B)\),
\(\beta_D=\arctan(b_D/a_D)\),
\(\alpha=\arctan(y/a(y))\), are
\[
       \frac\pi2+u-\alpha-\beta_B,
       \qquad v+\alpha+\beta_D.
\tag{16}
\]
The first is positive by sorting and the strictly sorted
u=0 contact. If y<0, the second actual inequality and
\(b_D\le c_q<1\) give
\(a(y)\sin v-|y|\cos v>0\), so the second gap is positive.
If y is nonnegative it is a sum of nonnegative terms,
and equality contradicts that same separating inequality.
The sum of the two gaps is unchanged. This direct check
does not assume a connected path of feasible contact states.
The diagonal candidate is therefore excluded by Section 2.

For the zero-tangent contact use
\[
 f_q(x)=\frac12+\frac12\cos x-d_q\sin x,
 \qquad a_B=f_q(u),\qquad b_D\ge f_q(v).
\tag{17}
\]
Since \(a_B\ge c_q\ge b_D\) and \(f_q\) decreases,
u≤v and t≥2u. The alternative BT-aligned state is
\[
 \delta=1-a_B,
 \quad y'=-\delta,
 \quad a'=a_q-\epsilon,
 \quad\epsilon=A_q-\sqrt{A_q^2-\delta-\delta^2}.
\tag{18}
\]
It lies on the actual q circle and is strictly sorted.
The positive-side squaring argument in Section 5 of the
original theorem uses only
\(c_q>.899\), \(A_q>1.9\), \(A_q<2\),
\(.9<d_q<.915\), and the exact identity \(d_q=A_q-1\).
These are all in (6). In particular it still gives
\(u<1/8\), and with \(r=\tan(u/2)<1/15\),
\[
 L=d_q(1-\cos u)+\tfrac12\sin u-(1-\cos u)\cot(2u),
\]
\[
 \epsilon<L,
 \qquad
 2A_qL-L^2-\delta-\delta^2
       >(2-A_q)r+\frac{314}{225}r^2>0.
\tag{19}
\]
The exact TD2 slack identity is unchanged, so (18) has
strict TD2 slack and an actual BT2 tie. Equation (16)
verifies its q-cycle eligibility too.

Only the aligned alternatives remain. Their two errors
are \((0,t)\) or \((t,0)\); hence the positive and negative
variations are unchanged. Every other state and error is
fixed. This proves the nonnegative-error part of (5).

## 5. Opposite individual signs and positive total

Use the construction in
[the signed-cancellation theorem](HAND_G3_POSITIVE_T_PRIMARY_TOTAL_SIGNED_CANCELLATION_TRANSPORT.md),
again retaining q in every actual circle equation.
Here its endpoint scalars are \(A=a_B\), \(B=b_D\), and
both belong to \([0,a_q]\). For u<0<v, first move T by
\[
                    a\mapsto a+\lambda,
             \qquad y\mapsto y+\lambda\tan u.
\tag{20}
\]
The first primary remains exactly fixed; the second
increases at rate \(\sin t/\cos u>0\). Sorting and the
exact true-core distance are nondecreasing. The unique
first exit from the bounded containing region is on the
outer q circle. Increasing y along that circle then
reaches first-primary contact before the positive diagonal:
its first projection there is at most
\[
                 a_q-c_q<1\le W(-u).
\tag{21}
\]
The strict inequality follows from \(a_q<3/2\), \(c_q>1/2\).

Put \(P=A-1/2\), \(X=a+1/2\), \(Z=|y|+1/2\).
For the negative-tangent contact arc set
\[
 S(u)=\cos u-P,\quad U(u)=\sqrt{q-S(u)^2},
\]
\[
 X=U\cos u+S\sin u,\qquad
 Z=-U\sin u+S\cos u.
\tag{22}
\]
Because \(-1/2\le P<1\), one has \(|S|\le3/2\).
Equation (10) gives U>1 uniformly. Thus
\[
 X'=Z(1+\sin u/U)>0,
 \qquad Z'=-X(1+\sin u/U)<0.
\tag{23}
\]
The arc moves toward u=0 with increasing y and strictly
improving sorting. On the positive-tangent contact arc,
\[
 U=\sqrt{q-P^2},\qquad
 X=U\cos u-P\sin u,
 \qquad Z=U\sin u+P\cos u.
\tag{24}
\]
Sorted contact gives \(1/2\le P<1\); q>2 then gives
U>P. Hence X−Z stays positive, y increases, and this
arc also reaches u=0. The two arcs join at the same
actual zero-tangent q-circle state, so there is at most
one join and no missing contact interval.

The exact required-B formulas and their strict derivative
bound do not involve a numerical radius estimate. With
v=t−u and r=S/U<1 on (22), they give
\[
 \begin{split}
 D_-'(u)&=-(\cos v-\sin v)
              -\sin t\{\cos(-u)-r\sin(-u)\}<-1/10,\\
 D_+'(u)&=\sin v-\cos v<-1/10.
 \end{split}
\tag{25}
\]
Therefore the opposite primary remains feasible all the
way to u=0. For v<0<u interchange the two projections
and replace y by −y, producing v=0 instead.

All outer states on the contact paths have
\(a\ge c_q>3/4\), so core avoidance is explicit. The
actual weak neighboring inequalities and the gap argument
in Section 2 preserve cyclic order during all three
motions. Only their endpoint is used as a canonical
q-boundary state. Each global variation decreases by the
magnitude of the negative original error. This proves
the remaining part of the pair theorem.

## 6. Reflection and the finite same-radius HG0/GA1 join

Reflect and reverse the local roles by
\[
              (B',T',D')=(A,G,H),
          \qquad \theta'=-\theta,\quad y'=-y.
\tag{26}
\]
Positive sorted outer H,A at q become negative sorted
outer D',B' at that same q. The actual HG0/GA1 errors
become the TD2/BT3 errors, respectively; their signed
sum is unchanged. Equation (26) transforms the actual
projections, circles and physical gaps, not only a
scalar relaxation.

Thus any HG0/GA1 pair of positive signed total has a
G-only same-q descendant with actual GA0 or HG alignment.
At HG alignment the unchanged \(b_H<.9\) implies
\(y_G\le b_H-1<-.1\), so that endpoint has the normal
G sign. At GA alignment no G sign is inferred without
another hypothesis. This statement covers either
individual error sign and either initial G radial kind.

The two Q-boundary joins in
[the wrong-sign pair reduction](HAND_G5_GLOBAL_PRIMARY_ENTRY_WRONG_SIGN_PAIR_REDUCTION.md),
Section 6, and
[positive GA with nonpositive total](HAND_G5_GLOBAL_PRIMARY_ENTRY_POSITIVE_GA_NONPOSITIVE_TOTAL.md),
Section 6, now hold throughout (2). Their nonpositive-total
local constructions were already proved inside the original
q circle. Their positive-total clauses use Sections 4--5
above in place of the older Q-only transport statements.
The genuine negative-GA1 clause uses the already same-q
[flat-core negative-GA transport](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md).

Its flat-core entry is also valid at q. If GA1 at a negative
error −s is feasible but GA0 is not, put
\(K_G=a_G+1/2\), \(D_G=b_G+1/2\),
\(X=a_A+1/2\), \(Z=b_A+1/2\). The contact-vector
comparison from the negative-primary entry proof gives
\[
 X^2+Z^2>
 1+K_G^2+D_G^2+2(D_G\cos s+K_G\sin s)
                         \ge K_G^2+(D_G+1)^2.
\tag{26a}
\]
An outer G at q would have \(K_G^2+D_G^2=q\), contradicting
the unchanged A containment at q. Hence G is core. If
\(D_G\ge1\), sorting makes the final expression at least
5>Q, again impossible. Thus \(b_G<1/2\), and the actual
core boundary is flat: \(a_G=7/12\). This uses q in the
outer contradiction and only Q as an upper numerical bound.

For completeness, the latter's boundary-neighbor eligibility
does not require a new radial equality. Its endpoint G is
on the actual flat core. With normal H,G,A signs, either
changed directed gap is greater than −h and less than π:
they are
\[
 d_{HG}+\alpha_H+\gamma,
 \qquad \pi/2+d_{GA}-\gamma-\alpha_A,
\tag{27}
\]
where every displayed local angle lies in \([0,\pi/4]\).
If either gap were nonpositive, its smaller angular
distance would be below h, contrary to the actual
two-square band. Thus both are positive. Their sum is
fixed, so the endpoint is an actual q-cycle. Clamping
the one G frame to H or A also cannot increase either
variation of the two changing errors.

Consequently **every retained HG0/GA1 pair at q** has a
G-only actual descendant with GA0 or HG alignment, under
the original low-GA outer H,A hypotheses. This includes
every G sign, radial kind, signed total and individual
error allocation. The reflected statement applies to
BT3/TD2. No assertion is made here about HG2 paired with
a sole positive GA1, or TD0 paired with a sole positive
BT3; those remain separate entry obligations.

## 7. Original anchors and equality scope

Every construction in this note fixes all five anchors
H,A,B,D,E at their actual original coordinates, frames
and circle ceiling q. It also fixes the other intermediate
square. A previously recorded strict loss at any anchor
therefore persists separately. G-only and T-only pair
operations can be composed without changing these facts.

At q=q_* there is no enlargement of the actual ceiling.
If subsequent established reductions reach the hard-owner
sharp class, the original unchanged anchors, rather than
the constructed G/T centers, must be used in recovering
the stationary equality data. In particular the canonical
five-anchor equality has
\[
 \theta_A=\theta_B=\theta_D=\theta_E,
       \qquad \theta_H-\theta_A=t_*>0,
\tag{28}
\]
by the equality statement of
[the aligned hard-class theorem](HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md).
The positive-total T transport retains
\(\theta_D-\theta_B=t>0\), inconsistent with (28).
Its reflected positive-total G transport retains
\(\theta_A-\theta_H=t>0\), also inconsistent with (28).
Thus those positive-total source cases cannot give
original sharp equality once the remaining entry steps
are joined in a way that preserves anchors or records
their strict losses.

A strict circle loss at the comparison intermediate
alone is not an anchor loss and is not used to make that
conclusion. In nonpositive-total branches one must still
recover original equality from the unchanged anchor
constraints and the complete hard-owner equality argument.
This note neither identifies a transported G/T state with
its original state nor asserts that an intermediate-only
loss excludes equality. Its same-radius theorem supplies
the precise data needed by that later equality assembly.

All radius estimates above are inequalities on the entire
interval (2), and every contact formula retains the actual
q. No radius mesh, sampled minimum, optimizer output,
Lean compilation or CI result is used.
