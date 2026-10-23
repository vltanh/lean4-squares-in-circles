# Two positive E primaries reach an actual aligned E endpoint at the same radius

## 1. Actual domain and conclusion

Put
\[
 q_L=19577/5000,\qquad Q_1=1957767069/500000000,
 \qquad Q=9789/2500,\qquad h=7/10.
\tag{1}
\]
Use an actual boundary-neighbor cycle at one radius
\(q_L\le q\le Q_1\), with the usual quarter word, real
frame spread and both variations below h. H and D are positive
and negative sorted outer q states, respectively. E is an
outer q state of **either signed tangent**. Retain actual
DE3 and EH1 with
\[
 d=\theta_E-\theta_D\ge0,\qquad
 r=\theta_H-\theta_E\ge0,\qquad t=d+r<h.
\tag{2}
\]
Every other actual state, frame and neighboring witness is
arbitrary and stays fixed in the construction.

**Paired-E endpoint theorem.** Changing E alone gives another
actual boundary-neighbor cycle at the same q with an outer E
and one of
\[
\begin{array}{c|c|c}
 &DE&EH\\ \hline
 d'=0&2&1\text{ at }t\\
 r'=0&3\text{ at }t&0.
\end{array}
\tag{3}
\]
The E frame stays in the original D/H interval. Both variations
are unchanged. Its signed tangent is not asserted to have its
original sign; all other six actual squares, their circles,
frames, signs and weak witnesses are identical. The original
DE3 or EH1 also remains feasible at its aligned tie.

When t=0 both secondaries are already actual and no construction
is needed. Thus weak zero-angle ties are included.

This theorem removes a positive *paired* E endpoint obligation.
It does not assert exclusion of either single-primary endpoint,
or identify the new E with the original E in an equality proof.

## 2. The two-anchor scalar ordering

Write \(y=y_E\) and
\[
 a(y)=\sqrt{q-(|y|+1/2)^2}-1/2,\quad
 c=\sqrt{q/2}-1/2,\quad
 a_0=\sqrt{q-1/4}-1/2.
\tag{4}
\]
The two actual projections are
\[
 a_D+a(y)\sin d-y\cos d\ge W(d),\qquad
 a(y)\sin r+y\cos r+a_H\ge W(r).
\tag{5}
\]
Here \(W(x)=(1+\cos x+|\sin x|)/2\), as usual.

Orient this local pair so that its first scalar anchor is the
larger primary:
\[
 (A,B,u,v,Y)=
 \begin{cases}
 (a_D,a_H,d,r,y),&a_D\ge a_H,\\
 (a_H,a_D,r,d,-y),&a_H>a_D.
 \end{cases}
\tag{6}
\]
The second line is the actual local reflection and reversal of
D,E,H; it exchanges the two inequalities in (5). It will be
undone at the endpoint. In both lines
\[
 c\le B\le A\le a_0,\qquad u,v\ge0,
 \qquad u+v=t,
\]
\[
 A+a(Y)\sin u-Y\cos u\ge W(u),\qquad
 a(Y)\sin v+Y\cos v+B\ge W(v).
\tag{7}
\]

These are exactly the two scalar contact inequalities of
[the positive T-pair theorem](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md).
Its scalar first anchor has the same interval \([c,a_0]\).
Its old second-anchor condition \(B\le c\) is not imposed:
we instead have \(B\le A\). The remaining sections explain
each place where that change matters.

## 3. Contact candidates and same-radius concavity

For fixed u, the first margin in (7) strictly decreases with Y
and the second strictly increases, because \(|a'(Y)|\le1\)
and \(\cos u>\sin u\), \(\cos v>\sin v\).
The first margin at the negative diagonal is
\[
 A-1/2+(c-1/2)(\sin u+\cos u)>0.
\tag{8}
\]
Increasing Y to its maximal value therefore reaches unique
first-primary contact or the positive diagonal. The contact
root increases with u; its value at u=0 is
\[
                         Y(0)=A-1\in(-c,c).
\tag{9}
\]
Neither (8), (9), nor the derivative of the contact root uses B.

Put \(P=A-1/2\), \(S=\sin t\), \(C=\cos t\).
The exact required second-anchor values on the positive and
negative contact branches are
\[
\begin{split}
 D_+(u)&=\tfrac12-PC+(S+C)\cos u+S\sin u
                    -S\sqrt{q-(\sin u-P)^2},\\
 D_-(u)&=\tfrac12-PC+(S+C)\cos u
                    -S\sqrt{q-(\sin u+\cos u-P)^2}.
\end{split}
\tag{10}
\]
These identities depend on A and q, not on B. The uniform
same-radius estimates in Sections 3--4 of
[the primary-pair theorem at the original radius](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md)
give
\[
 D_+''<-301577/6860000<0,
 \qquad D_-''<-471/2500<0.
\tag{11}
\]
Their hypotheses hold without alteration:
\(3/8<P<183/200\), \(q\ge q_L\), \(q<Q\), and every
angle lies in [0,h]. On the positive-diagonal branch the
required B increases with u, by the same explicit derivative
as in the original proof.

Consequently every feasible initial pair has a feasible
intrinsic candidate among u=0, v=0, the unique zero-tangent
contact, and the first positive-diagonal contact. The two
contact formulas agree at their zero-tangent join. Strict
concavity is used separately on their full intervals; no
connectedness of the feasible set is presumed.

## 4. E has two quarter gaps, both positive at every candidate

This is the geometric verification replacing the T-pair proof's
one-quarter/one-zero gap argument. Undo (6) and put
\[
 \beta_D=\arctan(b_D/a_D),\quad
 \beta_H=\arctan(b_H/a_H),\quad
 \alpha=\arctan(y/a(y)).
\]
The two actual changed center gaps are
\[
 g_{DE}=\pi/2+d-\beta_D-\alpha,
 \qquad g_{EH}=\pi/2+r+\alpha-\beta_H.
\tag{12}
\]
Sorting and d,r nonnegative make each nonnegative. A zero
first gap could only have d=0, D diagonal, and E positive
diagonal. A zero second gap could only have r=0, H diagonal,
and E negative diagonal.

In the orientation of (6), a first-aligned contact is strictly
sorted by (9), so its quarter gap is positive. The maximal
contact state is never the negative diagonal, by (8). Thus a
second-aligned candidate also has positive quarter gap. At a
positive-diagonal candidate, its first error is positive by
(9), and its other quarter gap is positive directly. These
statements are symmetric under undoing (6). Hence both gaps
in (12) are strictly positive for every feasible candidate.

Their sum is unchanged. All five other gaps, actual states
and witnesses are unchanged, and (7) supplies both changed
weak separations. The candidate is contained at q, lies on
its actual outer boundary and avoids the true core. It
therefore has winding one and is an actual boundary-neighbor
cycle. Its two nonnegative errors have the same total t,
so both captured variations are unchanged.

The [nearest-axis tie theorem](HAND_G3_GLOBAL_NEAREST_AXIS_TIE_LOCATIONS.md)
excludes either E diagonal on precisely this domain. Hence the
diagonal candidate is impossible, including when (6) reverses
its tangent sign. This uses the earlier E tie exclusion and
does not depend on the newer H/D strict-sorting theorem.

## 5. The zero-tangent contact needs only the new scalar ordering

Suppose the feasible candidate has Y=0 and u,v positive.
Set
\[
 A_0=a_0+1/2,\qquad d_0=a_0-1/2=A_0-1,
 \qquad f(x)=\tfrac12+\tfrac12\cos x-d_0\sin x.
\tag{13}
\]
First contact and the second inequality give
\[
                            A=f(u),\qquad B\ge f(v).
\tag{14}
\]
Our chosen order \(A\ge B\) is exactly what is needed here:
it implies \(f(u)\ge f(v)\). Since f strictly decreases,
\[
                              u\le v,\qquad 2u\le t.
\tag{15}
\]
This replaces the old sufficient condition \(A\ge c\ge B\).
No other scalar use of the old upper bound on B remains.

Let
\[
 \delta=1-A=d_0\sin u+(1-\cos u)/2>0,
 \qquad
 \epsilon=A_0-\sqrt{A_0^2-\delta-\delta^2}.
\tag{16}
\]
The first-aligned outer state is
\[
                    Y'=-\delta=A-1,\qquad a'=a_0-\epsilon.
\tag{17}
\]
It is strictly sorted since \(\delta\le1-c<c\), and its
first primary and secondary are both actual contact. The
second margin is bounded below by the same exact identity
as (30) of the original T-pair proof:
\[
 M=\sin t\{d_0(1-\cos u)+\tfrac12\sin u-\epsilon\}
                                  -(1-\cos u)\cos t.
\tag{18}
\]
The uniform same-radius proof gives
\[
 \epsilon<d_0(1-\cos u)+\tfrac12\sin u
                                  -(1-\cos u)\cot(2u).
\tag{19}
\]
To identify its full scope, \(A=f(u)\ge c\) gives u<1/8;
then \(z=\tan(u/2)<1/15\), and the positive-side square
in that proof has reserve
\[
                         (2-A_0)z+\frac{314}{225}z^2>0.
\tag{20}
\]
The radius bounds \(1.9<A_0<2\), \(.9<d_0<.915\),
\(c>.899\) hold uniformly on (1). Thus this is the same
whole-interval inequality, not a new unchecked endpoint claim.
Equations (15), (18), (19) give M>0. The zero-tangent candidate
has therefore been replaced by an actual first-aligned state
with strict opposite-primary slack. Section 4 supplies its
actual boundary-neighbor eligibility.

Only the two aligned candidates remain. Undoing (6), their
actual ties are precisely (3). All assertions of Section 1
follow.

## 6. A sign-preserving version has exactly one additional zero-tangent endpoint

Suppose the original E has nonpositive tangent. If a later
theorem requires this sign, do not use the optional orientation
exchange (6) and do not continue through Y=0. Instead put
\[
                  A=a_D,\qquad B=a_H,
              \qquad u=d,\quad v=r,\quad -c\le Y\le0.
\tag{21}
\]
No order between A and B is needed for the following result:
there is an E-only descendant at the same q, with E still
nonpositive and outer, at one of exactly these types:
\[
 \boxed{\quad d'=0;\qquad r'=0;\qquad y_E'=0.\quad}
\tag{22}
\]
In the first two types select the actual aligned secondary;
the third type retains the two actual E primaries. Every
other state and witness is fixed, and both variations are
unchanged. If the third type is distinct from the first two,
its two errors are positive and its actual coordinates are
\[
                    a_E'=a_0,\qquad y_E'=0,
\]
\[
                    a_D\ge f(d'),\qquad a_H\ge f(r'),
                       \qquad d'+r'=t.
\tag{23}
\]

Here is the complete additional proof. The first margin in
(7) is strictly decreasing in Y and positive at -c. Its
maximal feasible value on the restricted interval is therefore
its unique negative contact root, if that root is below zero,
and zero otherwise. As u increases, the first contact root
increases strictly. Hence the possible pieces, in order, are
one negative-contact branch followed by one zero-tangent
branch, either of which may be empty.

The required B on the negative branch is exactly D_- in
(10), which is strictly concave by (11). On the zero branch
the required B is
\[
                         D_0(u)=f(t-u).
\tag{24}
\]
Since f decreases strictly, D_0 increases strictly. The two
requirements agree at their join, because both evaluate the
same actual E=0 state. Thus feasibility at any initial u
implies feasibility at u=0, u=t, or the first zero-tangent
join. This proves (22) without extending a candidate past
the chosen sign boundary. The quarter-gap verification in
Section 4 applies verbatim: no negative diagonal is a maximal
candidate, and a first-aligned negative contact is strictly
sorted. If the zero branch starts at u=0, it is already the
first aligned alternative.

Equations (23) are the two actual projections of the
zero-tangent candidate, not scalar replacements for an
unmoved E. When the zero candidate is an interior join,
its first inequality in (23) is equality. There is no claim
here that this actual zero-tangent cycle is impossible; a
subsequent whole-cycle theorem must handle it. Reflecting
the local triple gives the analogous sign-preserving
trichotomy when the original E is nonnegative.

## 7. Finite use, sign bookkeeping, and equality scope

For an original outer E, every selected primary of nonpositive
error already has an actual secondary witness, by the
[outer-E comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md).
That comparison holds with H,D merely contained at the same
radius. Its local reflection exchanges the two E edges and
extends it to either E sign. On the working radius band its
only lower numerical bound \(a_0>707/500\) follows by
positive squaring at q_L; all its other displayed estimates
use q at most Q or the exact outer-q equality of E.

After selecting those actual secondaries, any still-paired E
primaries have positive errors and fall under Sections 1--5.
Thus, with H,D still outer at q, the outer-E owner alternatives
reduce in finitely many steps to no primary, one nonnegative
primary, or one positive primary with the other E edge aligned.
In particular an arbitrary positive paired-E allocation does
not require infinitely many additional split cases.

The E sign in (3) can change. A subsequent proof must either
admit that sign explicitly, use the sign-preserving trichotomy
(22) and separately exclude its actual E=0 endpoint, or
physically reflect the complete cycle with the usual owner
exchanges. The reflection swaps GA0 with BT2 and GA1 with
BT3; it does not automatically turn a one-sided entry theorem
into an applicable theorem. This note is an endpoint reduction,
not such a claim.

H,A,B,D and both intermediates have stayed at their original
coordinates and frames. E has stayed on the original q-circle
but may have moved, so original E equality still requires a
pullback or a strict retained-contact argument. A same-radius
E-circle equality alone does not recover its original state.

No angle mesh, sampled optimization, new scalar table, Lean
compilation or CI result is used. The changed-domain proof
reuses the explicit same-radius contact concavity and
zero-tangent square, with the new ordering and the two actual
quarter gaps verified above.
