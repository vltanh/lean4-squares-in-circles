# Positive paired T primaries reduce to actual aligned owners

## 1. Exact domain and conclusion

Put
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},\qquad
 R=\sqrt Q,\qquad
 c=\sqrt{Q/2}-\frac12,\qquad
 a_0=\sqrt{Q-\frac14}-\frac12,
\]
\[
 A=a_0+\frac12,\qquad d=a_0-\frac12=A-1,\qquad
 W(x)=\frac{1+\cos x+|\sin x|}{2}.
\tag{1}
\]
Use an actual G0--G2 boundary-neighbor cycle in cyclic role order
H,G,A,B,T,D,E, with quarter word \(0101011\), contained in the
Q-disk and avoiding the open radius-\(1/12\) disk. Its real frame
spread is less than h, and its positive and negative error
variations are each less than h. Each neighboring separation
is witnessed by an actual weak original-axis inequality.

Assume B and D are sorted outer states with negative signed
tangents. Write
\[
 B=a_B,\qquad D=b_D,\qquad c\le B\le a_0,\quad 0\le D\le c.
\tag{2}
\]
The capital letters B,D in scalar formulas denote these
coordinates, rather than the physical squares. Retain actual
BT3 and TD2 witnesses with errors
\[
 u=\theta_T-\theta_B\ge0,\qquad
 v=\theta_D-\theta_T\ge0,\qquad
 0<t=u+v<h.
\tag{3}
\]
Their exact inequalities are
\[
 B+a_T\sin u-y_T\cos u\ge W(u),\qquad
 a_T\sin v+y_T\cos v+D\ge W(v).
\tag{4}
\]
No sign or radial kind is assumed for T.

**Endpoint reduction.** There is another actual boundary-neighbor
cycle satisfying every unchanged witness, with the same six
squares other than T, the same B and D frames, the same total t,
and one of the following actual owner choices:
\[
 \begin{array}{c|c|c}
 &\text{BT}&\text{TD}\\ \hline
 u=0&2&2\ \text{with error }t\\
 v=0&3\ \text{with error }t&0 .
 \end{array}
\tag{5}
\]
Its T square is a sorted outer state. The frame spread does not
increase, and the positive and negative error variations are
unchanged. Every A- and E-primary error and every other state,
owner and sign remain unchanged.

The proof uses two strictly concave contact branches. Their
only additional intrinsic endpoints are a positive T diagonal
and a zero T tangent. The global nearest-axis theorem excludes
the diagonal; Section 5 replaces the zero tangent by a strictly
feasible BT-aligned state. This is a finite analytic reduction,
with no scalar mesh or sampled premise.

If t=0, both errors already vanish, and both secondary owners in
(5) are actual tied witnesses. Thus the zero-total boundary needs
no deformation.

## 2. Outerization and the unique maximal BT-contact state

For a fixed signed tangent y define the outer primary coordinate
\[
                     a(y)=\sqrt{Q-(|y|+1/2)^2}-1/2,
                      \qquad -c\le y\le c.
\tag{6}
\]
Increase \(a_T\) to \(a(y_T)\), keeping its tangent and physical
frame fixed. Both inequalities (4) improve because \(u,v\ge0\).
The sorted inequality and the distance from the origin to the
square do not decrease, and containment in the Q-disk is
preserved. Along this continuous entry, the two changing
neighboring gaps cannot cross zero: every pair remains disjoint,
contained, and outside the true core, so the two-square central
band gives smaller center angle greater than \(19/25\).
Consequently the resulting outer state retains the original
cyclic order. Only the final outer state, rather than an
intermediate radial state, is used in the subsequent G1/G2
arguments.

On the outer curve let
\[
 \begin{split}
 F_1(u,y)&=B+a(y)\sin u-y\cos u-W(u),\\
 F_2(v,y)&=a(y)\sin v+y\cos v+D-W(v).
 \end{split}
\tag{7}
\]
On either side of y=0, \(|a'(y)|\le1\). Since \(0\le u,v<h<\pi/4\),
\[
       (F_1)_y\le\sin u-\cos u<0,\qquad
       (F_2)_y\ge\cos v-\sin v>0.
\tag{8}
\]
The same strict monotonicity holds across y=0 by continuity.
Thus increasing y to its largest value allowed by BT3 improves
TD2. At the lower diagonal,
\[
        F_1(u,-c)=B-\tfrac12+(c-\tfrac12)(\sin u+\cos u)>0.
\tag{9}
\]
The maximal state therefore has either a unique BT contact
\(F_1(u,y)=0\), or y=c if \(F_1(u,c)\ge0\).

The contact tangent increases strictly with u. Indeed
\[
 (F_1)_u=(a(y)-\tfrac12)\cos u+(y+\tfrac12)\sin u>0.
\tag{10}
\]
For \(y\ge-1/2\) the two summands are nonnegative and the first
is positive. For \(y<-1/2\), sorting gives
\(a(y)-1/2\ge-y-1/2>0\), and \(\cos u>\sin u\) proves the claim.
Together with (8), this proves strict increase of the contact
root. At u=0 that root is
\[
                         y_B(0)=B-1\in(-c,c).
\tag{11}
\]
The strict bounds in (11) follow from \(B\ge c>1/2\) and
\(B\le a_0<1+c\).

Consequently the maximal states on the complete interval
\(0\le u\le t\) have, in order, a possibly empty negative-y
contact branch, a possibly empty positive-y contact branch,
and a possibly empty upper-diagonal branch. There is at most
one zero-tangent join and at most one first diagonal contact.
The T frame at u is \(\theta_B+u\), and \(v=t-u\).

## 3. Exact required-D functions and strict concavity

Set
\[
             S=\sin t,\qquad C=\cos t,\qquad P=B-\frac12,
             \qquad \phi(x)=\sin x+\cos x.
\tag{12}
\]
The following elementary bounds follow from (1)--(3):
\[
 \frac{899}{1000}<c<1,\quad
 \frac{19}{10}<A<2,\quad
 \frac9{10}<d<\frac{183}{200},\quad
 \frac38<P<\frac{183}{200},
\tag{13}
\]
\[
 \cos x>\frac34,\quad \sin x<\frac{13}{20},\quad
 1\le\phi(x)<\frac{10}{7}\qquad(0\le x\le h).
\tag{14}
\]
For example, \(Q/2-(1399/1000)^2=599/10^6>0\) proves
the lower bound for c. The remaining algebraic bounds follow
by squaring their positive sides. The trigonometric bounds
follow from the alternating Taylor bounds at h and
\(\sqrt2<10/7\).

On a positive-y contact put
\[
 X=a(y)+\frac12,\quad Y=y+\frac12,\quad
 z_+=\sin u-P,\quad M_+=\sqrt{Q-z_+^2}.
\]
Then
\[
 X\sin u-Y\cos u=z_+,\qquad
 X\cos u+Y\sin u=M_+.
\tag{15}
\]
The second coordinate is positive. Substitution in the TD2
inequality gives the exact required D:
\[
 \boxed{\;
 \mathcal D_+(u)=
 \frac12-PC+(S+C)\cos u+S\sin u-SM_+.
 \;}
\tag{16}
\]
Its second derivative is
\[
 \mathcal D_+''=
 -(S+C)\cos u-S\sin u+
 S\left\{\frac{Q\cos^2u}{M_+^3}
                -\frac{(\sin u-P)\sin u}{M_+}\right\}.
\tag{17}
\]
Here \(|\sin u-P|<183/200\), and
\[
 Q-(183/200)^2-(7/4)^2=\frac{127}{8000}>0,
\]
so \(M_+>7/4\). Using \(S+C\ge1\), \(Q<4\), and (14),
\[
 \mathcal D_+''<
 -\frac34+\frac{13}{20}
 \left\{\frac{256}{343}
       +\frac{183}{200}\frac{13}{20}\frac47\right\}
   =-\frac{301577}{6860000}<0.
\tag{18}
\]

On a negative-y contact put
\[
 X=a(y)+\frac12,\quad Z=-y+\frac12,\quad
 z_-=\phi(u)-P,\quad M_-=\sqrt{Q-z_-^2}.
\]
Sorting and \(u<\pi/4\) give
\[
 X\sin u+Z\cos u=z_-,\qquad
 X\cos u-Z\sin u=M_->0.
\tag{19}
\]
The exact TD2 requirement is now
\[
 \boxed{\;
 \mathcal D_-(u)=\frac12-PC+(S+C)\cos u-SM_-.
 \;}
\tag{20}
\]
Its second derivative is
\[
 \mathcal D_-''=
 -(S+C)\cos u+
 S\left\{\frac{Q(\cos u-\sin u)^2}{M_-^3}
                  -\frac{(\phi(u)-P)\phi(u)}{M_-}\right\}.
\tag{21}
\]
We have \(0<z_-<10/7-3/8=59/56\), and
\[
 Q-(59/56)^2-(5/3)^2
                 =\frac{490559}{17640000}>0.
\]
Thus \(M_->5/3\). Discarding the negative last term in (21)
and using \((\cos u-\sin u)^2\le1\),
\[
             \mathcal D_-''<
             -\frac34+\frac{13}{20}\frac{108}{125}
                  =-\frac{471}{2500}<0.
\tag{22}
\]

On an upper-diagonal branch the exact requirement is
\[
 \mathcal D_{\rm diag}(u)
       =\frac12-(c-\tfrac12)\phi(t-u),\qquad
 \mathcal D_{\rm diag}'(u)
       =(c-\tfrac12)(\cos(t-u)-\sin(t-u))>0.
\tag{23}
\]
Therefore, if some maximal state satisfies TD2, at least one
of the following intrinsic candidates satisfies TD2:

* u=0, a BT-aligned contact;
* u=t, a TD-aligned contact, unless it lies on the diagonal
  branch, in which case the first diagonal contact is no worse;
* the unique contact with y=0, when it lies strictly between
  0 and t;
* the first contact with y=c, when that branch is present.

This follows from strict concavity on each closed contact
branch and monotonicity on the diagonal branch. The two contact
formulas agree in value at y=0, because both are the same actual
TD2 projection. No claim of global concavity across that join
is needed. No connected path of TD-feasible contact states is
assumed.

## 4. Every feasible candidate is an actual boundary-neighbor cycle

The candidate T states are actual sorted outer squares at frames
between \(\theta_B\) and \(\theta_D\). They preserve both actual
neighboring separating inequalities by construction. Let
\[
       \beta_B=\arctan(b_B/a_B),\qquad
       \beta_D=\arctan(b_D/a_D),\qquad
       \alpha=\arctan(y/a(y)).
\]
Their two changing directed center gaps are exactly
\[
           g_{BT}=\frac\pi2+u-\alpha-\beta_B,\qquad
           g_{TD}=v+\alpha+\beta_D.
\tag{24}
\]
The first is at least u by sorting, and is positive if u>0.
At u=0 the contact (11) is strictly sorted, so it remains
positive.

If y is negative, feasibility of TD2 and \(D\le c<1\le W(v)\)
implies
\[
                    a(y)\sin v-|y|\cos v>0.
\]
Thus \(v>\arctan(|y|/a(y))=-\alpha\), and \(g_{TD}>0\).
If y is nonnegative, every summand in \(g_{TD}\) is
nonnegative. Equality would force v=y=D=0 and contradict
TD2. Hence this gap is also positive.

All other gaps are unchanged, and the sum of the two in (24)
is fixed. Therefore all seven gaps are positive and sum to
\(2\pi\). The two-square central band supplies the full
\(19/25\) lower gap bound. The candidate is an actual
boundary-neighbor cycle in the precise domain of
[the boundary-domain bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
The common-marker and word arguments can be evaluated at
these actual boundary states; no original marker is frozen
at a moved T.

In particular
[the global nearest-axis tie theorem](HAND_G3_GLOBAL_NEAREST_AXIS_TIE_LOCATIONS.md)
excludes every feasible candidate with y=c. Its T+ recoding
would give the excluded word 0100111, of class 0010111.
This proof uses the actual neighboring witnesses and the
positive physical gaps just verified. It requires no
nonconsecutive disjointness. The retained frame interval
and the sum u+v=t preserve all other global inputs.

It remains to handle the zero-tangent candidate.

## 5. A zero-tangent contact is dominated by a BT alignment

Suppose a feasible interior candidate has y=0 at errors u,v,
with \(u,v>0\) and u+v=t. Put
\[
                 f(x)=W(x)-a_0\sin x
                     =\frac12+\frac12\cos x-d\sin x.
\tag{25}
\]
Its BT contact and TD feasibility give
\[
                       B=f(u),\qquad D\ge f(v).
\tag{26}
\]
Because \(B\ge c\ge D\), we have \(f(u)\ge f(v)\).
The function f is strictly decreasing on \([0,h]\), so
\[
                              u\le v,\qquad t\ge2u.
\tag{27}
\]
Also \(B=f(u)<1\). Define
\[
        \delta=1-B=d\sin u+\frac{1-\cos u}{2}>0,\qquad
        \epsilon=A-\sqrt{A^2-\delta-\delta^2}.
\tag{28}
\]
The outer T state at the BT-aligned frame is
\[
                    y'=-\delta=B-1,\qquad a'=a_0-\epsilon.
\tag{29}
\]
It is strictly sorted: \(\delta\le1-c<c\). Its BT3 and BT2
projections both equal \(B+\delta=1=W(0)\).

We prove that (29) has strictly more TD2 projection than
the original zero-tangent requirement. Since \(D\ge f(v)\),
its TD2 slack at error t is at least
\[
 \begin{split}
 M&=(a_0-\epsilon)\sin t-\delta\cos t+f(v)-W(t)\\
  &=\sin t\{d(1-\cos u)+\tfrac12\sin u-\epsilon\}
                              -(1-\cos u)\cos t.
 \end{split}
\tag{30}
\]
We shall show
\[
 \epsilon<
 L=d(1-\cos u)+\frac12\sin u-(1-\cos u)\cot(2u).
\tag{31}
\]
Since \(0<2u\le t<h<\pi/2\), (31) implies
\[
 M>(1-\cos u)\{\sin t\cot(2u)-\cos t\}\ge0.
\tag{32}
\]
Thus the new TD2 witness is strict.

Here is a rational proof of (31) on the full required interval.
First \(f(u)=B\ge c\) forces u<1/8. Indeed the Taylor bounds
and \(d>9/10\) give
\[
 f(1/8)<
 1-\frac{(1/8)^2}{4}+\frac{(1/8)^4}{48}
       -\frac9{10}\{1/8-(1/8)^3/6\}
   =\frac{868901}{983040}<\frac{899}{1000}<c.
\tag{33}
\]
Set \(q=\tan(u/2)\). Then
\[
              0<q<\tan(1/16)
                <\frac{32}{511}<\frac1{15}.
\tag{34}
\]
The middle bound uses \(\sin x<x\) and
\(\cos x>1-x^2/2\). The exact half-angle identities give
\[
 \delta=\frac{2dq+q^2}{1+q^2},\qquad
 L=\frac{q\{1+4q^2-q^4+4dq(1-q^2)\}}{2(1-q^4)}.
\tag{35}
\]
On this whole interval,
\[
              L>\frac q2+2dq^2,\qquad
              L<\frac23q,\qquad
              \delta<2q.
\tag{36}
\]
For the first inequality, the difference from the claimed lower
bound is
\[
                    \frac{2q^3(1-dq+dq^3)}{1-q^4}>0.
\]
For the upper bound, discard the negative terms in the numerator
of L and use \(q<1/15,d<183/200\). The exact coefficient reserve is
\[
 \frac43(1-15^{-4})
       -\left(1+\frac4{225}+\frac{4(183/200)}{15}\right)
                =\frac{21727}{303750}>0.
\tag{37}
\]
Finally, \(2d+q<183/100+1/15<2\) proves the bound for \(\delta\).

Using \(A>19/10\), \(d>9/10\), \(A<2\), and
\(\delta<2dq+q^2\), (36) yields
\[
 \begin{split}
 2AL-L^2-\delta-\delta^2
 &>(A-2d)q+
       \left(4Ad-1-\frac49-4\right)q^2\\
 &>(2-A)q+\left(\frac{146}{25}-\frac{40}{9}\right)q^2\\
 &=(2-A)q+\frac{314}{225}q^2>0.
 \end{split}
\tag{38}
\]
Both sides of
\[
                        A-L<\sqrt{A^2-\delta-\delta^2}
\]
are positive: \(L<2/45<A\), and (29) is an actual point of
the sorted outer arc. Squaring is therefore reversible, and
(38) proves this inequality, equivalently (31).

The new state (29), at u'=0 and v'=t, satisfies the actual
neighboring inequalities by (30)--(32). Section 4 proves its
positive gaps and boundary-neighbor eligibility as well.
This disposes of the zero-tangent join without assuming
concavity across it.

## 6. Actual owner reselection and scope join

The finite alternatives in Section 3 now leave only the two
aligned states. At u=0 the actual BT3 projection is
\(B-y_T\), exactly the BT2 projection at that same state;
hence BT2 can be selected. At v=0 the actual TD2 projection
is \(y_T+b_D\), exactly the TD0 projection at that state;
hence TD0 can be selected. These are original-axis ties,
rather than virtual zeros inside a support bound.

Only T was changed. Its new frame is an endpoint of the
unchanged interval \([\theta_B,\theta_D]\), so global frame
spread cannot increase. The two nonnegative errors retain
their sum t, so their contribution to positive variation is
unchanged and their negative variation remains zero. Every
other real error and all A/E primary totals are unchanged.

In particular, with high GA and nonnegative selected signed
A- and E-primary totals, neither endpoint can exist. The
BT-aligned endpoint is excluded by
[the BT2 theorem with nonnegative A/E totals](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).
The TD-aligned endpoint is excluded by
[the positive-BT3/TD0 theorem](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
Thus the positive paired BT3/TD2 branch with u,v nonnegative
is excluded throughout that scope.

The endpoint reduction itself has no assumption on A/E totals
or on high GA. For opposite-sign T errors with positive sum,
[the signed-cancellation transport](HAND_G3_POSITIVE_T_PRIMARY_TOTAL_SIGNED_CANCELLATION_TRANSPORT.md)
reaches the alignment of the negative primary, with the same
positive remaining total and unchanged A/E data. These two
notes therefore exclude every positive signed BT3/TD2 total
when the A/E totals are nonnegative, including all individual
sign allocations. A negative A or E total still needs its own
endpoint theorem if one applies the actual reductions beyond
that nonnegative-total scope.

All scalar bounds above are explicit whole-interval
derivative bounds, elementary half-angle identities and
reversible positive-side squaring. No table, discretized
state domain, optimizer output, Lean compilation or CI
result is a premise.

