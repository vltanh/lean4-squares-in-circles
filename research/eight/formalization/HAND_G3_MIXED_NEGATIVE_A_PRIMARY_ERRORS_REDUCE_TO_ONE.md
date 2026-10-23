# A negative signed sum reduces two primary errors to one

## 1. Scope and output

Retain the original G0--G2 boundary data at
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},
 \qquad W(t)=\frac{1+\cos t+|\sin t|}{2}.
\tag{1}
\]
The four original states H, G, B and D are sorted outer states,
with signed tangents respectively positive, negative, negative
and negative. Retain the original owners
\[
 HG\in\{0,2\},\quad GA3,\quad AB2,\quad BT2,
 \quad TD\in\{0,2\},\quad DE2,\quad EH0.
\tag{2}
\]
No assumption on the TD error, frame order, or the signs and
radial kinds of T and E is made. The original A state may
initially have either sign and either radial kind.

Write the adjacent errors as
\[
 u=d_{GA},\qquad v=d_{AB},\qquad u+v<0,
\tag{3}
\]
Sections 2--6 first treat opposite signs. Section 7 treats two
negative errors by the already proved reflected core reduction.
An error equal to zero already selects the corresponding
secondary owner at that edge.

For the opposite-sign case, apply the actual-owner alternative in
[the negative-primary flat-core entry lemma](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md)
to the negative error. If that edge already has its actual
secondary owner feasible, the original system belongs to one
of the completed single-positive-primary classes. Otherwise
the construction below replaces only A, on its true flat core,
and gives one of these two necessary comparison systems:

* if \(u<0<v\), retain GA3 with error \(u+v<0\) and select
  actual AB0 at error zero;
* if \(v<0<u\), select actual GA2 at error zero and retain
  AB2 with error \(u+v<0\).

Every other state and frame is fixed. All retained neighboring
inequalities, the sorted-circle constraints, and the original
upper bounds on positive and negative variation remain valid.
Both total variations decrease by the removed positive error.
The new A frame lies between its original frame and one of the
unchanged G/B frames.

The both-negative case has the same terminal alternatives,
with both total variations unchanged instead of decreased.
Thus every sign allocation with (3) is covered.

This is a reduction of the necessary neighboring-inequality
system. No preservation of nonneighbor packing constraints or
of the original marker value at A is asserted or needed. The
single-negative-primary exclusion can be applied through its
proved force formulas and variation bounds. This note does not
itself supply that separate scalar exclusion for positive TD2.

## 2. The four exact flat-core caps

In the exceptional branch of the entry lemma, write
\[
 a_A=\frac7{12},\qquad b=y_A>0,
 \qquad K=\frac{13}{12},\qquad k_0=\frac1{12},
 \qquad P_G=a_G-\frac12.
\tag{4}
\]
The unchanged sorted outer G and B satisfy
\[
             0<P_G<\frac{183}{200},\qquad 0<b_B<\frac9{10}.
\tag{5}
\]
The original two primary projections are
\[
 P_{GA3}=a_G+\frac7{12}\sin u-b\cos u,
 \qquad
 P_{AB2}=\frac7{12}\sin v+b\cos v+b_B.
\tag{6}
\]
For \(r\ge0\), define
\[
\begin{aligned}
 U_-(r)&=-\frac12+P_G\sec r-K\tan r,\\
 U_+(r)&=-\frac12+P_G\sec r+k_0\tan r,\\
 L_-(r)&=\frac12+(\frac12-b_B)\sec r+K\tan r,\\
 L_+(r)&=\frac12+(\frac12-b_B)\sec r-k_0\tan r.
\end{aligned}
\tag{7}
\]
Because all relevant cosines are positive, (6) is equivalent to
\[
 \begin{array}{c|cc}
 &\text{negative error }-r&\text{positive error }r\\ \hline
 GA3& b\le U_-(r)&b\le U_+(r)\\
 AB2& b\ge L_-(r)&b\ge L_+(r).
 \end{array}
\tag{8}
\]
At zero,
\[
 U_-(0)=U_+(0)=a_G-1,
 \qquad L_-(0)=L_+(0)=1-b_B.
\tag{9}
\]

On \(0\le r<19/50\), the following signs are immediate from
(5):
\[
 U_-'(r)=\frac{P_G\sin r-K}{\cos^2r}<0,
 \qquad
 L_-'(r)=\frac{K+(\frac12-b_B)\sin r}{\cos^2r}>0,
 \qquad U_+'(r)>0.
\tag{10}
\]
In addition,
\[
 L_-(r)=\frac{W(r)+(7/12)\sin r-b_B}{\cos r}
                            \ge1-b_B>\frac1{10}.
\tag{11}
\]
The first comparison is strict for \(r>0\); the concluding
strict bound \(L_-(r)>1/10\) holds throughout.

## 3. A uniform increase of the feasible interval

Let the negative and positive magnitudes be \(n>p\ge0\),
and reduce both by \(\tau\in[0,p]\). All magnitudes occurring
below lie in \([0,19/50)\), by the flat-core entry lemma.

The exact Taylor bound
\[
 \cos r\ge1-r^2/2\ge\frac{4639}{5000},\qquad
 \left(\frac{4639}{5000}\right)^2-\frac{43}{50}
                       =\frac{20321}{25000000}>0
\tag{12}
\]
gives, on that interval,
\[
          \sec^2r<\frac{50}{43},\qquad
          0\le\sec r\tan r<\frac{19}{43}.
\tag{13}
\]

For a negative GA3 error, the feasible interval gap is
\[
 F_1(\tau)=U_-(n-\tau)-L_+(p-\tau).
\]
Differentiation gives
\[
\begin{split}
 F_1'(\tau)={}&K\sec^2(n-\tau)
       -P_G\sec(n-\tau)\tan(n-\tau)\\
 &+(\tfrac12-b_B)\sec(p-\tau)\tan(p-\tau)
       -k_0\sec^2(p-\tau).
\end{split}
\tag{14}
\]
For a negative AB2 error, the gap is
\[
 F_2(\tau)=U_+(p-\tau)-L_-(n-\tau),
\]
and
\[
\begin{split}
 F_2'(\tau)={}&K\sec^2(n-\tau)
       +(\tfrac12-b_B)\sec(n-\tau)\tan(n-\tau)\\
 &-P_G\sec(p-\tau)\tan(p-\tau)
       -k_0\sec^2(p-\tau).
\end{split}
\tag{15}
\]
Both have the same uniform lower bound:
\[
\begin{split}
 F_i'(\tau)
 &>\frac{13}{12}
   -\left(\frac{183}{200}+\frac25\right)\frac{19}{43}
   -\frac1{12}\frac{50}{43}\\
 &=\frac{10459}{25800}>\frac25,
 \qquad
 \frac{10459}{25800}-\frac25=\frac{139}{25800}>0.
\end{split}
\tag{16}
\]
The initial inequalities give \(F_i(0)\ge0\). Thus the upper
cap remains above the lower cap throughout either motion,
with strict room as soon as \(\tau>0\).

## 4. Negative GA3 and positive AB2

Suppose \(u=-n\), \(v=p\), \(0<p<n\). The genuine negative
GA3 branch of the entry lemma gives
\[
                    0<b<\frac{39}{250},\qquad n<\frac14.
\tag{17}
\]
The positive AB2 inequality implies
\[
\begin{split}
 b_B
 &\ge\frac12+(\frac12-b)\cos p-\frac1{12}\sin p\\
 &>\frac12+\frac{43}{125}\frac{31}{32}-\frac1{48}
   =\frac{9749}{12000}>\frac45.
\end{split}
\tag{18}
\]
The last reserve is \(149/12000\). Here
\(\cos p\ge1-p^2/2>31/32\) and \(\sin p\le p<1/4\).

Consequently \(L_+'<0\), and
\[
                     L_+(r)\le L_+(0)=1-b_B<\frac15.
\tag{19}
\]
For \(0\le\tau\le p\), choose
\[
 u_\tau=-(n-\tau),\quad v_\tau=p-\tau,
 \qquad b_\tau=\max\{b,L_+(p-\tau)\}.
\tag{20}
\]
At zero this is the original b. The lower AB2 cap is satisfied
by construction. The upper GA3 cap also holds: (10) gives
\(U_-(n-\tau)\ge U_-(n)\ge b\), and (16) gives
\(U_-(n-\tau)\ge L_+(p-\tau)\).

Equations (17), (19), and (20) give
\[
                            0<b_\tau<\frac15.
\tag{21}
\]
Thus A stays on its sorted true flat core. Its shifted corner
is uniformly small:
\[
 \left(\frac{13}{12}\right)^2+(b_\tau+\tfrac12)^2
            <\frac{5989}{3600}<Q.
\tag{22}
\]

At \(\tau=p\), A has B's real frame. The surviving error
is \(u_p=-(n-p)=u+v<0\). Since \(v_p=0\), the AB2 and
AB0 projections are the same, namely \(b_p+b_B\). Selecting
actual AB0 therefore gives the claimed one-negative system.

## 5. Positive GA3 and negative AB2

Suppose \(u=p\), \(v=-n\), \(0<p<n\). The genuine negative
AB2 branch gives
\[
                        0<b<\frac12,\qquad n<\frac{19}{50}.
\tag{23}
\]
For \(0\le\tau\le p\), choose
\[
 u_\tau=p-\tau,\quad v_\tau=-(n-\tau),
 \qquad b_\tau=\min\{b,U_+(p-\tau)\}.
\tag{24}
\]
At zero this is again the original b. The upper GA3 cap is
satisfied by construction. The lower AB2 cap holds because
\(L_-(n-\tau)\le L_-(n)\le b\), by (10), and
\(L_-(n-\tau)\le U_+(p-\tau)\), by (16).
The lower bound (11) consequently gives
\[
                         \frac1{10}<b_\tau\le b<\frac12.
\tag{25}
\]
In particular the minimum in (24) never reaches a zero or
negative tangent. A remains sorted and on its true flat core,
and its shifted corner satisfies
\[
 \left(\frac{13}{12}\right)^2+(b_\tau+\tfrac12)^2
                   <\frac{313}{144}<Q.
\tag{26}
\]

At \(\tau=p\), A has G's real frame. The GA3 and GA2
projections coincide there, both equal to \(a_G-b_p\).
Selecting actual GA2 leaves only the negative AB2 error
\(v_p=-(n-p)=u+v<0\).

## 6. Frames, variation, and the downstream use

The real-lift convention is
\[
                  u=\theta_A-\theta_G,\qquad
                  v=\theta_B-\theta_A.
\tag{27}
\]
In (20), set \(\theta_{A,\tau}=\theta_A+\tau\), ending
at \(\theta_B\). In (24), set
\(\theta_{A,\tau}=\theta_A-\tau\), ending at \(\theta_G\).
The new frame remains in the original frame interval. Because
the A tangent remains strictly smaller than its primary,
its canonical nearest-axis choice and quarter offsets are
unchanged throughout the motion.

Only the two incident errors change. Their sum stays fixed;
their positive and negative magnitudes both decrease by
\(\tau\). Hence the whole cycle retains
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+<h,\qquad \sum_i(-d_i)_+<h.
\tag{28}
\]
Every unchanged separating projection is identical. Equations
(8), (20), and (24) prove both changed projections feasible.
The original four sorted outer circles H, G, B, D are retained
exactly, while A remains a valid true-core boundary state with
strict shifted-circle slack. The other states and radial kinds
are untouched.

The resulting data therefore satisfy every algebraic, radial,
sign, and variation hypothesis used by the corresponding
single-negative-primary stress reduction. No original-witness
claim is made for a virtual inequality: the secondary witness
at the terminal aligned edge is an exact actual projection at
the constructed state. The reduction is independent of the
TD owner and of its signed error.

If a downstream single-negative estimate is stated only for
a genuine primary witness, its same-state secondary-owner
alternative may be checked again at the terminal state.
In particular the first construction allows \(b_p\) to reach
the interval \([39/250,1/5)\). In that event the local
shifted-circle argument of the entry lemma makes actual GA2
feasible. Otherwise its genuine-GA3 cut \(b_p<39/250\)
continues to hold. This does not require repeating any global
marker or variation reduction.

## 7. Two negative errors use the reflected core companion

Now suppose \(u<0\) and \(v<0\). If the negative GA3 witness
already has actual GA2 feasible, select that witness and only
the negative AB2 primary remains. Otherwise the entry lemma
gives the positive flat-core A state in (4), with
\(b<39/250\).

Apply the local reflected reversal to the ordered triple
\((B,A,G)\). To distinguish its role names, write
\[
 (\widetilde H,\widetilde G,\widetilde A)
       =(\text{reflection of B},\text{reflection of A},
                                      \text{reflection of G}),
\tag{29}
\]
and take real frames
\[
 \widetilde\theta_H=-\theta_B,\qquad
 \widetilde\theta_G=-\theta_A,\qquad
 \widetilde\theta_A=-\theta_G.
\tag{30}
\]
The signed tangents of this triple are
\(b_B,-b,b_G\), so it has precisely the normal signs required
by [the noncanceling negative-GA1 core companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md).
Its central state is flat core, and all its shifted corners
are bounded by the same \(Q\).

Both witness identities can be checked directly. Its HG0
projection is
\[
 b_B+\frac7{12}\sin v+b\cos v=P_{AB2},
\tag{31}
\]
and its GA1 projection is
\[
 a_G+\frac7{12}\sin u-b\cos u=P_{GA3}.
\tag{32}
\]
The associated errors are respectively v and u, because
\[
 \widetilde\theta_G-\widetilde\theta_H=v,\qquad
 \widetilde\theta_A-\widetilde\theta_G=u.
\tag{33}
\]
Thus the negative-GA1 and retained-HG0 hypotheses hold with
exactly the original two inequalities.

The companion replaces only \(\widetilde G\), on its true
flat core, and selects either
\(\widetilde\theta_G'=\widetilde\theta_A\) or
\(\widetilde\theta_G'=\widetilde\theta_H\). It keeps the
other two states and their circles fixed and gives a strictly
contained core state, with positive tangent magnitude below
\(83/200<1/2\). Reflecting back therefore replaces only A.

Since \(u,v<0\), the original frames obey
\[
                         \theta_B<\theta_A<\theta_G.
\tag{34}
\]
The selected A frame is either \(\theta_G\) or \(\theta_B\),
inside this unchanged frame interval. In the first case,
\[
                          u'=0,\qquad v'=u+v<0,
\tag{35}
\]
and the actual GA2 witness is available. In the second,
\[
                          u'=u+v<0,\qquad v'=0,
\tag{36}
\]
and actual AB0 is available. The projection identities at
alignment are the same ones used in Sections 4--5.

In either case the two affected errors remain nonpositive
and retain their sum. Hence their contribution to positive
variation stays zero, and their contribution to negative
variation stays \(-u-v\). All other errors are unchanged.
The exact frame span, circle, radial, sign, and variation
requirements for the one-negative necessary system therefore
hold. Any stronger genuine-primary cut may again be recovered
by the same-state secondary-owner alternative, as explained
at the end of Section 6.

Together with the two opposite-sign constructions and the
trivial zero-error cases, this covers every allocation
\(u+v<0\). It leaves only the separate one-negative-primary
scalar exclusion, with no assumption on the unchanged TD
owner or error.
