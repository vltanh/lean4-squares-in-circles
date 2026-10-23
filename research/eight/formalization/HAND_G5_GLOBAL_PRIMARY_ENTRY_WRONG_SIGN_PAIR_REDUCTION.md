# Wrong-sign normal-branch primary pairs have actual hard or normal endpoints

## 1. The local nonpositive-total theorem

Put
\[
 Q=9789/2500,\qquad h=7/10,\qquad
 L=447/800,\qquad K=13/12,\qquad
 \kappa_0=L+1/2=847/800,\qquad \ell=21/200.
\tag{1}
\]
Use a true-core, sorted necessary H,G,A triple whose shifted
corner squares are at most the same \(q\le Q\). H and A
have nonnegative signed tangents \(b_H,b_A\). The G tangent
has the wrong weak sign:
\[
                              y_G=g\ge0.
\]
Retain actual weak HG0 and GA1 witnesses. Write
\[
 v=\theta_G-\theta_H>0,\qquad
 -z=\theta_A-\theta_G<0,\qquad
 s=z-v=\theta_H-\theta_A\ge0,
\tag{2}
\]
with all three frames in an interval of length at most h.
Thus \(0<v\le z\le h\). The actual inequalities are
\[
 \begin{split}
 b_H+a_G\sin v-g\cos v&\ge W(v),\\
 a_A-a_G\sin z+g\cos z&\ge W(z),\\
 W(r)&=(1+\cos r+|\sin r|)/2.
 \end{split}
\tag{3}
\]
Every true-core primary exceeds L, and the Q-circle bounds
give \(a_i<283/200\), \(|y_i|<9/10\).

**Nonpositive-total reduction.** Keep H,A and every other
square and frame fixed, and replace only G by
\[
 \boxed{\quad
 \theta_G'=\theta_A,\qquad a_G'=7/12,\qquad
                   y_G'=-(a_A-1).
 \quad}
\tag{4}
\]
This is a sorted true flat-core state, strictly inside the
original q-circle. At (4), GA0 is an exact actual witness,
and HG0 has strict slack greater than \(1/25\). The real
frame interval does not expand; both positive and negative
variations of the two changing errors decrease by v.

The theorem includes the zero-total case \(s=0\), the weak
sign boundary \(g=0\), and all original weak witness ties.
No sign, radial-kind, owner or frame-order assumption is
made on B,T,D,E. No high-GA exclusion is used.

If the input is an actual boundary-neighbor seven-cycle,
the output is another actual boundary-neighbor cycle. The
two changed neighboring gaps are checked in Section 5.
The local theorem makes no assertion about omitted
nonneighbor inequalities.

## 2. The wrong zero target gives a fixed positive error

First,
\[
                              v>\ell=21/200.
\tag{5}
\]
Indeed, for \(v\le0\) the HG0 projection is at most
\(b_H<.9<1\), so feasibility already forces v positive.
For \(0\le v\le h\), the projection minus its width is
strictly less than
\[
 f(v)=.9+(283/200)\sin v-W(v)
                   =.4-\tfrac12\cos v+(183/200)\sin v.
\]
This function increases on \([0,h]\). At \(v=\ell\), the
upper sine and lower width Taylor bounds give
\[
 .9+(283/200)S_5(\ell)
       -\frac{1+C_6(\ell)+S_7(\ell)}2
       =-\frac{2760134361368693}{2048000000000000000}<0.
\tag{6}
\]
Here \(S_j,C_j\) are the usual alternating sine and cosine
Taylor polynomials. This proves (5), and hence
\[
                         0\le s<z-\ell,\qquad \ell<z\le h.
\tag{7}
\]

Adding the two actual inequalities in (3) gives
\[
 b_H+a_A\ge W(v)+W(z)
        +a_G(\sin z-\sin v)+g(\cos v-\cos z)\ge2.
\]
The last two terms are nonnegative because \(0<v\le z<h<\pi/2\).
Since \(b_H<.9\),
\[
                          a_A>1.1.
\tag{8}
\]
This conclusion uses the two actual witnesses; no radial
substitution or selected marker is involved.

The same actual pair gives the stronger span cut
\[
                                  s<1/3.
\tag{8a}
\]
To see this, put \(z=v+s\). Since g is nonnegative and
sine is increasing, the pair sum is at least
\[
 b_H+a_A\ge2+D_s(v),\qquad
 D_s(v)=W(v)+W(v+s)-2+L\{\sin(v+s)-\sin v\}.
\]
On \(0\le v\le h-s\),
\[
 D_s'(v)=-(L-1/2)\cos v+\kappa_0\cos(v+s)
                         -\tfrac12\{\sin v+\sin(v+s)\}.
\]
Using \(\cos h>.7648\), \(\sin h<.6443\), gives
\[
 D_s'(v)>\kappa_0(.7648)-.6443-(L-1/2)
                                      =53341/500000>0.
\]
Consequently
\[
 b_H+a_A-2\ge D_s(0)
       =J(s):=\kappa_0\sin s-\tfrac12(1-\cos s).
\tag{8b}
\]
This J is strictly increasing on \([0,h]\). But
\(b_H+a_A-2<.9+1.415-2=63/200\), whereas
\[
 J(1/3)-63/200
 \ge\kappa_0 S_7(1/3)+\tfrac12 C_6(1/3)-\tfrac12-63/200
                          =4907657/1259712000>0.
\tag{8c}
\]
This proves (8a). In particular this span cut is derived from
the current actual pair, independently of any transport.

## 3. The new state has a strict circle loss and an exact hard witness

By (8) and the global primary upper bound,
\[
                    .1<a_A-1<.415<7/12.
\tag{9}
\]
Thus (4) is strictly sorted and has the normal negative G
sign. Its tangent magnitude is below one half. Its nearest
point to the origin therefore lies at distance exactly
\(7/12-1/2=1/12\): it is on the true flat-core boundary.

Its shifted corner square is
\[
                      K^2+(a_A-1/2)^2.
\]
The unchanged A corner gives the strict comparison
\[
 \begin{split}
 q-\{K^2+(a_A-1/2)^2\}
 &\ge(a_A+1/2)^2+1/4-K^2-(a_A-1/2)^2\\
 &=2a_A+1/4-K^2>919/720.
 \end{split}
\tag{10}
\]
Thus the comparison G lies strictly inside the same actual
circle ceiling q, even if that ceiling is below Q.

At the aligned GA error, both GA0 and GA1 have projection
\[
                         a_A+y_G'=a_A-(a_A-1)=1.
\tag{11}
\]
This supplies an actual hard GA0 witness, including its weak
tie. It is not a virtual zero inside a support estimate.

## 4. The HG witness survives with a uniform strict reserve

The new HG error is \(-s\). Its actual HG0 slack is
\[
 \begin{split}
 \mathcal S
  &=b_H-(7/12)\sin s+(a_A-1)\cos s-W(s)\\
  &=b_H+a_A\cos s-\tfrac12-\tfrac32\cos s-K\sin s.
 \end{split}
\tag{12}
\]
Multiply the second inequality in (3) by \(\cos s>0\)
and add the first one. Since \(v=z-s\), the exact identities
\[
 \sin z\cos s-\sin v=\cos z\sin s,
 \qquad
 \cos v-\cos z\cos s=\sin z\sin s
\]
give
\[
 b_H+a_A\cos s\ge W(v)+W(z)\cos s
                   +(a_G\cos z+g\sin z)\sin s.
\tag{13}
\]
Substitute the positive-error width formulas and use
\(a_G\ge L\), \(g\ge0\). Then (12)--(13) yield
\[
 \mathcal S\ge E(z,s)
 :=\cos s\{\sin z+\cos z-1\}+B(z)\sin s,
\]
\[
                   B(z)=(L-1/2)\cos z+\tfrac12\sin z-K.
\tag{14}
\]
For fixed \(0\le s\le1/3\), the right side of (14)
strictly increases with z on \([0,h]\). Indeed
\[
 E_z=(\cos s+\tfrac12\sin s)\cos z
                   -\{\cos s+(L-1/2)\sin s\}\sin z>0.
\]
The two coefficients are positive, the first is at least the
second, and \(\cos z>\sin z\). Since \(z>s+\ell\),
it is enough to bound the single function
\[
 F(s)=E(s+\ell,s)
     =\{\sin(s+\ell)+\cos(s+\ell)-1\}\cos s
                                      +B(s+\ell)\sin s.
\tag{15}
\]
We prove
\[
                          F(s)>1/25\qquad(0\le s\le1/3).
\tag{16}
\]

This is a single strict concavity check. Product-to-sum
identities give
\[
 \begin{split}
 F(s)={}&\tfrac{\kappa_0}{2}\sin(2s+\ell)
       +\tfrac14\cos(2s+\ell)+\tfrac34\cos\ell
       +\tfrac{2-\kappa_0}{2}\sin\ell-\cos s-K\sin s.
 \end{split}
\tag{17}
\]
For \(0\le s\le1/3\), the angle \(w=2s+\ell\)
is at most \(463/600\). The alternating Taylor estimates
give \(\cos w>.716\), \(\sin w<.698\). Differentiating
(17) three times yields
\[
 F'''(s)=-4\kappa_0\cos w+2\sin w-\sin s+K\cos s
       <-4\kappa_0(.716)+2(.698)+K
       =-82939/150000<0.
\]
At zero,
\[
 F''(0)=1-2\kappa_0\sin\ell-\cos\ell
       <\ell^2/2-2\kappa_0(\ell-\ell^3/6)
       =-1385065311/6400000000<0.
\tag{18}
\]
Thus \(F''<0\) throughout the interval. For exact checks of
the coarse trigonometric bounds used above,
\[
 C_6(463/600)-.716
       =25071624501194591/33592320000000000000>0,
\]
\[
 .698-S_5(463/600)
       =5945364841457/9331200000000000>0.
\]

At the left endpoint,
\[
                         F(0)=\sin\ell+\cos\ell-1>.099.
\tag{19}
\]
At the right endpoint put \(r=1/3\), \(t=r+\ell=263/600\).
The coefficient \(B(t)\) of \(\sin r\) is negative: on
the entire range, \(B\le L-K<0\). Thus
the alternating Taylor bounds have the following direction:
\[
 \begin{split}
 F(r)\ge{}&\{S_7(t)+C_6(t)-1\}C_6(r)\\
          &+\{(L-1/2)C_6(t)+\tfrac12S_7(t)-K\}S_5(r)\\
   ={}&\frac{6533524812042884971846529701}
                  {148108270141440000000000000000}>1/25.
 \end{split}
\tag{20}
\]
The exact reserve in the last comparison is
\[
       \frac{609194006385284971846529701}
            {148108270141440000000000000000}>0.
\]
Strict concavity and (19)--(20) prove (16) on the entire
interval. Equations (14)--(16) now prove
\[
                                 \mathcal S>1/25.
\tag{21}
\]

## 5. Actual boundary order and variation

The changed frame \(\theta_G'=\theta_A\) was already in
the original frame interval. The old adjacent errors were
\((v,-z)\), and the new ones are \((-s,0)\), where
\(s=z-v\). Thus their positive variation falls from v
to zero, and their negative variation falls from z to s.
Every other error and witness is unchanged.

If the input is an actual boundary-neighbor cycle, define
\[
 \alpha_H=\arctan(b_H/a_H),\quad
 \alpha_A=\arctan(b_A/a_A),\quad
 \gamma=\arctan((a_A-1)/(7/12)).
\]
The two new oriented physical gaps, with the same quarter
increments 0 and 1, are
\[
              \Delta_{HG}'=-s+\alpha_H+\gamma,
              \qquad
              \Delta_{GA}'=\pi/2-\gamma-\alpha_A.
\tag{22}
\]
The second is strictly positive by sorting, since
\(\gamma<\pi/4\). The first is greater than \(-h\)
and less than \(\pi/2\). The two new squares at HG are
contained, avoid the true core, and are disjoint by the actual
HG0 inequality (21). The two-square central-band theorem
therefore gives smaller center angle greater than \(19/25\).
A nonpositive first gap in (22) would have magnitude less
than \(h<19/25\), a contradiction. Thus it too is positive.

All other gaps are unchanged, and the two in (22) have the
same sum as their old counterparts. The gaps still telescope
to \(2\pi\), so cyclic order and all boundary-neighbor
hypotheses survive. The new G is an actual canonical flat-core
state, and every other boundary state is unchanged. The
[boundary-domain bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md)
therefore permits subsequent G0--G2 consequences on this
descendant. No original marker is transported through a
noncanonical radial state.

## 6. Complete wrong-sign entry for a selected GA1

Now start on an actual normal low-GA boundary-neighbor cycle at Q
with a retained GA1 and \(y_G\ge0\), allowing arbitrary signs
at T and arbitrary original error signs elsewhere. The
global zero-owner implication excludes HG2, so HG0 is
retained. Its error v is positive, and (5) applies. Put
\[
                         t=v+d_{GA}=\theta_A-\theta_H.
\]
There are just two signed-total cases.

If \(t\le0\), then \(d_{GA}=-z\) with \(z\ge v\).
Sections 1--5 apply directly. The result has normal G and
actual GA0, with a strict G-circle loss and strict HG slack.

If \(t>0\), reflect the whole cycle and reverse its cyclic
order. The local roles are
\[
                   (B',T',D')=(A,G,H),
                   \qquad \theta'=-\theta,\quad y'=-y.
\tag{23}
\]
The two retained projections become BT3 and TD2 with errors
\(u'=d_{GA}\), \(v'=v\), whose sum is t. The endpoints
B',D' are negative sorted outer states: the original low-GA
theorems supply positive outer A,H. The intermediate T' may
have either sign and either radial kind.

For \(d_{GA}<0\), the
[signed-cancellation theorem](HAND_G3_POSITIVE_T_PRIMARY_TOTAL_SIGNED_CANCELLATION_TRANSPORT.md)
reaches actual GA alignment. For \(d_{GA}\ge0\), the
[positive paired-primary theorem](HAND_G3_POSITIVE_PAIRED_T_PRIMARY_ENDPOINT_REDUCTION.md)
reaches either GA alignment or HG alignment. Both theorems
allow arbitrary intermediate sign and preserve the other
six actual states and witnesses. Their nearest-axis and
boundary-order statements apply in the reflected G0--G2
boundary domain; they make no E-total or high-GA assumption.

Undo the reflection. At GA alignment, the actual GA0 witness
is tied with GA1 and may be selected. At HG alignment,
\[
                         b_H-y_G'\ge1
                \quad\Longrightarrow\quad y_G'<-.1,
\tag{24}
\]
so G has its normal sign. The remaining GA1 error is
exactly \(t>0\). Consequently every originally wrong-sign
GA1 branch has an actual descendant in one of the two classes
\[
 \boxed{\quad
       \text{GA0, with G sign arbitrary};
       \qquad
       \text{HG aligned, GA1 error positive, }y_G<0.
       \quad}
\tag{25}
\]
All other six states and witnesses are unchanged. In the
nonpositive-total case the first alternative has the stronger
normal-sign and strict-loss conclusions (9)--(10), (21).

The first alternative in (25) deliberately permits a wrong
G sign. At a positive-total GA-aligned endpoint, the unchanged
A might have \(a_A\le1\); a normal G sign must not be
inferred from alignment alone. When BT2 is also selected,
the arbitrary-sign hard-owner theorem applies. With a
remaining BT3 primary, its entry reduction is still required.

## 7. Reflected BT3 statement and equality scope

Reflecting the local theorem with roles
\((H,G,A)=(D,T,B)\), reversed frames and signed tangents,
gives the exact counterpart for \(y_T\le0\), BT3 and TD2.
If \(d_{TD}=v>0\), \(d_{BT}=-z\), and \(z\ge v\),
replace only T by
\[
 \theta_T'=\theta_B,\qquad a_T'=7/12,
                         y_T'=a_B-1> .1.
\tag{26}
\]
BT2 is exact, TD2 has slack greater than \(1/25\), and
the T circle loss exceeds \(919/720\). Frame spread and
both variations behave exactly as in Section 5.

For a selected BT3 at the Q boundary with any wrong-sign T and arbitrary signed
primary total, the positive-total transports and (26) give
the two precise alternatives
\[
 \boxed{\quad
       \text{BT2, with T sign arbitrary};
       \qquad
       \text{TD aligned, BT3 error positive, }y_T>0.
       \quad}
\tag{27}
\]
The G and T operations are independent: one changes only G,
the other only T, while H,A,B,D and all E data stay fixed.
They can therefore be composed when both selected primaries
have wrong intermediate signs.

This note removes the wrong-sign obstruction on each selected
primary edge, with the explicit hard-owner alternatives
(25), (27). It does not assert that both intermediates become
normal before the hard-owner reductions, nor does it solve
the remaining normal positive-primary entry. The actual
hard-owner theorem already permits arbitrary G/T signs once
GA0 and BT2 have both been reached.

Finally, the large strict loss in (10) concerns the comparison
intermediate G, not one of the five stationary anchors. It
must not by itself be used to exclude original equality in
the full sharp theorem. Original H,A,B,D,E are unchanged,
so any later equality conclusion must use their original
constraints and the hard-owner equality characterization.
All weak original ties remain in scope of the local reduction.
