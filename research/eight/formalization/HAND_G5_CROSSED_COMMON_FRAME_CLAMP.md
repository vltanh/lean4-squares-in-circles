# Clamp a crossed common frame to the outer frame after GA alignment

## 1. The local crossed side and the conclusion

Put
\[
 q_L=\frac{19577}{5000},\quad Q=\frac{9789}{2500},\quad
 p=\frac{50}{49},\quad S_0=2\sqrt{Q-1}-3,\qquad q_L\le q\le Q.
\tag{1}
\]
Retain normal signs at H,G,A,B,T,D, either E sign, true core
avoidance, sorted own-frame magnitudes, corner circles at most q,
and real frame spread at most \(7/10\). The actual witnesses are
\[
 HG=0,\quad GA=0,\quad BT=2,\quad TD\in\{0,2\},
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
Assume
\[
 \theta_G=\theta_A=\theta_B=\rho,\quad b_A+b_B=1,\quad
 \theta_T\le\rho,\quad
 0<r_0:=\rho-\theta_H<\frac1{25},\quad b_H>\frac34.
\tag{3}
\]

**Clamp theorem.** There is a descendant at the same q with
\[
                   \theta_H=\theta_G'=\theta_A'=\theta_B'>\theta_T.
\tag{4}
\]
H,T,D,E, all their coordinates and frames, and the original
mixed and TD witnesses are unchanged. Both middle corners can
be chosen strictly below q. Signs, sorting, true core, and the
real frame interval are retained.

No lower bound of \(1/2\) on the moving A tangent is assumed
in this theorem. The rate comparison includes the tangent
values below \(1/2\) that can arise during the move.

The large-tangent crossed reductions supply (3).
For HG0, use
[the large-tangent GA-alignment theorem](HAND_G5_CROSSED_NONCANCELING_LARGE_TANGENT_GA_ALIGNMENT.md).
For HG2, first use
[the crossed canceling reduction](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md)
to obtain an actual HG0 witness at GA alignment.
The HG0 capture gives \(r_0<.04\). If \(b_A\ge1/2\),
the same-circle HG0/GA0 bound then gives
\[
 b_H>\frac12+.292(1-.04^2/2)-.915(.04)>\frac34.
\tag{5}
\]
Thus the theorem completes the common-frame move in both
large-tangent crossed branches. Its more general input (3)
also allows any separately proved small-tangent entry.

## 2. Actual-circle caps throughout the proposed move

Translate the initial common frame to zero, write
\(\theta_H=-r_0,\theta_T=-u_0\), and move the common
A/B/G frame down by s. Set
\[
 r=r_0-s,\qquad u=u_0-s,\qquad
 0\le s\le \min(r_0,u_0).
\tag{6}
\]
The signed-E global intermediate-order theorem gives \(u_0>0\).
The extension to either E sign is the exact endpoint reflection
in Section 2 of the crossed canceling note.

Keep the actual \(b_H,b_T\) fixed. The same-circle HG0 inverse is
\[
 M(r)=\frac12+\cos r+\sin r-b_H,\qquad
 D(r)=M(r)\cos r-\sin r\sqrt{q-M(r)^2}.
\tag{7}
\]
G's transverse corner is D; the aligned GA condition requires
A's primary corner to be \(D+1\). Define
\[
                         L_A(r)=\sqrt{q-(D(r)+1)^2}.
\tag{8}
\]
These expressions are defined on the entire interval in (6),
and no G-floor clipping is needed.

Indeed, sorting and H's circle give \(b_H<.9\). Therefore
\(D_0:=D(0)=3/2-b_H\) lies in \((.6,.75)\).
At the sorted G corner with transverse corner \(D_0\), put
\(X_0=\sqrt{q-D_0^2}>1.83\). Its HG0 projection minus \(M(r)\) is
\[
 (D_0-1)(\cos r-1)+(X_0-1)\sin r\ge0.
\]
The projection increases with its transverse corner, so
\(D(r)\le D_0<.75\). Conversely \(M(r)\ge D_0>.6\) and
\(\sqrt q<1.98\) give
\[
 D(r)>.6(1-.04^2/2)-1.98(.04)>.52>\frac12.
\tag{9}
\]
Also \(M(r)<.79<\sqrt q\). Thus (7) is its positive, sorted
inverse branch. In particular \(L_A(r)>.92\), since
\(q_L-1.75^2>.92^2\).

For the opposite unchanged hard contact put
\[
 d=b_T+\frac12,\quad C(u)=d+\cos u,\quad
 w(u)=\sqrt{q-C(u)^2},\quad
 L_B(u)=w(u)\cos u-C(u)\sin u.
\tag{10}
\]
This is the actual BT2 transverse cap.
The initial hard contact gives \(1/2\le d<.915\), so
\[
 q-C(u)^2\ge q_L-1.915^2>.24.
\]
If \(X_B=C\cos u+w\sin u\), direct differentiation gives
\[
 L_B'(u)=-X_B(w-\sin u)/w<0,
\]
because \(w^2-\sin^2u\ge q-(d+1)^2>0\).
The cap stays positive as u decreases from \(u_0\).
At every cap point \(X_B\ge1+d\ge1.5\), so
\(L_B\le\sqrt{q-9/4}<1.291\).

The original two middle corners imply
\[
                       L_A(r_0)+L_B(u_0)\ge2.
\tag{11}
\]
Whenever the cap sum is at least two, positive transverse
corners below the two caps can be chosen with sum two.
Putting the middle points on their respective hard-contact
lines then realizes the adjacent necessary system.
Section 7 makes the endpoint construction explicit.

## 3. The unchanged endpoint budget restricts every active boundary

The actual H,D,E endpoint theorem, with either E sign, gives
\[
 b_H+b_D-p(\theta_H-\theta_D)+S_0<2.
\]
The unchanged all-sign TD charge consequently gives
\[
                       b_H-b_T+p(r-u)<1-S_0.
\tag{12}
\]
This holds throughout (6), since \(r-u\) is constant.

Consider an active cap boundary
\[
 L_A(r)+L_B(u)=2,\qquad Y=L_A(r),\quad B=L_B(u)=2-Y.
\tag{13}
\]
For this paragraph only enlarge the two middle circles to Q:
\[
 R_A=\sqrt{Q-Y^2},\quad R_B=\sqrt{Q-B^2},\quad
 P_A=R_A-1,\quad P_B=R_B-1,\quad
 w_A=\sqrt{Q-P_A^2}.
\]
The same-circle HG0 bound and actual BT2 contact give
\[
 \begin{split}
 b_H&\ge\frac12+(1-P_A)\cos r-(w_A-1)\sin r,\\
 b_T&\le P_B\cos u-B\sin u-\frac12.
 \end{split}
\tag{14}
\]
The function
\[
 f(r)=pr-\{\sqrt{Q-1/4}-1\}\sin r-\frac12(1-\cos r)
\]
is nonnegative on \([0,.04]\), by Section 4 of the
large-tangent GA-alignment theorem.
Since \(P_A\ge1/2\) and \(w_A\le\sqrt{Q-1/4}\),
(12)--(14) imply the weaker inequality
\[
 F(Y,u):=2-P_A-P_B\cos u+B\sin u-pu<1-S_0.
\tag{15}
\]
Both actual caps and every rate below still use q.

### Every active boundary has \(Y>48/49\)

Define
\[
 g_B(u)=P_B(\cos u-1)-B\sin u+pu.
\]
Concavity of \(x\mapsto\sqrt{Q-x^2}\), with \(Y+B=2\),
gives \(R_A+R_B\le2\sqrt{Q-1}\). Thus (15) requires
\(g_B(u)>0\). But on the hard-feasible interval
\[
 g_B'(0)=p-B,\qquad
 g_B''(u)=-\{P_B\cos u-B\sin u\}\le-\frac12.
\]
If \(B\ge p\), positivity is impossible. Therefore
\[
                              Y>2-p=\frac{48}{49}.
\tag{16}
\]

### When \(Y\le1\), the opposite angle is less than .06

Here \(1\le B<p\). At fixed positive u,
\[
 \partial_Bg_B(u)=\frac{B}{R_B}(1-\cos u)-\sin u<0.
\tag{17}
\]
The sign follows from \(B<R_B\) and \(u<7/10\).
Thus \(g_B(u)\le g_1(u)\).
At \(u=.06=3/50\), use \(\sqrt{Q-1}>683/400\),
the quartic upper cosine, and cubic lower sine:
\[
 \begin{split}
 g_1(.06)
 &<\left(\frac{683}{400}-1\right)
       \left(-\frac{.06^2}{2}+\frac{.06^4}{24}\right)
   -\left(.06-\frac{.06^3}{6}\right)+p(.06)\\
 &=-\frac{12375591}{980000000000}<0.
 \end{split}
\tag{18}
\]
Strict concavity and \(g_B(0)=0\) show that
\[
                  48/49<Y\le1\quad\Longrightarrow\quad u<.06.
\tag{19}
\]

### When \(1\le Y\le1.04\), the opposite angle is less than .158

Now \(.96\le B\le1\). The hard contact gives \(u<.23\):
evaluate its upper bound \(.731\cos u-.96\sin u\)
at .23 using the quartic upper cosine and cubic lower sine.
For \(u\ge.158\) on this feasible range,
\[
 F_Y=\frac{Y}{R_A}-\frac{B}{R_B}\cos u-\sin u
 <\frac{1.04}{1.68}
   -\frac{.96}{1.731}(1-.23^2/2)
   -\left(.158-\frac{.158^3}{6}\right)<0.
\tag{20}
\]
Also \(F_u=P_B\sin u+B\cos u-p>0\).
The expression before p increases with u while the hard
contact is feasible, and at .158 it is greater than
\[
 .7075\left(.158-\frac{.158^3}{6}\right)
                         +.96(1-.158^2/2)>p.
\tag{21}
\]
Hence the hypothetical range has its minimum F at
\(Y=1.04,u=.158\).
Positive squaring gives \(R_A<1.68345,R_B<1.73032\).
At that one point, the same Taylor polynomials give
\[
 \begin{split}
 F(1.04,.158)-(1-S_0)
 &>2(1.7075)-1.68345
       -.73032\left(1-\frac{.158^2}{2}+\frac{.158^4}{24}\right)\\
 &\quad+.96\left(.158-\frac{.158^3}{6}\right)-p(.158)-1\\
 &=\frac{46338843272333}{306250000000000000}>0.
 \end{split}
\tag{22}
\]
This contradicts (15). Thus
\[
                    1\le Y\le1.04\quad\Longrightarrow\quad u<.158.
\tag{23}
\]
These divisions come from the tangent value at an active
cap boundary, rather than a sampled angle partition.

## 4. Rates on the lower tangent range

Retain the actual q. At an active boundary put
\[
 R=\sqrt{q-Y^2},\quad D=R-1,\quad X=\sqrt{q-D^2},
 \quad t=\tan r.
\]
Implicit differentiation of the exact HG0 inverse gives
\[
 \mathcal A=L_A'(r)=\frac RY E,\qquad
 E=X-1+\frac{t(X-D)}{X-Dt}.
\tag{24}
\]
For the opposite cap put \(Z=\sqrt{q-B^2}\),
\(s_u=\sin u,c_u=\cos u\), \(U=(Z-1)s_u+Bc_u\).
Its gain as u decreases is
\[
                        \mathcal B=-L_B'(u)=\frac{ZU}{U+s_u}.
\tag{25}
\]

On \(48/49\le Y\le26/25\), the entire actual-q range has
\[
 1.68<R<1.72,\quad .68<D<.72,\quad
 1.84<X<1.86,\quad 0\le t<.041.
\tag{26}
\]
Here \(\mathcal A\) decreases with Y and increases with q
and r. Indeed, at fixed q,
\[
 \mathcal A_Y=-\frac{qE}{RY^2}+\frac DX+
       \frac{q\,t(1-t)}{X^3(1-(D/X)t)^2}.
\]
Since \(E>X-1>.84\), (26) gives
\[
 \mathcal A_Y<
 -\frac{q_L(.84)}{1.72(1.04)^2}
 +\frac{.72}{1.84}
 +\frac{Q(.041)}{1.84^3(1-(.72/1.84)(.041))^2}<-1.
\tag{27}
\]
At fixed Y, use \(X^2=Y^2+2R-1\):
\[
 E_R=\frac1X\left[1-
       \frac{t(1-t)(Y^2+R)}{(X-Dt)^2}\right]>0,
\tag{28}
\]
because the bracket exceeds
\(1-.041(1.04^2+1.72)/(1.84-.72(.041))^2>0\).
Thus \(\mathcal A_R=(E+RE_R)/Y>0\), proving the q sign.
Finally \(E_t=X(X-D)/(X-Dt)^2>0\), proving the r sign.

The opposite rate increases with q and decreases with u:
\[
 \partial_Z\mathcal B=
 \frac{U}{U+s_u}+\frac{Zs_u^2}{(U+s_u)^2}>0,\qquad
 \partial_u\mathcal B=-\frac{ZB}{(U+s_u)^2}<0.
\tag{29}
\]
For \(.96\le B\le p\), \(0\le u\le.158\), it also
decreases with B. Multiplying its B derivative by the
positive \(Z(U+s_u)^2\) gives
\[
 -BU(U+s_u)+Z^2s_uc_u-ZBs_u^2
 \le-.96\{.96(1-.158^2/2)\}^2+Q(.158)<0.
\tag{30}
\]

The angle restrictions (19),(23) and these monotonicities
reduce the two lower tangent ranges to four endpoints:
\[
 \begin{array}{ll}
 1\le Y\le1.04:&
 \mathcal A\le\mathcal A(Q,1,.04)<1.491,\quad
 \mathcal B\ge\mathcal B(q_L,1,.158)>1.493,\\[2pt]
 48/49<Y\le1:&
 \mathcal A\le\mathcal A(Q,48/49,.04)<1.53,\quad
 \mathcal B\ge\mathcal B(q_L,p,.06)>1.60.
 \end{array}
\tag{31}
\]
In the B notation the second argument is its transverse
corner B; in the A notation it is Y.

Here are explicit rational checks of these endpoint bounds.
For the first A endpoint use
\[
 \sqrt{Q-1}<1.70752,\quad D>.7075,\quad X<1.84799,
 \qquad \tan(.04)<.040022.
\]
Since E increases with X and decreases with D,
\[
 \mathcal A(Q,1,.04)<
 1.70752\left[
 .84799+\frac{.040022(1.84799-.7075)}
                  {1.84799-.7075(.040022)}\right]<1.491.
\tag{32}
\]
For the second endpoint, \(R<1.72,D>.719,X<1.844\)
at \(Y=48/49,q=Q\), so
\[
 \mathcal A(Q,48/49,.04)<
 \frac{1.72}{48/49}\left[
 .844+\frac{.040022(1.844-.719)}
                  {1.844-.719(.040022)}\right]<1.53.
\tag{33}
\]
The radical bounds follow by positive squaring.

For the B endpoints define the alternating polynomials
\[
 S_7(x)=x-\frac{x^3}{6}+\frac{x^5}{120}-\frac{x^7}{5040},
 \qquad S_9(x)=S_7(x)+\frac{x^9}{362880},
\]
\[
 C_6(x)=1-\frac{x^2}{2}+\frac{x^4}{24}-\frac{x^6}{720}.
\]
With
\[
 (Z_-,B,u)=(1.7074,1,.158)
       \quad\hbox{or}\quad(1.695,p,.06),
\]
positive squaring gives \(Z_-<\sqrt{q_L-B^2}\).
Put \(U_-=(Z_--1)S_7(u)+BC_6(u)\). Then
\[
                 \mathcal B(q_L,B,u)>
                    \frac{Z_-U_-}{U_-+S_9(u)}.
\tag{34}
\]
The two right sides exceed 1.493 and 1.60 by respectively
more than .00054 and .00426. This proves (31), and in
particular every active boundary with \(Y\le1.04\) has
\[
                         \mathcal B-\mathcal A>\frac1{500}.
\tag{35}
\]
All terminating decimals in this note are exact rationals.

## 5. The upper tangent range

For \(Y\ge26/25\), the separate
[upper-tangent cap-rate lemma](HAND_G5_CROSSED_UPPER_TANGENT_CAP_RATE.md)
applies to the actual q and every hard-feasible opposite
angle. It proves
\[
 \mathcal B-\mathcal A>
 \frac9{1000}+\frac3{20}\left(Y-\frac{26}{25}\right)>0.
\tag{36}
\]
That lemma differentiates both rates over their entire
tangent intervals and checks one intrinsic endpoint.
It does not assume the angle restrictions (19) or (23).

Combining (16),(35),(36), every possible active boundary has
\[
 \frac{d}{ds}\{L_A(r_0-s)+L_B(u_0-s)\}
                            =\mathcal B-\mathcal A>0.
\tag{37}
\]
This includes the case in which the moving A tangent passes
below \(1/2\).

## 6. Continue to H; reaching T first is impossible

The cap sum is differentiable on the compact interval (6),
and starts at least at two by (11). Equation (37) prevents
it from crossing from the feasible side to a value below
two. In fact it is strictly greater than two at every
positive time in (6). If it starts at two, (37) makes it
immediately larger. Any first later equality would have a
nonpositive left derivative, contradicting (37). The same
argument excludes equality at the final endpoint.

If \(u_0\le r_0\), the time \(s=u_0>0\) would give a feasible
descendant with \(G=A=B=T\) in frame. Realize its positive
cap-sum slack using (7)--(10): G is sorted on its q-circle,
A lies on its aligned GA contact, B lies on its original
BT2 contact, and the middle tangents sum to one. H,T,D,E
remain unchanged. The constructions preserve normal signs,
true core, circles, actual mixed and TD witnesses, and the
original real frame interval.

This contradicts the signed-E global intermediate-order
theorem, which requires \(\theta_G>\theta_T\).
Hence \(u_0>r_0\). The common frame reaches H at \(s=r_0\)
and is still strictly above T, with
\[
                       L_A(0)+L_B(u_0-r_0)>2.
\tag{38}
\]

## 7. Realization and separate strict losses

Put \(u'=u_0-r_0>0\), and set
\[
 D_0=\frac32-b_H,\quad
 b_G'=D_0-\frac12=1-b_H,\quad
 a_G'=\sqrt{q-D_0^2}-\frac12.
\]
Give G,A,B the common frame \(\theta_H\).
HG is then aligned and has transverse sum one.
Choose transverse corners satisfying
\[
 Y_A+Y_B=2,\qquad
 \frac12<Y_A<L_A(0),\qquad
 \frac12<Y_B<L_B(u').
\tag{39}
\]
Such a choice exists by (38). Each cap is less than
\(\sqrt{q-9/4}<1.291\), so the lower bounds in (39)
impose no additional restriction. Set
\[
 b_A'=Y_A-\frac12,\qquad a_A'=D_0+\frac12,
\]
\[
 b_B'=Y_B-\frac12,\qquad
 a_B'+\frac12=1+\frac{d+Y_B\sin u'}{\cos u'}.
\tag{40}
\]
GA0 and BT2 are equalities, and aligned AB has transverse
sum one. Both middle corners are strictly inside their
q-circles. For A this follows from \(Y_A<L_A(0)\).
For B, its squared corner value strictly increases with
\(Y_B>0\) along the hard-contact line in (40), and equals
q at the cap.

Both middle primaries are at least one and both tangents
are below .791, so sorting and true core hold.
Also \(.6<D_0<.75\) and \(a_G'>1.33\), so G is strictly
sorted and satisfies the true core. H,T,D,E and their
contacts remain unchanged. The common frame moved only
inside the original real interval.

Every original positive crossing in (3) therefore produces
separate strict A and B circle losses. Any inherited strict
middle loss is retained in this stronger form. A later
sharp terminal whose equality requires all five anchors
on the q-circle cannot arise from this positive crossing.
Equality is not inferred by identifying a constructed
state with its ancestor.

The proof uses two exact cap derivatives, the unchanged
endpoint budget, analytic monotonicity, and fixed rational
Taylor comparisons. No angular grid, numerical acceptance
premise, Lean compilation, or CI result is used.
