# A negative core DE3 with positive A total and arbitrary TD0

## 1. Scope and the continuous weights

Use the fixed-original-witness G0--G2 boundary at
\(Q=9789/2500\), and put
\[
 R=\sqrt Q,\qquad h=\frac7{10},\qquad L=\frac16,\qquad
 K=\frac{13}{12}.
\tag{1}
\]
The four sorted outer states H, G, B and D have signed tangents
respectively positive, negative, negative and negative. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=2,\quad TD=0,\quad DE=3,\quad EH=0.
\tag{2}
\]
The DE3 error is \(-s\), with \(0\le s\le h\), and E is on the
nonpositive true-core flat side:
\[
                         a_E=\frac7{12},\qquad b_E\ge0.
\tag{3}
\]
For a nonpositive core E with actual EH0, the flat-side conclusion
is the entry fact used in
[the negative-DE concentration theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_ANGLE_CONCENTRATION.md).
Thus (3) introduces no additional restriction in that core-E
branch.

At A permit a single nonnegative primary GA3 or AB2, or both
primaries with nonnegative signed total \(a\). This note treats
\[
                            L\le a\le h.
\tag{4}
\]
The other A arguments, and the original TD0 argument, are arbitrary.
A and T may have either sign and either radial kind. Assume the
actual neighboring inequalities and
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.
\tag{5}
\]
There is no such necessary system. There is no frame-order
assumption, and only the displayed inputs are used. In particular,
the assertion also applies to a transported necessary system
preserving them.

Use the high family from
[the negative-DE endpoint theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md),
now at parameter \(a\). With \(t=(15/8)(a-L)\), it is
\[
\begin{split}
 k&=.670158+.113718t+.006506t^2+.009026t^3+.001t^4,\\
 l&=1.005069-.146411t-.157739t^2+.162815t^3,\\
 c&=1.021248-.168873t-.165381t^2+.175944t^3.
\end{split}
\tag{6}
\]
The already proved ranges include
\[
 \frac23<k\le.800408,\quad .863<l\le1.005069,\quad
 .862<c\le1.021248,\quad k<l,c,
\tag{7}
\]
and all the balanced ratios and the correlated upper bound for c
in that theorem. The weights are held fixed when s or any remaining
angle varies.

The small range \(0\le a\le L\) is already covered, including all
E-owner choices, by
[the fixed secant-H theorem](HAND_G3_CORE_E_NEGATIVE_EH1_SECANT_H_SUPPORT.md).
The present result supplies the remaining large-a TD0 branch
with negative DE3 and actual EH0.

## 2. Four ordinary circle blocks

Let
\[
 q=\sec s,\qquad
 \overline S(f,g)=R\sqrt{f^2+g^2}-\frac{f+g}{2},
\]
and use the exact positive-A support charge
\[
 j(a)=W(a)-1-S(\sin a,1-\cos a)
\tag{8}
\]
from the signed A-combination theorem. Give the seven edges the
positive multipliers
\[
                         (k,l,l,c,c,q,1).
\tag{9}
\]
The selected A arguments contribute at least \(l j(a)\).
The core E cancellation is
\[
 qP_{DE3}(-s)=q a_D-\frac7{12}\tan s+b_E,
\tag{10}
\]
so its tangent cancels the EH0 tangent. The remaining DE demand
and flat-core contribution together give \(K\tan s\).

Unlike a TD2 argument, the original TD0 argument remains in an
ordinary outer-circle block. Its D force has components
\((q+c\sin d_{TD},c\cos d_{TD})\). The four pairs are therefore
\[
 (p_H,q_H)=(k,1),\quad (p_G,q_G)=(k,l),\quad
 (p_B,q_B)=(\min(l,c),\max(l,c)),\quad
 (p_D,q_D)=(\min(c,q),\max(c,q)).
\tag{11}
\]
Full-circle support is a valid upper bound for each actual sorted
circle. All pair ratios lie in \([1/2,1]\): for D this follows
already from \(.862<c<1.022\) and \(1\le q<1.308\).

Use
\[
\begin{split}
 N_{p,q}(u)&=\sqrt{p^2+q^2+2pq\sin u},\\
 U_{p,q}(u)&=p(\cos u+\sin u-1)
                         -R\{N_{p,q}(u)-N_{p,q}(0)\},\\
 V_{p,q}(u)&=q(\cos u-1)
                         -R\{N_{p,q}(-u)-N_{p,q}(0)\},\\
 \Psi_{p,q}(P,N)&=p(\cos P+\sin P-1)+q(\cos N-1)\\
 &\hspace{24mm}-R\{N_{p,q}(P-N)-N_{p,q}(0)\}.
\end{split}
\tag{12}
\]
The full-circle scalar baseline, after collecting all half-shifts,
is
\[
\begin{split}
 {\cal B}(a,s)={}&2k+3l+3c+q+2+l j(a)+K\tan s\\
 &-R\{\sqrt{1+k^2}+\sqrt{k^2+l^2}
                   +\sqrt{l^2+c^2}+\sqrt{c^2+q^2}\}.
\end{split}
\tag{13}
\]
At \(s=0\), this is exactly the high pure-A baseline in the
negative-DE endpoint theorem.

Delete only the selected A arguments and the DE argument from
the algebraic angular vector. The remaining variations obey
\[
                  P\le h-a,\qquad N\le h-s,\qquad
                              N-P=a-s.
\tag{14}
\]
For two A primaries, the deleted positive variation is at least a;
their deleted negative variation only enlarges this domain.
Any missing argument in an ordinary pair is allowed as a virtual
zero. In particular, the removed DE argument gives the D block
its second, initially zero, argument. Neither an original TD2
witness nor an original alignment is asserted.

The homogeneous two-simplex concentration proof applies to any
number of these full-circle blocks. It leaves, added to (13),
\[
\begin{array}{ll}
 V_i(a-s),&s\le a,\\
 U_i(s-a),&s\ge a,\\
 \Psi_i(h-a,h-s),&\text{either case},\\
 U_i(h-a)+V_j(h-s),&i\ne j,
\end{array}
\tag{15}
\]
with \(i,j\in\{H,G,B,D\}\). For a feasible necessary system the
minimum of these stresses is nonpositive. The rest of the proof
shows it is positive.

## 3. A D negative allocation is no worse than H

For all the coefficients in (7), all \(0\le s\le h\), and all
\(0\le u\le h\),
\[
                             V_D(u)\ge V_H(u).
\tag{16}
\]
At \(u=0\) both sides vanish.

First, for \(p/q\in[1/2,1]\), \(V_{p,q}(u)\) increases with p.
If \(p-q\sin u\le0\), this is immediate from its derivative.
Otherwise, squaring its positive fractions reduces the claim to
\[
 q^2\sin u\{2pq-(p^2+q^2)\sin u\}>0
\tag{17}
\]
for \(u>0\). Here \(2pq/(p^2+q^2)\ge4/5>\sin h\).
Thus it suffices to use \(p_D=.862\) and \(k=.800408\).

For fixed \(p=.862\), \(V_{p,q}\) is concave in
\(1\le q\le1.308\). Indeed
\[
 \frac{\partial^2 V}{\partial q^2}
 =Rp^2\left\{\frac1{(p^2+q^2)^{3/2}}
       -\frac{\cos^2u}{(p^2+q^2-2pq\sin u)^{3/2}}\right\}<0
\tag{18}
\]
for \(u>0\), since \(2pq/(p^2+q^2)>\sin u\).
At \(q=1\), (16) follows from p-monotonicity. It remains to compare
the two fixed pairs
\[
                         (.862,1.308),\qquad (.800408,1).
\tag{19}
\]

For a pair put \(C(t)=-RN_{p,q}''(t)\), \(B=pq\), and
\(\alpha=(p^2+q^2)/(pq)\). Direct differentiation gives, with
\(y=\sin u\),
\[
 C'(-u)=R\sqrt B\cos u\,
       \frac{\alpha^2-3-\alpha y+y^2}{(\alpha-2y)^{5/2}}.
\tag{20}
\]
Both B and \(\alpha\) are larger for the first pair in (19).
The fraction is positive and increases with \(\alpha\) on
\(2\le\alpha\le5/2,\ 0\le y\le.645\). Its derivative has the
sign of
\[
 15-\alpha^2-5\alpha y-y^2
 \ge15-(5/2)^2-5(5/2)(.645)-(.645)^2>.271.
\tag{21}
\]
Consequently the difference \(C_D(-u)-C_H(-u)\) decreases with u.
At zero, positive squaring gives
\[
                            C_D(0)<.655,\qquad C_H(0)>.603.
\tag{22}
\]
The difference \(F(u)=V_{.862,1.308}(u)-V_{.800408,1}(u)\)
therefore satisfies
\[
 F''(u)<-.308\cos h+.052<-.18.
\tag{23}
\]
Thus F is concave, and \(F(0)=0\). Its other endpoint is positive.
For complete rational endpoint data, put
\[
 A_D=2.453908,\quad B_D=1.127496,\quad
 A_H=1.640652966464,\quad B_H=.800408.
\]
The Taylor bounds at h and positive squaring give
\[
\begin{gathered}
 \sqrt{A_D}>1.56649,\quad
 \sqrt{A_D-2B_D\sin h}<1.00061,\\
 \sqrt{A_H}<1.28088,\quad
 \sqrt{A_H-2B_H\sin h}>.78062.
\end{gathered}
\tag{24}
\]
Their signed bracket is larger than .06562. Since
\(R>1.978787507\),
\[
             F(h)>.308\{C_{10}(h)-1\}
                          +1.978787507(.06562)>.0574.
\tag{25}
\]
Concavity proves \(F\ge0\), and completes (16).

## 4. Removing all saturated D alternatives

The D ratio obeys
\[
                 q_D/p_D<1.52,\qquad 1.52\sin h<1.
\tag{26}
\]
The direct same-block identities (24) in the negative-DE
concentration theorem therefore give
\[
 \Psi_D(P,N)\ge
 \begin{cases}
 V_D(N-P),&P\le N,\\
 U_D(P-N),&N\le P.
 \end{cases}
\tag{27}
\]
The first branch then uses (16).

For a separated negative D allocation, replace \(V_D\) by \(V_H\)
using (16). The balanced three-block separated estimate applies
even if the resulting positive and negative scalar indices are
both H: it bounds U and V independently and does not infer a
same-block original witness.

The only additional separated case has positive D. The
[separated-D comparison](HAND_G3_CORE_E_NEGATIVE_DE3_TD0_SEPARATED_D_DOMINATION.md)
proves, for \(P=h-a,\ N=h-s\) and \(j\in\{H,G,B\}\),
\[
 U_D(P)+V_j(N)\ge
 \begin{cases}
 V_j(N-P),&P\le N,\\
 U_D(P-N),&N\le P.
 \end{cases}
\tag{28}
\]
It uses only (6)--(7), so it applies throughout the present
necessary-system scope.

All alternatives remaining in H, G and B are exactly those of
the already proved high negative-DE theorem at its pure-A
endpoint \((a,z)=(a,0)\). Its whole-s reduction and endpoint
certificates make their stresses strictly positive. Equations
(16), (27), and (28) leave just one new scalar family:
\[
                    {\cal B}(a,s)+U_D(s-a),\qquad a\le s\le h.
\tag{29}
\]

## 5. Concavity of the new pure D-positive family

Fix a and the coefficients in (6). Put
\[
 x=\tan s,\quad w=\sqrt{1+x^2}=\sec s,\quad
 d=\cos a-\sin a,\quad f=\cos a+\sin a.
\]
After the D norm is combined, its square is
\[
 w^2+c^2+2cw\sin(s-a)
             =(x+c\cos a)^2+(1-c\sin a)^2.
\tag{30}
\]
Up to an x-independent constant, (29) is
\[
 w+Kx+\min(c,w)\{\phi(s-a)-1\}
          -R\sqrt{(x+c\cos a)^2+(1-c\sin a)^2}.
\tag{31}
\]
The last term is concave in x. Its second coordinate is positive,
since \(1-c\sin a>1-1.022(.645)>.34\).

If \(w\le c\), the charge before the norm in (31) is affine:
\[
                              d+(K+f)x.
\tag{32}
\]
If \(w\ge c\), it is
\[
                         w+c\frac{d+xf}{w}-c+Kx.
\tag{33}
\]
Its second derivative has the sign of
\[
              1+x^2+c\{(2x^2-1)d-3xf\}.
\tag{34}
\]
This expression is strictly negative on the required domain.

Here is an elementary whole-domain verification. For fixed
\(x\in[\tan L,\tan h]\), allow \(a\in[L,\arctan x]\), and put
\[
                         T(a)=(2x^2-1)d-3xf.
\]
One has \(T<0\) and \(T''=-T>0\). For example, if
\(2x^2-1\le0\) the sign is immediate; otherwise use
\(d\le1,\ f\ge1\) and \(2x^2-1-3x<0\) for \(x<.843\).
Thus T is convex in a. Since \(c>.862\), (34) is bounded above
by the maximum of its two endpoint bounds with \(c=.862\).

At \(a=\arctan x\), this upper bound is
\[
        \sqrt{1+x^2}\{\sqrt{1+x^2}-.862(2x+1)\}<0.
\tag{35}
\]
Indeed \(x\ge1/6\), the squared difference
\(.862^2(2x+1)^2-(1+x^2)\) is increasing there, and its value at
\(1/6\) is positive.

At \(a=L\), use
\[
 .8202<\cos L-\sin L<.8203,\qquad
                       \cos L+\sin L>1.152.
\]
The upper bound is no larger than the convex quadratic
\[
 {\cal P}(x)=1-.862(.8202)
             +\{1+2(.862)(.8203)\}x^2-3(.862)(1.152)x.
\tag{36}
\]
Since \(1/6<\tan L\le x\le\tan h<.843\),
\[
                         {\cal P}(1/6)<-.13,\qquad
                         {\cal P}(.843)<-.5
\tag{37}
\]
prove its negativity everywhere.

Finally, at the possible switch \(w=c\), the derivative of (31)
has the downward jump
\[
                         -\frac{x}{w}\{\phi(s-a)-1\}\le0.
\tag{38}
\]
Thus (29) is concave in \(x=\tan s\) on the entire interval
\(s\in[a,h]\). Its minimum occurs at \(s=a\) or \(s=h\).
The \(s=a\) value is the already certified high pure-A \(N_Z\)
endpoint. Only the latter endpoint is new.

## 6. One exact whole-interval endpoint certificate

Use the high pure-A polynomial data in Sections 6 and 8 of the
negative-DE endpoint theorem. Explicitly, with
\(S_-=S_{11}, S_+=S_9, C_-=C_{10}, C_+=C_{12}\),
\[
\begin{split}
 J_1(a)&=\tfrac12(C_-(a)-1)
                +(\tfrac12-1.414575672)S_+(a)-.302(a-L)^6,\\
 B(a)&=2k+3l+3c+3+lJ_1(a),\\
 P_H&=1+k^2,\quad P_G=k^2+l^2,\quad P_B=l^2+c^2,\\
 r_H&=.8+.6k,\quad r_G=.62k+.7846l,\quad r_B=.7071(l+c).
\end{split}
\tag{39}
\]
In particular \(B-1>1\) on \([L,h]\).

Put \(u=h-a\) and use the rational constants
\[
                 c_-=C_{10}(h),\quad c_+=C_{12}(h),
                 \quad s_-=S_{11}(h),\quad c_4=C_4(h).
\]
After multiplying the \(s=h\) value of (29) by \(\cos h>0\),
a polynomial lower elementary term and upper norm squares are
\[
\begin{split}
 E_h={}&c_-(B-1)+1+Ks_-
                  +c c_-\{C_{10}(u)+S_{11}(u)-1\},\\
 \widetilde P_H={}&c_+^2P_H,\quad
 \widetilde P_G=c_+^2P_G,\quad
 \widetilde P_B=c_+^2P_B,\\
 \widetilde P_D={}&1+c^2c_+^2+2cc_+S_9(u).
\end{split}
\tag{40}
\]
The cosine multiplication has the correct direction because
\(B-1>0\) and
\(C_{10}(u)+S_{11}(u)-1\ge0\) for \(0\le u\le8/15\).
For the latter, the simpler lower polynomial
\(u-u^2/2-u^3/6\) already suffices.

Choose positive auxiliaries
\[
\begin{split}
 \widetilde r_H&=c_4r_H,\qquad
 \widetilde r_G=c_4r_G,\qquad
 \widetilde r_B=c_4r_B,\\
 \widetilde r_D&=.758+.652c c_4+.55S_5(u).
\end{split}
\tag{41}
\]
Use the explicit rational norm numerator
\[
 {\cal N}(E;\mathbf r;\mathbf P)
 =2E\prod_i r_i
       -1.978787508\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j
\tag{42}
\]
and define
\[
 N_{hD}={\cal N}\bigl(E_h;
   (\widetilde r_H,\widetilde r_G,\widetilde r_B,\widetilde r_D);
   (\widetilde P_H,\widetilde P_G,\widetilde P_B,\widetilde P_D)\bigr).
\tag{43}
\]
The inequality
\(\sqrt P\le(P+r^2)/(2r)\) gives a lower bound for the
multiplied stress by \(N_{hD}/(2\prod\widetilde r_i)\).

Let \({\cal C}_{[L,h]}\) and \({\cal U}_{[L,h]}\) be the
explicit Chebyshev coefficient lower and upper aggregates (42)--(44)
of the endpoint theorem. Direct rational coefficient arithmetic
from (6), (39)--(43) gives
\[
\begin{gathered}
 \deg N_{hD}=30,\qquad
 \min_i{\cal C}_{[L,h]}(\widetilde r_i)>.83,\\
 {\cal U}_{[L,h]}(N_{hD}')<-.6995,\qquad
                         N_{hD}(h)>.0053133.
\end{gathered}
\tag{44}
\]
These are whole-interval coefficient bounds, with no evaluation
nodes. They make \(N_{hD}\) decreasing and positive throughout
\([L,h]\). Every denominator is positive. Thus the \(s=h\)
endpoint in (29) is strictly positive.

## 7. Completion

Section 5 reduces the sole new pure D-positive family to its
two positive endpoints. Sections 3--4 remove every additional D
allocation from the four-block concentration. The old three-block
alternatives are already positive by the high negative-DE
theorem. Consequently every alternative in (15), added to (13),
is positive, contradicting the necessary weighted stress.

This proves the scope in Section 1 for every original TD0 error.
The argument is a pointwise weighted-support relaxation of the
original inequalities; the fourth block does not replace the
original TD0 witness by a TD2 witness.
