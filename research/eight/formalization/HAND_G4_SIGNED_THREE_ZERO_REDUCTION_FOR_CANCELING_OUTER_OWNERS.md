# A signed three-zero reduction with the canceling outer owners

## 1. Scope: a radius-preserving necessary relaxation

Put
\[
 q_L=\frac{19577}{5000},\qquad Q=\frac{9789}{2500},
 \qquad q_L\le q\le Q.                                      \tag{1}
\]
The lower restriction in (1) is legitimate in a radius lower-bound
argument: first enlarge a smaller containing disk to squared radius
\(q_L<q_*\), without moving its squares. A constructed corner below
uses the actual q, not Q.

Retain the original signs
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\]
the original own-frame inequalities
\[
 a_i\ge b_i,\qquad
 (a_i+\tfrac12)^2+(b_i+\tfrac12)^2\le q,                       \tag{2}
\]
and real frames of total spread at most \(7/10\). Assume the ordering
\[
 \theta_D\le\theta_A,\theta_B\le\theta_H,\qquad
 \theta_D\le\theta_E\le\theta_H.                              \tag{3}
\]
No order is initially required of \(\theta_G,\theta_T\). Retain these
particular original SAT axes:
\[
\begin{array}{c|rrrrrrr}
 \text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
 \text{axis}&2&0&0\text{ or }2&2&0&3&1.
\end{array}                                                  \tag{4}
\]
The canceling appearances of the same \(b_G\) in HG2/GA0 and the same
\(b_T\) in BT2/TD0 are essential. The other original outer zero owners
HG0 and TD2 are not included.

**Three-zero reduction.** There are new A and B coordinates at the
same actual radius q and a common frame
\(\rho\in[\theta_D,\theta_H]\) for which
\[
\begin{split}
 b_H+a_A'\cos(\theta_H-\rho)-b_A'\sin(\theta_H-\rho)
       &\ge1+W(\theta_H-\rho),\\
 a_B'\cos(\rho-\theta_D)-b_B'\sin(\rho-\theta_D)+b_D
       &\ge1+W(\rho-\theta_D),\\
 b_A'+b_B'&\ge1,
\end{split}                                                  \tag{5}
\]
where \(W(z)=(1+\cos z+\sin z)/2\) for \(0\le z\le.7\).
The new coordinates satisfy (2), in fact
\[
                a_A',a_B'>1.1,\qquad 0\le b_A',b_B'<.665.     \tag{6}
\]
H, D and E, their own-frame coordinates, their frames and their two
original mixed inequalities are unchanged.

Equations (5) are the complete five-anchor necessary inequalities
obtained by aligning HG, AB and TD and eliminating G and T. They are
the endpoint system used by the aligned-zero E-boundary and
hard-quarter split comparisons. No replacement G or T state is used
in a later assertion about the original centers.

If any original zero difference
\[
 \theta_G-\theta_H,\qquad\theta_B-\theta_A,\qquad
 \theta_D-\theta_T                                           \tag{7}
\]
is nonzero, at least one new A or B corner value can be made strictly
less than q. This retains a strict anchor loss for a later equality
argument.

The signs, ordering and owners (3)--(4) are hypotheses. This theorem
does not assert that every candidate has them. It concerns the
necessary edge system (5); it does not preserve an original bad-S
condition or assert omitted nonneighbor or physical-gap conditions.

## 2. Elementary circle bounds

Write
\[
 f_q(b)=\sqrt{q-(b+\tfrac12)^2}-\tfrac12,\qquad
 C_q=\sqrt{q/2}-\tfrac12.
\]
Positive squaring and the original sorted circles give
\[
 C_q<.9,\quad a_i<U:=283/200,\quad a_i+b_i<1.8.                \tag{8}
\]
The primary bound remains valid without sorting when \(b\ge0\).
Every nonnegative own-frame center also satisfies
\[
                         \sqrt{a_i^2+b_i^2}<U.               \tag{9}
\]
Indeed \(a_i+b_i\ge r:=\sqrt{a_i^2+b_i^2}\), so the circle gives
\(r^2+r+1/2\le Q\), whereas
\[
                    U^2+U+\tfrac12-Q=13/8000>0.
\]

## 3. Every negative outer error aligns at fixed endpoints

Consider HG2/GA0. Normalize \(\theta_A=0\) and put
\[
 \Theta=\theta_H\ge0,\quad t=\theta_G,\quad e=\Theta-t>0.
\]
The value t may be negative. All relevant differences have absolute
value at most .7. Adding the two original inequalities cancels the
same actual \(b_G\). Retaining both width cusps gives
\[
\begin{split}
 F(t):={}&(a_A-\tfrac12)\cos t-J(t)\sin t\\
 &+(b_H-\tfrac12)\cos(\Theta-t)
       -(a_H+\tfrac12)\sin(\Theta-t)\ge1,                     \tag{10}
\end{split}
\]
where \(J(t)=b_A-1/2\) for \(t<0\), and \(J(t)=b_A+1/2\) for
\(t\ge0\). The expressions agree at zero.

Put \(A_x=a_A-1/2,\ H_y=b_H-1/2,\ H_x=a_H+1/2\).
Sorting gives \(H_x\ge H_y+1\). On either differentiable branch,
whenever \(F(t)\ge1\),
\[
\begin{split}
 F'(t)(\cos e-\sin e)\ge{}&
 1+\cos e+\sin e\\
 &-(A_x+J(t))\cos\Theta-(A_x-J(t))\sin\Theta.                 \tag{11}
\end{split}
\]
For completeness, (10) first implies
\[
 H_y(\cos e-\sin e)
 \ge1-A_x\cos t+J(t)\sin t+\sin e.
\]
Insert it in
\[
 F'(t)\ge-A_x\sin t-J(t)\cos t
                    +H_y(\sin e+\cos e)+\cos e;
\]
the angle-addition formulas give (11).

For \(t\ge0\), (8) bounds the last two coefficients by 1.8 and
.415. Cauchy--Schwarz and \(1.8^2+.415^2<1.85^2\) show that the
right side exceeds \(3/20\). For \(t<0\), the coefficients are
bounded by .8 and 1.415, and
\(.8^2+1.415^2<1.65^2\) gives reserve \(7/20\). These are upper
bounds because the sine and cosine of \(\Theta\) are nonnegative.
Also \(0<\cos e-\sin e\le1\).

Thus \(F'(t)>3/20\) wherever \(F(t)\ge1\). A forward first-crossing
argument, through the continuous cusp at zero if needed, keeps
\(F\ge1\) as t increases to \(\Theta\). Integration gives the
aligned necessary inequality
\[
 b_H+a_A\cos\Theta-b_A\sin\Theta
             >1+W(\Theta)+\frac3{20}e.                       \tag{12}
\]
H and A and their frames did not change. This is a necessary scalar
improvement, not a claim about physically moving an original G.

The reflected argument applies to BT2/TD0: replace \((H,A,G)\) by
\((D,B,T)\) and reverse frame signs. Thus every negative TD error
has the same improvement. From now on replace each negative outer
error by its aligned necessary inequality. The remaining outer errors
are nonnegative, with the G comparison frame above H and the T
comparison frame below D.

## 4. The remaining positive outer errors give effective caps

For a remaining HG error \(h=\theta_G-\theta_H\ge0\), set
\[
 B_H^{\rm eff}=\tfrac12+(b_H-\tfrac12)\cos h
                        +(a_H-\tfrac12)\sin h,\qquad
 D_H=\tfrac32-B_H^{\rm eff}.                                 \tag{13}
\]
At a previously aligned edge set \(h=0\), so \(B_H^{\rm eff}=b_H\).
Define \(D_D\) by the same formula using D and its remaining
nonnegative TD error. Write
\[
 t=\theta_G-\theta_A\ge0,\quad
 u=\theta_B-\theta_T\ge0,\quad d=\theta_B-\theta_A.
\]
The two original canceling pairs, or (12) for a pair already aligned,
give
\[
\begin{split}
 (a_A+\tfrac12)\cos t-(b_A+\tfrac12)\sin t&\ge D_H+\cos t,\\
 (a_B+\tfrac12)\cos u-(b_B+\tfrac12)\sin u&\ge D_D+\cos u.
\end{split}                                                  \tag{14}
\]
Sorting, \(0\le h\le.7<\pi/4\), and Cauchy--Schwarz give
\[
\begin{split}
 &(a_H-\tfrac12)\sin h+(b_H-\tfrac12)\cos h\\
 &\quad\le(\sqrt{q/2}-1)(\sin h+\cos h)
       <\tfrac25\sqrt2<283/500.
\end{split}
\]
Hence \(B_H^{\rm eff}<1.066\), and likewise at D. Conversely (14),
nonnegative tangents, and (8) imply \(D_H,D_D<U-1/2=.915\).
Therefore
\[
                       .434<D_H,D_D<.915.                   \tag{15}
\]

For either parameter D define the actual-q cap, for \(0\le z\le.7\),
\[
 c=\cos z,\quad s=\sin z,\quad C=D+c,\quad w=\sqrt{q-C^2},
 \quad X=Cc+ws,\quad L=wc-Cs.                                \tag{16}
\]
Its radicand is positive, and
\[
 w^2-s^2=q-D^2-1-2D\cos z
                   >q_L-(.915+1)^2>0.                      \tag{17}
\]
Direct calculation gives
\[
 X^2+L^2=q,\qquad (X-1)c-Ls=D,\qquad
 L'=-X(w-s)/w<0.                                            \tag{18}
\]
Rotating each original corner, using its first-coordinate lower
bound in (14), and rotating back yields
\[
 b_A+\tfrac12\le L_H(t),\qquad b_B+\tfrac12\le L_D(u).          \tag{19}
\]

### 4.1 A derivative reserve on the wider effective-cap range

Whenever \(L\ge1/2\),
\[
                              -L'>9/8.                       \tag{20}
\]
Put \(p=717/500=1.434\). Equations (15),(18) imply
\[
 p<X<383/200,\qquad \tan z\le(X-p)/L.
\]
The expression
\[
 -L'=X\frac{L+(X-1)\tan z}{L+X\tan z}
\]
decreases with \(\tan z\). Substitution and \(L^2=q-X^2\) give
\[
 -L'\ge\frac{X\{q+p-(p+1)X\}}{q-pX}.                         \tag{21}
\]
The denominator is positive. After clearing it, the difference from
\(9/8\) is
\[
 P(q,X)=-(p+1)X^2+(q+p+\tfrac98p)X-\tfrac98q.
\]
It increases with q since \(X>p>9/8\), and is concave in X. Its
two endpoint values at the smaller allowed radius are
\[
 P(q_L,p)=\frac{143611149}{250000000}>0,\qquad
 P(q_L,383/200)=\frac{26241}{10000000}>0.                     \tag{22}
\]
This proves (20) on the entire range.

### 4.2 A rotated-cap comparison

For fixed \(0\le v\le.7\), put
\[
 g_v(C)=\cos v\sqrt{q-C^2}-\sin v\,C.
\]
In the relevant domain,
\[
                C\ge D+\cos v\quad\Longrightarrow\quad
                g_v'(C)<-1.                                 \tag{23}
\]
With \(c=\cos v,s=\sin v\), its squared form is
\(2C^2>q(1-s)\). Since \(c\ge1-s^2,\ s<13/20\), (1),(15) give
\[
\begin{split}
 2(D+c)^2-q(1-s)
 &\ge2(D+1)^2-q+s\{q-(4D+2)s\}\\
 &\ge\frac{24639}{125000}+\frac{591}{2500}s>0.                 \tag{24}
\end{split}
\]
All quantities squared to obtain (23) are positive.

## 5. Both AB signs and owners align before the positive outer errors

By (3) and the remaining nonnegative outer errors, A and B lie
between the G and T comparison frames. Thus \(d\le t,u\), and all
quarter angles used below are in \([0,.7]\). Write the original
corner coordinates \(Z_i=b_i+1/2,\ X_i=a_i+1/2\).

For original AB axis 0 its exact inequality is
\[
 Z_A+X_B\sin d+Z_B\cos d
                  \ge1+\cos d+(\sin d)_+.                   \tag{25}
\]
Axis 2 is the reflected formula with A and B interchanged.

If \(d<0\), put \(v=u-d>u\) and keep A's actual corner and frame.
The same circle rotation as (19) bounds the rotated B term in
(25) by \(g_v(D_D+\cos u)\). Integrating (23), and using
\(\cos u-\cos v\ge1-\cos(v-u)\), gives the pointwise strict bound
\[
                           Z_A+L_D(v)>2.                     \tag{26}
\]
More explicitly, B's first rotated coordinate is
\(C_B=X_B\cos u-Z_B\sin u\ge D_D+\cos u\). The term in (25)
is at most \(g_v(C_B)\), hence at most
\(g_v(D_D+\cos u)\). The integration from \(D_D+\cos v\)
to \(D_D+\cos u\) proves (26).

Put B's new frame at A's frame and set \(b_B'=1-b_A\).
The unchanged actual bound \(0\le b_A<.9\) gives
\(0.1<b_B'\le1\). Equation (26) puts
\(Z_B'=2-Z_A\) strictly below the new B cap. Thus choose
\(a_B'<f_q(b_B')\) sufficiently close to the circle frontier
to preserve (14). The new B corner value is strictly below q.
The A hard inequality remains valid, and the new AB sum is one.

If \(d>0\), keep B's actual corner and frame, and put \(v=t-d\).
The A cap stays at least \(1/2\) on \([v,t]\), so (20) gives
\(L_H(v)>Z_A+(9/8)d\). The actual B coordinates satisfy
\[
\begin{split}
 &(X_B-1)\sin d+(Z_B-1)(\cos d-1)\\
 &\qquad<.915d+\tfrac14d^2\le1.09d,
\end{split}
\]
because \(X_B-1=a_B-1/2<.915\), \(Z_B\ge1/2\), and \(d\le.7\).
Together with (25), this proves
\[
                        L_H(v)+Z_B>2+\frac7{200}d.            \tag{27}
\]
Put A's frame at B's frame, set \(b_A'=1-b_B\), and choose
\(a_A'<f_q(b_A')\) close enough to the circle frontier. The new
A hard inequality holds, its corner value is strictly below q,
and the new AB sum is one.

For AB axis 2 apply the reflected arguments. If \(d=0\), leave
both actual A and B points unchanged. In every case the common-frame
pair satisfies
\[
                              b_A+b_B\ge1.                    \tag{28}
\]
The one newly constructed point need not yet be sorted. It has
nonnegative coordinates, its actual-q circle, and the paired hard
inequality. Its primary is positive: the latter and (9) give
\[
                              a_A,a_B>2-U>.5.                 \tag{29}
\]
Sorting will follow after the next two comparisons. If \(d\ne0\),
one strict A/B corner loss has already been retained.

## 6. A positive outer error aligns when its middle tangent is at least 1/5

Return to HG2/GA0, allowing A to be an intermediate point of
Section 5. It needs only nonnegative coordinates, its circle,
and \(a_A>.5\). Assume \(b_A\ge1/5\).
Put
\[
 \Theta=\theta_H-\theta_A\ge0,\qquad e=\theta_G-\theta_H>0.
\]
Both \(\Theta\) and \(\Theta+e\) lie in \([0,.7]\). Define
\[
\begin{gathered}
 V=(a_A-\tfrac12)\cos\Theta-(b_A+\tfrac12)\sin\Theta,\\
 U_A=(a_A-\tfrac12)\sin\Theta+(b_A+\tfrac12)\cos\Theta,\\
 F_0=b_H-\tfrac12+V,\qquad K=a_H-\tfrac12-U_A.
\end{gathered}
\]
The exact paired inequality is
\[
                         F_0\cos e+K\sin e\ge1.              \tag{30}
\]
We claim
\[
                              F_0>1+e/20.                    \tag{31}
\]

Suppose \(F_0\le1+e/20\), and put \(r_0=3/2-V+e/20\).
Then \(b_H\le r_0\). On the sorted H circle,
\[
 \frac{d}{db}\{f_q(b)\sin e+b\cos e\}
 =\cos e-\frac{b+1/2}{f_q(b)+1/2}\sin e
 \ge\cos e-\sin e>0.
\]
Hence the largest left side of (30) under the supposed F0 bound
occurs at \(b_H=\min(r_0,C_q)\), \(a_H=f_q(b_H)\).

If \(r_0\ge C_q\), that point is diagonal. Its F0 is at most
\(1+e/20\), whereas
\[
 K=C_q-\tfrac12-U_A
          <.4-\frac7{10}\frac34=-\frac18.
\]
Here \(a_A>.5,\ b_A+.5\ge.7,\ \cos\Theta>3/4\).

If \(r_0<C_q\), then \(V>.6\). During rotation from zero to
\(\Theta\), V remains positive, so
\(U_A\ge b_A+1/2\) and \(V\le a_A-1/2\). Thus
\[
                       K\le f_q(2-a_A)-\tfrac12-U_A<-1/16.   \tag{32}
\]
To check the strict comparison, put \(X=a_A+1/2,\ Y=b_A+1/2\).
Then \(Y\ge.7,\ X^2+Y^2\le q\), and \(X<1.851\) since
\(1.851^2+.7^2>Q\). Consequently
\[
\begin{split}
 q-(3-X)^2-(Y+\tfrac{15}{16})^2
 &<Q-(\tfrac{1149}{1000})^2-(\tfrac{131}{80})^2\\
 &=-\frac{344029}{4000000}<-\frac{2733}{32000}<0.              \tag{33}
\end{split}
\]
Positive squaring gives
\(f_q(2-a_A)+1/2<Y+15/16\), proving (32). This radical is
real because \(2-a_A\le r_0<C_q\).

Both cases bound the left side of (30) by
\[
 (1+\tfrac e{20})\cos e-\tfrac1{16}\sin e
 <1+\tfrac e{20}-\tfrac9{160}e
 =1-\tfrac e{160}<1,
\]
using \(\sin e>(9/10)e\) on \((0,.7]\). This contradicts
(30) and proves (31). In original coordinates,
\[
 b_H+a_A\cos\Theta-b_A\sin\Theta
                    >1+W(\Theta)+e/20.                     \tag{34}
\]
The endpoint corners are unchanged and have strict pair slack.
Reflection gives the same result for BT2/TD0 when \(b_B\ge1/5\).

## 7. The coupled order closes all three zero errors in this branch

First apply Section 3 to each negative outer zero error. Then align
AB by Section 5, using the effective caps (15). This retains H, D
and E and gives a common A/B frame between H and D, with (28).
The remaining outer errors are nonnegative.

At least one of \(b_A,b_B\) is at least \(1/2\). Its positive outer
error, if one remains, satisfies the hypothesis of Section 6.
Align that side; if already aligned, leave it alone. Its resulting
hard inequality gives
\[
                         a_i\ge2-b_{\rm outer}>1.1.
\]
The circle then gives \(b_i<.665\), because
\(1.6^2+1.165^2>Q\). Equation (28) now forces the other middle
tangent above .335, hence above \(1/5\). Section 6 aligns the
other positive outer error. This proves (5). The same primary
and circle argument on both sides proves (6), so sorting has
been restored automatically.

If the original AB error was nonzero, Section 5 already supplied a
strict A or B corner loss, and the outer comparisons did not change
those coordinates. If AB was originally aligned, A and B were never
reconstructed. Any nonzero outer error then leaves strict slack in its
final inequality in (5), by (12) or (34). Decrease that middle primary
slightly. The aligned AB condition depends only on its tangent, the
other hard pair is unchanged, and its own strict pair slack preserves
its hard inequality. Its corner value becomes strictly less than q.
The strict sorting and positivity in (6) persist under a sufficiently
small decrease.

Thus any nontrivial zero-error reduction in this owner class can retain
a strict loss in a terminal anchor. The original H/D/E mixed system
and its total frame span stayed fixed. No bad-S boundary was discarded:
this is a descendant necessary system, not an original-S contraction.

The outstanding extensions are HG0/TD2, other original quarter/mixed
owners, and other frame/sign orders. This note supplies none of those
hypotheses.

