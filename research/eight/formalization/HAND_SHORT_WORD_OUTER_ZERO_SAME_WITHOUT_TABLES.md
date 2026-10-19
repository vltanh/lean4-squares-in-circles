# All four favorable same-sign outer zero owners without angle tables

This note replaces the full interval table in
../SHORT_WRONG_WORD_OUTER_ZERO_SAME_HAND_PROOF.md. It proves every original
owner \((0,++,1),(1,--,3),(3,++,1),(3,--,3)\), on its entire feasible
angle domain, with corrected cost greater than .898. All state endpoints,
weak separators, and ties are included. Reflection/reversal in the parent
preserves the original angle and corrected cost exactly.

Every decimal is an exact rational. The argument uses the actual coupled
contact minimum. It excludes all interior minima by a scalar identity at
an angular stationary point; it does not enclose the contact surface by
boxes or assume completeness of a numerical stationary-point list.

## 1. Normalization and the complete contact domain

Set
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad
 r(y)=\frac{y+1/2}{a(y)+1/2}.
\]
Then \(a'=-r\), \(r'=Q/(a+1/2)^3\),
\(r''=3Q(y+1/2)/(a+1/2)^5\).
The four exact normalized tuples \((c,p,q,P,t)\) are
\[
\begin{aligned}
0&:(-.0613,0,.94766,0,.9994),\\
1&:(.27086,-.09133,.88074,.13422,1.03828),\\
2&:(-.75097,.51554,1.19909,0,.71553),\\
3&:(.74349,-.19335,.76744,.33147,1.1336).
\end{aligned}                                               \tag{1}
\]
Their costs and stipulated original transverse separators are
\[
 C=\phi+c+pa(b)+qb-PA(B)-tB,
 \qquad b+A(B)\sin\phi-B\cos\phi\ge W,
\]
\[
 W=(1+|\sin\phi|+\cos\phi)/2,\quad 0\le b,B\le d.
\tag{2}
\]
Nonpositive \(\phi\) is infeasible. For positive \(\phi\), minimizing
the increasing source label sets
\[
 b=W-A(B)\sin\phi+B\cos\phi.
\tag{3}
\]
The right side is positive throughout the possible domain: it increases
with \(B\), decreases with \(\phi\), and its value at \(B=0,\phi=.7\)
is greater than .293. Feasibility starts at the unique event \(\phi_a\)
where (3) with \(B=0\) equals \(d\):
\[
 1/2+(1/2)\cos\phi_a-(a_0-1/2)\sin\phi_a=d,
 \quad .1072632<\phi_a<.1072633.
\tag{4}
\]
The defining function decreases, and the two point signs follow from
alternating Taylor bounds. For each \(\phi\in[\phi_a,.7]\), (3) increases
strictly in \(B\); its feasible interval is \(0\le B\le B_d(\phi)\),
where the upper endpoint has \(b=d\). It is below the target diagonal:
\(B_d(.7)<.578<d\), and \(B_d\) increases. Thus there is no other
coordinate boundary. Every source satisfies \(b>.293\).

We shall use
\[
\begin{gathered}
1.414575671<a_0<1.414575672,\quad
.899214065109<d<.899214065110,\quad R<1.978788,\\
.26115<\rho:=1/[2(a_0+1/2)]<.262,\quad
\cos\phi>.764,\quad\sin\phi<.645.
\end{gathered}                                               \tag{5}
\]
All radical comparisons follow by positive squaring.

## 2. The one positive-primary-coefficient row

Row 2 admits one support on its entire feasible domain, independent of
the coupled argument below. Use \(\lambda=.90362\) in (2).
The source functional \(pa+(q-\lambda)b\) is concave; its axial endpoint
is smaller than its diagonal endpoint, so its minimum is \(pa_0\).
The target functional has coefficients
\(-\lambda\sin\phi\) and \(\lambda\cos\phi-t\).
Its derivative at the target axis is
\[
 \lambda(\cos\phi+\rho\sin\phi)-t.
\]
This is concave in \(\phi\); its values at .107 and .7 exceed .208 and
.127, respectively. Thus the target support is axial throughout.
The resulting lower bound is
\[
 F(\phi)=\phi+c+pa_0+\lambda/2
       +(\lambda/2)\cos\phi+\lambda(1/2-a_0)\sin\phi.
\]
It increases, since \(F'>1-1.043\lambda>0\).
Its single initial value is \(F(.107)>.898077\).
This proves the entire row 2 without an angle subdivision.

For the rest of the note retain only rows 0,1,3; they have
\(p\le0,P\ge0\).

## 3. Strict target convexity and the axial boundary

On the contact (3), write
\[
 k=\cos\phi,\ s=\sin\phi,\ U=A+1/2,\ V=B+1/2,
 \quad K=k+r(B)s,\quad J=r(B)k-s,
\]
\[
 v=(U-1)k+Vs>0,\quad
 l=q-pr(b)>0,\quad \alpha=-p r'(b)\ge0.
\]
Then \(b_B=K\), \(b_\phi=-v\), and
\[
 C_B=lK+Pr(B)-t,\qquad
 C_{BB}=\alpha K^2+(l s+P)r'(B)>0.
\tag{6}
\]
Thus each angle has a unique contact minimum, except for possible
boundary minimizers.

At \(B=0\), row 0 has
\(C_B=q(k+\rho s)-t<.94766(1.034)-.9994<0\).
Here is one whole-range proof of the same sign for rows 1 and 3.
Let \(h=-p>0\), and put \(b_x=1/2+(1/2)k-(a_0-1/2)s\).
The speed \(-b_x'=(a_0-1/2)k+s/2\) is concave and exceeds .963 at
both angle endpoints. Since \(r'>.557\),
\[
 r(b_x)\le1-.536(\phi-\phi_a)
       <1-.536(\phi-.1073).
\]
Also \(k+\rho s\le1+.262\phi-.479\phi^2\), by the sine/cosine
Taylor inequalities on \([0,.7]\).
Define \(D=.536h\), \(M=q+h+.1073D\). It follows that
\[
 C_B(0,\phi)<
 M+(.262M-D)\phi-(.479M-.0733D)\phi^2+.262P-t.
\tag{7}
\]
The discarded cubic was bounded by \(.7(.479D)\phi^2\).
The quadratic coefficient subtracted in (7) is positive. Its global
maximum, obtained by completing a square, is less than -.0027 in
row 1 and less than -.0623 in row 3. These are direct rational
substitutions of (1). Hence the axial target cannot be a minimum
when its feasible target interval has positive length.

## 4. The source-diagonal boundary

Put \(z_0=d-1/2\), \(z=z_0-s\), \(T=\sqrt{Q-z^2}\). The exact
source-diagonal target coordinates are
\[
 U=kT-sz,\quad V=sT+kz,\quad B_d=V-1/2,\quad f=1-k/T>0.
\tag{8}
\]
They satisfy \(U'=-Vf,V'=Uf\); the physical arc starts at
\(U=a_0+1/2,V=1/2\), and remains inside the target outer arc through .7.
At this boundary put \(L=q-p\). Its target derivative is
\[
 J_d=Lk+(Ls+P)V/U-t,
\quad J_d'=Lz/U+(Ls+P)Qf/U^2>0.
\tag{9}
\]
When \(z\ge0\), the sign is immediate. When \(z<0\), use
\(s>.3992\), \(|z|<.246\), \(U<1.915\), \(f>.532\) to obtain,
after multiplication by \(U^2\), the lower bound
\(L[-.246(1.915)+.3992Q(.532)]>0\).
The exact values \(J_d(.3)\) exceed .008 in all three rows.
Thus a source-diagonal point at angle at least .3 cannot minimize
in the target coordinate, since decreasing \(B\) lowers its cost.

For the entire earlier boundary \(\phi_a\le\phi\le.3\), write
\(\tau=\phi-\phi_a<.193\). We need only two speed estimates:
\[
 .91<B_d',\qquad B_d'(\phi_a)<.942,\qquad B_d''<.2.
\tag{10}
\]
For completeness, on this whole arc \(T>1.957\), \(0<z<.293\),
\(U>1.85\), \(U<1.915\), \(V\ge1/2\), and \(f>.4919\).
Furthermore
\[
 f'=s/T+zk^2/T^3,\quad
 f''=\frac{k}{T^5}\{T^4-(k^2+3zs)T^2-3z^2k^2\}>0.
\]
The last sign follows already from \(T^2>3.829\),
\(k^2+3zs<1.261\), and \(z^2<.086\).
Therefore \(f'\le f'(.3)<.162\). Now
\(B_d'=Uf>1.85(.4919)>.91\) and
\(B_d''=-Vf^2+Uf'<-(.4919)^2/2+1.915(.162)<.2\).
The initial speed in (10) is a fixed evaluation of (8) at the event
(4), using its two rational brackets.
Integration gives
\[
 .91\tau<B_d<.942\tau+.1\tau^2.
\]
The target cost \(-Pa(B)-tB\) has second derivative
\(Pr'(B)>.557P\) when \(P>0\), and is linear when \(P=0\).
Set \(m=t-P\rho>0\). The boundary cost is consequently at least
\[
 C(\phi_a)+ (1-.942m)\tau+
             [(.557P/2)(.91)^2-.1m]\tau^2.
\tag{11}
\]
Using \(m\le t-.26115P\), the coefficient of \(\tau\) after bounding
any negative quadratic term over \(0\le\tau\le.193\) exceeds .039,
.041, and .0082, respectively in rows 0,1,3. Thus (11) is greater
than its initial value. Those three initial values are
\[
 \phi_a+c+(p+q)d-Pa_0>.89808.
\tag{12}
\]
All possible source-diagonal boundary minima are now covered.

## 5. A coupled angular-stationarity identity

It remains to exclude a local minimum interior to both coordinates.
At such a point \(C_\phi=1-lv=0\), so \(v=1/l\).
Let \(b\) now be the source coordinate, and put
\[
 z=b-1/2,\quad T=z^2+l^{-2},\quad U=(Q+1-T)/2,
 \quad r_t=\sqrt{Q-U^2}/U.
\tag{13}
\]
These are not an independent relaxation: the contact rotation identity
\(v^2+z^2=(A-1/2)^2+(B+1/2)^2=Q+1-2U\) forces exactly (13).
Define
\[
 f_1(U)=\frac{Q-U}{U(Q+1-2U)},\qquad
 G(b)=z-\alpha/l^3.
\]
Solving the two rotated projection equations gives
\[
 C_{\phi\phi}=-lG(b),\qquad
 C_B=f_1(U)+r_t\{P+zl/T\}-t.
\tag{14}
\]
For example \(K/v=f_1(U)+r_tzl/T\), which proves the second identity.
If \(G>0\), the angular second derivative is negative, excluding a
minimum. We show \(C_B<0\) in every remaining case \(G\le0\).

The function \(f_1\) increases on \([1.747,1.902]\): its derivative
has positive numerator \(4QU-2U^2-Q(Q+1)\), as follows by its value
at 1.747 and its positive derivative on this interval.

### 5.1. Row 0

Here \(\alpha=0\), so \(G\le0\) means \(b\le1/2\).
Equation (13) gives \(U\le(Q+1-q^{-2})/2<1.90105\).
As \(P=0,z\le0\), (14) is at most
\(f_1(1.90105)-.9994<-.047\). No stationary minimum is possible.

### 5.2. A concave height function for rows 1 and 3

Write \(h=-p>0\), source \(u=a(b)+1/2\), source \(w=b+1/2\),
so \(l=q+hw/u\), \(\alpha=hQ/u^3\).
Direct differentiation gives
\[
 G'=1-\frac{3hQ(qw-hu)}{u^5l^4}>0.
\tag{15}
\]
Indeed \(u>1.399,w<1.4\); in row 1, \(l>.92\), and in row 3,
\(l>.85\), because \(b>.293\). Dropping the negative term \(-hu\)
bounds the subtracted fraction above by .345 and .873, respectively.
Thus \(G\) increases and the target height in (13) is strictly concave:
\(U'=-G\), \(U''=-G'<0\).

In row 1, the fixed comparison \(G(.6)>.0038\) forces \(b<.6\)
when \(G\le0\). Concavity and its two endpoint values give
\(U>1.846\) on \([.293,.6]\). Its tangent at .6, where
\(U<1.8892\) and \(|U'|<.004\), gives \(U<1.891\).
Hence \(r_t<.387\), \(l<.943\), \(T>Q+1-2(1.891)\), and
\[
 C_B<
 f_1(1.891)+.387\left\{.13422+
             \frac{.1(.943)}{Q+1-2(1.891)}\right\}
                  -1.03828<-.0096.
\tag{16}
\]
If \(z<0\), replacing it by .1 only increases the displayed upper
bound, so (16) includes the entire remaining source range.

### 5.3. Row 3

Now \(G(.78)>.0073\), so \(G\le0\) forces \(b<.78\).
The concave height function has
\[
 U(.293)>1.74760,\quad U(.78)>1.84228,\quad
 U(.77)<1.842327,\quad |U'(.77)|<.000008.
\]
The last tangent proves \(U<1.84234\) on the whole interval.
Let \(T_0=Q+1-2(1.84234)=1.23092\).
For \(b\le1/2\), (14) is at most
\(f_1(1.84234)+.533(.33147)-1.1336<-.042\).

For \(b\ge1/2\), use a chord of the concave height:
\[
 U\ge U_c(b):=1.74760+\frac{.09468}{.487}(b-.293).
\]
The target ratio \(r_t(U)\) is concave on this height range, since
\[
 r_t''(U)=\frac{Q(2Q-3U^2)}
                  {U^3(Q-U^2)^{3/2}}<0.
\]
Its tangent at \(U=1.84\), bounded outward by positive squaring,
therefore gives
\[
 r_t<3.31876-1.58863U
           \le3.31876-1.58863U_c(b).
\]
Also \(l\le l(.78)<.932\). Thus (14) is bounded above by the single
rational quadratic
\[
 D(b)=f_1(1.84234)+
 [3.31876-1.58863U_c(b)]
 \left[.33147+\frac{.932(b-.5)}{T_0}\right]-1.1336.
\tag{17}
\]
Its leading coefficient is negative, \(D'(.78)>.128\), and
\(D(.78)<-.00629\), by direct rational expansion. Hence it increases
throughout \([.5,.78]\) but remains negative. This proves \(C_B<0\)
throughout the whole possible nonnegative-angular-curvature regime.
Equations (14)--(17) exclude every interior minimum in all three rows.

## 6. The last angle boundary and compact-minimum conclusion

At \(\phi=.7\), (6) gives the uniform target curvature
\[
 C_{BB}>.33
\]
for each of the three tuples, over its entire actual contact interval.
For row 0 use \(.94766(.644)(.557)>.33\); the positive \(P\) term
makes the other two bounds stronger.
The three rational reference targets, in row order 0,1,3, are
\[
 .3116925,\quad .28470147,\quad .35856925.
\]
At each reference, substitution into (3) gives
\(C>.89809\), \(|C_B|<10^{-6}\).
One square completion consequently proves
\[
 C>.89809-10^{-12}/.66>.89808
\]
on each whole final-angle target interval.

The contact domain is compact. Its lower angle is the single state
(4), covered by (12). The final angle is covered above. The axial
target is excluded as a minimum by (7), except at the already covered
initial state. The source-diagonal boundary is covered by (9)--(12).
All interior minima are excluded by (14)--(17). These are every
boundary and stationary alternative of the actual contact domain.
Thus all three coupled families have cost greater than .89808.
Together with Section 2, this proves all four original families
strictly above .898 on their full domains.

## 7. Arithmetic and dependency scope

The fixed scalar comparisons use only (1), the explicit contact formulas,
positive radical brackets, and alternating sine/cosine series at the
named points. Machin's identity gives
\(1.57079632679489<\pi/2<1.57079632679490\) when needed.
The outward tangent coefficients in (17) are bounds at the single
fixed height 1.84; concavity, not a table of target heights, extends
that tangent over its entire domain.

The variable-domain arguments are source/target monotonicity, strict
contact convexity, the increasing diagonal derivative, and the coupled
stationarity identity (14). The latter keeps both states tied by their
actual circle and contact relations. No collection of sampled minima,
angle-support rows, or continuous coefficient lookup is an input.
