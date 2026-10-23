# The opposite hard envelope permits either intermediate sign

## 1. Scope and the unchanged signed budget

Put
\[
 Q=\frac{9789}{2500},\quad p=\frac{50}{49},\quad h=\frac7{10},
 \quad S_0=2\sqrt{Q-1}-3.
\tag{1}
\]
Retain the hard GA0/BT2 necessary cycle, sorted contained
corners, the true core, H,A positive and B,D negative, and either
sign of E. Keep either transverse owner on each zero edge and
DE2/DE3, EH0/EH1. Let the G/T signed variables be
\[
                         g=-y_G,\qquad t=y_T.
\]
At a wrong sign the corresponding zero owner must be HG0 or
TD2. Weak normal signs permit either zero owner. This weak
condition is sufficient for Sections 2--5 of
[the signed order proof](HAND_G5_SIGNED_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md):
its extra owner implication is used only when the intermediate
sign is genuinely wrong. Thus the proof also applies to the
comparison intermediates below, including a normal zero tangent.

Assume AB has been aligned with
\[
 \theta_A=\theta_B=\rho,\qquad b_A+b_B=1,\qquad
                       \theta_T\le\rho\le\theta_G.
\tag{2}
\]
All frames have spread at most h. The two unchanged outer
charges and the H/D/E endpoint estimate give
\[
 b_H+g\ge1-p(\theta_G-\theta_H),\qquad
 t+b_D\ge1-p(\theta_D-\theta_T),
\]
\[
 b_H+b_D-p(\theta_H-\theta_D)+S_0<2.
\tag{3}
\]
The endpoint estimate for either E sign is the exact H/D/E
reflection in Section 2 of
[the crossed canceling theorem](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md).
In particular,
\[
                  g+t+p(\theta_G-\theta_T)>S_0.
\tag{4}
\]
Only the strict version (4) is needed in this note.

We prove two extensions:

1. If \(b_A\ge1/2\), then \(g>0\). The reflected statement
   holds when \(b_B\ge1/2\).
2. The large-tangent crossed HG0 and HG2 reductions remain
   valid when the unchanged opposite T has either sign,
   provided \(t>-1/10\). Their output has \(G=\rho\), HG0,
   \(0<\rho-H<.04\), and \(b_B>.28\). The HG0 construction
   retains its strict A-circle loss; HG2 changes only G.

The second statement stops at GA alignment. It does not
invoke the common-frame clamp with a wrong opposite sign.

## 2. The free opposite-angle envelope

Write \(b=b_A\), \(Y_B=3/2-b\), and
\[
 r=\sqrt{Q-Y_B^2},\qquad P_B=r-1,\qquad
 M(b)=\max_{0\le v\le h}
        \{P_B\cos v-Y_B\sin v+pv\}.
\tag{5}
\]
For \(1/2\le b\le c_0:=\sqrt{Q/2}-1/2<.9\),
\[
 \ell:=\frac{683}{400}<r<r_+:=\frac{943}{500},\qquad
                              .6<Y_B\le1.
\tag{6}
\]
The lower bound follows from \(Q-1-\ell^2=7/160000>0\);
the upper follows from \(Q-.6^2<r_+^2\).

Set \(U(v)=P_B\sin v+Y_B\cos v\) and
\(V(v)=P_B\cos v-Y_B\sin v\).
The unique maximizer in (5) is interior and satisfies
\[
                 U(v)=p,\qquad V(v)=\sqrt{Q+1-p^2-2r}>0.
\tag{7}
\]
Indeed \(U(0)\le1<p\). On the enlarged r interval (6),
\(Y(r)=\sqrt{Q-r^2}<1.001\), and the function \(U(h)\)
decreases with r, because
\[
 \sin h-\frac rY\cos h<.65-1.7(.76)<0.
\]
At \(r=r_+\), positive squaring gives \(Y>.5988\).
The alternating polynomials \(S_7,C_6\) give
\[
             .886S_7(.7)+.5988C_6(.7)>p.
\tag{8}
\]
Thus \(U(h)>p\). The positive function U is concave on
\([0,h]\). Its superlevel set above p is an interval ending
at h, so the derivative \(p-U\) changes sign exactly once.
The crossing is on the increasing part of U, proving (7).

The stationary-envelope identities are
\[
 M'=\frac{Y_B}{r}\cos v+\sin v,\qquad
 M''=-\frac{Q\cos v}{r^3}
                         +\frac{(V+\cos v)^2}{r^2V}.
\tag{9}
\]
All derivatives here and below are with respect to b.
The useful whole-domain bounds are
\[
                         M''<\frac34
                    \quad(1/2\le b\le c_0),
\tag{10}
\]
and
\[
                         M''>\frac14
       \quad\left(1/2\le b\le b_*:=\sqrt{Q-9/4}-1/2\right).
\tag{11}
\]

### An exact degree-six certificate for the upper curvature

For a variable r in (6), define the explicit polynomials
\[
 K=Q+1-2r,\qquad
 C=2r^2-4Qr+Q(Q+1),\qquad
 D_0=r^3-3Qr+Q(Q+1),
\]
\[
 D=(K-p^2)D_0+r(Q-r^2)p^2,\qquad
 Y_+=\frac{Q+.822^2-r^2}{2(.822)}.
\tag{12}
\]
Let \(x=r-\ell\), \(d=r_+-\ell=.1785\), and put
\[
 V_- =.6777+\frac{.319-.6777}{d}\,x,\qquad
 B=\frac34r^3K^2+pCY_+,\qquad N=V_-B-D.
\tag{13}
\]
These are exact rational polynomials. The positive square
reserves at the two r endpoints show
\[
 \sqrt{K(\ell)-p^2}>.6777,\qquad
 \sqrt{K(r_+)-p^2}>.319.
\]
Concavity gives \(V>V_->0\). The elementary tangent bound
for a square root gives \(Y\le Y_+\).
The convex quadratic C is negative at both endpoints,
and therefore \(C<0\) throughout.

For completeness, the following short coefficient bounds
specify the entire polynomial certificate. Expand B and N
in x, with coefficients \(B_i,N_i\). Direct multiplication
of (12)--(13) gives
\[
 B_i>0\ (i=2,3,4,5),\qquad B_1<0,\qquad B_0+B_1d>4.3,
\tag{14}
\]
\[
 N_0>.8315,\quad -7.683<N_1<0,\quad N_3>0,\quad
                                      N_4,N_5,N_6<0,
\]
\[
                N_2+N_4d^2+N_5d^3+N_6d^4>27.57.
\tag{15}
\]
Thus B is positive and
\[
 N>.8315-7.683x+27.57x^2
       \ge .8315-\frac{7.683^2}{4(27.57)}>.29.
\tag{16}
\]
The defining formulas (12)--(13), rather than an approximate
fit to a derivative, determine every coefficient in (14)--(15).

To connect this polynomial to (9), use
\[
                 \cos v=\frac{(r-1)V+pY}{K}.
\]
Direct expansion yields the exact identity
\[
 \left(\frac34-M''\right)r^3VK^2
       =V\left\{\frac34r^3K^2+pCY\right\}-D.
\tag{17}
\]
Since \(C<0\), \(Y\le Y_+\), and \(B>0\), its right
side exceeds \(V_-B-D=N>0\). Every multiplier on the
left is positive. This proves (10).

### The lower curvature on the large-side interval

On the interval in (11), \(r<1.848\) and \(V<.678\).
Also \(v<.5\): \(U(.5)\) decreases with r, and at the
enlarged right endpoint \(Y(1.848)>.707\), so
\[
                       .848S_3(.5)+.707C_2(.5)>p.
\]
Consequently \(\cos v>7/8>.678\). In (9), the expression
\((V+c)^2/V\) decreases with V when \(V<c\). Hence
\[
 M''>
 \frac{(.678+7/8)^2}{1.848^2(.678)}-\frac{Q}{\ell^3}
 =\frac{23523196269012775}{92215887788577168}>\frac14.
\tag{18}
\]
This proves (11).

## 3. A wrong sign cannot occur on the larger middle tangent

Assume \(b=b_A\ge1/2\) and, contrary to the first claim,
\(g\le0\). Translate \(\rho\) to zero, and put
\(z=\theta_G\ge0\), \(v=-\theta_T\ge0\).
Enlarge only the two middle circle bounds to Q, and write
\[
 Y=b+1/2,\quad R_A=\sqrt{Q-Y^2},\quad P_A=R_A-1,
 \quad V_A(z)=P_A\cos z-Y\sin z.
\]
The two hard constraints imply
\[
 g\le\min\{0,V_A(z)-1/2\},\qquad
 t\le P_B\cos v-Y_B\sin v-1/2.
\tag{19}
\]

If \(b\le b_*\), let \(z_A\ge0\) be the root \(V_A(z_A)=1/2\).
Then
\[
          \min\{0,V_A(z)-1/2\}+pz\le pz_A.
\tag{20}
\]
Before \(z_A\) this follows from \(z\le z_A\).
After \(z_A\), the derivative is \(p-U_A(z)\), with
\(U_A=P_A\sin z+Y\cos z\). At the root,
\[
 U_A(z_A)^2=Q+3/4-2R_A>1.117^2>p^2.
\]
At h, \(U_A(h)\) increases with Y on the sorted arc,
because its Y derivative is \(\cos h-(Y/R_A)\sin h>0\).
At \(Y=1\) it exceeds \(.7075S_7(h)+C_6(h)>p\).
Concavity of \(U_A\) proves \(U_A>p\) on the whole
interval after the root, establishing (20).

Put
\[
                         J(b)=pz_A+M(b)-1/2.
\tag{21}
\]
The inverse-angle curvature \(z_A''>-1/16\) proved in
Section 5 of
[the large crossed lemma](HAND_G5_CROSSED_NONCANCELING_LARGE_TANGENT_GA_ALIGNMENT.md)
uses only \(1/2\le b\le b_*\), and so remains applicable.
By (11), \(J''>1/4-p/16>0\). Its maximum is at an endpoint.
The already proved balanced estimate gives \(J(1/2)<.409\).
At \(b=b_*\), positive squaring gives
\[
                    .7094<Y_B<.7095,\qquad r>1.8472.
\]
Thus \(V<.4243\). Moreover
\[
                    .8472S_7(.48)+.7094C_6(.48)>p,
\]
so \(v<.48\). Equations (7), (21) give
\[
                 J(b_*)<.4243+p(.48)-.5<.4142<S_0.
\tag{22}
\]
Therefore \(J<S_0\) throughout this interval.

If instead \(b\ge b_*\), then \(P_A\le1/2\). The same
concavity argument, now with \(U_A(0)=Y>1.29>p\),
shows that the left side of (20) is at most \(P_A-1/2\).
The full upper budget is consequently
\[
                         F(b)=R_A+M(b)-2.
\tag{23}
\]
By (10),
\[
                   F''<-\frac{Q}{(3/2)^3}+\frac34<0.
\]
At \(b=b_*\), the preceding angle bounds give
\[
 M'<\frac{.71}{1.847}+.462<.86<\frac{Y}{R_A}.
\]
Hence \(F'(b_*)<0\); F decreases thereafter, starting at
\(F(b_*)=J(b_*)<S_0\).

Equations (19)--(23) therefore give
\(g+t+p(z+v)<S_0\) for every \(b\ge1/2\).
This contradicts (4). Thus \(g>0\), with the identical
reflected conclusion for the larger B tangent.

## 4. The large crossed HG0 proof with a signed opposite T

Assume now \(g\ge0\), \(b_A\ge1/2\), and \(\theta_H<\rho\).
Use the notation and same-circle function \(B(r,z,b)\) in
Sections 2--3 of the large crossed lemma, with
\(r=\rho-\theta_H>0\). The actual signed T hard contact and
the unclipped TD charge still give
\[
                B(r,z,b)+\frac12+pr-M(b)<1-S_0.
\tag{24}
\]
The only change is that M is now the full envelope (5).
The same-circle G calculation, concavity in z, and all actual-q
constructions in that note have no T-sign input.

At the G-zero endpoint \(z=z_A\), its necessary bound is
\[
                         1-J(b)+f(r+z_A),
\quad
 f(s)=ps-\{\sqrt{Q-1/4}-1\}\sin s-\tfrac12(1-\cos s).
\]
The existing proof gives \(f\ge0\) on the whole enlarged
endpoint interval \([0,.9]\). The new \(J<S_0\) from
Section 3 therefore excludes this endpoint.

At \(z=0\), the crossing capture uses the function
\(\phi(b)\) in (43) of that same note. Its first three
terms have second derivative greater than \(39/50\).
Equation (10) now gives
\[
                         \phi''>39/50-3/4>0
\]
on the whole b interval. At the original rational pivot
\(b=27/40\), the free maximizer is exactly the one already
used there. Its proved estimates
\(\phi>47/80\), \(|\phi'|<1/1000\) are unchanged.
The same one-pivot convexity argument therefore proves
\[
                             0<r<.04.
\tag{25}
\]

The actual-q derivative calculation in Section 8 of the
large crossed lemma now applies verbatim: it retains H,
B,T,D,E and A's frame and tangent, moves G to \(\rho\),
and preserves HG0 and GA0. A positive original
\(\theta_G-\rho\) supplies a strict A-circle loss; any
inherited A loss is recreated after the temporary lift.
No T coordinate or frame has been changed.

## 5. The large crossed HG2 reduction with a small wrong opposite sign

For HG2, Sections 3--4 of
[the crossed canceling theorem](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md)
do not use T's sign. They lower G to \(\rho\), keeping
the five anchors and T unchanged. Its proof that the
descendant has \(G>T\) uses the signed order proof with
the weak owner condition stated in Section 1.

The only sign-dependent step is the short opposite-angle
bound in its Section 5. Replace its \(b_T\) there by the
actual signed t and assume only \(t>-.1\). Under the
same contrary assumption \(b_H\le b_G\), that proof's
three captures and two square comparisons still give
\[
               t+\frac12<.73\cos u-.962\sin u,\qquad u\ge0.
\]
At \(u=.32\),
\[
                         .73C_4(.32)-.962S_3(.32)<.4.
\]
The right side decreases, so \(t>-.1\) forces \(u<.32\).
For the same function
\[
               F(u)=.73\cos u-.962\sin u-\frac12+pu,
\]
one now has on this entire interval
\[
 F''\le-.73(1-.32^2/2)+.962(.32)=-.384784<-\frac{19}{50}.
\]
Since \(F(0)=.23\) and \(F'(0)=1431/24500\),
\[
 t+pu<F(u)\le .23+\frac{25}{19}
                          \left(\frac{1431}{24500}\right)^2<.235.
\tag{26}
\]
This is the identical final bound used in (25)--(28) of
the canceling proof. The signed TD charge therefore gives
the same contradiction, proving \(b_H>b_G\).
Its final lift of G and strict comparison of HG0 with HG2
are unchanged. The output has G at \(\rho\) and actual HG0,
with H,A,B,T,D,E exactly fixed.

Apply Section 4 at this already GA-aligned endpoint to
obtain (25). No A lift is required when the original
GA error is already zero.

## 6. The opposite tangent exceeds .28 after either crossed reduction

In both outputs, G is normal and GA aligned. The actual
all-sign zero charge and (25) give
\[
 b_H+b_G\ge1-pr>1-\frac2{49}.
\]
Since \(b_H<.9\) and \(a_A\ge1+b_G\),
\[
                        a_A>1.1-\frac2{49}.
\tag{27}
\]
The exact positive square comparison
\[
                  \left(1.6-\frac2{49}\right)^2+1.22^2>Q
\]
forces \(b_A<.72\). Thus \(b_B=1-b_A>.28\).
This deduction uses the actual unchanged tangent sum,
not an assumed clamp or a normal sign of T.

Every construction stays within the original frame interval
and retains the actual containing q. The full-Q calculations
above are only necessary upper bounds used to capture the
crossing and exclude a wrong large side. No sampled minimum,
angle mesh, Bernstein inventory, Lean run, or CI result is
a mathematical premise.
