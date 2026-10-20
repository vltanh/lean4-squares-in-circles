# Small wrong signs: transport on the ordered side and exclusion on the crossed side

## 1. Scope and purpose

Put
\[
 q_L=\frac{19577}{5000},\quad Q=\frac{9789}{2500},\quad
 p=\frac{50}{49},\quad h_0=\frac7{10},\quad
                         S_0=2\sqrt{Q-1}-3.
\tag{1}
\]
The H--G--A hard contacts, with a genuinely wrong G sign,
are
\[
 b_H+a_G\sin h-y_G\cos h\ge W(h),\qquad
 y_G+a_A\cos z-b_A\sin z\ge W(z),
\tag{2}
\]
where \(h=\theta_G-\theta_H\), \(z=\theta_G-\theta_A\),
\(W(u)=(1+\cos u+|\sin u|)/2\), and
\[
                           0<y_G<.1.
\tag{3}
\]
The zero owner here is HG0, as forced for a wrong original
sign. H and A have their normal positive signs and sorted
contained corners. Assume \(b_H<.9\), the true core, and
\[
                            .28\le b_A\le.5.
\tag{4}
\]

We prove two local statements.

* If \(0<h\le z\le h_0\), keeping H and A's tangent and
  frame fixed, a same-q construction reaches \(y_G'=0\)
  with positive HG error and a strict A-circle loss.
* In an AB-aligned hard necessary cycle with
  \(b_A+b_B=1\), \(T\le\rho=A=B\le G\), the crossed
  alternative \(H<\rho\) is impossible under (3)--(4).
  The opposite intermediate sign is unrestricted, provided
  its unclipped outer zero charge is available.

Their reflected statements apply to a wrong T sign. The
endpoint estimates below permit either E sign.

## 2. Ordered-side transport down to the tangent threshold .28

Work at \(q_L\le q\le Q\). Lift only A's primary to its
actual q-circle and put
\[
 Y=b_A+\frac12,\quad P=\sqrt{q-Y^2}-1,\qquad
 V(z)=P\cos z-Y\sin z,\quad U(z)=P\sin z+Y\cos z.
\tag{5}
\]
The actual hard contact and (3) give \(V(z)>.4\).
Moreover \(P< p_0:=.819\), since
\[
                            1.819^2+.78^2>Q.
\tag{6}
\]
The lifted A has primary greater than .9, so its sorting
and true-core conditions are strict.

Choose
\[
 y_G'=\max\{0,1/2-V(z)\},\qquad
 a_G'=\sqrt{q-(y_G'+1/2)^2}-1/2.
\tag{7}
\]
This decreases G's transverse coordinate and increases
its primary, hence improves HG0 because h is positive.
It preserves sorting and the true core. If \(V\ge1/2\),
G already has transverse coordinate zero and HG0 has
strict slack, because the original wrong sign was positive.

Suppose \(V<1/2\). Put
\[
 Z=1-V,\qquad w=\sqrt{q-Z^2},\qquad T=w-U.
\]
The optimized H tangent demand is
\[
 H(h)=\frac12+(1-V(\Theta+h))\cos h
                         -(w(\Theta+h)-1)\sin h,\qquad
 \Theta=\theta_H-\theta_A\ge0.
\tag{8}
\]
The identities in Sections 2--3 of
[the ordered wrong-sign transport](HAND_G5_INTERMEDIATE_SIGN_REMOVAL_IN_ORDERED_HARD_CLASS.md)
give
\[
 H'=\cos h-T\left(\cos h+\frac{Z\sin h}{w}\right),\qquad
 T=\frac{2(P+V)}{w+U},\quad
 U^2=q-2P-1-V^2.
\tag{9}
\]
We need these formulas only on the short intrinsic range
\[
                              .4\le V\le.5.
\tag{10}
\]
Here \(T>0\), and \(h\le z\) gives
\[
                \tan h\le\tan z\le\frac{P-V}{Y}.
\tag{11}
\]
At fixed V, T increases with P and decreases with q;
\((P-V)/Y\) has the same monotonicities. The factor Z/w
decreases with q. Thus the expression
\[
                       T\left(1+\frac{Z\tan h}{w}\right)
\]
is bounded above by setting \(P=p_0\), \(q=q_L\).
All roots remain positive there. Indeed
\[
              Y_0^2=q_L-(1+p_0)^2>.7788^2.
\tag{12}
\]
The concave arcs \(w(V)\) and \(U(V)\) at this envelope
have the endpoint lower bounds
\[
\begin{array}{c|cc}
 V&w&U\\ \hline
 .4&>1.885&>1.057\\
 .5&>1.914&>1.0136.
\end{array}
\tag{13}
\]
Their chords give
\[
 w>1.769+.29V,\quad U>1.2306-.434V,\quad w+U>2.9276.
\]
It therefore suffices that
\[
 \frac{2(.819+V)}{2.9276}
 \left\{1+\frac{(1-V)(.819-V)}
                    {.7788(1.769+.29V)}\right\}<1.
\tag{14}
\]
After multiplication by the positive denominator, its
reserve is the exact cubic
\[
 D(V)=.43515630912-1.1226136608V+1.548296V^2-2V^3.
\tag{15}
\]
Writing \(V=.4+x\), its nonconstant coefficients are
\(-.8439768608,-.851704,-2\). Thus D decreases on
\([.4,.5]\), and
\[
                            D(.5)=.01092347872>0.
\tag{16}
\]
This proves \(H'>0\) throughout the required wrong-sign arc.

Decrease h, leaving H and the lifted A fixed. V increases,
the chosen wrong tangent decreases, and the H demand strictly
decreases. The path must reach \(V=1/2\) before h reaches
zero: otherwise (8) at h=0 would force \(b_H\ge1\).
The same argument excludes simultaneous equality h=0,
V=1/2. Thus the endpoint has positive h and strict HG0
slack. Every frame remains between its original endpoints.

As in Section 4 of the cited transport, this slack recreates
a strict A-circle loss after the lift. If \(V>1/2\), decrease
A's primary slightly. If \(V=1/2\), make that decrease while
decreasing h continuously to retain \(V=1/2\), using
\(V_h=-U<0\). Sorting, the true core, positive h and HG0
slack persist. The opposite middle point is unchanged.
This proves the first statement, including its strict loss.

## 3. A stronger small-tangent endpoint envelope

For the crossed exclusion, enlarge only the two middle
circle bounds to Q and write
\[
 b=b_A,\quad Y=b+\frac12,\quad R=\sqrt{Q-Y^2},\quad P=R-1,
\]
\[
 Y_B=\frac32-b,\quad R_B=\sqrt{Q-Y_B^2},\quad P_B=R_B-1.
\tag{17}
\]
Let \(z_A\) be the positive root
\[
                         P\cos z_A-Y\sin z_A=1/2,
\]
and define the full opposite-angle envelope
\[
 M(b)=\max_{0\le v\le h_0}
        \{P_B\cos v-Y_B\sin v+pv\},\qquad
                         J(b)=pz_A+M(b)-1/2.
\tag{18}
\]
We claim
\[
                        J(b)<.4175\qquad(.28\le b\le.5).
\tag{19}
\]

This M equals the envelope used in Sections 3--4 of
[the small crossed normal-sign theorem](HAND_G5_CROSSED_SMALL_TANGENT_NONCANCELING_GA_ALIGNMENT.md),
even though v here is not restricted by a normal T sign.
To see this, \(U_B=P_B\sin v+Y_B\cos v\) is positive
and concave, while \(U_B(h_0)>p\). The last bound follows
because \(U_B(h_0)\) increases with \(Y_B\ge1\), and at
one it exceeds \(.7075S_7(h_0)+C_6(h_0)>p\).
If \(Y_B\ge p\), concavity gives \(U_B\ge p\) everywhere,
so \(M=P_B\). If \(Y_B<p\), the unique free maximizer
\(U_B=p\) is before the hard root \(V_B=1/2\), since
there \(U_B>1.117>p\). After that root, concavity and the
right endpoint again give \(U_B>p\). Thus extending the
angle domain creates no new maximum.

Put \(b_c=47/98\). On \([.28,b_c]\),
\[
                         J=pz_A+R_B-\frac32.
\tag{20}
\]
The inverse-angle formula is
\[
 z_{YY}=-\frac{Y}{R^3}(1+s/U)
       +\frac{c}{R^2U}(1+s/U)+\frac{sY}{R^2U^3},
\quad
 U=\sqrt{Q+3/4-2R},\quad s=\sin z_A,\quad c=\cos z_A.
\tag{21}
\]
On this entire interval,
\[
 .78\le Y<1,\quad1.7<R<1.8186<1.819,\quad
                       U>1.014,\quad z_A<.352.
\]
The R and U bounds follow by positive squaring. The angle
bound follows from
\(.819C_4(.352)-.78S_3(.352)<1/2\).
Consequently
\[
 z_A''<
 -\frac{.78}{1.819^3}
 +\frac{1+.352/1.014}{1.7^2(1.014)}
 +\frac{.352}{1.7^2(1.014)^3}<.46.
\tag{22}
\]
Since \(R_B<1.708\), (20) gives
\[
                     J''<p(.46)-Q/1.708^3<-.3.
\tag{23}
\]

Use the one rational comparison point \(b=.32\).
Positive squaring and alternating Taylor bounds give
\[
\begin{gathered}
 1.800888<R<1.800889,\qquad
 1.588458<R_B<1.588459,\\
 1.031417<U<1.031419,\qquad .32221<z_A<.32222.
\end{gathered}
\tag{24}
\]
For the upper root comparison use \(C_8,S_7\) at .32222;
for the lower use \(C_6,S_5\) at .32221.
Using
\[
             J'=\frac{Y_B}{R_B}-\frac pR(1+\sin z_A/U),
\]
these enclosures give
\[
                         J(.32)<.4173,\qquad |J'(.32)|<.01.
\tag{25}
\]
The global curvature (23) and a completed square imply
\[
 J(b)<.4173+\frac{.01^2}{2(.3)}<.4175
                                      \quad(.28\le b\le b_c).
\tag{26}
\]
On \([b_c,.5]\), the already proved inverse-angle and
free-envelope calculations give \(J''>0\). The two endpoint
values are below .4175 by (26) and \(J(.5)<.409\).
This proves (19) over the full interval.

## 4. The crossed signed budget

Translate the common frame to zero and write
\[
 \theta_H=-r,\quad\theta_G=z,\quad\theta_T=-v,\qquad
               r>0,\quad z,v\ge0,\quad r+z\le h_0.
\tag{27}
\]
The unchanged H/D/E estimate and the unclipped TD charge
give exactly
\[
                         b_H-t+p(r-v)<1-S_0.
\]
The opposite signed hard contact and (18) consequently imply
\[
                         b_H+\frac12+pr-M(b)<1-S_0.
\tag{28}
\]
This uses the actual signed t, not its magnitude.

Write \(k=\sqrt{Q-1/4}-1\) and
\[
 f(s)=ps-k\sin s-\frac12(1-\cos s),\qquad
 H_0(s)=\frac12+\frac12\cos s-k\sin s.
\tag{29}
\]
Section 3 of the small crossed normal-sign theorem proves
\[
                      f(s)>.007\qquad(.195\le s\le1.1).
\tag{30}
\]
Also \(z_A>.195\), by the same decreasing inverse-angle
comparison at \(Y=1\).

If the Q-circle lift of A has \(V(z)\ge1/2\), then
\(z\le z_A\). A wrong G makes the HG0 demand no smaller
than the G-zero demand \(H_0(r+z)\). The function \(H_0\)
decreases up to 1.1, so
\[
 b_H+\frac12+pr-M(b)
 \ge H_0(r+z_A)+\frac12+pr-M(b)
 =1-J(b)+f(r+z_A).
\tag{31}
\]
Here \(.195<r+z_A<.7+.352<1.1\).
Equations (19), (30) make (31) greater than
\(1-.4175+.007>1-S_0\), since \(S_0>.415\).
This contradicts (28).

It remains to consider \(.4<V(z)<.5\). The lower bound .4
comes directly from (3) and the Q-circle hard cap.
The smallest permitted wrong G tangent is \(1/2-V(z)\).
At that tangent the largest primary is
\[
 Z=1-V,\qquad w=\sqrt{Q-Z^2},\qquad a_G=w-\frac12.
\]
The HG0 projection decreases as the wrong tangent increases,
so its actual H demand is at least
\[
 B(r,z)=\frac12+Z(z)\cos(r+z)-(w(z)-1)\sin(r+z).
\tag{32}
\]

## 5. Two intrinsic endpoints in the HG angle

For fixed z, hence fixed \(Z\in[.5,.6]\), put
\[
                F_Z(s)=Z\cos s-(w-1)\sin s+ps.
\]
Its derivative is convex because
\(F_Z'''=Z\sin s+(w-1)\cos s>0\) on \([0,h_0]\).
Moreover \(F_Z'(h_0)<0\) uniformly. Indeed
\(Z\sin h_0+(w-1)\cos h_0\) increases with Z on this
interval, and at \(Z=.5\) it is greater than
\[
                         .5S_7(.7)+.914575C_6(.7)>p.
\tag{33}
\]
Thus \(F_Z'\) can cross zero only from positive to negative
before the right endpoint. On the entire segment
\(z\le s\le h_0\), the minimum of \(F_Z\) is at one of
its endpoints. Since
\[
                    B(r,z)+pr=\frac12+F_Z(r+z)-pz,
\]
it suffices to bound the two cases \(s=z\) and \(s=h_0\).

At \(s=z\), the ordered-side derivative (9)--(16) with
\(\Theta=0\), \(q=Q\), proves
\[
                  B(0,z)\ge B(0,z_A)=H_0(z_A).
\tag{34}
\]
After adding \(1/2-M(b)\), its lower bound is
\(1-J(b)+f(z_A)>1-.4175+.007>1-S_0\).

At \(s=h_0\), put
\[
 K(z)=\frac12+Z(z)\cos h_0-(w(z)-1)\sin h_0+p(h_0-z).
\]
The exact derivatives are
\[
 K'=U\left(\cos h_0+\frac Z w\sin h_0\right)-p,
\]
\[
 K''=V\left(\cos h_0+\frac Z w\sin h_0\right)
                           +\frac{QU^2}{w^3}\sin h_0.
\tag{35}
\]
On the whole intrinsic interval \(.4\le V\le.5\),
\[
 U^2=Q-2P-1-V^2>1.0137^2,\qquad w<1.914576.
\]
These bounds and \(C_6(h_0),S_7(h_0)\) give
\[
 K'(z_A)>
 1.0137\left\{C_6(.7)+\frac{S_7(.7)}{2(1.914576)}\right\}-p
 >-.0746,
\]
\[
 K''>.4C_6(.7)
             +\frac{Q(1.0137)^2S_7(.7)}{1.914576^3}>\frac23.
\tag{36}
\]
Integrate from \(z_A\) and complete the square:
\[
                       K(z)\ge K(z_A)-\frac34(.0746)^2.
\tag{37}
\]
Its contribution to (28) is therefore greater than
\[
 1-J(b)+f(h_0)-\frac34(.0746)^2
 >1-.4175+.007-\frac34(.0746)^2.
\]
This exceeds \(1-S_0\), because \(S_0>.415\) and the
exact remaining reserve is
\[
                 .007+.415-.4175-\frac34(.0746)^2=.00032613>0.
\tag{38}
\]
Both endpoint alternatives contradict (28). This excludes
the crossed wrong-sign branch and proves the second statement.

The comparison sectors are the actual ordered and crossed
outer-frame alternatives and the exact sign of the hard cap.
The new scalar bounds are one cubic, one global curvature
estimate, two intrinsic angle endpoints, and completed squares.
No angle or state mesh, numerical acceptance test, Lean run,
or CI result is a premise.
