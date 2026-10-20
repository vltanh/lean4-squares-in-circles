# A crossed noncanceling side with the large tangent reaches GA alignment

## 1. Scope and the radius-preserving conclusion

Put
\[
 Q=\frac{9789}{2500},\qquad p=\frac{50}{49},\qquad
 S_0=2\sqrt{Q-1}-3.
\tag{1}
\]
Retain the normal signs at H,G,A,B,T,D, either E sign, the true
core, sorted own-frame magnitudes, corner circles at most
\(q\le Q\), and a real frame interval of length at most \(7/10\).
The retained witnesses are
\[
 HG=0,\quad GA=0,\quad BT=2,\quad TD\in\{0,2\},
 \qquad DE\in\{2,3\},\quad EH\in\{0,1\}.
\tag{2}
\]
Assume that the middle zero has already been aligned:
\[
 \theta_A=\theta_B=\rho,\quad b_A+b_B=1,\quad
 \theta_T\le\rho\le\theta_G.
\tag{3}
\]
Consider the crossed, large-tangent branch
\[
             \theta_H<\rho,\qquad b_A\ge\frac12.
\tag{4}
\]

**Theorem.** Every such original necessary system satisfies
\[
                         0<\rho-\theta_H<\frac1{25}.
\tag{5}
\]
It has a descendant at the same \(q\) with
\[
                         \theta_G'=\rho,
\tag{6}
\]
retaining HG0 and GA0. H,B,T,D,E and all their frames and
coordinates are unchanged. A's frame and tangent are unchanged.
If the original \(\theta_G>\rho\), the descendant can be chosen
with A's corner value strictly below \(q\). An inherited strict
A loss is retained even if a temporary circle lift is used;
an inherited strict B loss is unchanged.

This is a GA-alignment lemma for a crossed outer frame. It does
not yet move the common frame to H or assert outer-zero alignment.
The reflected statement holds with B as the large middle tangent.

The proof uses the endpoint estimate from
[the all-mixed-owner order theorem](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md):
\[
 b_H+b_D-p(\theta_H-\theta_D)+S_0<2.
\tag{7}
\]
Its extension to either E sign is the exact H/D reflection in
Section 2 of
[the crossed canceling reduction](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md).
Only the strict inequality in (7) is needed here.

## 2. One scalar budget with the opposite original hard contact

Translate \(\rho\) to zero and write
\[
 \theta_H=-r,\quad \theta_G=z,\quad \theta_T=-v,
 \qquad r>0,\quad z,v\ge0,\quad r+z\le\frac7{10}.
\tag{8}
\]
The all-sign TD charge gives
\[
 b_T+b_D\ge1-p(\theta_D-\theta_T).
\]
Combining it with (7), without changing T or D, gives
\[
                  b_H-b_T+p(r-v)<1-S_0.
\tag{9}
\]

For the scalar comparisons in Sections 2--7, enlarge both
middle circles to the fixed ceiling \(Q\). This is only a
necessary-inequality comparison; the construction in Section 8
returns to the actual \(q\).

Put \(b=b_A\), and define
\[
 Y=b+\frac12,\quad R=\sqrt{Q-Y^2},\quad P=R-1,
\]
\[
 Y_B=\frac32-b,\quad R_B=\sqrt{Q-Y_B^2},\quad P_B=R_B-1.
\tag{10}
\]
GA0 implies \(a_A\ge1\), so the complete scalar range is
\[
 \frac12\le b\le b_*:=\sqrt{Q-\frac94}-\frac12.
\tag{11}
\]
For a general \(Y\) in the range used below, let \(z(Y)\) be the
unique nonnegative root of
\[
  (\sqrt{Q-Y^2}-1)\cos z-Y\sin z=\frac12.
\tag{12}
\]
Write \(z_A=z(Y)\), \(z_B=z(Y_B)\). The original hard
contacts imply \(0\le z\le z_A\), \(0\le v\le z_B\).
Positive squaring and the alternating sine and cosine
polynomials give
\[
 z_A<\frac15,\quad z_B<\frac{41}{100},\quad
 \frac{683}{400}<\sqrt{Q-1}<\frac{4269}{2500},
\]
\[
 Y\le\frac{1291}{1000},\qquad
 Y_B>\frac{709}{1000},\qquad R_B<\frac{231}{125}.
\tag{13}
\]
For example, the two angle bounds follow by evaluating the
decreasing left side of (12), using respectively
\(P<177/250,\ Y\ge1\) and
\(P_B<106/125,\ Y_B>709/1000\), at \(1/5\) and \(41/100\).

Set
\[
 V(z)=P\cos z-Y\sin z,\quad U(z)=P\sin z+Y\cos z,
 \quad w(z)=\sqrt{Q-V(z)^2}.
\tag{14}
\]
The same G circle and the actual HG0/GA0 inequalities give
\[
 b_H\ge B(r,z,b):=
 \frac12+\{1-V(z)\}\cos(r+z)-\{w(z)-1\}\sin(r+z).
\tag{15}
\]
Indeed, GA0 bounds \(b_G+1/2\) above by \(V(z)\).
On the sorted G arc, its HG0 projection increases with that
corner coordinate because
\(\cos(r+z)-\sin(r+z)>0\). Replacing it by \(V(z)\)
and using the same G circle proves (15).
The opposite actual BT2 contact gives
\[
 b_T\le P_B\cos v-Y_B\sin v-\frac12.
\tag{16}
\]
Consequently the original system must satisfy
\[
 B(r,z,b)-\{P_B\cos v-Y_B\sin v\}+\frac12+p(r-v)
                                                   <1-S_0.
\tag{17}
\]

## 3. Concavity leaves two intrinsic G endpoints

Put \(T=w-U\). On \(0\le z\le z_A\),
\[
 T>0,\quad T'=-\frac{VT}{w}<0,\quad
 T''=\frac{T(QU+V^2w)}{w^3}>0.
\tag{18}
\]
These follow by differentiating (14), or from
\(w^2-U^2=2R-1>0\). Since \(Y\ge1>P\), also \(T<1\).
Moreover \(U\ge Y\ge1\), \(V<177/250\), and
\(w<383/200\), whence
\[
 1-\frac{2VT}{w}>
 1-2\frac{177}{250}\frac{183}{383}>0.
\tag{19}
\]

For fixed \(r,b\), set \(h=r+z\) and
\[
 F(h)=\sin h\{T(h-r)-1\}+1-\cos h.
\]
The addition formula gives
\[
 B(r,z,b)=\frac32-V(-r)-F(r+z).
\]
Direct differentiation yields
\[
 F''(h)=
 \cos h\left(1-\frac{2VT}{w}\right)
       +\sin h\{1-T+T''\}>0.
\tag{20}
\]
Here \(0<h\le r+z_A<9/10<\pi/2\), so all factors
needed for this sign have already been established.

Thus \(B(r,z,b)\) is strictly concave on the complete scalar
interval \(0\le z\le z_A\), and
\[
             B(r,z,b)\ge
             \min\{B(r,0,b),B(r,z_A,b)\}.
\tag{21}
\]
The interval in this scalar comparison can have
\(r+z_A>7/10\). No new geometric state is asserted there:
(20) is an algebraic comparison on \(h<9/10\), and the next
section proves its endpoint estimate on exactly that enlarged
interval. The original state still has its original frame spread.

## 4. Two elementary angle and envelope facts

Let
\[
 k=\sqrt{Q-\frac14}-1,\qquad
 f(h)=ph-k\sin h-\frac12(1-\cos h).
\tag{22}
\]
Then
\[
 f(h)\ge0\quad(0\le h\le9/10),\qquad
 f(h)\ge f(1/25)\quad(1/25\le h\le7/10).
\tag{23}
\]
Here is one whole-interval check. Positive squaring gives
\(.914<k<.915\). On \([0,.7]\), \(f'\) is strictly convex,
since \(f'''=k\cos h+\frac12\sin h>0\).
Also \(f'(0)>0\) and \(f'(.7)<0\). It follows that f first
increases and then decreases on this interval; every interval
\([a,.7]\) has its minimum at an endpoint.
The degree-five upper sine, degree-six lower cosine, and
degree-seven lower sine give
\[
 f(.7)>.007,\qquad f(.04)<.005,\qquad f'(.7)<0.
\]
For the remaining interval,
\(\sqrt{.915^2+.5^2}<1.043\), so
\[
 f(h)\ge .007+(p-1.043)(h-.7)>0
                    \quad(.7\le h\le.9).
\]
These estimates prove (23). All displayed terminating decimals
in this note are exact rational numbers.

The opposite-angle envelope is
\[
 M(b)=\max_{0\le v\le z_B}
       \{P_B\cos v-Y_B\sin v+pv\}.
\tag{24}
\]
Its maximizer is positive, because \(p>Y_B\).
Write \(V=P_B\cos v-Y_B\sin v\) and
\(U=P_B\sin v+Y_B\cos v\) in this paragraph.
Since \(U'=V\ge1/2\), the maximizer is either the unique
free point \(U=p\), or \(v=z_B\).
The change between those alternatives occurs at
\[
 R_B=\chi:=\frac{Q+3/4-p^2}{2}
                 =\frac{2719408}{1500625}.
\tag{25}
\]
For \(R_B\le\chi\) the free maximum is used. For
\(R_B\ge\chi\) the endpoint maximum is used.
The two formulas and their first derivatives agree at the
transition, because the derivative in v is zero there.
Thus M is continuously differentiable on (11).

We will use the following second-derivative bounds:
\[
 \begin{array}{ll}
 3/8<M''<3/4,& R_B<\chi,\\[2pt]
 M''<p\,11/20,& R_B>\chi,
 \end{array}
\qquad
 z_A''>-1/16,\quad z_B''>1/8\ \ (R_B>\chi).
\tag{26}
\]
The primes in (26) mean b derivatives; the second derivative
of \(z_B=z(3/2-b)\) has the same sign and value as the
second derivative of z with respect to its argument.
Sections 5 and 6 supply the full analytic checks of (26).

## 5. Inverse-angle curvature without an angle subdivision

For (12), write
\[
 R=\sqrt{Q-Y^2},\quad
 U=\sqrt{Q+\frac34-2R},\quad s=\sin z,\quad c=\cos z.
\]
Implicit differentiation gives
\[
 z_Y=-\frac{1+s/U}{R},
\]
\[
 z_{YY}=
 -\frac{Y}{R^3}(1+s/U)
 +\frac{c}{R^2U}(1+s/U)
 +\frac{sY}{R^2U^3}.
\tag{27}
\]
In particular the first two terms combine as
\((1+s/U)(cR-YU)/(R^3U)\).

For the A inverse, (13) gives
\[
 R\ge1.5,\quad Y,U<1.291,\quad U>1.117,\quad
 s<.2,\quad c>.98.
\]
Dropping the last positive term in (27) therefore gives
\[
 z_A''>
 -\frac{(1.291^2-.98\cdot1.5)(1+.2/1.117)}
             {1.5^3\cdot1.117}>-\frac1{16}.
\tag{28}
\]
For the boundary B inverse, \(R_B>\chi>1.8\),
\(Y_B<.8\), \(.98<U\le p<1.021\),
\(R_B<1.85\), \(s<.4\), and \(c>.915\).
The combined first two terms in (27) are positive and give
\[
 z_B''>
 \frac{.915\cdot1.8-.8\cdot1.021}{1.85^3\cdot1.021}
 >\frac18.
\tag{29}
\]
For an upper bound, drop the negative term in (27):
\[
 z_B''<
 \frac{1+.4/.98}{1.8^2\cdot.98}
 +\frac{.4\cdot.8}{1.8^2\cdot.98^3}
 <\frac{11}{20}.
\tag{30}
\]
The three rational margins in (28)--(30) are respectively
greater than \(.00098,.0034,.0015\).
Since the boundary formula in (24) is
\(M=1/2+pz_B\), this proves all boundary assertions in (26).

## 6. Free-envelope curvature from one convex rational function

At the free point \(U=p\), put \(R=R_B\), \(Y=Y_B\),
\(V=\sqrt{Q+1-p^2-2R}\), \(c=\cos v\), \(s=\sin v\).
Differentiating the stationary envelope gives the exact identities
\[
 M''=-\frac{Qc}{R^3}+\frac{(V+c)^2}{R^2V}
     =\frac{c(V+c)}{R^2V}-\frac{Y(p+s)}{R^3}.
\tag{31}
\]
The free range has
\[
 \ell:=683/400<R\le\chi<1.813,\quad
 1/2\le V<.678,\quad Y>.794,\quad v<.345,\quad c>.94.
\tag{32}
\]
For the angle bound, evaluate
\(.813\cos(.345)-.794\sin(.345)<1/2\)
using the degree-four upper cosine and degree-three lower sine.
The quadratic lower cosine then gives \(c>.94\).
The first identity in (31) gives
\[
 M''>
 \frac{(.678+.94)^2}{1.813^2\cdot.678}
                  -\frac{Q}{\ell^3}>\frac38.
\tag{33}
\]
Here \((V+.94)^2/V\) decreases for \(V\le.678<.94\).

For the upper bound, \(p=(R-1)s+Yc\) implies
\(s\ge(p-Y)/(R-1)\). The second identity in (31) yields
\[
 M''\le A(R)-\frac{Y(p-Y)}{(R-1)R^2},
\quad
 A(R)=\frac1{R^2\sqrt{Q+1-p^2-2R}}
              +\frac{R^2+R-Q}{R^3}.
\tag{34}
\]
This single function A is convex on \([\ell,\chi]\).
In fact, with \(V^2=Q+1-p^2-2R\),
\[
 A''=
 \frac{6V^4-4RV^2+3R^2}{R^4V^5}
       +\frac{2R^2+6R-12Q}{R^5}.
\]
Completing the square in the first numerator gives
\[
 A''\ge
 \frac{7/3}{1.813^2\cdot.678^5}-\frac{12Q}{\ell^5}
 >1.7>0.
\tag{35}
\]
Consequently A lies below the one chord between its two
domain endpoints. Direct positive squaring at \(\ell\),
where \(V>.6777\), and rational arithmetic at \(\chi\),
where \(V=1/2\), give
\[
                         A(\ell)<.649,\qquad A(\chi)<.808.
\tag{36}
\]

For the term subtracted in (34), put
\[
 \eta=\frac{Q-1-\ell^2}{2}=\frac7{320000},\qquad
 \kappa=\frac{.79}{(\chi-1)\chi^2}.
\]
Concavity of the square root, followed by
\(R^2\ge\ell^2+2\ell(R-\ell)\), gives
\[
 Y=\sqrt{Q-R^2}\le1+\eta-\ell(R-\ell).
\]
Since \(Y>.79\) and \(p-Y>0\), we obtain the affine lower bound
\[
 \frac{Y(p-Y)}{(R-1)R^2}
       \ge\kappa\{p-1-\eta+\ell(R-\ell)\}.
\tag{37}
\]
Subtract this line from the upper chord in (36).
Its two endpoint values are less than \(3/4\); their exact
rational reserves are
\[
 \begin{split}
 &\frac34-.649+\kappa(p-1-\eta)>.107,\\
 &\frac34-.808+
       \kappa\{p-1-\eta+\ell(\chi-\ell)\}>.00098.
 \end{split}
\tag{38}
\]
The difference is affine, so (38) proves \(M''<3/4\)
on the entire free interval. This completes (26).
There is no angular mesh or list of interval rows in this argument.

## 7. Exclude the zero-transverse endpoint and capture the crossing

At \(z=z_A\), equation (15) becomes
\[
 B(r,z_A,b)=\frac12+\frac12\cos h-k\sin h,
 \qquad h=r+z_A.
\]
Using \(f(h)\ge0\) from (23), the left side of (17) is at least
\[
 1-\left\{pz_A+M(b)-\frac12\right\}.
\tag{39}
\]
Set \(J(b)=pz_A+M(b)-1/2\).
On the free branch, (26) gives
\(J''>3/8-p/16>0\).
On the boundary branch, it gives
\(J''=p(z_A''+z_B'')>p/16>0\).
The first derivatives agree at the transition, so J is convex
on the entire b interval. Its maximum is therefore at one
of the two intrinsic b endpoints.

At \(b=1/2\), \(z_A<.196\), hence \(pz_A<1/5\).
The free maximizer in (24) is less than \(.04\):
at that angle \(U>p\), by the cubic lower sine and quadratic
lower cosine. Throughout this smaller interval \(V>.66\).
Taylor's integral remainder, or two integrations of
\((V+pv)''=-V<-.66\), gives
\[
 J(1/2)<
 \frac15+.708-\frac12+\frac{(p-1)^2}{1.32}
 <.409.
\tag{40}
\]
At \(b=b_*\), \(z_A=0\), \(R_B>1.84\), and
\(U(z_B)^2=Q+3/4-2R_B<p^2\). Thus the envelope is
at \(z_B\). The quartic upper cosine and cubic lower sine give
\[
 .848\cos(.406)-.709\sin(.406)<1/2,
\]
so \(z_B<.406\) and
\[
 J(b_*)=pz_B<p(.406)=\frac{203}{490}<.415<S_0.
\tag{41}
\]
The last inequality follows by squaring
\(\sqrt{Q-1}>1.7075\).
Equations (40)--(41) and convexity give \(J<S_0\)
everywhere. Therefore (39) contradicts (17).
The G-zero endpoint is excluded for every \(r\ge0\)
allowed in the enlarged scalar comparison.

It remains to exclude \(r\ge.04\) at \(z=0\).
Write \(w_A=\sqrt{Q-(R-1)^2}\).
Since \(w_A-1\le k\), \(1-P\le1/2\), and (23) holds,
\[
 B(r,0,b)+pr\ge B(.04,0,b)+p(.04)
                      \quad(.04\le r\le.7).
\tag{42}
\]
Thus it suffices to bound below
\[
 \phi(b)=1+(2-R)\cos(.04)-(w_A-1)\sin(.04)
                              -M(b)+p(.04).
\tag{43}
\]
This function is convex on (11). Indeed,
\[
 R''=-Q/R^3,\qquad
 w_A''=\frac{1-Q/R^3}{w_A}
       -\frac{Y^2(1-1/R)^2}{w_A^3}<\frac18.
\]
Here \(R<1.708\), \(w_A>1.847\).
The second derivative of the first three terms of (43) is
therefore greater than
\[
 \frac{Q(1-.04^2/2)}{1.708^3}-\frac{.04}{8}
 >\frac{39}{50}.
\tag{44}
\]
The exact reserve over \(39/50\) is
\(3307169/15570896600\).
Combine (44) with (26): on the free branch
\(\phi''>39/50-3/4>0\), and on the boundary branch
\(\phi''>39/50-p\,11/20>0\).
The first derivative is continuous at the transition.

One rational pivot now suffices. At \(b_0=27/40\), direct
positive squaring and the alternating sine and cosine
polynomials give
\[
 \begin{gathered}
 1.592160<R<1.592161,\quad
 1.888106<w_A<1.888107,\\
 1.798603<R_B<1.798604,\quad
 .526458<V<.526462,\quad
 .292830<v<.292832.
 \end{gathered}
\tag{45}
\]
Here v is the free maximizer: substitute the two rational
angle endpoints into
\((R_B-1)\sin v+Y_B\cos v=p\), whose left side is
strictly increasing. At this pivot
\[
 M=V+pv,\qquad
 M'=\frac{Y_B}{R_B}\cos v+\sin v.
\]
Using the degree-six lower and degree-eight upper cosines,
and the degree-seven lower and degree-nine upper sines,
the enclosures (45) imply
\[
                   \phi(b_0)>\frac{47}{80},\qquad
                   |\phi'(b_0)|<\frac1{1000}.
\tag{46}
\]
For completeness, the lower reserve in the first comparison is
\[
 \frac{427597243323022613251}
      {9689941406250000000000000}>0.
\]
The same substitutions put the derivative strictly between
\(.0003165\) and \(.0003195\).
Thus (46) uses only one displayed rational point, not an
optimizer or a sampled minimum.

Convexity and \(|b-b_0|\le7/40\) now give
\[
 \phi(b)>
 \frac{47}{80}-\frac7{40000}
 =\frac{117}{200}+\frac{93}{40000}.
\tag{47}
\]
But \(S_0>.415\), so \(1-S_0<117/200\).
Equations (42)--(47) contradict (17).
Together with (21) and the excluded endpoint (39), this proves
the capture (5) for the original state.

## 8. Direct GA alignment at the actual circle ceiling

Return to the actual \(q\), keep \(b_A\) fixed, and lift only
A's primary to its containing q-circle if necessary.
Use (14), (18), and (20) with Q replaced by q.
Feasibility implies \(q\ge13/4\), \(R\ge1.5\), \(Y\ge1\).
The same proof gives \(z_A<.2\), \(0<T<1\), and \(F''>0\).
By (5), the complete endpoint angle satisfies
\[
                         h_{\max}=r+z_A<.24.
\tag{48}
\]

At \(V=1/2\),
\[
 w_0=\sqrt{q-\frac14},\quad
 U_0=\sqrt{q+\frac34-2\sqrt{q-Y^2}},\quad
 T_0=w_0-U_0.
\]
The quantity \(T_0\) decreases with Y and increases with q
on the feasible range. To check the latter claim,
\[
 \partial_qT_0=
 \frac1{2w_0}-\frac{1-1/R}{2U_0}>0,
\]
because \(U_0\ge Y\ge1\), \(R<1.708\), and \(w_0<1.915\).
Its maximum is therefore at \(q=Q,Y=1\).
There \(U_0>1.118\), using
\(\sqrt{Q-1}<1.7076\), so
\[
                         T_0<.797,\qquad w_0<1.915.
\tag{49}
\]

At this endpoint, differentiation gives
\[
 F'(h_{\max})
 =\cos h_{\max}(T_0-1)
       +\sin h_{\max}\left(1-\frac{T_0}{2w_0}\right).
\]
This expression increases with both \(T_0\) and \(w_0\)
on the range in (48). Consequently
\[
 \begin{split}
 F'(h_{\max})
 &<-.203(1-.24^2/2)
          +.24\left(1-\frac{.797}{3.83}\right)\\
 &=-\frac{1698643}{239375000}<-\frac1{150}.
 \end{split}
\tag{50}
\]
Since \(F''>0\), the same upper derivative bound holds
throughout \(r\le h\le r+z_A\). Because
\(B=3/2-V(-r)-F\), this gives
\[
                    B(r,0,b_A)<B(r,z,b_A)-z/150
                         \qquad(z>0).
\tag{51}
\]
Thus the required H tangent strictly decreases when G moves
from z to zero. The exact HG0/GA0 pair has strict slack at
GA alignment.

At the new frame choose \(b_G=P-1/2\) and
\(a_G=\sqrt{q-P^2}-1/2\), using the actual lifted A.
Then GA0 is an equality and HG0 holds with the slack just
proved. Here \(0\le b_G<.208\), while \(a_G>a_A\ge1\);
sorting and the true core are preserved. Every frame remains
inside the original real interval.

For \(z>0\), lower A's primary slightly and adjust \(b_G\)
continuously to keep the aligned GA0 equality. The strict
HG0 slack persists, so A's circle becomes strictly less than q.
This also recreates any inherited A loss after the temporary
lift. If \(z=0\), skip the lift and keep A and G exactly as
they were. B and its separate circle loss have never changed.
This proves the radius-preserving statement and its strictness.

All new scalar claims above follow from differentiation,
convexity, two intrinsic endpoints, positive squaring, and
alternating Taylor inequalities at the displayed rational
arguments. No numerical search result, angular row inventory,
Lean compilation, or CI output is a premise.
