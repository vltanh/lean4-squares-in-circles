# The positive outer edge-3 family without tangent or contact tables

This note completes the table-free hand proof of
`../WRONG_0011011_EDGE3_POSITIVE_OUTER_PAIR_HAND_PROOF.md`.
It replaces all four early-angle tangents and all four moving-contact
rectangles in that manuscript. It also supplies single whole-domain
arguments for its two remaining coordinate/angle splits and imports
the newly table-free zero-contact result in place of its historical
mixed-pair derivative rows.

The resulting theorem covers all four original signed axes, both
angle halves, and every closed coordinate boundary:

\[
 C=\phi+R(b)-J(B)>.89777>.89765,
 \qquad |\phi-\pi/2|\le.7,
 \quad 0\le b,B\le d.                                      \tag{1}
\]

Here, with every terminating decimal interpreted as a rational,

\[
 Q=9789/2500,\quad a(y)=\sqrt{Q-(y+.5)^2}-.5,
 \quad d=\sqrt{Q/2}-.5,\quad \ell=\pi/2-.7,
\]
\[
 R(y)=-.01025a(y)+.16031y+.63457a(y)y,
\]
\[
 J(y)=.03965+3.85510y-1.49748y^2-1.89442a(y)y.
\]

Reflection and reversal give the partner edge-5 family. No numerical
mesh, verifier, or polynomial-coefficient lookup is a premise.

## 1. One quadratic minorant covers all early contacts with small source

Put \(g=.98\). Concavity of \(R\), with its endpoint secant on
\([0,.35]\), gives the whole chord

\[
 R(b)\ge R(0)+gb>-.01450+gb\qquad(0\le b\le.35).
\]

Lower axis 1 requires

\[
 b\ge .5+\sin\phi-U(B)\sin\phi+V(B)\cos\phi,
 \quad U=\sqrt{Q-(B+.5)^2},\quad V=B+.5.
\]

Consequently, on \(\ell\le\phi\le1.3\), every such pair has
\(C\ge F(B,\phi)\), where

\[
 F=\phi-.01450+g/2+g\sin\phi-J(B)
                 -gU\sin\phi+gV\cos\phi.                    \tag{2}
\]

This lower bound remains valid if the relaxed source coordinate in
the separator is negative. Let \(r=V/U\).
Then

\[
 F_B=g(r\sin\phi+\cos\phi)-J',\qquad
 F_{BB}=gQ\sin\phi/U^3-J''.
\]

Moreover \(F_{BBB}<0\), since
\(r''/r'<2.15\) and \(J'''\ge3(1.89442)r'\).
Thus \(F_B\) is concave in \(B\); it also decreases with \(\phi\),
because \(r\cos\phi-\sin\phi<0\) on the entire lower range.
The endpoint comparisons

\[
 F_B(.34,1.3)>.0129,\qquad F_B(d,1.3)>.0444
\]

show that \(F_B>0\) throughout \(.34\le B\le d\).
It suffices to control \(0\le B\le.34\).
There \(F_{BB}\) decreases with \(B\) and increases with
\(\sin\phi\). Its least corner value satisfies

\[
 F_{BB}(.34,\ell)>1.29038>m,\qquad m=1.29.                  \tag{3}
\]

Fix the single reference target \(B_*=.27\), and mark its exact
radical values by stars. A square completion in (3) gives

\[
 F(B,\phi)\ge G(\phi):=
 F(B_*,\phi)-\frac{\{g(r_*\sin\phi+\cos\phi)-J_*'\}^2}{2m}.
                                                               \tag{4}
\]

We prove this one minorant decreases throughout the early angle
range. Its derivative has only two harmonics:

\[
 G'=1+a_1\cos\phi+b_1\sin\phi
                  +a_2\sin2\phi+b_2\cos2\phi,
\]
\[
\begin{aligned}
 a_1&=-g(U_*-1)+gJ_*'r_*/m,& b_1&=-gV_*-gJ_*'/m,\\
 a_2&=g^2(1-r_*^2)/(2m),& b_2&=-g^2r_*/m.
\end{aligned}                                                \tag{5}
\]

Both first-harmonic coefficients are negative. This harmonic is
convex on the whole interval; both its endpoint values are less
than \(-1.379\). Also \(\sqrt{a_2^2+b_2^2}<.439\).
Differentiating (5) four times therefore gives

\[
 G^{(5)}<-1.379+16(.439)=5.645.
\]

At the single rational angle \(1.085\),
\(G'''<-.2809\) and \(|G''''|<.5755\).
Every angle under consideration is within \(.215\) of this point.
Taylor's theorem consequently gives the uniform bound

\[
 G'''<-.2809+.5755(.215)+(5.645/2)(.215)^2<-.026.             \tag{6}
\]

Thus \(G'\) is strongly concave. At \(\phi=1.257\),
\(G'<-.0042423\) and \(|G''|<.000016\).
A second square completion proves

\[
 G'<-.0042423+\frac{.000016^2}{.052}<-.00424<0.
\]

The only cost evaluation required is the right endpoint:

\[
 G(1.3)>.90209>.89777.                                      \tag{7}
\]

Equations (2)--(7) cover every early lower-axis-1 pair with
\(b\le.35\), for every target \(0\le B\le d\).
They replace the complete four-tangent list by one target-coordinate
quadratic and one whole-angle derivative argument.

## 2. The moving source-cut derivative is concave on its full arc

For the remaining source states \(b\ge.35\), the parent's actual
contact cost has a concave derivative in \(B\), as follows directly
from \(R'',R'''<0\) and \(J'''>3(1.89442)r'\).
It is enough to prove its derivative positive at the source cut
\(b=.35\), after which a minimum is at that cut or one of the two
diagonal endpoints already proved in the parent manuscript.

The source-cut curve is

\[
 Z=.15+\sin\phi,\quad Y=\sqrt{Q-Z^2},\quad
 U=Z\sin\phi+Y\cos\phi,\quad
 V=Y\sin\phi-Z\cos\phi,\quad B=V-.5.
\]

With \(f=1-\cos\phi/Y\), its exact derivatives are

\[
 B'=Uf,\qquad U'=-Vf,\qquad B''=-Vf^2+Uf',
\]
\[
 f'=\frac{\sin\phi(Q-1-.15^2)-.15(1+\sin^2\phi)}{Y^3}>0.
                                                               \tag{8}
\]

Both \(f\) and \(f'\) increase: for \(f'\), the numerator
increases with \(\sin\phi\), while its denominator decreases.
The endpoint values and these monotonicities give on the whole arc
\(\ell\le\phi\le1.3\):

\[
\begin{gathered}
 1.510<U<1.831,\quad .752<V<1.279,\quad1.635<Y<1.755,\\
 .632<f<.837,\quad .365<f'<.571,
 \quad -.345<B''<.746,\quad B'>1.510(.632),\\
 .252<B<.779,\quad -1.134<J''(B)<1.9,
 \quad J'''(B)>3.83.
\end{gathered}                                                \tag{9}
\]

Let \(g_1=R'(.35)<.877\), and set

\[
 D(\phi)=g_1Y/U-J'(B(\phi)).
\]

Since \(r\sin\phi+\cos\phi=Y/U\) on this contact, \(D\) is
exactly the derivative needed at the source cut.
For \(q=Y/U\), differentiating the quotient gives

\[
 q''=Y''/U-2Y'U'/U^2-YU''/U^2+2Y(U')^2/U^3.
\]

Here \(Y',U'<0\), \(Y''\le Z\sin\phi/Y\), and
\(-U''=Uf^2+Vf'\). Thus the one uniform upper bound is

\[
\begin{aligned}
 q''<&\frac{1.114(.964)}{1.635(1.510)}
 +\frac{1.755(.837)^2}{1.510}
 +\frac{1.755(1.279)(.571)}{1.510^2}\\
 &+\frac{2(1.755)(1.279)^2(.837)^2}{1.510^3}<2.98.
\end{aligned}
\]

Also \(-J''B''<.847\): a positive product requires opposite signs,
and the two possibilities are bounded by \(1.134(.746)\) and
\(1.9(.345)\). Equations (8)--(9) now give

\[
 D''=g_1q''-J'''(B')^2-J''B''
 <.877(2.98)-3.83\{1.510(.632)\}^2+.847<-.027.              \tag{10}
\]

The two endpoints satisfy
\(D(\ell)>.0644\) and \(D(1.3)>.0912\). Concavity therefore
proves \(D>0\) on the entire moving contact arc.
No enclosures of that arc on angle rectangles are needed.

The original concave-derivative minimum principle consequently
reduces every contact with \(b\ge.35\) to the source cut or a
diagonal. The source cut is covered by (7). The two complete
diagonal proofs in the parent are whole-arc concavity arguments,
whose smallest endpoints exceed \(.8977886\) and \(.8977888\).
This closes the full early lower-axis-1 range.

## 3. Later zero contacts use the completed mixed theorem

The later lower-axis-1 reduction uses the zero-source contact curve
on \([1.3,\pi/2]\). Its two imported assertions are

\[
 1.0424(r\sin\phi+\cos\phi)-J'(B_z)>0,
 \qquad \phi-.01449-J(B_z)>.9025.
\]

They are now table-free by Section 6.2 of
`HAND_WRONG_0011011_MIXED_COMPONENTS_WITHOUT_TABLES.md`, together
with the unchanged whole-arc scalar concavity in its cited parent.
The replacement proves the derivative on the entire zero arc by
strict concavity and its two endpoints; its initial scalar part is
strictly increasing. Since \(R'(0)>1.0424\) and \(R(0)>-.01450\),
the positive outer contact derivative is positive and its zero cost
exceeds \(.90249\). The parent's actual contact reduction and its
target-diagonal bound then complete the later range.

## 4. Two additional whole-domain simplifications

The parent lower-axis-3 proof requires

\[
 R'(b)+j r(b)\sin\phi-j\cos\phi>0,\qquad j=1.176.
\]

It suffices to take \(\phi=\ell\), because increasing \(\phi\)
increases this expression. Set \(V=b+.5\), \(U=a(b)+.5\), and
\(E(b)=R'(b)+jr(b)\sin\ell\). Its second derivative is

\[
 E''=\frac{3Q}{U^5}
 \{- .63457Q+(.327535+j\sin\ell)V\}<0.                     \tag{11}
\]

Indeed \(V<1.4\) and \(\sin\ell<.765\) make the braces
negative. Both endpoint values of \(E-j\cos\ell\) exceed \(.31\).
Concavity proves the entire source-derivative inequality at once,
replacing the two source-coordinate estimates. The subsequent
one-variable strongly convex scalar in the parent is unchanged.

For lower axis 4, feasibility already forces \(\phi>1.2\) and

\[
 B\le (a(0)-.5)\csc\phi-.5-(d+.5)\cot\phi<.415.
\]

Since \(J(B)\le .03965+jB\) on this target range, the cost is
bounded below by the single scalar

\[
 F_4(\phi)=\phi+R(0)-.03965
 -j\{(a(0)-.5)\csc\phi-.5-(d+.5)\cot\phi\}.
\]

It decreases throughout \([1.2,\pi/2]\), because

\[
 F_4'=1-j\frac{d+.5-(a(0)-.5)\cos\phi}{\sin^2\phi}
 <1-j\{1.399-.915(.363)\}<0.
\]

Its right endpoint satisfies

\[
 F_4(\pi/2)=\pi/2+R(0)-.03965-j(a(0)-1)>1.02.              \tag{12}
\]

This removes the two former angle-cap ranges entirely.

## 5. Complete family assembly

The source chord, quadratic minorant, and moving-contact curvature
in Sections 1--2 replace every early support and contact rectangle.
Section 3 supplies the table-free later zero-contact dependency.
Section 4 supplies full-range versions of the two further splits.
The other parent arguments use explicit derivative signs, contact
monotonicity, the two concave diagonal curves, and individual endpoint
or strongly convex reference comparisons. They retain all original
axis alternatives and every inactive-source boundary. Their union
therefore proves (1), including ties.

All point comparisons have the displayed rational inputs and radical
expressions. Integer-square bounds suffice for each radical.
Alternating sine/cosine sums at the finitely many stated rational
angles, together with \(3.141592653589793238<\pi<3.141592653589793239\),
supply the trigonometric point enclosures. The harmonic remainder
bounds (6) and (10) apply on their entire domains and are the
continuum arguments; no finite collection of sampled contacts is
used to infer them.
