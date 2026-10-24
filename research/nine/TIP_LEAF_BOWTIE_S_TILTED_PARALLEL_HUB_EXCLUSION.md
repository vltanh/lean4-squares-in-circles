# A tilted S articulation cannot have a parallel hub across its u side

**Status: complete whole-feature hand exclusion; root and separate
independent full hand audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1<\frac{61}{60}.
\tag{1}
\]
The exact positive graph is H–A–B–H, H–C–E–H, and A–L.
A has exact degree three, H degree four, and B,C,E degree two.
L is a radial S leaf. All three additional physical units remain
present.

Use A's orthonormal side frame and its leaf application as local
coordinate origin. The actual circle origin is
\[
 O=(Da,Db),\qquad a\ge b>0,\quad a^2+b^2=1,\qquad A=[0,1]^2.
\tag{2}
\]
The leaf force points in direction \((-a,-b)\). Suppose AH has
the A-owned outward normal \(e_x\), and H is parallel to A:
\[
                         H=[1,2]\times[\eta,\eta+1].
\tag{3}
\]
The actual AH mean remains arbitrary in the shared support interval.

**Theorem.** This entire interface is impossible. No hypothesis
is made about the B physical circle mask, the AB/BH owners,
the H petal frame, the three remaining units, or any variable
shared-side application mean. This is exactly the u-owned,
parallel-H subfamily of the tilted-S articulation; it makes no
claim about a different AH side before a separate feature reduction.

## 1. Exact root force and mean coordinates

Write the A-to-B normal as n, and normalize the leaf magnitude
to one. With positive magnitudes \(\mu,\nu\), A's true balance is
\[
                            \mu n+\nu e_x=(a,b).
\tag{4}
\]
The unit-triangle side-normal lemma at A gives \(n_x\ge0\),
while (4) gives \(n_y>0\). There are exactly two AB features:
an A-owned \(e_y\) normal on its top side, or a strict
northeast normal at \(W=(1,1)\).

A's two normal lines intersect. Its exact torque puts their
intersection on the line through 0 and O, so write it
\((\sigma a,\sigma b)\). The purely geometric behind-port
lemma and the actual AH mean give
\[
             Q=(1,\sigma b),\qquad
             0\le\sigma,\quad \sigma a\le1,\qquad
                          \eta\le\sigma b\le\eta+1.
\tag{5}
\]
No proper concurrence of B is needed for this reduction.
For AB owned by \(e_y\), the actual mean is
\[
                   P=(\sigma a,1),\qquad \mu=b,\quad\nu=a.
\tag{6}
\]
For a strict northeast AB normal, its application is W. Whenever
the root intersection differs from W, its direction is
\[
 n=\frac{(1-\sigma a,\,1-\sigma b)}
         {\sqrt{(1-\sigma a)^2+(1-\sigma b)^2}}.
\tag{7}
\]
In particular its first component is at most its second.
The coincident root intersection W could occur only when
\(a=b\) and \(\sigma=\sqrt2\); it is absent from the only
high-support domain used below.

Let g be the B-to-H normal, with magnitude \(\gamma>0\).
At H the two triangle normals are \(-e_x,-g\), so the
side-normal lemma gives \(g_x\ge0\). H's genuine degree-four
equation is
\[
                         M:=F_C+F_E=\nu e_x+\gamma g,
                              \qquad M_x>0.
\tag{8}
\]
The tips B,C,E are loaded because each has exact degree two
and physically touching neighbors. A is physically clear by
the actual radial-leaf classification. H is physically clear
because H,C,E cannot be a boundary triangle.

We use the complete opposite-petal implications at arbitrary H:
a nonparallel C/E root intersection is a negative multiple
\(q_0=-tM\), with proper outward ports; after the already
excluded both-H-owned perpendicular case, one actual port
maximizes M on H. These are
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Sections 2–4.
We also use END_TRIANGLE_HIGH_FACE_EXCLUSION.md.

## 2. The complete low-support domain is immediate

Here and below support coordinates and norms are relative to
the actual circle origin O, not to the local origin of A.

If \(Da\le1\), H has nonnegative minimum x-coordinate
\(1-Da\). By (8), the x-coordinate of \(q_0\) is negative.
A minimum-x port or a tangential H-owned side mean cannot
satisfy the proper outward relation. Thus both actual C/E
ports lie on H's maximum-x side. For a parallel petal
interface this follows directly from its common normal
\(M/|M|\), whose x-component is positive.

That side has height
\[
                         2-Da\ge2-D>59/60,
\]
contrary to the high-face theorem.

It remains only \(Da>1\). Put
\[
       \delta=D-1,\qquad x=1-Da,\qquad h=1-Db,\qquad r=R-\sqrt2.
\]
Then the complete residual bounds are
\[
 \begin{gathered}
   0<\delta<1/60,\qquad -\delta<x<0,\qquad
   0<Db<11/60,\qquad 49/60<h<1,\\
   R^2>17/4,\qquad r>129/200,\qquad
   \sigma\le1/a<D.
 \end{gathered}
\tag{9}
\]
Indeed \(D^2b^2<D^2-1<121/3600\). The true-coordinate
version of W is \((x,h)\), and
\[
              |W-O|^2=D^2+2-2D(a+b)<D^2.
\tag{10}
\]
It also has norm greater than \(49/60>r\); for the latter
comparison it suffices to use \(R<21/10\) and \(\sqrt2>7/5\).

## 3. One complete low-bottom hub consequence

We record a routing consequence used in every remaining branch.
Suppose H has true coordinates
\[
                       H=[x,x+1]\times[t,t+1],
       \qquad -1/60<x<0,\quad -1/2<t<0,
\tag{11}
\]
and \(M_x>0,\ M_y\le0\). Then the C/E petal is impossible.

If \(M_y=0\), M is H's east side axis. Both actual root ports
lie on its maximizing side. To recall the complete axis argument:
a root-owned transverse axis conflicts with transverse balance
and the triangle nonobtuse lemma; a root-owned longitudinal
axis makes both forces parallel; otherwise the two strict
vertex normals have opposite transverse signs and positive
longitudinal sum, so both vertices lie on the far side.

If \(M_y<0\), the unique maximizing vertex is the lower-right
one, \((x+1,t)\). A parallel interface puts both ports there.
For any other allowed interface, one actual port is there.
The other possible feature is exhaustive:

* The lower-left vertex has norm below
  \(\sqrt{1/3600+1/4}<129/200<r\), so is circle-clear.
* The upper-left strict vertex is opposite and forbidden by
  the physical unit-triangle support-span lemma.
* The upper-right or same lower-right vertex is on the far-x side.
* H-owned west or north normals have negative dot product with M,
  contrary to the triangle nonobtuse-normal consequence.
* For an H-owned south mean, its x-coordinate is \((q_0)_x<0\).
  If it belongs to the side, that coordinate lies in \([x,0)\).
  Its norm is therefore below r by (11).
* An H-owned east application lies on the far-x side.

Thus both actual petal ports lie on the side of height
\[
                           x+1=2-Da>59/60.
\]
The high-face theorem proves the consequence. All means and
zero proper-length endpoints have been retained.

## 4. The entire A-owned top AB side

Suppose \(n=e_y\), with actual mean (6). B lies wholly above
the line of local height one. Since H touches B, (3) implies
\(\eta\ge0\). Meanwhile (5),(9) give
\[
                         0\le\eta\le\sigma b<Db.
\tag{12}
\]
Thus H's true bottom \(t=\eta-Db\) lies in \((-11/60,0)\).

The mutual normal has \(g_x\ge0\). It cannot have \(g_y>0\):
H's minimum-g vertex or horizontal support face would then
have local height \(\eta<1\), and could not belong to B.
Therefore \(g_y\le0\), and (8) gives \(M_y\le0\).
Section 3 excludes the entire top-side alternative, with
every AB,AH and BH mean and every B mask.

## 5. The free AB vertex alternative, including its full shared exception

Now n is strict northeast and its actual application is W.
By (10), B cannot have two physical circle corners: every
point of a radial S square has norm at least D. Thus B is
physically unique.

If BH is a singleton, the fixed-point selection theorem
GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes a free AB
normal whenever the two physical applications are distinct.
Its exact coincident exception would require W to be the
radial-D inner vertex, of norm r. This is impossible by
the strict norm inequality following (10). Thus the entire
singleton BH domain has no free AB.

If BH is a positive-length shared side, B is parallel to H.
A strict northeast normal at its minimum support W forces
\[
                            B=[1,2]\times[1,2].
\tag{13}
\]
Because H has the same horizontal interval and still meets A,
the actual shared BH side forces \(\eta=0\) and \(g=-e_y\).
The entire side mean remains arbitrary. Hence H's true bottom
is \(t=-Db\in(-11/60,0)\), while (8) gives
\(M_x>0,\ M_y<0\). Section 3 excludes this shared exception
directly. No special endpoint-normal choice, B force ratio
or replacement of its mutual-contact mean was used.

This covers every free AB possibility.

## 6. The B-owned AB side and every mutual owner

The only remaining strict northeast AB contact is B-owned.
The selected point convention puts W in that side's relative
interior. Write
\[
 \begin{gathered}
       n=(s,c),\quad v=Jn=(-c,s),\quad
       0<s\le c,\quad s^2+c^2=1,\\
       B=W+[0,1]n+[-\rho,1-\rho]v,\qquad 0<\rho<1.
 \end{gathered}
\tag{14}
\]
The inequality \(s\le c\) follows from (7) and \(\sigma\ge0\).

At B, the side-normal triangle lemma gives \(n\cdot g\le0\).
Together with \(g_x\ge0\), this leaves exactly
\[
                 g=-v \quad\hbox{if B owns BH},\qquad
                 g=-e_y \quad\hbox{if H owns BH}.
\tag{15}
\]
Every other side-axis sign fails one of the two inequalities.
A free BH is removed by the same fixed-tip selection: B is
unique, W is side-interior, and a free BH point is a distinct
B vertex. No AH mean is frozen. A shared BH would force the
frames B,H to coincide, inconsistent with the strict n in (14).

The alternative \(g=-v=(c,-s)\) is physically impossible.
H's minimum-g point is its upper-left vertex, of local x=1.
But every point on B's maximum-g side is
\[
                         W-\rho v+\tau n,\qquad0\le\tau\le1,
\]
whose x-coordinate is \(1+\rho c+\tau s>1\).
There is no actual contact.

Thus \(g=-e_y\). B's actual minimum-y vertex is
\[
                         T=W-\rho v=(1+\rho c,1-\rho s).
\tag{16}
\]
It lies on H's top side, with the actual x-coordinate in its
relative interior. Therefore
\[
                  \eta=-\rho s,\qquad
                  t=\eta-Db=-k,\quad k:=Db+\rho s>0.
\tag{17}
\]

## 7. The actual B circle corner forces k<1/2

In B's own frame, the true application W has
\[
               p_n=xs+hc>0,\qquad p_v=-xc+hs>0.
\tag{18}
\]
B's two actual pair forces are nonparallel, since n has
strictly positive x-coordinate and \(g=-e_y\).
The general-neighbor proper-concurrence calculation thus
puts its concurrence at \(W+\lambda n\), \(\lambda\ge0\),
as a positive multiple of its unique circle corner.

Its transverse own coordinate is the positive \(p_v\), so
the circle corner uses B's maximum-v face. Its normal own
coordinate also uses the maximum-n face because
\(p_n+1/2>0\). With \(V=1-\rho\), the actual circle corner is
therefore
\[
             Z=(x+s-Vc,\quad 1+c+s-k).
\tag{19}
\]
Both coordinate conclusions use the true physical unique
corner, not an equated resultant in a two-corner mask.

Suppose \(k\ge1/2\). If \(Z_x\le0\), then \(Vc\ge x+s\), so
\[
 \begin{aligned}
 \rho s
   &=s-Vs\\
   &\le s-\frac{s^2}{c}-\frac{xs}{c}\\
   &\le s-s^2+\delta
    \le\frac14+\delta.
 \end{aligned}
\tag{20}
\]
We used \(c\le1,\ s/c\le1,\ x>-\delta\). Equations (9),(20)
give
\[
                  k<\frac{11}{60}+\frac14+\frac1{60}
                            =\frac9{20}<\frac12,
\]
a contradiction.

Consequently \(Z_x>0\), and (19) gives
\[
            0<Z_x<s\le1/\sqrt2,\qquad
            0<Z_y\le\frac12+\sqrt2.
\tag{21}
\]
The second positivity is also immediate from the original
expression \(Z_y=h+c+Vs\).
Thus
\[
                  |Z|^2<
                     \frac12+\left(\frac12+\sqrt2\right)^2
                     =\frac{11}{4}+\sqrt2
                     <\frac{17}{4}<R^2,
\tag{22}
\]
contradicting that Z lies on the circle. We have proved
\[
                                      0<k<1/2.
\tag{23}
\]

By (17), H now satisfies (11), and its actual resultant in (8)
has \(M_x>0,\ M_y<0\). Section 3 supplies the final contradiction.

## 8. Complete scope and common certificate

The cases \(Da\le1\), A-owned vertical AB, free AB with singleton
or shared BH, and B-owned strict AB are exhaustive. The only
physical radial mask was eliminated by the actual norm of W,
and the coincident radial-D exception was checked separately.
Every genuine shared-side application remains its actual mean.

All selections used here are already part of the common
fixed-tip prelist. They involve distinct singleton physical
applications and do not impose any new relation on a shared
AH or BH mean. H retains its true degree-four equation; only
B and the actual C/E tips use degree-two implications.

The theorem excludes the entire u-owned AH, parallel-H
alternative within the tilted-S tip-leaf bowtie. The other AH
features belong to the separate tilted-S assembly. All three
arbitrary completion squares remain present. No numerical
pose sampling, post-extraction normal change, motion, Lean
compilation or CI is used.

