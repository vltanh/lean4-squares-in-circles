# Every enclosed pair has boundary centers beyond its two outward faces

**Status: complete hand reduction; root and independent full hand audits passed.**
Let the convex boundary-center polygon contain every enclosed unit, have
edges of length at most \(\sqrt2\), and have all its vertices in the
open disk of radius \(M=91/60\). Every vertex is at distance at least
\(1/2\) from every enclosed unit. These are the established C7 center
polygon properties. Keep

\[
k=3721/7200,\qquad e=k-1/2=121/7200.
\]

The own coordinates of every enclosed unit's center have absolute value
less than \(k\), by `C7_INNER_SIDE_CORNER_RESTRICTIONS.md`.

We prove a whole geometric reduction: for any two interior-disjoint
enclosed units, one can find two actual boundary-square centers beyond
opposite outer faces of the pair. The squares and these faces need not be
parallel. The argument does not use the small relative-angle bound, does
not assume that either inner pair or outer/inner pair actually touches,
and retains every tangential offset. The resulting four-square capacity
problem is not solved here.

## 1. A missing outward middle-face zone violates the center-radius bound

Write one enclosed unit in its own frame as

\[
T=(a,b)+[-1/2,1/2]^2,\qquad a\ge9/20.
\]

Its outward right middle-face zone is

\[
Z=\{(x,y):x\ge a+1,\ |y-b|\le1/2\}.
\]

**Lemma.** At least one polygon vertex lies in \(Z\).

Suppose otherwise. The whole missing-zone endpoint argument from
`PARALLEL_INNER_PAIR_DIAMETER_EXTRACTION.md`, Section 1, applied after
reflection and translation, supplies an edge with endpoints

\[
A=(a+1/2+u,b+1/2+v),\qquad
B=(a+1/2+w,b-1/2-z),
\]

where \(u,w,v,z>0\) and

\[
u^2+v^2\ge1/4,\quad w^2+z^2\ge1/4,
\qquad V:=v+z\le V_0:=\sqrt2-1<1/2.
\tag{1}
\]

This argument uses only the polygon's containment, endpoint clearance,
and edge-length bound; its translation does not affect those hypotheses.
Put \(X=a+1/2\ge19/20\). The elementary identity for the mean of two
squared vertical coordinates gives

\[
\frac{|A|^2+|B|^2}{2}
\ge X^2+X(u+w)+\frac{u^2+w^2}{2}
       +\frac{(1+V)^2}{4}.
\tag{2}
\]

Since \(0\le v,z\le V<1/2\), the concavity of
\(f(t)=\sqrt{1/4-t^2}\) on \([0,V]\) gives

\[
u+w\ge f(v)+f(V-v)\ge\frac12+\sqrt{\frac14-V^2}.
\]

Also \(u^2+w^2\ge1/2-v^2-z^2\ge1/2-V^2\). Thus (2) is at least

\[
F_X(V)=X^2+X\left(\frac12+\sqrt{\frac14-V^2}\right)
       +\frac12+\frac V2-\frac{V^2}{4}.
\tag{3}
\]

For fixed \(X>0\), this function is concave in \(V\). It increases
with \(X\), so it suffices to bound the two endpoint values of
\(F_{19/20}\) on \([0,V_0]\). At zero,

\[
F_{19/20}(0)=941/400>8281/3600=M^2.
\]

At the other endpoint use the exact rational comparisons

\[
V_0>33/80,\qquad V_0^2<43/250,\qquad
\sqrt{1/4-V_0^2}>279/1000.
\]

The first two follow respectively from
\((113/80)^2<2\) and \((707/500)^2<2\); the third follows from
\(1/4-43/250=39/500>(279/1000)^2\). Substitution in (3) yields

\[
F_{19/20}(V_0)>
\frac{361}{400}+\frac{19}{20}\frac{779}{1000}
+\frac12+\frac{33}{160}-\frac{43}{1000}
=\frac{11529}{5000}>M^2.
\tag{4}
\]

The last difference is \(497/90000>0\). Both endpoints, hence all
values in (3), exceed \(M^2\). This contradicts \(|A|,|B|<M\)
and proves the lemma. Every sign and own-axis version follows by an
orthogonal change of coordinates about the fixed containing-circle
origin.

## 2. Both members of every separated pair satisfy the threshold

Choose an actual SAT axis owned by the left unit \(T\), and direct it
toward the right unit \(U\). Set this axis equal to \(e_x\). After a
reflection and a quarter-turn relabeling of \(U\)'s frame, write

\[
C_T=(-\alpha,\beta),\qquad
C_U=\xi u+\eta v,
\quad u=(c,s),\ v=(-s,c),
\quad c\ge s\ge0,\quad c^2+s^2=1.
\]

All four own center coordinates have absolute value less than \(k\).
Separation says

\[
\alpha+\xi c-\eta s\ge\frac{1+c+s}{2}.
\tag{5}
\]

Using \(\xi<k\) and \(-\eta<k\), we get

\[
\alpha>\frac12-e(c+s)>\frac12-2e>\frac9{20}.
\tag{6}
\]

Using \(\alpha<k\) and \(\eta>-k\) instead gives

\[
\xi>\frac12-e\frac{1+s}{c}
\ge\frac12-e(1+\sqrt2)>\frac9{20}.
\tag{7}
\]

For (7), \((1+s)/c\) is increasing on \(0\le s\le1/\sqrt2\),
with endpoint \(1+\sqrt2<5/2\); and \(e<1/50\). The same bound
on \(e\) proves the strict final inequality in (6).

Apply Section 1 to \(T\)'s outward left face and to \(U\)'s
outward \(u\)-face. There are actual boundary centers of the form

\[
C_L=C_T-(1+\delta)e_x+t e_y,
\qquad
C_R=C_U+(1+\varepsilon)u+r v,
\tag{8}
\]

where

\[
\delta,\varepsilon\ge0,\qquad |t|,|r|\le1/2.
\tag{9}
\]

These two centers are distinct. Indeed (5) gives a strictly positive
horizontal separation between the two zones. They belong to two actual
unit boundary squares, each contained in the original containing disk;
no orientation of either boundary square is imposed by (8).

## 3. Exact remaining four-square constraints

Writing the nonnegative separation excess in (5) as \(g\), direct
substitution in (8) gives the useful identity

\[
(C_R-C_L)_x=
\frac32(1+c)+g+\delta+\varepsilon c+(1/2-r)s.
\tag{10}
\]

For C7 the independently proved strict boundary-center diameter bound
gives \(|C_R-C_L|<3\). Thus in the nonparallel case \(s>0\),

\[
g+\delta+\varepsilon c+(1/2-r)s<\frac32(1-c),
\qquad
\frac12-r<\frac32\tan(\theta/2),
\tag{11}
\]

where \(c=\cos\theta\), \(s=\sin\theta\). This places the right
outer center near the relevant end of its outward middle-face zone.
Equations (8)--(11) do not by themselves prove a capacity or radius
bound: both actual outer square frames, their containment, all remaining
ring bodies, and the inner tangential displacement remain part of the
problem. The known pair-angle theorem restricts this residual domain to
\(0<\sin\theta<4/15\), without changing any of these obligations.
