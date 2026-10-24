# The entire right-outside inner-pair branch is impossible

**Status: complete hand branch theorem; root and separate independent full hand audits passed.**
Use the C7 hypotheses, the fixed circle origin, and the exact pair
notation from `C7_INNER_PAIR_FAR_FACE_CENTERS.md`:

\[
C_T=(-\alpha,\beta),\qquad C_U=\xi u+\eta v,
\quad u=(c,s),\quad v=(-s,c),\quad c=\cos\theta,
\quad s=\sin\theta>0.
\]

The chosen actual SAT normal is owned by the left unit \(T\). All
own center coordinates have absolute value less than

\[
k=3721/7200,\qquad e=k-1/2=121/7200,
\]

and all boundary centers have norm less than \(M=91/60\), with
pairwise distances less than three. The far-face theorem supplies

\[
C_R=(\xi+1+\varepsilon)u+(\eta+r)v,
\qquad\varepsilon\ge0,\quad |r|\le1/2,
\]

and, with \(\tau=\tan(\theta/2)\), its exact gap budget gives

\[
r>1/2-3\tau/2.
\tag{1}
\]

**Theorem.** The case \(\xi\ge1/2\) is impossible, with every
outer-square frame and SAT owner retained. Consequently every remaining
nonparallel enclosed pair has

\[
\boxed{\xi<1/2,\qquad \alpha>1/2.}
\tag{2}
\]

The original separating axis is still owned by the outside left unit.
No alternate separator or interchange of owners is assumed. The entire
asymmetric case (2) remains a separate capacity obligation.

## 1. An outside unit's ray witness has a nearly radial frame

Suppose an inner unit has own center \((a,b)\), with
\(a\ge1/2\), \(0\le b<a\). Every boundary unit meeting its
outgoing center ray has center radius \(\rho\ge3/2\), by
`CENTER_COVER_PIERCING.md`, Lemma 1.1. Choose its side axis nearest
its radial center direction, with angular difference
\(0\le\psi\le\pi/4\). Containment in \(D_Q\),
\(Q=1105/256\), gives

\[
\rho^2+\rho(\cos\psi+\sin\psi)+1/2\le Q,
\qquad \cos\psi+\sin\psi\le401/384.
\]

Thus \(\sin\psi<1/20\). Indeed, putting \(w=\sin\psi\),
\(\cos\psi\ge1-w^2\); on \([1/20,1/\sqrt2]\) the concave
function \(w-w^2\) is greater than \(17/384\) at both endpoints.

For a separator owned by this boundary unit, let \(n\) be its normal
directed from the inner unit, and let \(m\) be a perpendicular own
axis. The normal projection of its center exceeds one. The minor own
projection, however, has absolute value less than \(M/20\), so
\(n\) must be the positive major own axis. Consequently

\[
n\cdot C>\frac32\frac{399}{400},
\qquad |m\cdot C|<\frac{91}{1200}.
\tag{3}
\]

Use the radial-tail notation

\[
z=(a,b),\quad H=n\cdot z+H_T(n),
\quad\lambda=H/(n\cdot z).
\]

The outgoing ray forces \(n\cdot z>0\). The separator and ray
strip then imply the two useful necessary inequalities

\[
H<61/60,
\qquad |\lambda(m\cdot z)|<691/1200<3/5.
\tag{4}
\]

These facts do not require the balanced-sector condition of the previous
sharp-tail manuscript.

## 2. Uniform witness localization for \(3/16\le b<3/8\)

Assume now

\[
1/2\le a\le k,\qquad 3/16\le b<3/8.
\tag{5}
\]

We prove that every outgoing ray witness has

\[
\boxed{C_x>36/25.}
\tag{6}
\]

### 2.1. Separators owned by the inner unit

A rightward separator gives \(C_x\ge a+1\ge3/2\).
For an upward separator, write \(h\in[1/2,1/\sqrt2]\) for the
outer unit's coordinate halfwidth. Then

\[
C_y\ge b+1/2+h,
\qquad C_x\ge a(1+1/(2b))-h.
\tag{7}
\]

If \(b\ge a/2\), the squared lower bound in (7) increases with
\(h\): half its derivative at the lower endpoint is at least
\(1/2-(a-b)>0\). It is therefore at least

\[
F_U=\left(a(1+1/(2b))-1/2\right)^2+(b+1)^2
\ge\frac1{16b^2}+(b+1)^2>M^2.
\tag{8}
\]

The last strict inequality is the elementary estimate (3) in
`C7_OUTSIDE_INNER_RAY_WITNESS.md`; its proof gives the stronger bound
\(58/25\). If \(b\le a/2\), both lower coordinates in (7) are
positive, and their sum is at least

\[
a+b+1/2+a/(2b)\ge9/4.
\]

For the last inequality put \(q=a/b\ge2\) and use \(a\ge1/2\):
the sum is at least \(1+(q+1/q)/2\ge9/4\). Thus
\(|C|^2\ge81/32>M^2\), again impossible. Negative coordinate
normals cannot separate an outgoing ray point.

### 2.2. A leftward mixed-sign boundary-owned normal

For \(n=(-v,u)\), \(m=(u,v)\), put \(t=v/u<b/a\). The
unclipped candidate from the exact ray-strip expression is

\[
C_* =\lambda(a,b)+(n-m)/2,
\quad \lambda=\frac{b+1/2+(1/2-a)t}{b-at},
\quad\lambda'=\frac{a+b}{2(b-at)^2}.
\]

Its coordinate derivatives are strictly positive, with lower bounds

\[
(C_*)_x'\ge\frac{a(a+b)}{2b^2}-\frac12>0,
\quad
(C_*)_y'\ge\frac{a+b}{2b}-\frac1{\sqrt2}>0.
\]

Both initial coordinates are positive. This also verifies that the
tangential clipping is inactive. The resulting norm is at least
\(F_U>M^2\), so this entire sign case is impossible.

### 2.3. Positive-quadrant boundary-owned normals

Write \(n=(u,v)\), \(m=(-v,u)\), \(u,v\ge0\). We claim
\(v<1/20\). If \(v\ge1/20\) and \(u\ge2/3\), concavity
on \(v\in[1/20,\sqrt5/3]\) gives

\[
H\ge u+v/2>61/60,
\]

by the two endpoint values, contrary to (4). Hence \(u<2/3\).

If \(u\le1/3\), then \(v\ge2\sqrt2/3\), and

\[
av-bu\ge v/2-3u/8>41/120,
\qquad \lambda\ge1+1/(2a)>9/5.
\]

It follows that \(|\lambda(m\cdot z)|>123/200>3/5\), again
contradicting (4).

It remains to consider \(1/3\le u<2/3\). Put \(w=u+v\).
Concavity gives \(w>5/4\). If
\(b\ge a(v-u)/w\), then

\[
H\ge a/w+w/2\ge\tfrac12(w+w^{-1})
>41/40>61/60,
\]

which is impossible. Thus \(av-bu>au+bv>0\), and

\[
|\lambda(m\cdot z)|>H\ge u+v/2
>1/3+\sqrt5/6>3/5,
\]

the final contradiction. This proves \(v<1/20\).

Since \(1-u\le v^2\), \(a+1/2<2\), and
\(b+1/2\ge1/2\), one has \(H\ge a+1/2\), hence
\(n\cdot C\ge a+1\ge3/2\). Equation (3) therefore gives

\[
C_x\ge u(n\cdot C)-v|m\cdot C|
>\frac32\frac{399}{400}-\frac1{20}\frac{91}{1200}
>36/25.
\tag{9}
\]

### 2.4. Downward mixed-sign boundary-owned normals

Let \(n=(u,-v)=(\cos\varphi,-\sin\varphi)\),
\(m=(v,u)\). Put \(g=\lambda(av+bu)>0\). While
\(0\le\varphi\le\pi/4\), differentiation gives

\[
g'=\lambda'(av+bu)+H,
\qquad \lambda'=\frac{a+b}{2(au-bv)^2}>\frac{13}{10}.
\]

For the last bound use \(a\le k<13/25\), \(b\ge3/16\):
\(\lambda'\ge1/(2a)+3/(32a^2)>7075/5408>13/10\).
Also \(av+bu\ge b\) and \(H\ge u\ge1/\sqrt2>7/10\).
Consequently \(g'>15/16\). The function \(g\) continues to
increase on its whole domain \(au-bv>0\); hence (4) first rules
out \(\varphi\ge\pi/4\). At zero,

\[
g(0)=b(1+1/(2a))>153/416.
\]

Together with (4), the derivative bound yields

\[
\varphi<\frac{16}{15}\left(\frac{691}{1200}-\frac{153}{416}\right)
=\frac{6491}{29250}<\frac9{40}.
\tag{10}
\]

Using (3), \(\cos\varphi\ge1-\varphi^2/2\), and
\(\sin\varphi\le\varphi\), we obtain the actual-center bound

\[
C_x=u(n\cdot C)+v(m\cdot C)
>\frac32\frac{399}{400}\left(1-\frac{81}{3200}\right)
-\frac{91}{1200}\frac9{40}
=\frac{3689763}{2560000}>\frac{36}{25}.
\tag{11}
\]

Both-negative normals have \(n\cdot z\le0\) and are impossible.
This exhausts all separator owners and signs and proves (6).

## 3. The ray witness is the extracted far-face square

The cap \(D_{M^2}\cap\{x\ge36/25\}\) lies in the disk centered
at \((36/25,0)\) of radius
\(\sqrt{M^2-(36/25)^2}<1/2\). Its diameter is therefore less
than one. Two physical boundary units cannot have centers there,
because their open radius-half inscribed disks would intersect.

The outward middle-face center has first coordinate at least \(a+1\),
so it is in this cap. By (6), every outgoing ray witness is the same
actual boundary unit. Reflection preserves this conclusion for an
inner center \((a,-b)\) satisfying (5).

## 4. The full right-outside branch enters the witness domain

Suppose \(a:=\xi\ge1/2\). The outside-face theorem gives
\(|\eta|<3/8\), and the extracted right center has own normal
coordinate at least \(3/2\). Thus

\[
|\eta+r|<\sqrt{M^2-9/4}<9/40.
\tag{12}
\]

If \(\eta\ge0\), the actual inner-pair separation and both main
coordinate bounds give

\[
(1/2+\eta)\tau<e,
\quad r>1/2-3\tau/2>1/2-3e>9/40,
\]

contradicting (12). Therefore \(\eta=-b\) with \(0<b<3/8\).
The same pair inequality now reads

\[
\tau<\frac{e}{1/2-b}.
\tag{13}
\]

Equations (1), (12), and (13) imply

\[
b>11/40-\frac{3e}{2(1/2-b)}.
\tag{14}
\]

If \(b\le3/16\), the product
\((1/2-b)(11/40-b)\) is at least \(7/256\), whereas (14)
would make it less than \(3e/2=121/4800<7/256\). This is
impossible. Hence \(b>3/16\), and the whole right-outside branch
lies in the domain (5).

## 5. A signed height inequality gives the contradiction

Reflect the inner own frame vertically. The inner center is now
\((a,b)\), and the extracted far center is

\[
C_R=(a+1+\varepsilon,b-r).
\]

Section 3 says this same unit meets the outgoing ray. Since \(a>b\),
that ray first leaves the inner square on its right face, at height
\(b(1+1/(2a))\). If \(h_S\) is either coordinate halfwidth
of the actual outer square, ray membership therefore gives

\[
b-r+h_S\ge b(1+1/(2a)),
\qquad r\le h_S-b/(2a).
\tag{15}
\]

In fact \(h_S<3/5\). The center has first coordinate at least
\(3/2\) and second coordinate of absolute value less than \(9/40\),
so the sine of its radial angle from this first axis is less than
\(3/20\). By Section 1 an own side axis differs from that radial
direction by an angle with sine less than \(1/20\). The resulting
own-frame sine is less than \(1/5\); the total angle is less than
\(\pi/4\). Thus its halfwidth is less than \((1+1/5)/2=3/5\).
Equation (15) gives

\[
r<\frac35-\frac{b}{2k}.
\tag{16}
\]

On the other hand, (1) and (13) give

\[
r>\frac12-\frac{3e}{2(1/2-b)}.
\tag{17}
\]

These bounds are incompatible throughout \(3/16\le b\le3/8\).
Indeed the function

\[
f(b)=\frac{b}{2k}-\frac1{10}-\frac{3e}{2(1/2-b)}
\]

is concave and has the positive endpoint values

\[
f(3/16)=\frac{4109}{5581500}>0,
\qquad f(3/8)=\frac{136499}{2232600}>0.
\]

Thus the lower bound in (17) strictly exceeds the upper bound in (16).
This proves the theorem for the entire right-outside branch. The
exhaustive outside-coordinate cover in
`C7_OUTSIDE_INNER_RAY_WITNESS.md`, Section 4, leaves exactly (2),
with the original left-owned separating axis retained.

No circle-load positivity, regularity, common square orientation,
numerical pose subdivision, Lean compilation, or CI is used in this
branch theorem. The positive-C7 capacity parent remains open in the
asymmetric sector (2).
