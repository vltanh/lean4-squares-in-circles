# A three-boundary path makes an obtuse angle at its middle center

Date: October 28, 2026.

**Status: complete fresh force-free hand theorem, saved for full
independent and root review.**

Let A,B,C be three distinct actual interior-disjoint unit squares in
the disk of radius R, where

\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

Suppose all three physically touch the circle and B,C each physically
touch A. There is no force, load-weight, selected-normal or degree
premise. Write their actual centers as a,b,c.

**Theorem.**

\[
                            (b-a)\cdot(c-a)<0.
\tag{2}
\]

In particular the two center displacements cannot lie in the same
closed coordinate quadrant with positive scalar product. This is a
statement about the actual centers, not an assertion that their two
contact normals must be obtuse.

## 1. Complete angular and radial inputs

The degree-free physical theorem `CIRCLE_CONTACT_ANGULAR_ORDER.md`
gives, with respect to the unchanged circle origin,

\[
              \frac54<|a|,|b|,|c|<\frac{61}{40}.
\tag{3}
\]

Every two distinct physical boundary-center directions have minor
separation greater than pi/5. Each actual boundary contact has minor
separation less than 2pi/5. The two contact directions at a must
therefore be on opposite sides of its radial direction: if they were
on the same side, their two angles from a would both belong to
(pi/5,2pi/5), and their difference would be less than pi/5, contrary
to the pair separation of b and c.

Choose orthonormal e,f, with a=r e, so that

\[
 b=s(\cos\alpha\,e+\sin\alpha\,f),\qquad
 c=t(\cos\beta\,e-\sin\beta\,f),
 \qquad \frac\pi5<\alpha,\beta<\frac{2\pi}5.
\tag{4}
\]

Here r,s,t all obey (3). No force-resultant direction or physical
circle-corner mask has replaced a center direction.

## 2. Two uniform elementary trigonometric inequalities

For every theta in [pi/5,2pi/5],

\[
                     \cos\theta<\frac{13}{16},
             \qquad \sin\theta+\cos\theta>\frac54.
\tag{5}
\]

The first follows from
cos(pi/5)=(1+sqrt(5))/4<13/16, since sqrt(5)<9/4.
For the second, sin(theta)+cos(theta) is strictly concave on this
interval and is bounded below by the smaller endpoint value.
At pi/5, sin(pi/5)>1/2 and cos(pi/5)>3/4. At 2pi/5,

\[
 \cos(2\pi/5)=\frac{\sqrt5-1}{4}>\frac3{10},\qquad
 \sin^2(2\pi/5)=\frac{5+\sqrt5}{8}>\left(\frac{19}{20}\right)^2.
\tag{6}
\]

These last bounds use sqrt(5)>11/5 and sqrt(5)>111/50 respectively.
Both are strict exact comparisons: their squared reserves are 4/25
and 179/2500. Thus the endpoint sum is greater than
3/10+19/20=5/4, proving (5). The upper radical comparison has
squared reserve 1/16.

## 3. Each displacement has a larger tangential than radial component

Set

\[
          u=r-s\cos\alpha,\quad v=r-t\cos\beta,
       \qquad p=s\sin\alpha,\quad q=t\sin\beta.
\tag{7}
\]

The first inequality in (5) and (3) imply u,v>0, since

\[
           \frac54-\frac{61}{40}\frac{13}{16}
                         =\frac7{640}>0.
\tag{8}
\]

The second inequality in (5) gives p>u and q>v. For example,

\[
 s(\sin\alpha+\cos\alpha)>\frac{25}{16}
              >\frac{61}{40}>r,
 \qquad \frac{25}{16}-\frac{61}{40}=\frac3{80}>0.
\tag{9}
\]

Equations (4),(7) now read b-a=-u e+p f and c-a=-v e-q f.
Their scalar product is uv-pq<0, proving (2).

## 4. Exact scope and pin

All inequalities are strict throughout the whole closed radius window.
Every physical circle mask and every contact endpoint is retained.
The theorem permits arbitrary positive degrees, zero individual
circle weights and additional actual packing units. It does not need
global force balance, an unbroken positive graph path, or any
equation at the middle square.

The sole substantive imported physical theorem is the whole
`CIRCLE_CONTACT_ANGULAR_ORDER.md`, SHA-256

    2625b3a2b730525a6397bc90232e78c5e1aac8091381c1f5e5fc8a71ef1da449.

Only its complete Sections 1--3 are used: center annulus, pair
separation and contact-angle upper bound. All new radical and
rational comparisons in Sections 2--3 were recomputed with exact
Fraction arithmetic during writing. There is no numerical
pose, force simplification, changed normal, Lean/CI computation or
metadata promotion in this source.
