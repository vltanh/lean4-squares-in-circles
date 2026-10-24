# Distinct triangle articulations cannot carry a D leaf and an S leaf

**Status: complete exact hand proof; root and independent full hand audits passed.**
In the explicit window

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\tag{1}
\]

no selected positive component can be a triangle A,B,C with a radial
D leaf at A and a radial S leaf at B. The proof covers the entire
mixed-leaf distinct-articulation layout, including parallel forces at
C, both physical C corner counts, arbitrary common normals and every
shared-side mean. It excludes the five-body core itself and retains
all four additional packing squares.

## 1. Whole-family domain and positive concurrence

The domain theorem `TRIANGLE_DISTINCT_LEAVES_DOMAIN.md` already
excludes R<=sqrt(17)/2 and H=0. Hence it suffices to work in

\[
 R>\frac{\sqrt{17}}2,\qquad H\ne0,
 \qquad d=\sqrt{R^2-\tfrac14}-1,
 \qquad \delta=d-1<\frac1{60}.
\tag{2}
\]

Rotate the D leaf east and put r=R-sqrt(2), s=1-r. Its full
articulation domain is

\[
             A=[-s,r]\times[t-1/2,t+1/2],\qquad |t|<1/2.
\tag{3}
\]

We will only need the loose exact inequalities

\[
                     r>\frac12,\qquad s>\frac3{10}.
\tag{4}
\]

The second follows from r<7/10, itself a consequence of
R<21/10 and sqrt(2)>7/5.

B is an S articulation, avoids zero, and meets the disk of radius
delta. Let n=(n_x,n_y) be the actual unit normal on AB, directed from
A to B. The supporting-half-plane conditions and a point of B of
norm at most delta imply

\[
                           h_A(n):=\max_{x\in A}n\cdot x\le\delta.
\tag{5}
\]

The cycle force lines at A cannot be parallel. If they were, force
balance with its eastward leaf would make the AB normal horizontal.
But either horizontal support value of A is at least min(s,r)>3/10,
contrary to (5). Therefore the complete port-orientation theorem
`TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md` applies at A: its
two cycle force lines intersect at

\[
                              q_A=(q,0),\qquad q>0.
\tag{6}
\]

That theorem retains the full parallel radial-S chart at C. No
nonparallel or unique-corner premise at C is being added here.

## 2. The contact with B is above A and has no leftward component

Because zero is in A's open interior, its two coordinate support
contributions in any direction are nonnegative. Equations (4)--(5)
give

\[
                         |n_x|<\frac1{18}.
\]

Thus n_y is nonzero. Reflect vertically so n_y>0; positivity of q in
(6) is preserved by this reflection. Put epsilon=t+1/2, so A's top
side is y=epsilon and 0<epsilon<1. Then

\[
 n_y>\frac{17}{18},\qquad
 \varepsilon n_y\le h_A(n)\le\delta,
 \qquad 0<\varepsilon<\frac3{170}.
\tag{7}
\]

Suppose n_x<0. Its support point on A is the unique northwest vertex
P=(-s,epsilon). The normal line through P meets y=0 at

\[
 q=-s-\varepsilon\frac{n_x}{n_y}
   <-\frac3{10}+\frac3{170}\frac1{17}<0,
\tag{8}
\]

contrary to (6). Hence

\[
                              n_x\ge0,\qquad n_y>0.
\tag{9}
\]

If n_x>0, the AB application is the northeast vertex. If n_x=0,
its actual application may be any permitted top-side mean. Both
are retained by the support value

\[
                           h_A(n)=r n_x+\varepsilon n_y.
\tag{10}
\]

## 3. A directional support-span lemma

**Lemma 3.1.** Let a unit square T have a minimum support point p
for a nonzero normal m. If u is a unit vector and m dot u<0, then

\[
                       \max_{x\in T}u\cdot(x-p)<1.
\tag{11}
\]

*Proof.* If p is a vertex, write
\(T=p+[0,1]w_1+[0,1]w_2\) with orthonormal inward axes.
The minimum-support condition puts m in their nonnegative cone.
Since m dot u<0, at least one of u dot w_1,u dot w_2 is negative.
Thus the positive u-span is at most the other positive component.
It is strictly less than one: equality would force u to be exactly
the other axis, making m dot u nonnegative.

If p is side-interior, one inward axis is parallel to m and has
negative u-component. Only the tangential interval can contribute to
the positive u-span. Its whole length is one and its projection has
absolute value strictly less than one, since u has a nonzero normal
component. The same argument includes side endpoints. These are all
support-point types. \(\square\)

## 4. C cannot reach B

Let m be the actual unit normal from A to C. Force balance at A has
positive coefficients

\[
                        \alpha e_x+\mu n+\nu m=0.
\]

Equation (9) forces both components of m to be strictly negative.
Consequently its unique support point on A is the southwest vertex

\[
                              Q=(-s,\varepsilon-1).
\tag{12}
\]

The square C has Q as a minimum-m support point, and m dot n<0.
Lemma 3.1 therefore gives

\[
                      \max_{x\in C}n\cdot x<n\cdot Q+1.
\tag{13}
\]

But (10)--(12), s+r=1, and n_x,n_y nonnegative imply

\[
 h_A(n)-n\cdot Q=n_x+n_y\ge1.
\tag{14}
\]

Every point of B lies in n dot x>=h_A(n), whereas (13)--(14)
place every point of C strictly below that supporting line. Thus B
and C are closed-disjoint, contradicting their positive triangle
contact.

This proves the entire D/S distinct-articulation exclusion. The
unit-square argument does not require a side owner for either cycle
normal, and (10) explicitly retains the vertical shared-side means.
Together with the earlier D/D domain exclusion, only the full S/S
distinct-articulation family remains for C1.3.b2. No completion
capacity, numerical sample, Lean compilation, or CI is used.
