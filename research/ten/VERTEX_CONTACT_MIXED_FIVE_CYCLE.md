# Distinct vertex contacts on a uniquely loaded central square

**Status:** independently reviewed exact conditional hand proof.
This treats a further subcase of the three-loaded five-cycle. It does not
treat a central square with two circle vertices, or arbitrary side-interior
contact points.

Consider a whole positive component

\[
                           A-U-C-V-B-A
\]

with precisely A,B,C loaded, where U,V are unloaded degree-two
transmitters. Assume \(79/40\le R\le3/\sqrt2\), and suppose that C
has a unique circle vertex and that both transmission contacts on C are
vertices. The transmission widths W_1,W_2 belong to
\(\{1,\sqrt2\}\), by
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

**Theorem.** This configuration is impossible.

The common-contact case is already excluded in
[COMMON_CORNER_SIDE_TRANSMISSIONS.md](COMMON_CORNER_SIDE_TRANSMISSIONS.md)
and
[COMMON_CORNER_MIXED_TRANSMISSIONS.md](COMMON_CORNER_MIXED_TRANSMISSIONS.md).
We prove the remaining distinct-vertex cases below.

## 1. Two elementary support facts

No two interior-disjoint unit squares contained in the disk can share a
point of its boundary circle. Such a point would be a vertex of each
square, by strict convexity of the disk. If p is that point and e is one
of its unit incident edge vectors, containment gives

\[
                     2p\cdot e+1\le0.
\]

Thus each square's closed pi/2 tangent cone at p lies strictly inside
the open inward half-plane. Two such cones cannot have disjoint interiors:
their total angular width is pi, while their combined angular span inside
that open half-plane is strictly less than pi. Local interior overlap
would follow. In particular, a circle vertex of C cannot be either
transmission contact.

We also use the following elementary coordinate bounds. A unit square
supported at Q with inward normal \((-p,-q)\), where
\(p\ge q\ge0\) and \(p^2+q^2=1\), can extend at most q to the
right of Q. A unit square supported at Q with inward normal \((r,-s)\),
where r,s>=0 and r²+s²=1, can extend at most s to its left. For vertex
support, at most one incident edge can point in the relevant horizontal
direction, and its horizontal component is at most the stated bound.
For side support, that component of the unit tangent is exactly the
stated bound, while inward normal translation moves the other way.

Rotate and reflect C's own axes so its center is (a,b), with a,b>0.
Its unique circle vertex is

\[
                        (a+1/2,b+1/2),
 \qquad R^2=(a+1/2)^2+(b+1/2)^2.                           \tag{1}
\]

Write its positive circle-force coefficient as lambda. Outgoing contact forces are
the negatives of the actual forces into C. Their sum is
\(-\lambda(a+1/2,b+1/2)\), and their total torque about the origin
is zero.

## 2. Adjacent contacts on the bottom edge

Suppose the two contact vertices are

\[
             P_L=(a-1/2,b-1/2),\qquad P_R=(a+1/2,b-1/2).
\]

Their outgoing forces have the forms

\[
                         f_L=(-u,-v),\qquad f_R=(w,-z),
\]

where u,v,w,z>=0 and each force is nonzero. Force and torque balance
give the exact identities

\[
 v=\lambda(a+1/2),\qquad
 z=\lambda(b-a),\qquad
 u=v+w.                                                    \tag{2}
\]

Indeed force balance first gives u−w=lambda(a+1/2) and
v+z=lambda(b+1/2). Substitution into the torque equation

\[
 -(a-1/2)v+(b-1/2)u-(a+1/2)z-(b-1/2)w=0
\]

gives v−z=lambda(2a−b+1/2), which yields (2). In particular b>=a,
and the left unit transmission direction is \((-p,-q)\) with p>=q>0.
Write the right direction as \((r,-s)\), with r,s>=0.

The endpoint support facts show

\[
 \begin{aligned}
 \max_x A&\le a-1/2-W_1p+q\le a-1/2,\\
 \min_x B&\ge a+1/2+W_2r-s\ge a-1/2.                       \tag{3}
 \end{aligned}
\]

If w>0, then r>0 and the second bound is strict, contradicting A--B
contact. Therefore w=0. Since the right force is nonzero, z>0, and its
direction is vertically down. The first bound in (3) is strict unless

\[
                  W_1=1,\qquad p=q=1/\sqrt2.              \tag{4}
\]

Even under (4), contact between A and B requires equality in both support
bounds. The only way to attain the full rightward displacement 1/sqrt(2)
from the left support point is a unit edge perpendicular to
\((-1,-1)/\sqrt2\), starting at that support point. Consequently A is
a diamond, with center

\[
                   c_A=(a-1/2-1/\sqrt2,
                         b-1/2-\sqrt2).                   \tag{5}
\]

Similarly B must attain the full leftward displacement one from a support
point with inward normal (0,−1). It is an axis-parallel unit square with
that point as its upper-right vertex, and has center

\[
                             c_B=(a,b-1-W_2).              \tag{6}
\]

Since b<R−1/2<2 and W_2>=1, the second coordinate of c_B is negative.
Loading of both B and C therefore yields

\[
 (a+1/2)^2+(b+1/2)^2
   =(a+1/2)^2+(3/2+W_2-b)^2,
\]

so

\[
                              b=(1+W_2)/2.                \tag{7}
\]

Neither allowed width is compatible with loading of A.

* If W_2=1, then b=1 and a<=1. Equation (1) and R>=79/40 give
  a>31/40. Formula (5) now gives |(c_A)_x|<1/2 and
  |(c_A)_y|<1. Every vertex of A consequently has norm less than
  \(\sqrt5/2+\sqrt2/2<9/8+3/4=15/8<R\).
* If W_2=sqrt(2), then b=(1+sqrt(2))/2 and a<=b. One also has a>1/4:
  otherwise (1) would give
  \(R^2< (3/4)^2+(7/4)^2=29/8<(79/40)^2\).
  Formula (5) gives \(-1<(c_A)_x\le0\) and
  \((c_A)_y=-1/\sqrt2\). Its center norm is less than
  \(\sqrt{3/2}<49/40\), so every vertex has norm less than
  \(49/40+3/4=79/40\le R\).

Both alternatives contradict A's positive circle load. This excludes
the adjacent bottom contacts. Adjacent left contacts follow by exchanging
the two coordinate axes. Adjacent top or right contacts are impossible
already by force balance: their outward forces have nonnegative second
or first component respectively, while the required force sum has both
components strictly negative.

## 3. The two non-circle opposite corners

The only opposite pair avoiding C's circle vertex is

\[
             P_L=(a-1/2,b+1/2),\qquad P_R=(a+1/2,b-1/2).
\]

Write their outgoing forces as \((-u,v)\) and \((w,-z)\), with
nonnegative components. Force balance gives

\[
 u-w=\lambda(a+1/2),\qquad
 z-v=\lambda(b+1/2).
\]

Substitute these into the torque equation

\[
 (a-1/2)v+(b+1/2)u-(a+1/2)z-(b-1/2)w=0.
\]

It simplifies to w=v. Hence u>v. The left transmission direction is
\((-p,q)\) with p>q>=0. Reflection of the support bound from Section 1
shows

\[
                        \max_x A
                        \le a-1/2-W_1p+q<a-1/2.
\]

The right outgoing direction has the form (r,−s), and the same estimate
as in (3) gives \(\min_x B\ge a-1/2\). Again A and B cannot touch.

All distinct vertex pairs are now excluded. Therefore if C has a unique
circle vertex in a remaining mixed five-cycle, at least one of its two
transmission contacts must lie in the relative interior of a side.
