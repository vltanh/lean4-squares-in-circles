# A two-edge arm and a direct leaf at different triangle roots are impossible

**Status: complete whole-attachment hand exclusion; root and separate
independent full hand audits passed.** Work in
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The exact positive graph is the triangle A,B,C, the two-edge arm
\(A-U-L_A\), and a direct leaf \(L_B\) at B. The six bodies
leave three arbitrary physical squares, which remain in place.

**Theorem.** This entire distinct-root arm-and-leaf attachment is
impossible. Both genuine leaf types, both original transmitter
widths, the complete physical C circle mask, all owners and all
actual shared-side means are included. A and B retain their exact
degree-three equations; no smaller-component exclusion is applied
after deleting either branch.

## 1. The full load, width and small-root domains

Put
\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 r=R-\sqrt2,\qquad
 \varepsilon=\max(d-1,0)<1/60.
\tag{2}
\]
The two leaves are loaded and radial S or D. U, as the central
neighbor of its genuine leaf, is physically circle-clear.
Its exact degree two therefore gives a normal transmitter of
width \(w\in\{1,\sqrt2\}\).

Rotate the arm leaf direction east. Its true leaf application is
\(r_Ae_x\), where \(r_A\in\{r,d\}\), and the actual other arm
application is
\[
                    p_{AU}=xe_x,\qquad x=r_A-w,
                     \qquad A\subset\{x_1\le x\}.
\tag{3}
\]
Here x is a scalar coordinate, and \(x_1\) denotes the first
coordinate of a variable point.

A D leaf with a diagonal transmitter is impossible: their
off-origin contact would be vertex/vertex with a radial normal,
excluded by the existing strict nonradial point-normal choice.
All three remaining arm alternatives satisfy
\[
             x\le d-1\le\varepsilon,\qquad
                    |x|<31/60<r.
\tag{4}
\]
For example, \(d>9/10\), \(\sqrt2<17/12\) give
\(d-\sqrt2>-31/60\); the other two alternatives are smaller
in absolute value. Also
\(r>67/120>31/60\), from
\(R\ge79/40\) and \(\sqrt2<17/12\).
These are the complete arm bounds of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Section 1.

Since A contains the point (3) of norm below r, it is physically
circle-clear. B is physically circle-clear by the central
endpoint theorem for its genuine leaf. C is loaded: an unloaded
degree-two transmitter cannot have its two neighbors A,B
physically touching.

Thus the full loaded set is exactly \(L_A,L_B,C\). Let their
nonzero circle-resultant vectors be \(F_A,F_B,F_C\), where the
first two subscripts indicate their branch roots. The actual
bridge cuts give
\[
                      F_A=\alpha e_x,\quad\alpha>0,\qquad
                         F_A+F_B+F_C=0.
\tag{5}
\]
The three resultant directions are distinct by the strict
boundary-resultant direction theorem. Hence they are
noncollinear, and any two are independent.

B meets the small disk \(D_\varepsilon\). For a D leaf B
contains0 in its interior. For an S leaf, its support point
is \(d e_B\), and the unit inward segment belongs to B.
This segment contains0 if \(d\le1\), or contains
\((d-1)e_B\) if \(d>1\). In every case
\[
                                B\cap D_\varepsilon\ne\varnothing.
\tag{6}
\]
In particular, if n is any actual A-to-B normal with application
P and supporting height \(h=P\cdot n\), then
\[
                                    h\le\varepsilon.
\tag{7}
\]

## 2. The zero common-moment alternative is impossible

Orient the triangle cyclically and call its common directed
origin moment \(\mathcal H\). The two bridge forces and the
circle force at C have zero origin moment, so the moment
is indeed common.

Suppose \(\mathcal H=0\). If C's two pair lines were
nonparallel, their intersection would be0. The general-neighbor
positive-concurrence calculation for a boundary unit excludes
this. Precisely, use the rectangle normal-line part of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, as explicitly
scoped in TRIANGLE_DISTINCT_LEAVES_DOMAIN.md, Section 2:
positivity of the concurrence uses genuine unit neighbors and
the width obstruction, not a boundary-neighbor premise.
That premise is needed only for the separate nonparallel-line
conclusion, which is not being imported here.

Therefore C's pair forces are parallel. The full parallel
boundary-square classification and outer-face width screen
make C radial S or radial D, with both neighbors at its inner
support. The D alternative gives the same inner vertex to
A and B. The selected off-origin nonradial convention would
put that vertex in the relative interior of a side of each
neighbor. Their inward half-planes would overlap.

For radial S, rotate its direction east. Its two actual means
have zero origin moment, so both are exactly \((d,0)\).
The two neighboring units must occupy the two left quadrants
at this inner-side-interior point. After reflecting if needed,
\[
              A=[d-1,d]\times[0,1],\qquad
              B=[d-1,d]\times[-1,0].
\tag{8}
\]
This retains endpoint means of the actual positive-length
shared sides.

At B, its two cycle outward forces point strictly east and
strictly north. Its genuine leaf resultant must consequently
point strictly southwest. It cannot be type D, whose direction
is a side axis of B. A type-S radial support in this strict
direction is its lower-left vertex \((d-1,-1)\). Its norm
would have to equal d, forcing
\[
                              (d-1)^2+1=d^2,
                  \qquad\hbox{hence }d=1.
\]
But the resulting radial vector is purely vertical, not
strictly southwest. This contradiction excludes the S
alternative too.

This local zero-moment argument uses only B's true direct leaf.
No direct-leaf formula is applied at the arm root A. We have proved
\[
                                  \mathcal H\ne0.
\tag{9}
\]

## 3. The actual A concurrence is positive when it exists

The hypotheses of RADIAL_TRIANGLE_CONCURRENCE.md now hold:
the three genuine external resultants (5) are nonzero and
noncollinear, each has zero origin moment, and (9) holds.
At every nonparallel cycle root its concurrence is a positive
multiple of its external resultant.

In particular, if A's two cycle lines are nonparallel,
\[
                                 q_A=(q,0),\qquad q>0.
\tag{10}
\]
Every actual triangle port on A lies in its outward-normal
direction from \(q_A\), by the purely physical proper-port
lemma of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2.

The structural theorem retains the full possibility that B
or C has parallel cycle forces. Its wall-mean proof applies
in that case; no concurrence or circle-weight normalization
is invented at the parallel body.

## 4. An aligned articulation cannot contact the central B

First suppose A is aligned with the arm and its cycle forces
are nonparallel. Write
\[
                       A=[x-1,x]\times[l,l+1],
                            \qquad l\le0\le l+1,
                       \qquad s=1-x\ge1-\varepsilon.
\tag{11}
\]
The inclusion of0 in the vertical interval follows from the
actual application (3), even when0 is an endpoint.

We exhaust the actual AB normal and feature.

If it is a left-axis normal, its supporting height is s.
If it strictly exposes either left vertex \(P=(-s,y)\), the
proper-port line through (10) gives
\[
            n=\frac{(-s-q,y)}{\sqrt{(s+q)^2+y^2}},\qquad
            P\cdot n
               =\frac{s(s+q)+y^2}{\sqrt{(s+q)^2+y^2}}\ge s.
\tag{12}
\]
For \(y\ne0\), squaring gives the strict positive surplus
\(y^2(s(s+2q)+y^2)\); for \(y=0\), equality is immediate.
Thus all left features violate (7), because
\[
                         s\ge1-\varepsilon>\varepsilon.
\tag{13}
\]

A right-axis AB normal would have zero vertical component.
The true A equation
\[
                         \alpha e_x+\mu n_{AB}+\nu n_{AC}=0
\tag{14}
\]
would make the other normal horizontal too, contrary to the
present nonparallel case.

For an A-owned top or bottom axis, the unit-triangle
side-normal lemma makes the other normal nonobtuse to it.
Their vertical components therefore cannot cancel in (14).
This excludes all such actual means, including side endpoints.

The only remaining AB alternative is a strictly exposed right
vertex. Its normal has positive first coordinate and a nonzero
vertical sign. Equation (14) forces the AC normal to have
negative first coordinate and the opposite nonzero vertical
sign. It would strictly expose the opposite left vertex.
The physical unit-triangle support-span lemma excludes two
opposite strictly exposed vertices, since B,C physically touch.

These cases exhaust the entire aligned A interface, without
assuming a frame or contact type at B.

## 5. A tilted articulation forces the far diagonal support

Suppose instead that A is tilted relative to the arm, while
its two cycle lines are nonparallel. Its rightmost point
\(p_0=(x,0)\) is its unique vertex. Choose inward orthonormal
side vectors u,v with
\[
 u_x=-a,\quad v_x=-b,\qquad a,b>0,\quad a^2+b^2=1,
           \qquad A=p_0+[0,1]u+[0,1]v.
\tag{15}
\]

If \(q>x\), the point \(q_A\) has both own coordinates
strictly negative relative to \(p_0\). Every actual port
P then has \(P-q_A\) with both own coordinates strictly
positive. The proper-port relation makes its outward normal
strictly positive in both coordinates. Both cycle contacts
would consequently be the single far vertex \(p_0+u+v\).
Their nonparallel lines would intersect at that vertex,
contrary to (10) and its negative first coordinate.
Thus
\[
                                0<q\le x.
\tag{16}
\]
In particular x is positive. The full arm cover (3)--(4)
then forces the S/width1 arm, with
\[
                          x=\delta=d-1,\qquad0<\delta<1/60.
\tag{17}
\]
In A's own coordinates \(q_A\) has entries
\[
                         a(\delta-q),\quad b(\delta-q),
                          \qquad 0\le\text{each}<\delta.
\tag{18}
\]

At the actual AB port P let
\(P-q_A=\ell n_{AB}\), \(\ell\ge0\).
Equation (7) and \(|q_A|\le\delta\) give
\[
              \ell=P\cdot n_{AB}-q_A\cdot n_{AB}\le2\delta.
\tag{19}
\]
Every far-coordinate face of A is at distance at least
\(1-\delta>2\delta\) from \(q_A\). Hence P lies on one
of the two coordinate-minimum faces near \(p_0\), or at
\(p_0\) itself. Its outward normal has both own components
nonpositive, with at least one strictly negative.

The arm force \(\alpha e_x\) has own components
\(-\alpha a,-\alpha b\). Equation (14) therefore forces
both own components of \(n_{AC}\) to be strictly positive.
Its actual support is the far vertex
\[
                                  P_F=p_0+u+v.
\]
The proper-port relation and (18) yield its support height
\[
 \begin{split}
 P_F\cdot n_{AC}
   &=|P_F-q_A|+q_A\cdot n_{AC}\\
   &\ge\sqrt2(1-\delta)-\delta
        >\frac43>d.
 \end{split}
\tag{20}
\]
For the strict rational comparison one may use
\(\sqrt2>7/5\) and \(\delta<1/60\), giving a bound
greater than \(34/25\).

But every contained unit lying beyond a supporting line
has supporting height at most d, by
OUTER_BRIDGED_TRIANGLE_EXCLUSION.md, Section 1.
Thus C cannot fit beyond (20). This excludes the entire
tilted articulation domain.

## 6. Parallel A forces and the whole-attachment conclusion

If the two A cycle normals are parallel, their sum is
\(-\alpha e_x\). They cannot have opposite outward signs,
because B,C touch and A has positive width. They must both
point west.

Consequently B lies beyond A's left support:
\[
                   x_1\le\min_A x_1\le x-1
                         \le\varepsilon-1<-\varepsilon.
\]
This contradicts (6). No A concurrence is used in this case.

Sections 4--6 exhaust every A frame and every parallel or
nonparallel cycle-force pair. Section 2 retained the full
zero-moment and physical C circle-mask cover. Thus the
entire length-two arm at A plus direct leaf at distinct root B
is excluded, with all three additional physical squares
still present.

No secondary minimizer, numerical pose sampling, replacement
of a shared mean, Lean compilation or CI is used.

