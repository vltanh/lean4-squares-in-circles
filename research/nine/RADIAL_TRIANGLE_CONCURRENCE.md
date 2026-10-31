# Positive radial concurrences in a physical triangle with nonzero cycle moment

**Status: complete hand structural theorem; root and separate
independent full hand audits passed.**

Let three interior-disjoint unit squares A,B,C physically touch
pairwise, with positive forces on the three triangle edges. At
each body retain all its other forces in one nonzero vector
\(F_A,F_B,F_C\). Suppose the origin moment of each of these
three aggregates is zero, and the full force equations give
\[
                 F_A+F_B+F_C=0,
\tag{1}
\]
with the three directions noncollinear. No degree assumption
beyond these actual aggregate equations is imposed by this
lemma. In its applications the aggregates are genuine radial
bridge forces or actual circle-load vectors.

Orient the cycle A to B to C to A. Its directed positive
edge-force vectors are \(f_{AB},f_{BC},f_{CA}\), so
\[
 \begin{split}
 F_A&=f_{CA}-f_{AB},\\
 F_B&=f_{AB}-f_{BC},\\
 F_C&=f_{BC}-f_{CA}.
 \end{split}
\tag{2}
\]
Zero external origin moments make the three directed cycle
moments equal. Assume their common value satisfies
\[
                              \mathcal H\ne0.
\tag{3}
\]

**Theorem.** At every body whose two cycle force lines are
nonparallel, those lines meet at a strictly positive multiple
of that body's actual external resultant:
\[
                             q_i=\tau_i F_i,\qquad\tau_i>0.
\tag{4}
\]
The conclusion retains all contact owners and actual shared-side
means. A body whose two cycle forces are parallel is not
assigned a fictitious concurrence.

## 1. The purely physical proper-port fact

For any three pairwise-touching unit squares and any two
nonparallel actual outward normals n,m from one square, their
lines meet at q with
\[
                            P=q+a n,\qquad Q=q+b m,
                                \qquad a,b\ge0.
\tag{5}
\]
This is the geometric lemma proved in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2.
It needs no load or circle hypothesis at that square.
For completeness, its complete feature cover is:

* If one normal is a square side axis, the unit-triangle
  side-normal lemma makes the other normal nonobtuse to it.
  Intersecting their lines in the corresponding common-side
  frame gives both parameters in (5) nonnegative, including
  every side mean and endpoint.
* Otherwise both normals strictly expose vertices. Opposite
  vertices would put the other two squares beyond a normal
  gap at least1, whereas their strict transverse support span
  is below1; so they could not touch. Equal vertices give
  a=b=0. Adjacent vertices give positive intersection parameters.
  For \(P=(0,1),Q=(0,0)\),
  \(n=(-u,v),m=(-w,-z)\), the exact parameters are
  \(a=w/(vw+uz)\), \(b=u/(vw+uz)\).

This exhausts all actual features without selecting or replacing
a normal. Also, if the two cycle normals at any body are
parallel, they must have the same outward sign: opposite
supports of a unit square separate the two other squares
by a positive width, contradicting their physical contact.

## 2. All three cycle pairs are nonparallel

Taking the origin moment of (2) at the intersection q_i gives
\(\det(q_i,F_i)=0\). Hence
\[
                               q_i=\tau_i F_i
\tag{6}
\]
for a real number \(\tau_i\). The scalar is nonzero because
\(\mathcal H\ne0\): otherwise both cycle lines at that body
would pass through0 and have zero moment.

At each actual edge, (5) for its two endpoints gives
\[
 \begin{split}
 q_B-q_A&=\lambda_{AB}f_{AB},\\
 q_C-q_B&=\lambda_{BC}f_{BC},\\
 q_A-q_C&=\lambda_{CA}f_{CA},
 \end{split}\qquad \lambda_{AB},\lambda_{BC},\lambda_{CA}>0.
\tag{7}
\]
Initially each coefficient is nonnegative, after dividing
the sum of the two proper-port lengths by the positive force
magnitude. Equality would make the two concurrence points
equal. Since the corresponding external directions are
nonparallel, (6) would make both points0, contrary to (3).
This proves the strict signs in (7).

Put
\[
                         L=\lambda_{AB}+\lambda_{BC}+\lambda_{CA}.
\]
Substitute \(f_{BC}=f_{AB}-F_B\) and
\(f_{CA}=f_{AB}+F_A\) into the sum of (7). It gives
\[
                      f_{AB}
                  =\frac{\lambda_{BC}F_B-\lambda_{CA}F_A}{L}.
\tag{8}
\]
The first identity in (7), together with (6), now gives
\[
 \tau_B F_B-\tau_A F_A
       =\frac{\lambda_{AB}\lambda_{BC}}L F_B
         -\frac{\lambda_{AB}\lambda_{CA}}L F_A .
\]
The two vectors \(F_A,F_B\) are independent by (1) and
noncollinearity. Comparing their coefficients yields
\[
 \tau_A=\frac{\lambda_{AB}\lambda_{CA}}L>0,\qquad
 \tau_B=\frac{\lambda_{AB}\lambda_{BC}}L>0,\qquad
 \tau_C=\frac{\lambda_{BC}\lambda_{CA}}L>0.
\tag{9}
\]
This proves (4) in the whole nonparallel domain.

## 3. One cycle pair is parallel, with its actual means

There cannot be two parallel cycle pairs. Two such pairs
would force all three edge directions to be collinear,
making all three vectors in (2) collinear, contrary to
the hypothesis.

Let K be the unique parallel body, and I,J the other two.
Rotate so \(F_K\) points east. Section 1 shows that its two
outward cycle normals both equal \(-e_x\). Their actual
applications lie on one common support line:
\[
                         P_I=(h,y_I),\qquad P_J=(h,y_J).
\tag{10}
\]
Write their positive magnitudes as \(\mu_I,\mu_J\).
The zero external moment at K gives
\[
                         \mu_I y_I+\mu_J y_J=0.
\tag{11}
\]
The nonzero common cycle moment makes both heights nonzero,
so they have opposite signs. Relabel I,J if necessary to
have \(y_I<0<y_J\).

At I,J their normals toward K are \(e_x\). The proper-port
fact (5) therefore puts their genuine nonparallel concurrences
at
\[
                     q_I=P_I-a e_x,\qquad
                     q_J=P_J-b e_x,\qquad a,b\ge0.
\tag{12}
\]
Their heights are exactly \(y_I,y_J\). For the force f
directed from I to J, the two proper-port relations on that
edge give
\[
                              q_J-q_I=\lambda f,\qquad\lambda>0.
\tag{13}
\]
Strict positivity follows from the distinct heights in (12).
Thus \(f_y>0\).

The complete force equations at the two remaining bodies are
\[
                F_I+\mu_Ie_x+f=0,\qquad
                F_J+\mu_Je_x-f=0.
\tag{14}
\]
Consequently \((F_I)_y<0<(F_J)_y\). Each q_i is a real
multiple of F_i by the same zero-moment calculation as in
(6), and its nonzero height has the same sign as that
resultant. Hence both multiples are strictly positive.

This proves (4) for every nonparallel body, retaining the
entire parallel-body mean interval and without assigning
a concurrence to K.

## 4. Exact limitations

The zero-moment alternative \(\mathcal H=0\) remains outside
this theorem and must be dealt with in its application.
Likewise the three external resultants must be nonzero and
noncollinear. They are actual aggregates, not redistributed
fractions of a higher-degree body's circle force.

The argument is algebraic after the complete physical
proper-port lemma. It uses neither a chosen drawing of
straight contact chords nor a presumed concurrence inside
a square. No circle-mask restriction, new point-normal
selection, numerical pose sampling, Lean or CI is used.

