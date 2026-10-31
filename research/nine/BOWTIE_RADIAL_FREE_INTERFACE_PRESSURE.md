# A free articulation contact at a radial end-triangle tip has positive pressure

**Status: complete hand implication; root and separate independent full hand audits passed.**
Work in the declared radius window. Let A--B--C--A be an actual
unit-square triangle, with B,C positive degree-two loaded tips.
Suppose C has two physical circle corners and AC is a free
point-only vertex/vertex contact. Then, in the compatible selected
certificate,
\[
                            c_A\cdot(F_B+F_C)>0.
\tag{1}
\]
The statement retains all circle weights, owners, means and the
additional positive edges of A. If B also has two physical circle
corners, (1) follows from RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md.
We therefore assume throughout the proof that B has exactly one
physical circle corner.

## 1. The radial tip forces two distinct inner-vertex applications

Rotate and reflect so
\[
 C=[H,H+1]\times[-1/2,1/2],\qquad
 H=\sqrt{R^2-1/4}-1>9/10,
 \qquad Q=(H,1/2)=A\cap C.
\tag{2}
\]
A circle point cannot be shared, so this is one of the two inner
vertices of C. The strict free normal from A into C has the form
\[
                    m=(\cos\alpha,-\sin\alpha),
                             0<\alpha<\pi/2.
\tag{3}
\]
Its origin moment at Q is strictly negative. Since C's circle
forces have zero origin moment, its other positive contact must
have strictly positive moment when directed from B into C.

This eliminates C's upper tangential side and the upper inner
vertex Q, whose inward normals all have negative moment. The
outer side admits no contained unit beyond it: its support H+1
is greater than R-1. The outer vertices are circle points. A
radial-inner-side contact with a boundary B is excluded by
C7_FORCE_POLYGON.md, Lemma2.1.

The lower tangential side is impossible as well. Such a contact
would put B in y<=-1/2. But A has a minimum-(-m) support point
at Q, and (-m) dot (-e_y)=m_y<0. The strict support-span lemma
therefore gives
\[
                              \min_A y>-1/2,
\tag{4}
\]
preventing AB contact.

Consequently BC is a singleton at the other inner vertex
\[
                T=(H,-1/2),\qquad
                   g=(a,b),\quad a,b>0,\quad a^2+b^2=1,
\tag{5}
\]
where g points from B into C. It is not a C side axis. In
particular BC cannot be a positive-length shared side.

## 2. Singleton AB: both remaining normals have owners

If AB is a singleton, the two B applications are fixed points.
They cannot coincide in a positive star: the sole possible
coincident exception in GENERAL_FIXED_TIP_NORMAL_SELECTION.md
is a radial-D inner vertex of norm R-sqrt(2), and T is shared
by two boundary squares, so has strictly greater norm.

The same compatible finite selection therefore removes every
free AB or BC normal at B. Since g is not a C axis, B owns BC
and T is in the relative interior of a B side. Put
\[
 h=Jg=(-b,a),\qquad
 B=T-[0,1]g+[-s,1-s]h,
       \qquad0<s<1,\quad V=1-s.
\tag{6}
\]
The AB normal is owned by A or by B. Sections3--4 exclude both
alternatives. No force at A or choice of the two C weights is
used in those exclusions.

## 3. An A-owned AB axis would force H<1/2

Let P be the AB application. It is a B vertex and a relative
interior point of an A side. The triangle owned-normal lemma
makes that side one of the two sides incident to Q: m is strict
in the A vertex cone, so its scalar product with the AB axis
cannot vanish and must be positive. In particular |P-Q|<1.

Three B vertices are farther than1 from Q. In the g,h frame,
Q-T=(b,a). The vertices T-sh and T-g-sh have an h-distance
at least a+s, while T-g+Vh has a g-distance 1+b>1. For the
first vertex specifically, b^2+(a+s)^2>1. Thus
\[
                 P=T+Vh,\qquad t=|P-Q|<1.
\tag{7}
\]
The AB normal points strictly into B at this vertex, so write
\[
 n=-p g-q h,\qquad p,q>0,\qquad
             p=(V-a)/t,\quad q=b/t.
\tag{8}
\]
The formulas follow because n is perpendicular to the A side
PQ. They imply
\[
                             a<V<\min(2a,1).
\tag{9}
\]

Let mu,gamma>0 be the AB,BC magnitudes. B's circle force is
mu n-gamma g, negative in both own coordinates. Its unique
circle corner is therefore
\[
 z=T-g-sh=-Xg-Yh,
 \quad X=1-Ha+b/2>0,\quad Y=Hb+a/2+s>0.
\tag{10}
\]
Torque about z gives mu(q-p)=gamma s. The two coordinates
of its force equation then give
\[
                    \frac XY=\frac{b+aV-V^2}{sb}.
\tag{11}
\]
Substitute (10), s=1-V, and clear the positive denominators.
The exact result is
\[
 2Hb(a+b-V^2)=N,
 \quad N=b^2-ab-V-2aV+(3a+2)V^2-2V^3.
\tag{12}
\]
We prove
\[
 \begin{split}
 D_0&:=b(a+b-V^2)-N\\
    &=2ab+(1+2a)V-(3a+b+2)V^2+2V^3>0.
 \end{split}
\tag{13}
\]

If a>=1/6, the four cubic Bernstein coefficients of D_0 on
0<=V<=1 are
\[
 2ab,\quad 2ab+(1+2a)/3,\quad
 2ab+(a-b)/3,\quad 2ab+1-a-b.
\tag{14}
\]
They are all positive. For the third, multiply by3 and use
b(6a-1)+a>0. The last is (a+b)(a+b-1)>0. Since the Bernstein
basis is nonnegative and sums to1, (13) follows on the whole
interval.

If 0<a<1/6, use V<2a and b<=1 in (13) to get
\[
 D_0\ge2ab+V(1-4a-6a^2)>0,
\tag{15}
\]
because 1-4a-6a^2>1/6. This proves (13) throughout (9).
The quantity b(a+b-V^2) is positive, so (12)--(13) imply
H<1/2, contradicting (2).

## 4. A B-owned AB axis contradicts the unique tip's original forces

The two A applications P,Q are vertices. They cannot coincide:
the B half-plane and the A,C quadrants would fill a whole turn,
making AC a positive-length shared side. Opposite A vertices
are excluded by the support-span argument in
BOWTIE_TIP_OWNED_PRESSURE.md, Section1, which uses only the two
strict A vertex normals and the physical BC contact. Thus they
are adjacent and |P-Q|=1.

The AB axis cannot be parallel to g. Otherwise B's circle force
would be parallel to one of its side axes, whereas its unique
physical circle corner has nonzero components along both axes.
The remaining choices are +h and -h.

For n=+h, the AB point has the form P=T-sh-ell g with
0<ell<1. Then
\[
                     |P-Q|^2=(ell+b)^2+(s+a)^2>1,
\tag{16}
\]
which is impossible. Hence n=-h and
\[
 P=T+Vh-ell g,\quad0<ell<1,\qquad
 P-Q=-Lg-Kh,\quad L=ell+b,\quad K=a-V.
\tag{17}
\]
The A support condition for -h gives K>=0; also L>0 and
L^2+K^2=1. Equality K=0 would align the A and B frames at
their relative-side-interior B contact, making AB a shared
segment. It is excluded by the present singleton hypothesis.
Thus K>0. The two inward A axes at Q are
\[
                        -Lg-Kh,\qquad -Kg+Lh.
\tag{18}
\]

Write g=(cos(beta),sin(beta)), 0<beta<pi/2. The original free
normal m in (3), expressed in the g,h frame, is
(cos(alpha+beta),-sin(alpha+beta)). Its strict support at Q and
the first axis in (18) give
\[
                    \alpha+\beta<\arctan(L/K)<\pi/2.
\tag{19}
\]
Therefore the unit vector
\[
                            n_0=Kg-Lh
\tag{20}
\]
is an A side normal along PQ and is strictly inside C's inward
vertex cone at Q. Its angle below the positive x-axis is
arctan(L/K)-beta, which lies strictly between alpha and pi/2.
It is a valid auxiliary geometric support axis of the same two
fixed squares. It has not been substituted into the certificate.

We now use the following geometric content of
BOWTIE_MIXED_OWNER_PRESSURE.md, Section6.2. In the chart with an
A-owned side support at a vertex of a radial tip, the other A
contact lying in the relative interior of the unique tip's side,
and the unique tip owning the mutual contact, the physical
geometry and the unique tip's force/torque equations are
inconsistent for 0<t<=1. No force or torque equation at the
radial tip is used in that argument.

This precise endpoint form follows from the displayed proof:
the radial direction is determined by which vertices are
unshareable circle points; equations(38)--(41) use only the two
physical squares; equations(42)--(50) use only the unique tip's
original two positive forces. The quadratic is proved positive
on the entire closed interval 0<=t<=1. The earlier strict
selection t<1 is not needed in this geometric implication.

Apply it here with the radial tip C and the unique tip B. The
auxiliary support is (20), the other articulation normal remains
the original -h, and the mutual normal remains the original
B-owned g, with its orientation reversed when the tips are
renamed. Their A applications are the two endpoints Q,P of
one A side, so t=1. The scalar product n_0 dot (-h)=L is
strictly between0 and1; this is the acute chart. Every force
equation used is still B's original equation, which does not
involve n_0. The cited geometric contradiction therefore
excludes this alternative without changing a normal or a weight
in the extracted stress.

## 5. Shared AB: an actual full pressure proof

It remains to keep a positive-length AB segment, with its genuine
mean. Rotate and reflect in the common A,B frame so, relative
to the free AC vertex Q,
\[
 A=Q+[-1,0]^2,\qquad
 B=Q+[0,1]e_x+[h-1,h]e_y,\quad-1<h<1,
 \qquad n_{AB}=e_x.
\tag{21}
\]
The triangle owned-normal lemma and the strict free A vertex
normal make m have positive x-component. Reflecting vertically
if necessary makes its y-component positive too, so Q is the
upper-right A vertex as written.

First BC cannot be free. Such a contact would make its point T
a B vertex. But |T-Q|=1 by Section1. Among the four vertices
in (21), this forces h=0 and T-Q=(0,-1) or (1,0).
In the first case the radial C square with inner edge QT is
either A or B. In the second it is B or the aligned square
above B, which shares a full side with B. These contradict,
respectively, interior disjointness or a free singleton BC.
Thus B owns BC and T is in the relative interior of a B side.

Its axis g cannot be parallel to e_x: B's circle force would
then be parallel to one of B's axes, contrary to its unique
physical circle corner. Nor can g=-e_y, since that would put
the maximum-y C point T at B's bottom h-1<0 relative to Q,
although Q belongs to C. Consequently g=e_y and T is on
B's top side. The radial C inner edge has the form
\[
                    T-Q=(f,-j),\qquad f,j>0,\quad f^2+j^2=1.
\tag{22}
\]
Its radial direction is e=(j,f), since T minimizes y on C.
In coordinates about the original circle origin this gives
\[
 Q=(Hj-f/2,Hf+j/2),\quad
 c_A=(Hj-f/2-1/2,Hf+j/2-1/2).
\tag{23}
\]
The second component is positive, since
\[
                Hf-(1-j)/2>f(H-1/2)>0.
\tag{24}
\]

The first component is positive too. If it were nonpositive,
then Hj<=(1+f)/2. This forces f>1/2: for f<=1/2 we would
have j>=sqrt(3)/2>17/20 and Hj>153/200>3/4, a contradiction.
B's force is mu e_x-gamma e_y, so its unique circle corner is
its lower-right vertex. In the original coordinates it is
\[
                       z_B=(Q_x+1,Q_y-j-1).
\tag{25}
\]
Its first component is positive and at most3/2 under the
supposition, while its second is negative and strictly greater
than (9/10)(1/2)-1/2-1=-21/20. Therefore
\[
                 |z_B|^2<9/4+441/400=1341/400<R^2,
\tag{26}
\]
which is impossible. Both components in (23) are thus positive.

Finally M=mu e_x+nu m, with positive mu,nu and both components
of m positive. This proves (1) for the entire shared AB branch,
independently of its application mean and the C corner weights.

## 6. Scope and exhaustion

Every free AC contact at a radial C tip was routed in Section1
without choosing a new normal. The two singleton-AB owner cases
are impossible; the shared AB case has strictly positive pressure.
The two-radial mask was already positive independently of any
normal selection. Thus the theorem covers its entire premise.

A free articulation edge at a unique tip whose other contact is
a shared side remains a different interface. Its variable shared
mean has not been frozen or removed here. No completion square,
physical corner mask, numerical certificate, Lean compilation or
CI is used or discarded by this implication.
