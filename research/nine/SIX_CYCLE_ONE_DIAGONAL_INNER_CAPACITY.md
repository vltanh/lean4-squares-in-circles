# The whole unique-corner, one-diagonal alternating six-cycle has inner capacity at most one

**Status: complete hand region theorem; root and separate independent
full audits passed.** Work with the common selected
physical certificate in
\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Let the entire positive component be an alternating six-cycle with
three loaded bodies and three unloaded exact-degree-two transmitters.
Suppose all three loaded bodies have exactly one **physical** circle
corner, and exactly one transmitter is diagonal.

**Theorem.** The whole bounded central free region of the actual
six-body ring has area strictly less than two. Consequently at most
one of the three remaining physical unit squares can be central.
At least two must lie in the actual exterior channel regions of
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md.

Every genuine shared-side application mean is retained. In particular,
the loaded body opposite the diagonal channel need not have singleton
contacts. This is a region theorem, not a core exclusion or a completed
joint cap bound. Physical two-circle-corner loaded masks remain outside
the stated premise.

## 1. The complete unique-corner turn bound, including shared sides

Orient the strictly convex three-concurrence polygon counterclockwise
using SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md. At a loaded body write its
incoming/outgoing channel directions as \(n_-,n_+\), their positive
magnitudes as \(\mu_-,\mu_+\), and the positive polygon turn as
\(0<\vartheta<\pi\).

Choose positively oriented own square axes so its unique circle corner
is \(z=(a,b)\), \(a,b>1/2\), and the square is
\[
                          [a-1,a]\times[b-1,b].
\tag{2}
\]
Proper concurrence, force balance and the positive common moment give
\[
\begin{gathered}
 q=\tau z\in S,\quad0<\tau\le1,\qquad
 p_-=q-\alpha n_-,\quad p_+=q+\beta n_+,\quad\alpha,\beta\ge0,\\
 \mu_-n_- -\mu_+n_+=\kappa z,\quad\kappa>0,\qquad
                    \det(q,n_-),\det(q,n_+)>0.
\end{gathered}
\tag{3}
\]
Put
\[
             t=1-\tau,\qquad X=1-ta,\qquad Y=1-tb.
\tag{4}
\]
Containment of q gives \(0\le X,Y\le1\). We prove
\[
        \boxed{\vartheta\le3\pi/4},\qquad
        \vartheta=3\pi/4\ \Longrightarrow\ q=z.
\tag{5}
\]

### 1.1. Every loaded side-axis owner

The moment signs permit just these loaded side axes: incoming actual
outward normal \(+e_x\) or \(-e_y\), and outgoing actual outward
normal \(+e_y\) or \(-e_x\).

For an incoming \(+e_x\) normal, \(n_-=-e_x\), and force balance
makes both components of \(n_+\) negative. Its turn is less than
\(\pi/2\). For an outgoing \(+e_y\) normal, both components of
\(n_-\) are positive, with the same conclusion. These statements
retain the actual shared-side means.

The remaining axes are incoming \(n_-=e_y\) and outgoing
\(n_+=-e_x\). Together they give turn \(\pi/2\).
Suppose only the incoming bottom axis occurs. The non-axis outgoing
application is a vertex. The circle vertex is unshareable; the positive
moment permits the upper-left vertex, or the lower-left vertex when
\(b>a\). Their directions from q are, respectively,
\[
                         (-X,1-Y),\qquad(-X,-Y).
\]
The first gives turn at most \(\pi/2\). In the second case \(Y\le X\),
so the turn is at most \(3\pi/4\). Equality requires \(X=Y\), hence
\(t=0\) because \(a\ne b\), proving \(q=z\).
The outgoing-left-axis case is symmetric: an incoming lower-right
vertex gives turn at most \(\pi/2\); an incoming lower-left vertex
requires \(a>b\), and \(X\le Y\) gives (5), with equality only at
\(t=0\).

The only possible zero-vector limit is q equal to the lower-left
vertex, with \(a=b>1\). An outgoing strict vertex normal at q then
has angle strictly between \(\pi\) and \(5\pi/4\) by (3). Paired with
the incoming bottom axis its turn is strictly less than \(3\pi/4\).
The incoming strict-vertex/outgoing-left-axis case is symmetric.
This also covers coincident actual applications when an axis is owned.

### 1.2. Every interface without a loaded side-axis owner

Both applications are vertices. Neither neighbor is a diagonal
transmitter: existing compatible diagonal avoidance requires the
other endpoint of a diagonal transmitter to be in a strict
loaded-side interior. Thus both neighbors here are side transmitters.

The two applications cannot coincide. If they equal \(p\ne q\),
(3) makes the two pair forces parallel. If both equal q, each
neighboring transmitter meets that loaded vertex in the relative
interior of its own side. An endpoint would be a singleton
vertex/vertex contact carrying a transmitter side-axis normal,
contrary to strict point-normal selection. Two open side-interior
half-planes at q overlap unless their normals are opposite, which
is again the excluded parallel-force case.

Nor can just one application equal q. A vertex on the positive
ray through the unique circle corner is necessarily the lower-left
vertex with \(a=b\). A distinct non-circle vertex on a normal ray
from it is adjacent and produces a loaded side axis, outside this
case. Thus both parameters in (3) are positive.

The moment signs now leave exactly these three ordered vertex pairs:
\[
\begin{array}{c|c}
p_-&p_+\\ \hline
(a,b-1)&(a-1,b)\\
(a-1,b-1)&(a-1,b),\quad a>b\\
(a,b-1)&(a-1,b-1),\quad b>a.
\end{array}
\tag{6}
\]
The first pair gives direction vectors
\((X-1,Y)\) and \((-X,1-Y)\). Their scalar product is
\(X(1-X)+Y(1-Y)\ge0\), so the turn is at most \(\pi/2\).

The second gives \((X,Y)\) and \((-X,1-Y)\).
Its determinant is \(X>0\), and scalar product plus determinant is
\[
                            X(1-X)+Y(1-Y)\ge0.
\tag{7}
\]
Thus \(\cos\vartheta+\sin\vartheta\ge0\), proving the \(3\pi/4\)
bound. The third pair gives determinant \(Y>0\) and the same sum.
Equality in (7) requires \(X,Y\in\{0,1\}\). If \(t>0\), neither
can equal one, so both are zero: the already excluded zero-vector
case. Otherwise \(t=0\) and \(q=z\).
This proves (5) throughout the full physical unique-corner domain.

## 2. The diagonal endpoints and their complete other-port cover

Write the cycle
\[
                          B-W-C-U_C-T-U_B-B,
\tag{8}
\]
where W is diagonal and the other two transmitters have width one.
The three turns sum to \(2\pi\); (5) therefore makes each at least
\(\pi/2\).

The turns at B and C are strictly less than \(3\pi/4\).
Otherwise their concurrence equals their circle corner by (5).
The diagonal channel is a loaded side axis; its normal application
then has its other coordinate equal to that of the circle corner,
so is an endpoint of that loaded side. This contradicts the strict
relative-side-interior conclusion of diagonal avoidance.
Outer-side-axis cases already have turn less than \(\pi/2\).

Using the other endpoint's strict bound and the remaining bound
\(\vartheta_T\le3\pi/4\), we obtain
\[
 \frac\pi2<\vartheta_B,\vartheta_C<\frac{3\pi}4,\qquad
                              \vartheta_T\le\frac{3\pi}4.
\tag{9}
\]
In particular the remaining B or C application cannot have a loaded
side-axis normal: together with its diagonal axis that would give
turn at most \(\pi/2\).

Normalize the actual diagonal channel as
\[
              p_{BW}=(l,h),\quad p_{WC}=(l+\sqrt2,h),\quad h>0.
\tag{10}
\]
The endpoint frame and half-plane theorem give the unique corners
\[
 z_B=(-a,b),\quad z_C=(c,d),\qquad a,c>1,\quad b,d>1/2,
 \qquad 1-a=l,\quad c-1=l+\sqrt2.
\tag{11}
\]
Nonnegative center heights come from the full endpoint theorem;
physical uniqueness makes them strictly positive.
The complete feature cover in Section1 and (9) force the other
applications to be precisely the inner lower vertices
\[
                    p_B=(1-a,b-1),\qquad p_C=(c-1,d-1).
\tag{12}
\]
No mean is frozen here: a shared contact would have a loaded side
axis, just excluded by (9). The diagonal applications themselves
remain arbitrary strict side-interior points. Consequently
\[
                   Y_B=h+1-b\in(0,1),\qquad
                   Y_C=h+1-d\in(0,1).
\tag{13}
\]

The actual normals from B and C into their side transmitters are
\[
 n_B=(\cos\eta_B,-\sin\eta_B),\qquad
 n_C=(-\cos\eta_C,-\sin\eta_C),
\]
with the exact complete angular domain
\[
 \frac\pi4<\eta_B,\eta_C<\frac\pi2,\qquad
                    \eta_B+\eta_C=\vartheta_T\le\frac{3\pi}4.
\tag{14}
\]
All magnitudes, transverse transmitter positions and T's shared-side
means remain unrestricted.

## 3. The actual contact-hexagon area

Translate (10) to put its left application at \((0,0)\). Write
\(w=\sqrt2\), \(c_i=\cos\eta_i\), \(s_i=\sin\eta_i\).
The six actual contact points, in the order (8), are
\[
\begin{split}
 &(0,0),\quad(w,0),\quad(w,-Y_C),\\
 &(w-c_C,-Y_C-s_C),\quad(c_B,-Y_B-s_B),\quad(0,-Y_B).
\end{split}
\tag{15}
\]
The two points on T are its original applications. They need not
be unit distance apart or be vertices. In particular a genuine
T/transmitter shared side with its variable mean is retained.

The shoelace identity gives the positive area A after reversing
this clockwise order:
\[
\begin{split}
2A={}&(w+c_B-c_C)Y_B+(w-c_B+c_C)Y_C\\
     &+(w-c_C)s_B+(w-c_B)s_C.
\end{split}
\tag{16}
\]
Both coefficients of \(Y_B,Y_C\) are positive, because
\(0<c_B,c_C<1/\sqrt2\). Using (13),
\[
       A<w+\frac12\{w(s_B+s_C)-\sin(\eta_B+\eta_C)\}.
\tag{17}
\]
Set \(\Sigma=\eta_B+\eta_C\). Then
\[
 s_B+s_C\le2\sin(\Sigma/2),\qquad
                    \frac\pi2<\Sigma\le\frac{3\pi}4.
\tag{18}
\]
The function \(2\sqrt2\sin(\Sigma/2)-\sin\Sigma\) is strictly
increasing there: its derivative is
\(\sqrt2\cos(\Sigma/2)-\cos\Sigma>0\).
At the upper endpoint its value is
\(\sqrt{4+2\sqrt2}-1/\sqrt2\). Therefore
\[
                  A<\frac{3\sqrt2}{4}
                         +\frac12\sqrt{4+2\sqrt2}<\frac52.
\tag{19}
\]
For the final exact comparison, multiply by four and square positive
sides:
\[
3\sqrt2+2\sqrt{4+2\sqrt2}<10
       \quad\Longleftrightarrow\quad68\sqrt2<102,
\]
which follows from \(\sqrt2<3/2\).

## 4. The whole central free union, with every mean and routing limit

The chord through W is its entire horizontal diagonal. Its length
is \(\sqrt2\), and its inward square cap has area \(1/2\).
The complete winding/chord-cap theorem of
CONTACT_RING_HOLE_AREA.md, Sections1--2, consequently gives
\[
\begin{split}
 \operatorname{area}(\text{whole central free region})
 &\le A-\frac12\\
 &<\frac{3\sqrt2}{4}
       +\frac12\sqrt{4+2\sqrt2}-\frac12<2.
\end{split}
\tag{20}
\]
No subtraction at the other five bodies is needed.

This bounds the full central free union. At shared junctions use
the arbitrarily small physical routing and compact-interior winding
limit detailed in SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, Section3.
The limiting winding is zero or one. Every central completion
interior contributes its full unit area, and the actual inward
half of W lies in the winding-one region and is occupied.
No artificial small routing face can evade (20).

Two central interior-disjoint unit squares would contribute area
two and contradict (20). Thus at least two of the three actual
extras must lie in the three proved exterior caps, each with the
exact actual-height and center constraint from the cap theorem.

The numerical one-diagonal/shared core is not a premise and is
not excluded. A whole joint capacity bound for the caps and the
remaining possible central unit is still needed. Physical radial
loaded masks, the zero-diagonal width class, other load orbits and
larger positive graphs retain their separate complete scopes.
No secondary motion, changed selected normal, numerical certificate,
Lean compilation or CI is used.

