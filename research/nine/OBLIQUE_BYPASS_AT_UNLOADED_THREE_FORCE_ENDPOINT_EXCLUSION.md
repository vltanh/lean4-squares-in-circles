# An oblique unit bypass cannot end at this unloaded three-force vertex

Date: October 27, 2026.

**Status: complete fresh hand local proof, saved for full independent
and root review.** The theorem is radius-free. Its sole force equation
is the full unloaded degree-three equation at V. The two actual
unloaded degree-two transmitters X,Y, all selected normals and every
original mean remain. The original H2_D0.L013 caller is specified in
Section 10; this source does not by itself claim a whole coarse cell.

## 1. Whole local hypotheses and the initial normal convention

Let A,B,C,V,X,Y be six distinct actual interior-disjoint unit squares.
Retain the selected positive edges

    A--X--V--B--A,       A--Y--C--V.

The complete positive neighborhoods of X,Y,V are respectively

    {A,V},              {A,C},              {X,B,C},

and these three units have zero total circle load. A,B,C can have
arbitrary further positive neighbors, forces and circle masks. No
force equation of degree two is assigned to V. No circle or radius
inequality is assumed anywhere in the local proof.

Use the common initial physical normal selection of
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Sections 2 and 7: normals at
singleton vertex/vertex interfaces strictly expose both vertices,
and avoid both incident units' diagonal directions. This is the
existing finite diagonal avoidance, chosen before multipliers and
positive-graph extraction. At a four-unit junction it is the same
compatible restriction a!=b on the matched pair parameters. All
other finite exclusions remain compatible with it. No equilibrium
normal is reselected in this argument.

Assume the actual frames of B and X are not parallel.

**Theorem.** This whole local situation is impossible.

The degree-free theorem `UNIT_BYPASS_NORMAL_CHANNEL.md` makes X a
side-normal transmitter of reserve one, because B physically touches
both channel endpoints A,V. Its complete transverse-separation
statement places B on one side of X. Rotate, reflect and translate
the local notation, without using any circle-origin equation, to put

\[
 X=[0,1]\times[-1,0],\qquad
 A\subseteq\{x\le0\},\qquad V\subseteq\{x\ge1\},
 \qquad B\subseteq\{y\ge0\}.
\tag{1}
\]

The original two X applications are

\[
                  E=(0,z),\qquad R=(1,z),\qquad -1\le z\le0.
\tag{2}
\]

Their force magnitudes are the same positive number lambda. Their
height z is the original mean, not an endpoint chosen for the proof.

Since B is oblique, its lowest vertex P and two upward inward axes
give the exact actual representation

\[
 \begin{split}
 B&=P+[0,1]u+[0,1]v,\\
 P&=(p,h),\\
 u&=(c,s),\\
 v&=(-s,c),\\
 c,s&>0,\quad c^2+s^2=1,\quad h\ge0.
 \end{split}
\tag{3}
\]

Touching A and V forces the horizontal projection of B to cover
[0,1]. Hence

\[
           1-c\le p\le s,\qquad 0<p<1.
\tag{4}
\]

In particular B's rightmost coordinate is at most c+s<=sqrt(2),
its leftmost is at least 1-c-s> -1, and its highest coordinate
is h+c+s>1. Every B point of height zero, if one exists, is P;
that point has first coordinate strictly between 0 and 1.

The second unchanged transmitter gives actual applications Q_A,Q_C
and its unit direction m, directed from A toward C, with

\[
 Q_C-Q_A=w m,\qquad
 w\in\{1,\sqrt2\},\qquad
 Q_A\in\mathop{argmax}_{A} m\cdot x,\quad
 Q_C\in\mathop{argmin}_{C} m\cdot x.
\tag{5}
\]

This is the full original Y2 equation, including its two possible
widths and all actual side means.

## 2. A support-coordinate bound for any actual neighboring unit

We will use this radius-free observation. Suppose P_0 minimizes
n=(r,-t) on an actual unit S, where r,t>0 and r^2+t^2=1. Then

\[
       \min_{Z\in S}Z_x\ge (P_0)_x-t,\qquad
       \max_{Z\in S}Z_y\le (P_0)_y+r.
\tag{6}
\]

If P_0 is the strict minimum vertex, its two inward orthogonal unit
axes have strictly positive scalar products with n. At most one
inward axis has negative first coordinate, since n is a positive
linear combination of those orthogonal axes and n_x>0. If it is (-a,-b),
a,b>0, then -ra+tb>0, so a<t. Thus the leftward extension is
strictly less than t. The other inequality follows by the reflected
argument: an inward axis with positive second coordinate has that
coordinate strictly less than r. These observations also include
the possibility of no extension in one of the relevant directions.

If S owns n, put j=(t,r). The full actual side-mean representation is

\[
            S=P_0-\eta j+[0,1]n+[0,1]j,
                        \qquad 0\le\eta\le1.
\]

Its minimum first coordinate is (P_0)_x-eta t and its maximum
second coordinate is (P_0)_y+(1-eta)r. This proves (6) for every
owner and both original side endpoints. If a support vertex is an
owned-side endpoint, it is included in this second case.

## 3. The entire actual upper contact cover at an oblique endpoint

First suppose V is oblique to X. Its minimum-x support is the unique
vertex R of (2). Choose its two inward axes as

\[
       f=(a,b),\qquad j=(b,-a),\qquad a,b>0,\quad a^2+b^2=1,
       \qquad V=R+[0,1]f+[0,1]j.
\tag{7}
\]

The actual V--B contact cannot use R, whose height is at most zero,
or the lower vertex R+j, whose height is negative. Their adjacent
lower side likewise lies at height at most zero. The only B point
that could have height zero is P, and p<1, so the closed endpoint
at R is excluded too. The far vertex R+f+j has first coordinate
1+a+b>2, beyond B's rightmost coordinate.

The side R+f+[0,1]j has outward normal f. Both components of f are
positive. A minimum of f on B has u coordinate zero, because
f dot u>0; consequently its first coordinate is at most p<1.
It cannot lie on that V side. This excludes its whole side mean,
not just a particular application.

The other far side R+j+[0,1]f has outward normal j. Here
j dot v=-bs-ac<0, so every minimum-j point of B has v coordinate
one. Its first coordinate is at most p-s+c<=c<1. This cannot
be an actual point of V, either. Both far-side means and all
their closed endpoints have therefore been covered.

It follows that the actual contact has the form

\[
                       Q=R+\xi f,\qquad 0<\xi\le1.
\tag{8}
\]

Every possible V outward normal there has positive second
coordinate: the closed upper-vertex cone is generated by -j and f.
It must also have negative first coordinate. If that coordinate
were nonnegative, the minimum B feature would again have u
coordinate zero and first coordinate at most p<1.

Write the complete actual V-to-B force as

\[
                         (-\beta,\gamma),\qquad\beta,\gamma>0.
\tag{9}
\]

Since this vector has strictly positive scalar product with B's
axis v, every actual minimum B point has v coordinate zero. Its
u coordinate is some original tau with 0<tau<=1. Therefore

\[
 Q=P+\tau u,\qquad
 \frac\gamma\beta\le\frac cs.
\tag{10}
\]

The weak inequality is precisely the B-owned side case; tau=1
includes the strict B vertex and the right owned-side endpoint.
The other endpoint tau=0 has first coordinate p<1 and cannot
belong to V. Every possible actual side mean remains in (10).

Comparing (8),(10) and using (2),(4) gives

\[
 \begin{split}
 \xi a&=p+\tau c-1\le s+\tau c-1,\\
 \xi b&=h+\tau s-z\ge\tau s,\\
 \xi(a-b)&\le s-1+\tau(c-s)<0.
 \end{split}
\tag{11}
\]

The last inequality holds whether c>=s or c<s: its upper bound
is respectively c-1 or s-1. Thus

\[
                                  a<b.
\tag{12}
\]

The horizontally reflected argument is purely geometric and applies
to A without any degree premise. If A is oblique to X, its maximum-x
vertex is E, and its upward inward axis can be written

\[
          f_A=(-a_A,b_A),\qquad a_A,b_A>0,\quad
                       a_A^2+b_A^2=1.
\]

Its actual B contact is E+xi_A f_A with 0<xi_A<=1, and

\[
                                  a_A<b_A.
\tag{13}
\]

For a direct check, that B point is P+tau_A v and the reflected
version of (11) is
xi_A(a_A-b_A)<=c-1+tau_A(s-c)<0. No equation at A has been used.

## 4. Full V3 excludes its entire owned near-side B interface

If the actual normal in (8) is -j, retain its complete mean xi,
including xi=1, and write the V-to-B force as mu(-j), mu>0.
The V-to-X force is -lambda e_x at R. Full V3 makes the remaining
V-to-C force

\[
                            \lambda e_x+\mu j.
\tag{14}
\]

Its scalar products with f and j are respectively lambda a>0
and lambda b+mu>0. Its actual V application is therefore the
strict far vertex R+f+j. Torque about the unchanged R gives

\[
          0=\mu\xi-\mu-\lambda(b-a),\qquad
          \mu(\xi-1)=\lambda(b-a)>0,
\tag{15}
\]

contrary to xi<=1. This uses all three original positive forces.
It includes a selected B normal owned at the V upper vertex.

Thus the remaining V--B application is the strict upper vertex
R+f, and its actual force (9) satisfies

\[
                  b\gamma-a\beta>0.
\tag{16}
\]

Its first coordinate in (10) yields the useful whole-frame bound

\[
           a\le c+s-1\le\sqrt2-1<\frac5{12},
                         \qquad b>\frac9{10}.
\tag{17}
\]

For the last bound, 1-25/144=119/144>81/100. The strict
radical comparison preceding it follows from 2<(17/12)^2.

## 5. The complete V-to-C feature cover when V is oblique

Full V3, with every magnitude retained, gives

\[
                   F_{VC}=(\lambda+\beta,-\gamma).
\tag{18}
\]

It is strictly Southeast. Its scalar product with j is positive,
so the entire actual V support lies on R+j+[0,1]f. There are
exactly three possibilities, according to the sign of its scalar
product with f.

### 5.1. The strict far vertex is impossible

If that scalar product is positive, the application is R+f+j.
The full torque about R is then

\[
       0=-b\gamma+a\beta+(a-b)\lambda.
\tag{19}
\]

The first two terms have negative sum by (16), and the last is
negative by (12). This is a contradiction.

### 5.2. The entire V-owned far side is too far for Y

If the scalar product is zero, the actual normal is j=(b,-a)
and the application is

\[
                 P_C=R+j+\eta f,\qquad 0\le\eta\le1.
\tag{20}
\]

Retain that whole original mean. Applying (6) to the actual C
and using (17) gives

\[
 \min_{Z\in C}Z_x
   \ge 1+b+\eta a-a
   \ge 1+b-a
   >\frac{89}{60}>\sqrt2.
\tag{21}
\]

The last squared reserve is 7921/3600-2=721/3600>0.
Every A point has first coordinate at most zero, so the actual
channel in (5) would have length greater than sqrt(2). This is
impossible. Both eta endpoints and every C support owner are
included.

### 5.3. The strict lower vertex forces C wholly beyond x=1

The only remaining case is

\[
                        P_C=R+j=(1+b,z-a).
\tag{22}
\]

Its full torque, with the original B application R+f, is exactly

\[
                    (b-a)\gamma=a\lambda+(a+b)\beta.
\tag{23}
\]

In particular

\[
       \frac cs\ge\frac\gamma\beta
             >\frac{a+b}{b-a}>1,
                         \qquad c>s.
\tag{24}
\]

These inequalities imply the uniform bound

\[
                                  a<\frac7{20}.
\tag{25}
\]

Indeed if s/c>=1/2, (24) gives (a+b)/(b-a)<2 and hence b>3a,
so a<1/sqrt(10)<7/20. If s/c<=1/2, then
c+s<=(1+1/2)/sqrt(1+1/4)=3/sqrt(5). Formula (17) gives
a<=3/sqrt(5)-1<7/20. This last comparison follows by squaring
3/sqrt(5)<27/20: 720<729. The weak split endpoint is included.

Write the unit normal of (18) as n=(n_x,-n_y), n_x,n_y>0.
With theta=beta/(lambda+beta) in (0,1), (23) gives

\[
 \frac{n_y}{n_x}
       =\frac{a+b\theta}{b-a}
       <\frac{a+b}{b-a},\qquad
                 n_y<\frac{a+b}{\sqrt2}<b.
\tag{26}
\]

For the final strict comparison, (17),(25) give
a/b<7/18<2/5<sqrt(2)-1. Thus a+b<sqrt(2)b.
Applying (6) at the actual port (22) now proves

\[
                              C\subset\{x>1\}.
\tag{27}
\]

No C force, circle mask or concurrence has been assumed in
Sections 2--5. In particular a C-owned contact mean in (22)
has not been replaced by a C vertex.

## 6. The full parallel-V alternative in the oblique-B chart

If V is parallel to X, write its actual rectangle as

\[
       V=[1,2]\times[H-1,H],\qquad
                   H-1\le z\le H,
                   \quad H\le1.
\tag{28}
\]

B cannot meet V's bottom side or either bottom vertex: their
heights are at most z<=0, and the only possible zero-height B
point has first coordinate p<1. V's right side and its right
vertices lie at x=2, beyond B. A North contact on V's top would
have to be B's unique lowest point P, again with p<1.

Thus a V-to-B force either is West on its full left-side support,
or strictly Northwest at its upper-left vertex (1,H). In the
West case, full V3 with its West X force makes V-to-C exactly
East. C then lies in x>=2, immediately contradicting (5).
This includes any coincident/owned endpoint of that West face.

In the remaining case write the full force as (-beta,gamma),
beta,gamma>0. Equation (18) still holds, and its V application is

\[
       P_C=(2,H-1)=E+(2,-\rho),\qquad
                       \rho=z-(H-1)\in[0,1].
\tag{29}
\]

Formula (6) gives min_C x>=2-n_y>1. Thus (27) holds here as
well. Both original VX mean endpoints rho=0,1 remain. No torque
identity or extra equation at A,B,C is needed in this row.

## 7. The original Y must be diagonal, with two actual owned endpoints

All remaining cases have (27). From Q_A,x<=0 and Q_C,x>1,
the unchanged equation (5) gives w m_x>1. Consequently

\[
               w=\sqrt2,\qquad m_x>1/\sqrt2,
                              |m_y|<m_x.
\tag{30}
\]

The actual Y applications are its two opposite diagonal vertices.
Neither can also be a vertex of its neighbor: at a vertex/vertex
singleton the selected normal avoids Y's diagonal direction by
Section 1. Therefore Q_A and Q_C are each in the relative
interior of the actual neighboring side normal to m. Both A and
C own this exact channel axis, and their frames are parallel.

This is an inference from the original pre-certificate choice,
not a new normal selection or physical displacement. The full
two side-interior coordinates remain arbitrary in (0,1).

## 8. The axis-horizontal Y endpoint case is impossible

If A is parallel to X, its own axis m and (30) force m=e_x.
Its maximum m side is x=0; hence C's actual minimum m side is
x=sqrt(2), by (5). Since the V-to-C normal is strictly Southeast,
its minimum point on this actual axis-parallel C is its unique
upper-left vertex. Therefore its first coordinate is sqrt(2).

But the same actual application is (22) or (29). Its first
coordinate is respectively 1+b>19/10 or 2, both strictly
greater than sqrt(2). This is a contradiction. The original
transverse Y means do not enter this strict coordinate comparison.

## 9. The remaining oblique-A endpoint coordinates have opposite signs

It remains that A is oblique to X. It owns m by Section 7 and
has maximum-x vertex E. If m_y<0, write m=(k,-l) with k>l>0.
The upward inward axis of A at E would then be -m=(-k,l),
contradicting (13). If m_y=0, A would be parallel, already
excluded. Thus write

\[
              m=(k,l),\qquad k>l>0,\quad k^2+l^2=1,
                         \qquad Jm=(-l,k).
\tag{31}
\]

The actual maximum-m side of A is E+[0,1]Jm. Retain its actual
Y coordinate alpha and C's actual Y coordinate delta:

\[
 \begin{split}
 Q_A&=E+\alpha Jm,\qquad 0<\alpha<1,\\
 Q_C&=E+\sqrt2 m+\alpha Jm,\\
 C&=Q_C-\delta Jm+[0,1]m+[0,1]Jm,
                              \qquad 0<\delta<1.
 \end{split}
\tag{32}
\]

Let n=(n_x,-n_y) be the original V-to-C normal. Then

\[
                  n\cdot Jm=-n_x l-n_y k<0.
\]

Every actual minimum-n point of C consequently lies on its
maximum-Jm side. This includes both strict C vertices and a
C-owned side with its complete original mean. In particular
the actual V contact must satisfy

\[
                (P_C-E)\cdot Jm=\alpha+1-\delta>0.
\tag{33}
\]

On the other hand, the complete original V feature cover gave
only (22) or (29). Those give respectively

\[
 \begin{split}
 (P_C-E)\cdot Jm&=-(1+b)l-a k<0,\\
 \text{or}\qquad (P_C-E)\cdot Jm&=-2l-\rho k<0.
 \end{split}
\tag{34}
\]

The second inequality retains rho=0 because l>0. Equations
(33)--(34) contradict each other. This finishes every remaining
oblique-B frame, all actual contact owners and all original means.

## 10. Exact original inner-pentagon scope

For the original two-spoke/no-chord interior pentagon with exterior
cycle 0--1--2--3--4--0, interior H and spokes 0--H--2, take

    A=0, B=1, V=2, C=3, X=H, Y=4.

In the exact positive load set {0,1,3}, X,Y,V are unloaded with
their full positive degrees 2,2,3. The complete graph degrees
are A3/B2/V3/C2/X2/Y2. Every premise of Section 1 is literal.
No circle equation at A/B/C, physical-clear assertion at unloaded
V or Y, or special position of an extra square was used.

This source excludes the entire oblique rim1/H interface of
`M6.B6.PENTAGON.H2_D0.L013`. The complementary parallel interface
is the independently accepted complete source
`PARALLEL_BYPASS_AT_UNLOADED_THREE_FORCE_ENDPOINT_EXCLUSION.md`,
SHA0643b1ea0c6cd66724f2ad130c9cbd3fb2ffdbb53979e43170d7b58b2023e3be.
An exact parent assembly can therefore join the two full physical
frame alternatives after the present proof receives independent
review. All nine original packing squares remain, and the proof
does not modify a finite cover, ledger, remote state, Lean file
or CI workflow. No sampled pose or numerical optimizer is a premise.
