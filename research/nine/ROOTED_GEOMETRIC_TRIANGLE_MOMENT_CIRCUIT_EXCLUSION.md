# A geometric directed-moment triangle cannot surround an outside origin-interior unit

Date: October 27, 2026.

**Status: accepted complete hand theorem or reduction after full root and separate independent reviews.**
Reviewed mathematical SHA-256: `fc55c0a5395b4cca051299416c99a7532df4f9ae440daee9ab9badc4d29ffbc3`. Root review: REVIEW_C3_334_B1_TRIANGLE_AND_DIAMOND_ROOT_2026_10_27.md. Separate review: REVIEW_GEOMETRIC_TRIANGLE_MOMENT_CIRCUIT_C6_2026_10_27.md. No original force, circle atom, normal,
contact mean, checklist label or shared ledger is changed.

Keep actual interior-disjoint unit squares contained in the origin disk
of radius

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60, M_*=91/60.

Every actual contained unit center has norm less than M_*. A contained
unit beyond a support height h requires h<=d. These are the complete
geometric bounds in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md Section 1.

## 1. Exact geometric statement and the meaning of auxiliary coefficients

Let T_1,T_2,T_3 be three actual pairwise-touching unit squares. For each
oriented edge of the cycle 1->2->3->1 retain an actual common point p_ij
and a unit common separating normal n_ij pointing from T_i to T_j.
If that edge belongs to the original positive certificate, retain its
original selected normal and actual aggregate application. A physical
edge with zero stress may also be used, with a specified actual common
point and common separating normal. No positive force on such an edge
is asserted by this theorem.

Assume that the three directed geometric line moments

    h_12=det(p_12,n_12), h_23=det(p_23,n_23),
    h_31=det(p_31,n_31)                                (1)

are nonzero and have the same sign. Let E be a fourth actual unit,
distinct from T_1,T_2,T_3, with O in int E.

**Geometric circuit theorem.** These conditions are impossible.

For the proof define positive auxiliary numbers

    mu_ij=1/|h_ij|, f_ij=mu_ij*n_ij.                  (2)

These numbers are geometric algebraic parameters only. They are not
the original physical pair magnitudes. No original stress is altered,
no circle force is split, and no new physical certificate is claimed.
In particular the vectors below are not claimed to be actual circle
resultants or sums of actual forces outside a triangle face.

Define three auxiliary vectors by exact differences:

    F_1=f_31-f_12, F_2=f_12-f_23, F_3=f_23-f_31.      (3)

They sum to zero. Equations (1)--(2) give one nonzero value

    det(p_12,f_12)=det(p_23,f_23)
                 =det(p_31,f_31)=H in {1,-1}.         (4)

Thus the two auxiliary outward vectors at each actual square have
total origin moment zero. Equations (3)--(4), positive auxiliary
coefficients and physical geometry are the only algebraic input.
No complete force equation at a higher-degree actual body is replaced
by a two-edge physical equation.

## 2. The geometric concurrences are positive multiples of the auxiliary vectors

The full physical proper-port theorem is radius-free: at a body with
two nonparallel actual outward normals n,m and concurrence q, its
actual ports are q+a*n,q+b*m with a,b>=0. If the two normals are
parallel, they have the same outward sign, since opposite supports
would separate the other two touching units. This is precisely
RADIAL_TRIANGLE_CONCURRENCE.md Section 1, whose proof uses no load,
degree or external-force premise.

We give the exact algebraic scope transfer for the remaining facts.
It is not an application of a physical-force theorem to a purported
new stress.

First every F_i is nonzero: F_i=0 in (3) would give opposite outward
normals at T_i. The F_i are noncollinear as well. If they were all
parallel to one axis e, a parallel pair at any T_i would force all
three f_ij parallel to e. Their required same-outward-sign conditions
at three vertices would then alternate signs around an odd cycle,
which is impossible.

Thus under supposed collinearity all three pairs would be nonparallel.
Equations (3)--(4) put each concurrence q_i on the e line through O.
At an actual edge, properness gives

    q_j-q_i=lambda_ij*f_ij, lambda_ij>=0.             (5)

Any two distinct q_i would force their edge vector, and hence all
three edge vectors by (3), parallel to e, already excluded. Therefore
all q_i coincide. Every proper length in (5) is then zero, so all
three actual contact applications equal that common point q.

At each square the two nonparallel outward normals now belong to its
vertex normal cone at q. Their positive sum is -F_i and lies strictly
inside that cone. The square's entire right-angle tangent cone, except
q, consequently lies in the open half-plane F_i.(x-q)>0. Two of the
three nonzero collinear F_i have the same sign. Two disjoint right-angle
cones cannot both lie strictly inside one open semicircle. This gives
the physical overlap contradiction and proves noncollinearity.

Every pair F_i,F_j is therefore independent, and at most one triangle
pair can be parallel. At each nonparallel body, (3)--(4) give

    q_i=t_i F_i.                                     (6)

Here t_i!=0, since H!=0. If all pairs are nonparallel, the coefficients
in (5) are strictly positive: equality would put the same nonzero
point on two independent auxiliary-vector lines. Put
Lambda=lambda_12+lambda_23+lambda_31. Summing (5) and using (3)
gives, by comparing the independent F_1,F_2 coefficients,

    t_1=lambda_12*lambda_31/Lambda,
    t_2=lambda_12*lambda_23/Lambda,
    t_3=lambda_23*lambda_31/Lambda.                   (7)

All three are strictly positive.

If K is the unique parallel body, rotate so F_K points east. Its
two actual outward normals are west, with ports (h,y_I),(h,y_J).
Equation (4) gives their positive weighted mean height zero and
nonzero individual heights. Relabel so y_I<0<y_J. Properness puts
the other two concurrences q_I,q_J at those same respective heights.
Their difference is a positive multiple of the directed I-to-J
normal, hence that normal has positive vertical component. Equations
(3) give (F_I)_y<0<(F_J)_y. The scalar multiples in (6) are therefore
strictly positive at both nonparallel bodies. No concurrence is
assigned to K.

This is the full algebra of the accepted noncollinearity and positive
concurrence proofs, using (3)--(4) and physical properness only. Neither
proof uses positivity, radiality or physical realizability of any
external force represented by the auxiliary F_i.

## 3. Each actual square meets its positive auxiliary-vector ray

We now verify the same precise geometric scope for the positive-ray
lemma in GLOBAL_CLOSURE_TWO_DECORATED_TRIANGLES_ORIGIN_INTERIOR.md
Section 1. Its local proof uses only the properties established in
Section 2, the zero pair moment (4), the actual square support features
and the containing disk. The full argument is as follows.

At a nonparallel body K write its two auxiliary outward vectors as
mu_1*n_1,mu_2*n_2, their sum as M=-F_K, and its concurrence as
q=-tM with t>0. Its actual ports are P_i=q+a_i*n_i, a_i>=0.
Suppose K has no point s F_K with s>0. Then q is outside K, so
a_1,a_2>0. With W=mu_1/a_1+mu_2/a_2, the actual convex mean is

    P_bar=sum_i [(mu_i/a_i)/W]*P_i
         =q+M/W=(1/W-t)M in K.                      (8)

If P_bar lies on a side of K with outward own-axis normal N, both
actual ports lie on that side. Their normals have nonnegative dot
product with N, and at least one is positive: both zero would make
the two normals parallel. Thus M.N>0 on every side containing P_bar.
In particular -M points strictly into K at any such boundary mean,
including a vertex.

The coefficient in (8) cannot be negative by the assumed ray avoidance.
It cannot be zero: if P_bar=O is interior, the positive F_K ray enters
K immediately; if O is on a boundary side or vertex, the just-proved
strict inward property gives the same conclusion. Hence P_bar=cM
with c>0, and O is not in int K.

Choose and reflect an own coordinate so K has its interval [a,a+1],
a>=0. Equation (8) gives M_x>=0. Equality would put P_bar on the
minimum-x side and contradict M.(-e_x)>0. Therefore M_x>0 and
q_x<0. Properness at both ports forces (n_i)_x>0 and puts both
actual ports on the far side x=A=a+1>=1.

Their vertical normal components cannot have one common strict sign:
that would put both ports at the same vertex and make q that vertex.
The proper-port relations put q_y between the two port heights,
including the possible horizontal-normal equality. Since q and P_bar
are opposite nonzero multiples of M, zero also lies between those
port heights. Write P_i=(A,y_i). The zero auxiliary pair moment is

    A M_y=sum_i mu_i*y_i*(n_i)_x.

It makes M_y/M_x a positive weighted mean of y_i/A. Substituting
q=-tM in the unchanged proper-port slopes yields the inequalities

    P_i.n_i>=A/(n_i)_x>=1/(n_i)_x.                  (9)

For clarity, the sign in this slope step is exact: set
z_i=y_i/A and z=M_y/M_x, so q_y/q_x=z. Properness gives
(n_i)_y/(n_i)_x=(A z_i+t M_x z)/(A+t M_x), a convex
combination of z_i and z. Because q_y lies between the two y_i,
and has the opposite weak sign from their weighted mean A z,
the two z_i bracket zero. For the upper port z_i>=0, its normal
vertical component is nonnegative and its ratio is at most z_i;
for the lower port the reflected inequalities hold. Hence
y_i*(n_i)_y>=A*(n_i)_y^2/(n_i)_x, which gives (9).
This includes a zero vertical normal and an endpoint-valued mean.

Each actual contained neighbor requires P_i.n_i<=d<61/60. Therefore
(n_i)_x>60/61, |(n_i)_y|<11/61 and P_i.n_i>=1. Its center c_i has
c_i.n_i>=3/2 and |c_i|<M_*. Consequently

    (c_i)_x>(3/2)(60/61)-(27/120)(11/61)
             =3501/2440=:L_*.

The two neighbor centers lie in the same open cap rectangle, whose
squared diameter is

    (M_*-L_*)^2+4(M_*^2-L_*^2)
       =52124381/53582400<1.                         (10)

This contradicts their distance at least one, proving the ray claim
for every nonparallel body. The strict transverse bound uses
sqrt(181)/60<27/120, exactly as in the original cap proof.

At a parallel body the two actual ports have strictly opposite
transverse heights and one common outward normal n. Thus n is an
own side axis. If that side's support height h were at least one,
both neighbor centers would have n-coordinate at least3/2, giving
an even smaller cap of squared diameter less than

    (1/60)^2+4[(91/60)^2-(3/2)^2]=29/144<1.

Hence h<1. The square has n-interval [h-1,h] and transverse zero
strictly in its side interval. A strictly negative point of the n
axis belongs to the square; this is a positive F_K-ray point.
This covers the entire parallel case with its original means.

We have proved, for every actual T_i,

    D_i=s_i F_i in T_i with s_i>0.                    (11)

No actual external-force premise was used in any of these cases.

## 4. The actual contact triangle has nonzero winding about O

Because O belongs to int E and the actual units have disjoint open
interiors, O belongs to none of the closed T_i. Strictly separate
each compact T_i from O by v_i.x>=c_i>0. Equation (11) gives
v_i.F_i>0. At a nonparallel pair, (6)--(7) then give v_i.q_i>0.
Thus conv(T_i union {q_i}) avoids O, even if q_i lies outside T_i.

The chord between the two unchanged contact ports inside T_i can
therefore be replaced by the two segments through q_i by an
endpoint-fixed homotopy avoiding O. At a parallel body use the
actual positive-ray point D_i from (11) instead. These homotopies
need to avoid O; they are not asserted to avoid the whole E.

If all pairs are nonparallel, properness at both endpoints makes
each original port a point of [q_i,q_j]. The replaced contact
loop is consequently the triangle q_1,q_2,q_3, with possible
collinear subdivisions. Equation (3) and t_i>0 give

    q_1/t_1+q_2/t_2+q_3/t_3=0.

O has strictly positive barycentric coordinates in this nondegenerate
triangle. Its winding is nonzero, so the original contact loop also
has nonzero winding about O.

In the one-parallel case use the frame of Section 2. The replaced
loop is

    D_K, P_I, q_I, q_J, P_J, D_K,

where D_K=(x_D,0), x_D>0; P_I,q_I have the same strictly negative
height; P_J,q_J have the same strictly positive height. The two
triangles D_K,P_I,q_I and D_K,P_J,q_J avoid O, including their
degenerate limits. Remove the corresponding two broken segments
by homotopies in those triangles. The remaining triangle is
D_K,q_I,q_J. Its vertices are positive multiples of the three
auxiliary F_i, so the same barycentric argument puts O strictly
inside it. The actual contact loop again has nonzero winding.

## 5. The actual outside unit contradicts the contact area

The original contact loop has vertices p_12,p_23,p_31; each side
belongs to an actual T_i. Its boundary avoids int E. Winding is
therefore constant on the connected int E and is nonzero there,
by Section 4 and O in int E.

A collinear or repeated-vertex contact loop has winding zero away
from its image, so it is already impossible. Otherwise the loop is
an ordinary nondegenerate triangle. Its bounded interior contains
the entire int E. Every side is a chord of a unit square, of length
at most sqrt(2), so its area is at most sqrt(3)/2<1. It cannot
contain int E of area one. This proves the geometric circuit theorem.

The proof is entirely about the unchanged physical squares, contact
points and normal lines. Auxiliary coefficients only establish the
geometric identities (3)--(4); they are never assigned to actual
circle atoms or claimed as an admissible new physical stress.
The theorem has no degree premise at any triangle body and includes
all proper-length, shared-mean and contact-polygon degeneracies.

No standalone original graph or coarse-cell closure is claimed here.
Its actual incidence and moment-sign hypotheses must be established
by a separate caller. No physical motion, numerical pose, normal
reselection of a positive edge, Lean compilation, CI, remote write
or shared-ledger edit is used.
