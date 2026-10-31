# Two force-free boundary-point lemmas and the entire positive transverse North-roof return exclusion

Date: October 28, 2026 UTC. Author: roof_uniform continuation.

**Status: complete proposed geometric lemmas and complete stated return
feature exclusion, awaiting separate full review and root adoption.
The entire North interface and original roof ABC.S family remain open.**

The first two lemmas apply to actual unit squares at every R>=2 and
have no upper radius bound, degree, force, selected owner, or circle
coefficient hypothesis. Their proofs use the diameter of the same real
unit that contains two stated points. A stated point may be any actual
shared mean, since that mean belongs to the actual closed square.

## 1. A circle-adjacent return cannot reach the unit radial side through one unit

Let (n,e) be any orthonormal frame. Suppose an actual circle point Z
with |Z|=R>=2 satisfies

    Z.n<=0, Z.e>=1/2.

Let j be a unit vector with j.e>=0, and put V=Z+j. Suppose P is any
actual point satisfying

    P.n>=1, P.e=1/2.

Then no unit square can contain both P and V. This applies in
particular when Z is a physical circle corner of one original unit
and V is its real adjacent vertex.

Indeed P.n-j.n>=0 because j.n<=1. Since Z.n<=0,

    |P.n-j.n-Z.n|>=|Z.n|.

Similarly Z.e+j.e-1/2>=Z.e-1/2>=0. Consequently

    |P-V|^2
       >=(Z.n)^2+(Z.e-1/2)^2
        =R^2-Z.e+1/4
       >=R^2-R+1/4
       >=9/4>2.                                    (1)

The final inequality follows from R>=2 and monotonicity of R^2-R on
[2,infinity). The diameter squared of a unit square is 2, proving the
claim. The closed endpoints Z.n=0, Z.e=1/2, j.e=0 and P.n=1 are all
included. No contact normal, point, or body has been moved.

## 2. A half-width point fixes the sign of every physical circle corner

Let K be any actual unit square in the disk of radius R>=2. Suppose
K contains an actual point P with

    |P.j|<=1/2, P.w>0

in an arbitrary orthonormal frame (j,w). Then every physical circle
corner Z of K has Z.w>0.

Otherwise Z.w<=0 and |Z|=R imply

    P.Z=(P.j)(Z.j)+(P.w)(Z.w)<=R/2.

Thus

    |Z-P|^2=R^2+|P|^2-2P.Z
       >=R^2-R+|P|^2>=2+|P|^2>2,                   (2)

again contrary to the actual unit diameter. The strictness follows
from P.w>0, so P is not the origin. This proves the assertion for
every physical circle corner separately, including corners whose
individual coefficients may be zero in a later application. Any
nonzero nonnegative full circle resultant therefore has positive
w projection.

## 3. Literal retained North-roof chart

Use the complete necessary-domain theorem in
OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md.
All nine original squares, actual means and selected normals remain.
Its notation is retained:

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=1+epsilon, 0<epsilon<1/60,
    0<a<=epsilon, sqrt(2 epsilon)<b<31/120,
    Q=(k,1-b), k=(1-a)t/b, 0<t<b,
    A=Q+[0,1]j+[0,1]w,
    j=(-C_A,S_A), w=(S_A,C_A),
    C_A,S_A>0, C_A^2+S_A^2=1,
    Z_A=Q+w is A's unique physical circle corner,
    q_j=Q.j<-1/2,
    R_A=Q+D j, 0<D<1,
    the original H-to-A normal is exactly w.         (3)

The actual radial C is

    C=[d,d+1]n+[-1/2,1/2]e,
    n=(-C_n,-S_n), e=(-S_n,C_n),
    C_n,S_n>0, C_n^2+S_n^2=1.

The real CB application or mean satisfies

    P_CB.n>=d>1, P_CB.e=1/2.                        (4)

Its full original C-to-B normal g has g.e>0 and g.n<=0. Both physical
C circle coefficients remain original, independent and nonnegative.

The complete original AB force vector G satisfies

    G.j>0,
    P_AB=Q+j+y w, 0<=y<=1.                          (5)

Its positive w feature G.w>0 would force y=1. Its negative w feature
forces y=0. For G.w=0 the complete original side mean is retained.

## 4. The actual circle point Z_A satisfies the complete diameter lemma

We establish every premise of Section 1 from the entire retained
domain (3), without a genericity restriction or a numerical mesh.

First q_j<-1/2 gives k>1/2 and hence

    t=kb/(1-a)>b/2.

The original hub strip a beta+t alpha<=epsilon and b^2>2 epsilon
therefore imply

    alpha<b^2/(2t)<b.                               (6)

In the HC-side row S_n=alpha. In the opposite HC row,

    S_n=(alpha+zeta beta)/sqrt(1+zeta^2),
    0<zeta<=c/(1+a_H), c=t beta-a alpha<t beta<b beta.

Thus in both complete rows

    0<S_n<2b<31/60,
    C_n>5/6.                                        (7)

For the second inequality, 1-(31/60)^2-(5/6)^2=139/3600>0.

We next prove S_A<1/2. If S_A>=1/2, then C_A<=sqrt(3)/2, so k<1
and 1-b>89/120 give

    q_j=-k C_A+(1-b)S_A
        >-sqrt(3)/2+89/240>-1/2,

contradicting (3). The last comparison follows from
sqrt(3)/2<209/240, whose squared reserve is 481/57600. Consequently

    S_A<1/2,
    C_A>sqrt(3)/2>6/7,
    (Z_A)_x=k+S_A<3/2,
    (Z_A)_y=1-b+C_A>89/120+6/7=1343/840.             (8)

Both coordinates of Z_A are positive. Equations (7)--(8) give

    Z_A.n<0,
    Z_A.e=-S_n(Z_A)_x+C_n(Z_A)_y
        >-(31/60)(3/2)+(5/6)(1343/840)
         =2809/5040>1/2.                            (9)

The last reserve is 289/5040. Finally,

    j.e=C_A S_n+S_A C_n>0.                          (10)

Thus (4),(9),(10) meet every hypothesis of Section 1 with the same
actual circle point Z_A, the same actual unit axis j, and the same
actual CB mean P_CB. No selected normal has been altered.

## 5. The entire positive-w AB feature is impossible

If G.w>0, then (5) makes the actual AB point

    P_AB=Q+j+w=Z_A+j.

The actual B would contain this point and P_CB. Section 1 says their
distance squared exceeds 2, contradicting B's real unit diameter.
Therefore the entire retained original feature G.w>0 is excluded:

    G.j>0, G.w<=0.                                  (11)

The remaining exact support cover is

    G.w<0: P_AB=Q+j;
    G.w=0: P_AB=Q+j+y w, 0<=y<=1.                  (12)

No statement here removes either endpoint or any allowed original
mean from the zero-w case. Any further endpoint exclusion would need
its own physical argument. The two real physical C corners and their
complete independent weight interval remain throughout.

## 6. Every remaining physical B corner has positive w projection

At the actual P_AB in (12), its j coordinate relative to the unchanged
circle origin is q_j+1. We have q_j>-k>-1, since S_A>0 and C_A<1,
and q_j<-1/2. Its w coordinate is q_w+y, where

    q_w=k S_A+(1-b)C_A>0.

Hence

    0<P_AB.j<1/2, P_AB.w>0.

Section 2 applies to the actual boundary B at this actual mean. Every
physical B circle corner has strictly positive w projection, and so
its full original circle resultant satisfies

    F_B.w>0.                                        (13)

For the unchanged magnitudes M,mu,delta and full A coefficient kappa,
the exact surviving full A3/B2 equations consequently imply

    G_w=M C_A+mu-kappa(q_w+1)<=0,
    0<F_B.w=G_w+delta(g.w).

Thus

    M C_A+mu <= kappa(q_w+1)
              < M C_A+mu+delta(g.w).               (14)

This quantitative interval uses the original forces and actual masks.
It does not manufacture a two-force equation at A or equalize the C
circle coefficients. The unique-versus-two-circle B alternatives,
all remaining CB supports and both rows of (12) are still genuine
obligations of the same original North interface.

## 7. Exact input and scope

| Operative source | SHA256 | Literal use |
| --- | --- | --- |
| OPEN_ORIGIN_S_ROOT_NORTH_RADIAL_RETURN_UNIQUE_FAR_A_CORNER_REDUCTION.md | 74fa5a6ffc854cf1f04e230baa77495c49debb570ef80c9f40c9bf6a25c2ab94 | Complete chart, exact actual HA and AB sides, radial C contact cover, true A3/B2/C2 identities and unique A circle corner |

Sections 1--2 are self-contained force-free lemmas. The remaining
sections exclude one entire original return feature, with every
original mean and physical coefficient endpoint retained as stated.
They do not close the North interface, roof ABC.S, or any other whole
original fine or coarse family. No inventory, ledger or metadata is
changed. There was no pose search, mesh, computational exclusion
certificate, Lean compilation, CI, or remote action.
