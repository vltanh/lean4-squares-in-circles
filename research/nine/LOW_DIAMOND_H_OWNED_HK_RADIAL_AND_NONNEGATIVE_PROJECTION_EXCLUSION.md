# The whole radial-B return when H owns HK, and the nonnegative root projection

**Status: complete hand proof; root and separate independent full-source
and original owner/radius-join review passed on October 25, 2026. See
REVIEW_LOW_H_OWNED_HK_RADIAL_AND_UUS_JOIN_2026_10_25.md. The complete
UUS join closes exactly two existing gates and adds no ID.**

Keep the original nine squares, all three completion squares, true
H5/K3/A2/B2, the intact HXY petal, every positive force and every original
application mean. A and K have unique **physical** circle corners. B has
either one physical circle corner or the radial two-corner mask; every
nonnegative individual radial circle weight, including a zero endpoint,
is retained. The selected necessary certificate is the one already used
in GENERAL_FIXED_TIP_NORMAL_SELECTION.md, without changing any extracted
normal or multiplier here.

Work in the unchanged negative-A upper-left chart and throughout

    q0=6241/1600 <= q=R^2 <= 1105/256,
    c_H.zA<0.

**Theorem.** In the strict H-owned n-normal HK row:

1. If c_H.n>=0, neither physical mask of B is possible.
2. If c_H.n<=0, every point of H has squared norm strictly less than
   13/16. Consequently H cannot touch a radial two-corner B.

Thus the entire radial-B mask in this HK row is excluded. A surviving
unique-B branch, if any, must have c_H.n<0. The theorem does not claim
the remaining unique-B branch is excluded.

## 1. Accepted complete fan and original coordinates

Use LOW_DIAMOND_H_OWNED_HK_RETURN_FAN.md, Sections 1--3, with its full
saved-source and direct-prerequisite review. In K's positively oriented
orthonormal (f,g) frame the coordinates are

    n=(E,d), j=(-d,E), E,d>0, E^2+d^2=1,
    r0=s/E, delta=v/E, tau=1-delta,
    V=(X,h), F=X+1, W=h+1,
    zK=(F,W), F^2+W^2=q,
    U=V+w j, H=U+[-1,0]n+[-1,0]j,
    0<w<1-r0, 0<r0<1, r=r0+w<1.                  (1)

The accepted fan proves

    X>0, h>0, F>1, W>1,
    E>v>=1/sqrt(2), 0<d<u,
    0<tau<1-v, 0<u<=v, u^2+v^2=1.                (2)

In A's original ordered frame,

    zA=(a,b), a>b>3/5, a<2,
    n=(u,v), j=(-v,u), f=(s,c), g=(-c,s),
    c,s>0, c^2+s^2=1,
    E=su+cv, d=sv-cu,
    P=(a-1,b-1)=V-r0 j, T=(a-1,b),
    L=(a-1)s+bc, X=L-delta.                        (3)

The two original positive n forces on H are beta at P and eta at V.
They have different applications and are not combined for torque.
Let nu>0 be the HB magnitude, ell its H-to-B normal, gamma>0 the KB
magnitude and k its K-to-B normal. The actual H5 force equation is

    (beta+eta)n+nu ell+M=0, c_H.M>0,                (4)

where M is the actual resultant of the intact HXY petal. The strict
pressure sign is the already proved end-triangle lemma in
BOWTIE_CELL_CLOSED.md, Section 2, applied at this arbitrary-degree root.
No degree-two replacement for H or K is made.

Write the H-frame coordinates of V as

    N=V.n=EX+dh>0, J=V.j=Eh-dX,
    cn=c_H.n=N-1/2, cj=c_H.j=J+w-1/2.              (5)

Since H owns HK, the physical HKB triangle and
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md give

    ell.n>=0.                                     (6)

The accepted complete physical KB fan leaves only

    k=-f, with all of B in {f<=X}; or
    k_f<0<k_g, with the fixed KB point Q=(X,W).     (7)

All other KB features, their owners and their original side means have
already been excluded geometrically. One further support separation
from that fan will be used below:

    min_K j=J-d > J+w-1=min_H j,                   (8)

because 1-w>r0>u>d. Hence ell=-j cannot occur: a B beyond H's lower
j support could not touch K.

## 2. If cn>=0, the true H5 equation forces one strict H vertex

Put D=av-bu>0; the sign follows from a>b and v>=u>0. Also zA.n>0.
The original negative-A pressure is exactly

    0>c_H.zA=(zA.n)cn-D cj.

If cn>=0 this gives cj>0. Taking the scalar product of the unchanged
H5 equation (4) with c_H then gives

    c_H.ell<0.                                    (9)

In H coordinates, (6), cn>=0 and cj>0 show that ell.j<0. Equality
ell.n=0 would force ell=-j, excluded by (8). Therefore

    ell.n>0, ell.j<0.                             (10)

Thus H's physical ell-support consists of the one fixed vertex

    Y=U-j=V-(1-w)j.

In K coordinates it has

    Y_f=X+d(1-w)>X,
    Y_g=h-E(1-w).                                 (11)

The first alternative in (7), k=-f, is impossible because all of B
would have f coordinate at most X, whereas Y belongs to B. The only
remaining KB feature is its upper-left fixed point Q=(X,W), with
k_f<0<k_g. Moreover

    |Q-Y|^2=d^2(1-w)^2+[1+E(1-w)]^2
           =1+2E(1-w)+(1-w)^2>1.                  (12)

Both pair applications are now distinct fixed physical points before
any use of generic selection. Their fixedness follows from the strict
support cones of H and K, so no shared-side mean has been specialized.

### 2.1. The actual KB normal is B-owned for either physical mask

If B has one physical circle corner, apply the previously selected
distinct-fixed-application theorem
GENERAL_FIXED_TIP_NORMAL_SELECTION.md to its genuine B2 star, with
applications Y and Q. Neither incident edge can be free. Because k is
strictly inside K's upper-left normal cone, it is not K-owned. Thus k
must be B-owned. The coincident radial-D exception does not apply by
(12). This is a property of the original selected certificate; no
post-extraction choice of a normal is made.

If B has two physical circle corners, no generic selection is needed.
Put T_B=sqrt(q-1/4). Every radial two-corner unit square has only the
following two squared vertex norms:

    q, and rho_B^2=(T_B-1)^2+1/4=q+1-2T_B.         (13)

The actual fixed Q has

    |Q|^2=X^2+W^2=q+1-2F.

Since W>1, T_B^2=F^2+W^2-1/4>F^2, so T_B>F. Since F>1,

    rho_B^2<|Q|^2<q.                              (14)

Consequently Q is neither an inner nor an outer vertex of B. It is
in the relative interior of a physical B side. Its inward support
normal k is therefore a B side axis. This argument retains both radial
circle forces and all their weight endpoints.

### 2.2. Both B-side support alternatives contradict the fixed points

In either mask k is an inward B side axis. Apply the physical triangle
normal lemma at B to its outward normals -k and -ell. Because -k is a
B side axis, it gives

    ell.k>=0.                                     (15)

If ell.k>0, every minimum-ell support point of B lies on its minimum-k
side: in the orthogonal side coordinates of B, the coefficient in the
k direction is strictly positive. Both Y and Q therefore lie on that
same unit side. Their distance is at most 1, contrary to (12). This
includes a relative-interior support or an endpoint; it does not assert
that both points must be vertices.

If ell.k=0, ell is one of B's two perpendicular side axes. From (10),

    ell_f=E(ell.n)-d(ell.j)>0.

Because k_f<0<k_g, the rotated vector Jk=(-k_g,k_f) has negative f
coordinate. Thus ell=-Jk. Choose the common minimum corner I in the
orthogonal B axes k,ell; then

    B=I+[0,1]k+[0,1]ell,
    Q=I+t ell, Y=I+t' k, 0<=t,t'<=1.

It follows that

    Q_f-Y_f=t ell_f-t' k_f>=0,

contrary to (11), which gives Q_f-Y_f=-d(1-w)<0. This includes the
zero-orthogonality endpoints and every original side mean.

The alternatives (15) are exhausted. Thus cn>=0 is impossible for
both physical masks of B.

## 3. If cn<=0, the two original contacts place H in a small disk

This section is purely physical after the original A2 relation is
used. It does not assume any particular HB or KB feature, owner, force
ratio or application mean. Now 0<N<=1/2 by (5).

### 3.1. The actual upper-g K circle corner has positive j projection

In A's original frame,

    zK=zA-(1,0)+tau f+g.

Hence, with the same D=av-bu as above,

    zK.j=E+v-D-tau d=J+E-d.                       (16)

The strict bounds a<2, b>3/5 give D<2v-(3/5)u. Together with (2),

    zK.j > E-v+(3/5)u-tau d
          > (3/5)u-(1-v)u
           =u(v-2/5)>0.                           (17)

Every inequality is strict on the full original row; no K2 replacement
or individual-circle-weight choice is used.

If J<=0, (17) implies 0<J+E-d<=E-d. The K circle equation in H's
orthonormal frame would therefore give

    q=(N+E+d)^2+(J+E-d)^2
      <=N^2+2N(E+d)+(E+d)^2+(E-d)^2
      <=1/4+sqrt(2)+2
       <15/4<q0,                                  (18)

where N<=1/2 and E+d<=sqrt(2). This is impossible. Thus

    J>0.                                          (19)

The original A2 origin moment gives the usual concurrence of the n
line at P, the g line at T and the radial line through zA. Explicitly
the first two intersect at

    C_A=P+(c/E)n=T-(u/E)g.

Its original x coordinate is (a-1)+cu/E>0, so its scalar multiple
of zA is positive. Since zA.j=-D<0,

    P.j=C_A.j<0, or equivalently r0-J>0.           (20)

This uses true A2 only; HA and HK still have their separate applications
P and V. Equations (19)--(20) say that those two actual boundary-square
contacts are on opposite sides of the n axis.

### 3.2. A uniform lower norm for every point of a boundary square

Let

    rho=R-sqrt(2)>0, x=rho^2.

If a physical unit square contains a circle corner z, each of its
points Z has |Z-z|<=sqrt(2), and hence |Z|>=R-sqrt(2)=rho. This
applies to P in A and V in K. Because their common n coordinate is N,
their j coordinates J-r0 and J have the strict opposite signs above,
so

    J>=b0, r0-J>=b0,
    b0=sqrt(x-N^2)>0.                             (21)

Here the radicand is indeed positive. The elementary exact comparison
sqrt(2)<99/70 and R>=79/40 gives

    rho>157/280,
    x>5/16, since (157/280)^2-5/16=149/78400>0.     (22)

Since N<=1/2, x-N^2>1/16. Adding (21) and using r0<1 gives
2b0<1. In particular

    x=N^2+b0^2<1/2,
    k0=sqrt(x-1/4)>1/4,
    k0<N<=1/2, k0<=b0<1/2.                       (23)

No sampled radius or angle subinterval is involved.

### 3.3. Every point of H has squared norm less than 13/16

H's n-coordinate interval is [N-1,N]. As N<=1/2, its absolute value
is at most 1-N. Its j-coordinate interval is [J+w-1,J+w]. Using
the two separate inequalities in (21), w>0 and r=r0+w<1 gives

    J+w-1>b0-1,
    J+w=r-(r0-J)<1-b0.                            (24)

Thus every point Z of H satisfies

    |Z|^2<(1-N)^2+(1-b0)^2
          =2+x-2(N+b0).                           (25)

For N,b0 in [k0,1/2] with N^2+b0^2=x=k0^2+1/4,

    (N b0)^2-k0^2/4=(N^2-k0^2)(1/4-N^2)>=0.

All quantities are nonnegative, so N b0>=k0/2 and then
N+b0>=k0+1/2. Substitution into (25) yields

    |Z|^2<1+x-2sqrt(x-1/4)
           =1/4+(1-k0)^2
           <1/4+(3/4)^2=13/16.                   (26)

The last comparison uses 1/4<k0<1/2 from (23). This is a uniform
whole-square bound, not only a center bound or a bound at one contact.

## 4. A radial B cannot reach this whole H

A radial two-circle-corner B, in its own radial frame e,k_B, is

    B=[T_B-1,T_B]e+[-1/2,1/2]k_B,
    T_B=sqrt(q-1/4).

Every point Z of B therefore has |Z|>=T_B-1. The exact radius-window
comparison

    q0-1/4-(191/100)^2=101/40000>0

gives T_B-1>91/100. Consequently

    |Z|^2>(91/100)^2=8281/10000>13/16,             (27)

with final reserve 39/2500. This contradicts the whole-H bound (26)
at any actual HB point. It is independent of both radial circle
weights, all actual HB/KB normal owners and every original mean.

The cn>=0 and cn<=0 alternatives exhaust the row. Together they prove
the stated entire radial-B exclusion, while recording precisely the
strict cn<0 restriction on the remaining unique-B branch. All original
forces and physical bodies remain present. No finite pose sample,
angle partition, coefficient table, Lean compilation or CI is a premise.
