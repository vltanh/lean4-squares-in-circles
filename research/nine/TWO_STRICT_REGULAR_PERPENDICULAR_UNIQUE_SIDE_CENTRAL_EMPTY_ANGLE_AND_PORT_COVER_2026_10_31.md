# Central emptiness for a whole angle and port cover of the regular unique side feature

Date: October 31, 2026 UTC.

**Status: complete hand implication for the stated union of parameter
regions.** In the entire regular two-strict, both-roof-owned,
perpendicular-AD chart with two physically unique loaded endpoints and
an unloaded side transmitter, the actual central pocket is empty of
additional unit squares whenever either

    Theta >= 2*pi/3

or

    min(beta_B,beta_C) <= 3/4.

These are whole regions of the original feature. The remaining strict
region is not claimed excluded. No pose sample, numerical certificate,
Lean invocation or CI is used.

## 1. The unchanged physical chart

Retain the full chart and every original equation of
`TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`,
Sections 1--5. In particular, A and D remain the actual unloaded true3
hubs, V remains the actual loaded true2 roof endpoint, B and C remain
the actual loaded true2 exterior endpoints with one physical circle
corner each, and N remains the actual unloaded true2 side transmitter.
All original square positions, positive pair magnitudes, applications,
physical circle masks and individual circle coefficients are retained.

Use the source notation

    h=(c,-s), e=Jrot(h), k=(C,S), v=Jrot(k),
    H=sin(alpha+beta), J=cos(alpha+beta),
    F=J-H>0, Sigma=J+H>1,
    x=1+s-H*rho in (0,1),
    m=x/y, n=F/(1-rho),
    b=(-m*h+e)/p, a=(n*k+e)/q,
    w=Jrot(b), z=Jrot(a).

The genuine AD application W and genuine exterior applications K,L
satisfy the unchanged geometric identities

    K-W=-x*h+e,
    W-L=k+v=F*h+Sigma*e.                          (1)

The complete physical-mask and angle cover in the cited source gives

    pi/4<delta_B,delta_C<pi/2,
    Theta=delta_B+delta_C in (pi/2,3*pi/4),
    0<beta_B,beta_C<1,
    T=K+beta_B*w,
    U=L+beta_C*z,
    u=T-U, |u|=1,                                (2)

where delta_B is the clockwise angle from b to u and delta_C the
clockwise angle from u to a. These are the actual endpoint directions
and actual side coordinates, not newly selected applications.

The full endpoint torques, circle equations and original A/D/V equations
remain assumptions. The proof below uses only the exact consequences
(1)--(2), so it does not discard or replace any original equation.

## 2. The actual occupied cuts in the central contact pentagon

Use the original chorded-cycle embedding. Its central contact pentagon
has boundary

    W -> L -> U -> T -> K -> W.

This is the bounded contact region on the pentagon side of the original
AD chord. Write its nonnegative area as A_poly. Let A_free be the area
of its actual complementary region after all original unit squares
are retained. If that region has more than one component, A_free may
equivalently denote their total area; this only strengthens the upper
bound used here.

The actual vertex

    I_A=W-x*h=K-e

of A cuts off the triangle with vertices W,K,I_A. Its area is exactly
x/2. Similarly the actual vertex

    I_D=W-k=L+v

of D cuts off the triangle with vertices W,L,I_D, whose area is exactly
1/2. Both triangles lie on the central side of their respective contact
chords and inside their original physical squares. Their interiors are
disjoint, since the original A and D are interior-disjoint. The weak
contact-cycle embedding keeps these occupied triangles inside the
contact pentagon: the other contact edges cannot cross their interiors,
as those edges lie in the other original interior-disjoint units.

Consequently

    2*A_free <= 2*A_poly-x-1.                    (3)

Any portion of N or any other original square in this contact pentagon
only decreases A_free. No translation of N and no replacement of its
original transverse side means is made in (3).

## 3. One exact area identity retains all angles and side coordinates

Put Delta=K-L. The determinant convention is det(h,e)=1. Since the
angle from b to a is clockwise Theta,

    det(b,a)=-sin(Theta).

Expanding the signed area of the original pentagon, with its actual
orientation, gives

    2*A_poly
      =x*Sigma+F
       +beta_B*(Delta.b)+beta_C*(Delta.a)
       -beta_B*beta_C*sin(Theta).                (4)

For completeness, the first term is

    det(K-W,L-W)=x*Sigma+F,

and the other three terms in (4) are the exact changes produced by
T=K+beta_B*w and U=L+beta_C*z. In the displayed boundary order the signed
area is the negative of (4); A_poly is its nonnegative geometric area.

The unchanged unit bridge in (2) also gives

    Delta.b=cos(delta_B)+beta_C*sin(Theta),
    Delta.a=cos(delta_C)+beta_B*sin(Theta).       (5)

Substitution of (5) into (4) and then (3) yields the exact useful upper
bound

    2*A_free <= C0+S_area,                       (6)

where

    C0=x*(Sigma-1)+F-1,
    S_area=beta_B*cos(delta_B)
          +beta_C*cos(delta_C)
          +beta_B*beta_C*sin(Theta).             (7)

The entire hub contribution is strictly negative:

    C0 < (Sigma-1)+F-1 = 2*J-2 < 0.              (8)

Here x<1 and Sigma>1 give the first strict inequality, while
0<alpha+beta<pi/4 gives J<1. Thus the reductions below use the actual
A and D occupied cuts; they do not estimate the uncut pentagon alone.

## 4. Complete central exclusion for Theta at least 120 degrees

Suppose Theta>=2*pi/3. Because both beta values are strictly below one
and the three trigonometric quantities in (7) are positive,

    S_area
      <cos(delta_B)+cos(delta_C)+sin(Theta)
      =2*cos(Theta/2)*cos((delta_B-delta_C)/2)
        +sin(Theta)
      <=2*cos(Theta/2)+sin(Theta)
      <=1+sqrt(3)/2
      <2.                                        (9)

The penultimate inequality holds on the entire closed interval
[2*pi/3,3*pi/4]: both cos(Theta/2) and sin(Theta) decrease there, so
their displayed sum is at most its value at 2*pi/3. Equations (6),
(8) and (9) give A_free<1. An additional unit square has area one
and therefore cannot belong to the actual central pocket.

This includes the exact Theta=2*pi/3 boundary and all genuine side
coordinates in their original open intervals.

## 5. Complete central exclusion when either actual side coordinate is at most three quarters

Suppose first beta_B<=3/4. From (2),

    cos(delta_B),cos(delta_C)<1/sqrt(2),
    sin(Theta)<=1,
    beta_C<1.

It follows throughout this whole closed beta_B range that

    S_area < 3/(4*sqrt(2))+1/sqrt(2)+3/4
           =7/(4*sqrt(2))+3/4
           <2.                                   (10)

The final exact comparison is 7<5*sqrt(2), or 49<50 after squaring
positive sides. The calculation is unchanged with B and C exchanged.
Thus min(beta_B,beta_C)<=3/4 implies A_free<1 by (6) and (8), again
excluding every additional central unit square.

The exact beta_B=3/4 and beta_C=3/4 boundaries are included. No
assumption on equality or ordering of the positive endpoint force
magnitudes is involved.

## 6. The complete retained remainder

Combining Sections 4--5 proves central emptiness throughout the stated
union. If the actual central pocket contains any further unit square,
all of the following strict restrictions are therefore necessary:

    pi/2<Theta<2*pi/3,
    3/4<beta_B<1,
    3/4<beta_C<1.                                (11)

The full original torques continue to give

    p*(1-beta_B)=ell*(sin(delta_B)-cos(delta_B)),
    q*(1-beta_C)=ell*(sin(delta_C)-cos(delta_C)),
    ell>0.                                      (12)

In particular, (11)--(12) retain both strict inequalities

    ell*(sin(delta_B)-cos(delta_B))<p/4,
    ell*(sin(delta_C)-cos(delta_C))<q/4.

Neither (11) nor these last inequalities is asserted sufficient for
physical feasibility. Every circle equation, all three completing
squares and every other original condition remain. This manuscript
does not exclude the whole strict remainder (11), and it does not turn
the loaded N of D02.L1345 into an unloaded side transmitter.

The result is a geometric central-capacity consequence for the original
D02.L135 two-unique side caller. Its use with separate outer-pocket
capacity theorems must retain those theorems' own physical and embedding
hypotheses.
