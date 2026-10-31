# The actual A hub pocket has capacity one in the entire far-return radial/radial mask

Date: October 31, 2026. **Complete hand literal transfer to the entire
original radial/radial far-return A pocket.**

This source verifies the physical chart, both proper endpoint rays, both
port moments, the actual exterior vertex and the original closing arc
needed by the existing opposite-vertex high-roof pocket proof. Properness
at V is derived from its unchanged full star; no physical-boundary-neighbor
premise is falsely imposed on D. The unloaded hub A retains its third
positive AD force throughout.

## 1. Original chart and fixed hand inputs

Retain all nine actual units and the exact original unique-V, Type II
D-owned roof-direction, far-A-vertex side return of D02.L135. Assume
both B and C are physically radial. Keep every original force, selected
normal, physical circle corner, individual coefficient, side mean and
the original positive AD chord.

Use the complete hand chart from

    TYPE_II_FAR_RETURN_RADIAL_RADIAL_SIDE_POCKET_EMPTY_HAND_EXCLUSION_2026_10_31.md
    TYPE_II_FAR_RETURN_RADIAL_RADIAL_CENTRAL_STRIP_EMPTY_HAND_EXCLUSION_2026_10_31.md.

In the actual oriented `(d0,n)` frame write

    D=sqrt(R^2-1/4)-1, 117/125<D<61/60,
    0<e<1/2, 0<q<5/12,
    J=sqrt(1+e^2), S=1/J, C=e/J,
    H=(1+e)/sqrt((1+e)^2+(1+q)^2),
    k=(1+q)/sqrt((1+e)^2+(1+q)^2),
    h=(H,-k), e_A=(k,H), H^2+k^2=1,
    f=(-a,b), w=Jrot(f), a=1/sqrt(1+q^2), b=q*a.

The actual V own axes and its unique physical circle vertex are

    East=(S,C), North=(-C,S),
    V=P0+[0,1]*East+[0,1]*North,
    Z=P0+East+North=lambda*(1,z), lambda>0, 0<z<1.

The original A vertices and applications satisfy

    R_A=P0+omega*North, 0<omega<1,
    W=R_A-e_A,
    K=Q_B=W-h=R_A-h-e_A,
    A=R_A-[0,1]*h-[0,1]*e_A.                       (1)

Thus the original AV and AB ports R_A,K are opposite vertices of A.
They are genuine side-interior applications at V and B respectively.
The positive AD application W is the other intermediate A vertex,
on the inward arc, and is not removed.

The original B radial port and full side force obey

    B=[D,D+1]*f+[-1/2,1/2]*w,
    K=D*f-X*w, 0<X<1/2,
    T=D*f+w/2,
    d_N=cos(theta)*f-sin(theta)*w,
    P_B*X=ell*D,
    G_B=P_B*f+ell*d_N, P_B,ell>0.                 (2)

All radial circle weights remain the actual independent weights.

## 2. Both hubs are physically interior, and the A port line has positive height

Put r=tan(theta), s=sin(theta), c=cos(theta), j=Jrot(d_N).
The preceding exact strip proof gives

    2/3<r<4/5, s>1/2, c>3/4,
    0<=W.d_N<(1-c)/(2*c)<1/6,
    W.n=1-D in (-1/60,8/125).

Using `W.d_N=-s*W.d0+c*W.n` gives

    -11/30<W.d0<12/125,
    |W.n|<1/15.

For the upper bound, `W.d0<(1-D)/r<12/125`; if 1-D is
nonpositive, the stated positive upper bound is immediate. For the
lower bound use s>1/2 in
`W.d0>(-1/60-1/6)/s`. Consequently

    |W|^2<(11/30)^2+(1/15)^2=5/36<1/4.             (3)

Since both actual hubs contain W, every point of either is within
|W|+sqrt(2)<2 of O. Thus both hubs are strictly inside the actual
circle R>2; there is no omitted physical hub circle contact.

Define the actual oriented diagonal frame

    d_A=(h+e_A)/sqrt(2),
    g_A=(e_A-h)/sqrt(2)=Jrot(d_A).

The two A ports have equal height

    h_A=R_A.g_A=K.g_A=W.g_A+1/sqrt(2)>0,            (4)

by (3). Their d_A coordinate gap is sqrt(2). The outer intermediate
vertex is exactly

    V_A=R_A-h=W+e_A-h,

on the original A arc without the positive AD spoke.

## 3. Both actual endpoint axes lie in the required closed 45-degree sectors

B's inward own normal f points left and upward in the `(d_A,g_A)` frame.
The two positive components are

    -f.d_A=[a*(H+k)-b*(H-k)]/sqrt(2)>0,
    f.g_A=[a*(H-k)+b*(H+k)]/sqrt(2)>0.

The second positivity follows from

    H/k=(1+e)/(1+q)>(1-q)/(1+q).

Moreover f.g_A<-f.d_A is equivalent to q*H<k, which follows from
q*e<1. Thus for an actual angle phi_B in (0,pi/4),

    f=-cos(phi_B)*d_A+sin(phi_B)*g_A.               (5)

V's original AV normal East likewise points right and upward:

    East.d_A=[(1+e)*H+(1-e)*k]/(sqrt(2)*J)>0,
    East.g_A=[(1+e)*k-(1-e)*H]/(sqrt(2)*J)>0.

Its upper component is smaller than its right component because e*k<H,
again a consequence of e*q<1. Hence for phi_V in (0,pi/4),

    East=cos(phi_V)*d_A+sin(phi_V)*g_A.             (6)

These are literal original angles, not reselected endpoint normals.

## 4. Proper endpoint rays follow from the unchanged full stars

### 4.1. The actual unique V

The two incoming lines at V are `R_A+t*East` and `P0+u*n`.
Their actual intersection is

    I_V=R_A+omega*e*East=P0+(omega/S)*n.

Both legs are strictly positive. The complete V force and origin torque
make I_V parallel to its unique physical circle force, a positive
multiple of Z. The multiple is positive because both I_V.n and Z.n
are positive: R_A.n=1-D+H>0, and the added East leg has positive
n component. Thus

    I_V=R_A+t_V*East=lambda_V*Z,
    t_V=omega*e>0, lambda_V>0.                     (7)

No two-force equation at A or D has been used. The actual AV point remains
R_A, with its original side coordinate omega.

For its reflected port moment, (7) gives

    R_A.North=lambda_V*(Z.North)>0.                (8)

Also Z.East>Z.North>0, because 0<z<1 and

    Z.East/Z.North=(1+e*z)/(z-e)>1.

The denominator is positive in the original unique-V chart. Therefore
Z.East>R/sqrt(2)>1, so the actual V minimum-East support
`N_V=R_A.East=Z.East-1` is positive.

### 4.2. The actual radial B with its full circle mean

Write s=sin(theta), c=cos(theta). The full B resultant in (2) has
f component P_B+ell*c and w component -ell*s. Its actual full radial
circle mean has coordinates `(D+1,eta_B)` in the `(f,w)` frame, where

    eta_B=-(D+1)*ell*s/(P_B+ell*c)<0.

This uses both actual physical corners and the original coefficient
ratio. Intersect its positive radial ray with the original f line through
K, whose w coordinate is -X. The f coordinate of the intersection is

    I_B.f=X*(P_B+ell*c)/(ell*s)
          =D/s+X*c/s,

using P_B X=ell D. Hence

    I_B=K+t_B*f,
    t_B=D*(1/s-1)+X*c/s>0.                         (9)

The radial multiplier is positive since X>0 and eta_B<0. This is the
exact proper endpoint ray required by the geometric pocket proof. It
does not presume equal weights or discard an individual zero weight.
Its port moment is the strict original value

    -K.w=X>0.                                     (10)

## 5. The complete opposite-vertex geometric chart is literal

Write the two actual ports in the diagonal frame as

    K=(-X_A,h_A), R_A=(Y_A,h_A), X_A+Y_A=sqrt(2).

Both X_A,Y_A are positive. From (2),(5),

    X_A=D*cos(phi_B)-X*sin(phi_B)>0,
    X_A<D<61/60,

because D>X and cos(phi_B)>sin(phi_B)>0. Thus
Y_A=sqrt(2)-X_A>0.

At V, the strict reflected moment (8) and the positive support N_V give

    Y_A=N_V*cos(phi_V)-(R_A.North)*sin(phi_V)
        <=N_V<D.

The last inequality follows from its actual unique circle vertex:
`R^2=(N_V+1)^2+(Z.North)^2` and `Z.North>1/2`. Accordingly

    3/8<X_A,Y_A<61/60<41/40.                       (11)

For the lower bound use their fixed sum and
sqrt(2)>7/5, giving `sqrt(2)-61/60>3/8`.

Each endpoint owns its actual normal at a genuine side interior. Its
whole actual square, full physical circle mask, positive normal support,
strict transverse port moment and proper radial ray are exactly the
data in Section 2, equations (2)--(10), of

    OPPOSITE_HUB_VERTEX_TIP_OWNED_HIGH_ROOF_POCKET_CAPACITY_ONE.md.

The left endpoint is the actual radial B, whose gap-facing physical
circle corner is `(D+1)*f-w/2`. The right endpoint is the actual unique
V with its actual circle corner Z. The endpoint rays (7),(9) supply the
properness explicitly, so the cited source's separate generic method
for obtaining properness from a boundary neighbor is not invoked.

The geometric proof from those verified data depends on no additional
degree equation at either endpoint and no equation at an internal body.
The original third AD force at A and all other original forces remain.

## 6. The actual outer A vertex is in the high-roof domain

We have H,k>1/2. For H, use

    H>12/sqrt(433)>1/2;

for k, use e<1/2,q>0, giving `k>2/sqrt(13)>1/2`.
On the positive unit-circle arc where both coordinates exceed 1/2,

    H+k>(1+sqrt(3))/2>4/3.

The first bound follows by minimizing sin(xi)+cos(xi) on
`pi/6<xi<pi/3`; the second uses sqrt(3)>5/3. The actual outer
vertex in (4) has n coordinate

    V_A.n=1-D+H+k>-1/60+4/3=79/60>5/4.

In particular

    |V_A|>5/4.                                    (12)

Thus the entire original outer-vertex domain satisfies the high-roof
premise of the cited complete hand pocket theorem.

## 7. The same actual pocket and its capacity

The original exterior A arc is `R_A -> V_A -> K`; W is on the other
A arc. The two endpoint pieces to the gap-facing circle corners lie in
the unchanged V and B. They form the same occupied opposite-vertex
crosscut used by the geometric proof just cited.

The correct closing circle arc is the upper arc in the original n frame.
Indeed both A port n coordinates exceed 1/2: they are 1-D+H and
1-D+k, and the stronger bounds in Section 6 give H,k>8/15, hence
both coordinates exceed 31/60. The outer A arc rises from those ports.
The B endpoint piece
can run from K to `D*f-w/2` and then to `(D+1)*f-w/2`, increasing its
n coordinate. The V piece can run from R_A to `P0+North` and then to
Z, also increasing its n coordinate. Their circle endpoints are in the
first and second `(d0,n)` quadrants respectively. The entire upper
closing arc has positive n coordinate and omits the actual radial C
circle corners. The actual exterior order V--A--B--N--C--D--V therefore
identifies exactly the original A pocket. In the diagonal frame both
gap-facing circle corners also have g_A coordinate greater than h_A>0,
by their verified own-coordinate chart. The shorter upper arc just
identified is therefore the same upper-g_A closing arc of the cited
geometric proof. No noncanonical embedding or extra physical contact
changes this bounded-side label.

The purely geometric Sections 3--7 of
`OPPOSITE_HUB_VERTEX_TIP_OWNED_HIGH_ROOF_POCKET_CAPACITY_ONE.md` now
apply to this literal chart. For clarity, those sections use (11),(12)
to put the whole pocket above its positive port height and prove that
height exceeds 1/2. Every additional unit then supplies a connected
5/4-circle arc longer than pi/4. The actual A roof splits the available
arcs into two disjoint support caps. Its complete smaller-port scalar
comparison and actual endpoint-face routing make one cap shorter than
pi/4; the other has length at most pi/2. Thus two additional units
cannot occupy this pocket.

All its physical prerequisites have been verified here. In particular
the cited source is used for its continuous geometric and scalar proof,
not for its different original graph/load caller or for a nonexistent
two-force equation at A. Compact-interior routing treats weak physical
junctions and additional zero-load contact subdivisions exactly as in
that proof; their occupied barriers can only remove free space.

Consequently the actual A exterior pocket has capacity at most one
throughout the entire original far-return radial/radial physical mask.
The whole original nine-square conclusion still requires its other
actual region capacities and their literal assembly. No original fine
or coarse flag is changed by this source.

This is a hand proof with explicit full-star endpoint calculations and
an exact application of an existing hand scalar theorem. No numerical
packing certificate, external mathematical script, Lean/Lake invocation,
CI, remote write or replacement of an original mean was used.
