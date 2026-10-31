# An owned tilted leaf and a North neighbor force the other root's North contact

Date: October 27, 2026.

**Status: complete original-domain necessary reduction, submitted for
full root and separate independent review.** The source excludes
both strict AD vertices in the owned-B-leaf, North-BC interface.
It retains the entire actual North/North interface at the end;
it does not claim that remaining interface closed.

Keep the original high one-owner adjacent-S component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+E, 0<E<1/60,
    R^2=(2+E)^2+1/4<=Q_*=1105/256.

A has its strict outer-lower genuine S leaf. In world coordinates,

    A=[-X,h] times [-v,H],       X=1-h, H=1-v,
    X^2+v^2=d^2, |h|<=E,
    P_AB=(h,-k),       0<k<v<13/50.

The actual AB normal is East, owned by A alone. B is tilted and
has its owned far-axis genuine S leaf. With its actual axes

    j=(s,-c), f=(c,s),       c,s>0, c^2+s^2=1,

its positively oriented own frame is

    B=[E,d] times [-w,T],       T=1-w,
    d*e_M=(d,0),       P_AB=(E,-w),
    h=E*s-w*c,       k=E*c+w*s.

Assume the original BC normal is B-owned North. Its entire
actual mean and unchanged B3 equation are

    Q_BC=(q,T),       q=E+ell,
    ell=w*s/c in [0,1].                               (1)

C has one physical circle corner. D may have either mask, with
both original circle weights retained in its two-corner case.
All nine actual squares, original forces and application means
remain.

## 1. Two direct bounds from the real root identities

Put p=c/s. The actual A leaf identity and k<v give

    w^2+2wc<2E(1+s).                                  (2)

Equivalently, with S=sqrt(1+p^2),

    E>[w^2*S+2wp]/[2(S+1)].                           (3)

The right side increases separately in w and p. This follows
from the increasing functions S/(S+1) and p/(S+1).

From (1), p>=w. We claim

    w<3/20,       T>17/20.                            (4)

At w=p=3/20, comparison with E=1/60 is already impossible:
multiplying the required inequality by its positive denominator
would give

    (30w^2-1)*sqrt(1+p^2)+60wp-1<0,

whereas sqrt(1+p^2)<=1+p^2/2 and 30w^2-1<0 give the positive
lower bound 683/32000. Monotonicity of (3) excludes all
w>=3/20,p>=w. This proves (4), including the original ell=1
endpoint.

We also record the exact implication

    v>43/240 implies k<3/20.                          (5)

Indeed if k>=3/20, then
w^2=h^2+k^2-E^2>1/45. The actual small support gives
wc<=E(1+s)<1/30; hence c<sqrt(45)/30<1/4 and s>24/25.
Equation (1) gives c>=ws, so wc>=w^2s>8/375. Thus the actual
A radius satisfies

    v^2=2E(1+s)+E^2-2wc-h^2
       <241/3600-16/375<(43/240)^2.

This proves (5) without a C/D equation or altered mean.

## 2. Complete loaded-C geometry at the actual North point

Apply the full local high vertical-port theorem in Section 1 of
ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md.
Its local hypotheses are only a genuine loaded two-force unit,
one physical circle corner, its other neighbor physically
boundary, and an actual incoming North point (q,T) with q>0
and T>37/50. They hold here; no parallel-root caller is used.

If C owns North, its actual unique corner and center in B's frame
are

    Z_C=(Z,T+1),       Z=sqrt(R^2-(T+1)^2)>1/2,
    z_C=(Z-1/2,T+1/2).                               (6)

Its unchanged proper radial point yields

    q>=T*Z/(T+1).                                    (7)

If C does not own North, its actual strict minimum vertex is
(q,T). For actual inward axes

    a0=(a,b),       b0=(-b,a),
    a,b>0, a^2+b^2=1,

the same complete local theorem gives

    Z_C=(q+a,T+b),
    q*b-T*a>1/2,
    a/b<1/2,       a<1/2.                            (8)

The opposite-circle corner is excluded by the actual proper
radial point inside C, not by a new moment assumption. In
particular (8) gives q>1/2. All other physical C frames and the
axis limits belong to the owned case (6).

First, both cases imply the useful bound

    q>1/4+w.                                         (9)

For the tilted case use (4) and q>1/2. For the owned case, use
R^2>17/4 in (7). The squared comparison with 1/4+w is

    (1-w)^2*[17/4-(2-w)^2]-(1/4+w)^2*(2-w)^2
      =w*[7/4-(173/16)w+(19/2)w^2-2w^3].

For 0<w<3/20 the bracket is greater than 971/8000, even after
discarding its positive quadratic term. At w=0 the actual strict
R^2>17/4 still makes (9) strict. But (1) would then give
q=E<1/4, so w=0 is itself impossible in this North interface.
Thus the original zero-depth endpoint has been covered.

Equations (1),(9) imply

    p<3/10.                                         (10)

Indeed w/p=q-E>w+7/30. This first forces p<1. If p>=3/10,
then w>7p/[30(1-p)]>=1/10. At the comparison point
w=1/10,p=3/10, the same rational lower test for (3) is
137/2000>0. Monotonicity contradicts E<1/60.

In the tilted-C case we have the stronger bound

    p<1/4.                                          (11)

Here q>1/2 gives w/p>29/60. If p>=1/4, then w>29/240.
The comparison point w=29/240,p=1/4 in (3) has the positive
rational lower reserve 4771/20480. This proves (11).

## 3. A uniform actual C-center angle in world coordinates

For C owning North, (4),(6) and R^2<=Q_* give

    0<(z_C)_j=Z-1/2<9/20,
    (z_C)_f=T+1/2>27/20.                             (12)

For the horizontal bound, Z^2<Q_*-(37/20)^2
=5721/6400<(19/20)^2. Thus the actual center angle in B's
(j,f) frame exceeds arctan(3).

This own frame is rotated clockwise from the world frame by
phi=arctan(p). By (10), its actual world angle therefore satisfies

    theta_C>arctan(3)-arctan(3/10)
             =arctan(27/19)>0.                       (13)

For a tilted C, we can sharpen its actual horizontal center
bound directly to

    (z_C)_j<1/2,       (z_C)_f>27/20.                 (14)

The vertical inequality follows from (4),(8) and a+b>=1.
If the horizontal coordinate were at least 1/2, its actual
circle corner would satisfy

    R^2>[1/2+(a+b)/2]^2+[17/20+b]^2=:F(a).

For 0<=a<=1/2, b=sqrt(1-a^2), this expression is concave.
After expansion its nonconstant part is
-a^2+a/2+(11/5+a/2)*sqrt(1-a^2), whose second derivative is
strictly negative. Its minimum is therefore at an endpoint.
At a=0 its excess over Q_* is 679/6400. At a=1/2 it is
889/400+(49/40)sqrt(3), whose excess over Q_* exceeds
1549/70400, using sqrt(3)>19/11. Both contradict containment.
This proves (14), with all original tilt endpoints retained.

If its horizontal center coordinate is positive, its own-frame
angle exceeds arctan(27/10); otherwise it is at least pi/2.
Combining (11),(14), either case gives

    theta_C>arctan(27/10)-arctan(1/4)
             =arctan(98/67)>arctan(27/19).            (15)

Consequently the full uniform conclusion (13) holds for every
actual C frame, original North mean and unique physical mask.

## 4. The entire strict Northwest AD feature is impossible

The complete A3 equation makes the vertical AD force component
positive. At a strict Northwest contact its actual point is
(-X,H), and its unchanged force and torque give the actual
normal proportional to (-r,1), where

    r=X*(v-k)/[v*(1-v+k)],
    0<r<X/(1-v).

The actual inward unit-normal segment belongs to D. Its far
endpoint has squared norm

    d^2+2-2v+2U,
    U=[X*r+(1-v)]/sqrt(1+r^2).                        (16)

Containment would require U<=d-3/8+v.

If v<=43/240, then U>=1-v>d-3/8+v, since d<61/60.
If v>43/240, (5) gives k<3/20. For v<=1/4, monotonicity in
the original formula for r yields r>4/25, so

    U>1361/(60sqrt(641))>107/120>d-3/8+v.

For v>1/4 the same formula gives r>3/8, and

    U>529/(60sqrt(73))>1>d-3/8+v.

These are the exact scalar comparisons from Section 4 of
ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md, here with
the literal actual X,v,k. The hypotheses were just checked
independently. The unit-normal endpoint is outside R in every
case. No D degree, circle-mask or new contact-owner premise
is used in this complete feature exit.

## 5. The entire strict Northeast AD feature is impossible

The complete original-domain bound in Section 4 of
OUTER_LOWER_S_OWNER_BOUNDARY_NEIGHBOR_CENTER_ANGLE.md applies
at the actual AD point (h,H), with the actual D-owned
Northeast normal. Its proof retains every original side mean
and the zero proper-distance endpoint. A physical two-corner
D is impossible at this feature by the radial-boundary owner
theorem, so its unique-corner D2 clause is legitimate. It gives

    0<theta_D<arg(h,H)
       <=pi/2+arctan(5/222).                         (17)

By (13),(15), both actual boundary centers have positive height.
The original C-before-D minor-center order and strict 40-degree
physical separation would require their positive angle gap
to exceed 2*pi/9. Instead (13),(17) imply

    theta_D-theta_C
      <arctan(19/27)+arctan(5/222)
       =arctan(4353/5899)
       <arctan(3/4)<2*pi/9.                          (18)

The rational comparison has reserve
3*5899-4*4353=285>0. For the last elementary angle inequality,
cos(arctan(3/4))=4/5 and
4*(4/5)^3-3*(4/5)=-44/125>-1/2; the triple-angle formula,
with all angles in their indicated acute ranges, gives
arctan(3/4)<2*pi/9. Thus (18) contradicts actual separation.

This closes the complete other strict AD feature without
discarding any actual C mean or imposing an orientation on D.

## 6. The exact remaining original interface

Only the actual A-owned North AD normal remains. Its full
original mean is

    Q_AD=(-X*k/v,1-v).

The BC normal remains the actual B-owned North normal, with
the entire original mean (1). We have proved the necessary
bounds

    0<w<3/20,       c/s<3/10,
    theta_C>arctan(27/19),
    v>43/240 implies k<3/20.

No physical orientation of C or D is assigned: either may be
tilted at the actual support vertex, and D may still have its
two physical circle corners. The root equations, original C2
and D2 equations, true degrees, actual means and all nine
completion squares remain available in this precise
North/North domain. This source makes no assertion that the
domain itself is impossible.

No numerical search, sampled pose, shortened root equation,
altered mask, normal reselection, compilation, CI, remote
action or shared-metadata change is a premise.

