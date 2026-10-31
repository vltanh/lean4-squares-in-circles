# The North/North pair cannot have a tilted C and an axis-owned D

Date: October 27, 2026.

**Status: complete original-domain hand exclusion, submitted for full
root and separate independent review.** This is a complete shared
boundary-frame case for both surviving B leaf types. It keeps C2,D2
and every original contact mean. Other boundary-frame cases remain
separate.

Keep all nine actual squares and the original adjacent-S component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+E, 0<E<1/60,
    R^2=(2+E)^2+1/4<=Q_*=1105/256.

A is the sole AB side owner and has its strict outer-lower genuine
S leaf. Its actual AD normal is North at (-t_D,H), where
t_D>0 and 37/50<H<1. C,D each have one physical circle corner.
B's actual BC normal is North in its own positively oriented frame

    j=(s,-c),       f=(c,s),       c,s>0, c^2+s^2=1.
    p=c/s.

Write its original BC point in this frame as P=(q,T), T=1-w.
The accepted complete North reductions give

    0<w<3/20,       T>17/20,       p<1/4,              (1)
    q>0,       q<=E+w/p,                              (2)
    w^2+2wc<2E(1+s).                                  (3)

For an owned B leaf, (1)--(3) are exactly Sections 1--2 of
ADJACENT_S_C4_OWNED_TILTED_LEAF_NORTH_CONTACT_REDUCTION.md
in the present tilted-C case.

For a strict B leaf, the complete source
ADJACENT_S_C4_STRICT_TILTED_ROOT_NORTH_CONTACT_REDUCTION.md gives
p<1/4, k<3/20 and its actual parameters xi,U,w with
U=1+xi, 0<xi<E, U^2+w^2=d^2, and xi(1+s)>wc.
Its actual k=xi*c+w*s satisfies

    k-w=c*[xi-wc/(1+s)]>0.

Thus w<k<3/20. Its retained North mean
q=xi+w/(pU+w) is less than E+w/p. Finally

    w^2+2wc
      <2(E-xi)+E^2-xi^2+2xi(1+s)
       =2E(1+s)+(E-xi)*(E+xi-2s)
       <2E(1+s),

because p<1/4 implies s>97/100 and E+xi<1/30.
This verifies all the common premises directly for the strict
leaf as well; the owned-leaf mean formula is not assigned to it.

Every cycle edge has an actual side-axis owner in the common
compatible certificate. Here C,D are physically unique and both
root nonleaf pairs are nonparallel, so the accepted all-cycle
owner selection has exactly its required scope. In particular
CD retains an actual C or D side axis and its original mean.

Assume that C does not own its incoming f axis, while D owns
its incoming world-North axis. We prove that this entire case
is impossible.

## 1. The actual tilted C and a sharper corner bound

The complete high vertical-port theorem gives the actual C frame
in B's coordinates:

    C=P+[0,1]u+[0,1]v0,
    u=(a,b),       v0=(-b,a),
    a,b>0, a^2+b^2=1,
    Z_C=P+u=(q+a,T+b),                                (4)
    q*b-T*a>1/2,       a/b<1/2.

Its opposite-circle corner has already been excluded by the
true unique-corner C2 proper point, with its actual boundary
neighbor D. The original radial point is

    q_C=P+rho*f=lambda*Z_C in C,
    rho=(q*b-T*a)/(q+a)>0.                            (5)

All coordinates in (4)--(5) are the actual original ones.

In fact

    a<7/25,       b>24/25,       0<q+a<51/50.          (6)

To prove the first two bounds, suppose a/b>=7/24. Equation (4)
gives q>(Ta+1/2)/b, hence

    Z_C.u=q*a+T*b+1
       >T/b+a/(2b)+1
       >(17/20)*(25/24)+7/48+1=65/32.

Its other own coordinate satisfies Z_C.v0<-1/2. Therefore

    |Z_C|^2>(65/32)^2+1/4
             =Q_*+61/1024,

a contradiction. Thus a/b<7/24, equivalent to the first two
bounds in (6). The actual circle height is T+b>181/100.
Its circle identity now gives q+a<51/50, since

    (51/50)^2+(181/100)^2-Q_*=3/32000>0.

## 2. Its proper radial point is above its actual left vertex

We prove the strict original-distance bound

    rho>a+p*b.                                       (7)

A useful consequence of (3) is that the function

    F(w,p)=[w^2*sqrt(1+p^2)+2wp]
                         /[2(sqrt(1+p^2)+1)]

is less than E<1/60. It is increasing separately in w and p;
this follows from the increasing functions
sqrt(1+p^2)/(sqrt(1+p^2)+1) and
p/(sqrt(1+p^2)+1).

If a<=1/5, then b>97/100 and T+b>91/50. The actual circle
identity gives q+a<101/100. Together with p<1/4,

    (q+a)*(a+p*b)<(101/100)*(1/5+1/4)
                   =909/2000<1/2.                   (8)

If a>1/5, (4) instead gives q>67/100. Equations (2) and
E<1/60 imply w/p>49/75. Were p>=1/5, we would have
w>49/375. At w0=49/375,p0=1/5, the exact comparison

    (30w0^2-1)*(1+p0^2/2)+60w0*p0-1
       =11009/156250>0

shows F(w0,p0)>1/60: use
sqrt(1+p0^2)<=1+p0^2/2 and 30w0^2-1<0.
Monotonicity contradicts (3). Consequently p<1/5 in this
second range. Equations (6) then give

    (q+a)*(a+p*b)<(51/50)*(7/25+1/5)
                   =612/1250<1/2.                   (9)

Both ranges retain their shared endpoint. By (4),(5), (8)--(9)
imply rho>1/[2(q+a)]>a+p*b, proving (7).

In world coordinates the actual C inward axes are

    u=(e,f0),       v0=(-f0,e),
    e=a*s+b*c>0,       f0=b*s-a*c>0.                 (10)

The positivity of f0 follows from a/b<1/2 and p<1/4.
Its actual minimum-x vertex is P+v0. Equation (7) says

    (q_C-(P+v0))_y
       =s*(rho-a)-c*b
       =s*(rho-a-p*b)>0.                             (11)

This concerns the same actual radial point and the same actual
vertex. No force line or application is reselected.

## 3. The full original CD owner cover

D owns North at the actual negative-horizontal application
(-t_D,H), with H>0 and t_D>0. The negative-port clause of the
true unique-corner vertical theorem therefore gives D's actual
upper-left circle corner. Its x coordinate is strictly negative.

Let g be the original unit normal from D toward C, gamma>0 its
original magnitude, and nu_D>0 the actual AD magnitude.
The full original D2 equation is

    -nu_D*e_y+gamma*g+F_D=0,

where F_D is its positive original radial circle force. Its
horizontal component is negative. Hence

    g_x>0.                                           (12)

No root equation or neighbor degree is substituted here.

Since CD has an actual side-axis owner, (10)--(12) leave exactly
three possible directions:

- D-owned East;
- C-owned u=(e,f0), strictly Northeast;
- C-owned -v0=(f0,-e), strictly Southeast.

D's vertical axes have zero horizontal component and its West
axis has negative one. C's two other axis signs have negative
horizontal component. These three cases therefore exhaust every
original owner and include all possible side-mean endpoints.

### D-owned East

C's actual minimum-x point is the vertex P+v0. The common contact
therefore has that point, even if the original D mean is an endpoint.
The genuine C2 proper radial point for this incoming East normal
must lie on the horizontal line through P+v0. This contradicts
the strict vertical inequality (11).

### C-owned Northeast

The actual C minimum-u side is P+[0,1]v0. Every point of this
side has world height less than

    T+e<1+a+c<1+7/25+1/4=153/100.                    (13)

Here P_y=T*s-q*c<T, q>0. D's support in the strictly Northeast
direction is its upper-right vertex, of height H+1>87/50.
That actual vertex cannot belong to the side in (13).
This argument includes both endpoints and the complete original
C side mean.

### C-owned Southeast

The actual C minimum-(-v0) side is

    P+v0+lambda0*u,       0<=lambda0<=1.

Its original proper radial line is parallel to -v0. Comparing
the u coordinates of its actual point with (5) forces

    lambda0=rho*b.                                   (14)

This is the unchanged original mean; its full interval is retained.
By (4)--(6),

    lambda0> b/[2(q+a)]>8/17.

Writing the actual CD point Q0 in B's frame, (14) gives

    (Q0)_j=q-b+lambda0*a
       =(q+a)-b-a*(1-lambda0)<3/50,
    (Q0)_f=T+a+lambda0*b>17/20+192/425.              (15)

Since p<1/4 gives s>97/100 and c<1/4, its world height obeys

    (Q0)_y=s*(Q0)_f-c*(Q0)_j
       >(97/100)*(17/20+192/425)-3/200
        =1+42111/170000>1.                           (16)

If (Q0)_j is negative the bound is only stronger. On the other
hand D's support in the strictly Southeast direction is its
lower-right vertex, of height H<1. This contradicts (16).
The original lambda0=1 endpoint is included; no strict side
position was imposed.

## 4. Exact complete frame conclusion

All actual CD side-owner cases contradict the original geometry
or genuine C2/D2 equations. Thus the North/North interface cannot
have C tilted at its actual f_B minimum and D owning its world
North axis.

The proof applies to both actual B genuine-leaf types because
their common scalar premises were checked separately at the start.
It does not turn their distinct North mean formulas into one
another. It also does not assign the conclusion to a two-corner D:
the unique physical D mask and its actual upper-left radial force
were explicit premises here.

All nine original squares, true A3/B3/C2/D2 equations, physical
masks, actual side owners, original weighted means and both real
leaves remain. The two other boundary-frame cases are not claimed
closed by this source. No numerical pose, selected surrogate
normal, compilation, CI, remote action or metadata change is used.

