# A radial boundary square forces an owned adjacent-root contact

Date: October 27, 2026.

**Status: complete hand necessary-domain and compatible owner-reduction
theorem, submitted for full root and separate independent review.**
This covers the entire physical mask in which at least one of C,D
has two circle corners. It is not a whole mixed-mask exclusion.

Keep the original positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,

with genuine S leaves L,M, physically clear A,B, and positive total
circle loads at C,D. Work in

    d=1+epsilon=sqrt(R^2-1/4)-1,
    0<epsilon<1/60,       R^2<=1105/256.

Assume C has two physical circle corners, so its actual square is
radial S. D may have either complete physical mask. Every individual
zero circle weight, original normal owner and application mean remains.
The same nine actual units are retained.

The conclusion is that the original AB normal has a side-axis owner
at A or B in the common compatible necessary certificate. Its proof
uses the earlier true-S-three-force singleton preselection, not the
unique/unique force-cycle determinant. It therefore includes the
mixed physical mask that the latter theorem deliberately retained.

## 1. The full physical CD feature cover

Use C's actual radial coordinates

    C=[d,d+1] times [-1/2,1/2].

An outward C normal with positive first component either exposes an
outer circle corner, which no other unit can contain, or is East on
the outer side. The latter would put the neighboring unit's minimum
horizontal support at d+1; its width at least one would then exceed
the containing disk. Thus it cannot occur.

The West inner-side normal cannot have a physical boundary neighbor
D, by the complete force-free Lemma 2.1 of C7_FORCE_POLYGON.md,
including every actual point on that side. Hence the original CD
normal has a nonzero vertical component. Reflect to make it positive.

The complete remaining CD alternatives are therefore

    n_CD=(-a,b), a,b>0, at Q=(d,1/2);                  (1a)

or

    n_CD=(0,1), at Q=(x,1/2), d<=x<=d+1.             (1b)

The actual mean x in (1b) is retained. In both cases the original
positive CD force has strictly positive origin moment. No normal
selection or equation at D is used to obtain this cover.

## 2. The BC point is an actual inner corner owned by B

Let m be the original C-to-B normal, with magnitude mu>0. Since B
contains its genuine point epsilon*e_M,

    h_C(m)<=epsilon.

For m_x>=0 the support is at least 1/2, so m_x<0. If m_y>0,
the BC point is (d,1/2) and its torque is strictly positive, as is
the complete CD torque in both (1a) and (1b). C's true zero origin
moment excludes this. If m_y=0 the point is (d,y), and the same
equation makes y<0. If m_y<0 the point is (d,-1/2). Thus the
unchanged BC point P always satisfies

    d<|P|<=sqrt(d^2+1/4).                               (2)

### 2.1. No B vertex belongs to the annulus

For tilted B use its actual shallow genuine-leaf chart, valid from
A's real epsilon-near point alone:

    B=[U-1,U] times [V-1,V],
    U^2+V^2=d^2,       U>=1-epsilon,       0<V<4/15.

Its actual vertex norms squared are

    d^2,
    d^2+1-2U<d^2,
    d^2+2-2(U+V)<d^2,
    d^2+1-2V>d^2+7/15.

They miss (2) completely. This chart and its physical derivation are
Section 3 of
ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md;
neither its unique-mask selection nor a triangle premise is used.

For aligned B use the genuine-leaf frame

    B=[epsilon,d] times [h-1,h],       0<=h<=1.

The left vertices have norm below d. A possible right vertex in (2)
can, after reflection, be written P=(d,h), 0<h<=1/2. Its original
B-to-C normal is (c,s), c,s>=0. If s=0, C would have minimum
support d in B's genuine leaf direction. A radial S unit has such
minimum support only in its own radial direction, so C would equal
the actual distinct leaf M. Therefore s>0.

Let alpha>0 be the actual East leaf force. The full balancing B-to-A
force is (-alpha-mu*c,-mu*s), so its actual point is the lower-left
B vertex. Full origin torque gives

    alpha*(1-h)=mu*(s-c).

Hence s>c. Put w=1-h>=1/2 and k=1-h*c/s, so w<=k<=1.
The actual B-to-A unit normal is (-k,-w)/sqrt(k^2+w^2).
A's genuine epsilon-near point forces

    w^2<=epsilon*(k+sqrt(k^2+w^2))
        <=epsilon*(1+sqrt(2))<1/24,

contrary to w^2>=1/4. This keeps c=0 and both actual height
endpoints. Thus no aligned B vertex belongs to (2) either.

Consequently P lies in the relative interior of an actual B side.
B owns the original BC normal, and not merely a limiting replacement
normal.

### 2.2. The inner-side mean alternative is excluded

If m_y=0, the B-owned B-to-C support is d in C's radial direction.
For tilted B, all its own support heights U,V,1-U,1-V are below d.
For aligned B, the perpendicular heights are at most one, its
opposite-leaf support is -epsilon, and the only remaining support d
would identify C with its actual leaf M. This is impossible.

Therefore the original contact is exactly

    P=(d,-1/2),
    n_BC=(c,s),       c,s>0,       c^2+s^2=1.           (3)

It is a fixed actual C vertex and a relative B-side-interior point.
Put

    H=d*c-s/2,       t=d*s+c/2>1/2,
    H^2+t^2=d^2+1/4.                                  (4)

The strict t bound follows from d>1 and c+s>1. No choice of the
two C circle weights has entered the argument. In particular (1b)'s
original CD mean is still arbitrary.

## 3. Complete full-B3 routing at the near root edge

The following also gives the exact singleton hypotheses required for
the finite selection in Section 4.

### 3.1. Tilted B

The force-free theorem
SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md removes B's
positive-vertical boundary normals and its East own normal. Since B
owns BC, only West and South could remain. Both West-side endpoints
have norm below d, so the whole West side misses (2). Thus BC is
the actual South own normal.

Use B's actual own axes u,v with

    B=[U-1,U]u+[V-1,V]v,
    d*e_M=Uu+Vv,
    n_BC=-v,
    H=1-V>11/15,
    P=t*u+(V-1)*v,
    U-1<t<U.                                          (5)

The sign of u is fixed by t>1/2 in (4). The alternative negative
t cannot be in the actual u interval, whose lower endpoint is at
least -epsilon. These coordinates may reflect the earlier C frame;
all zero torque equations remain unchanged under that reflection.

Write the original genuine leaf force as alpha*(U,V), alpha>0,
and the original BC magnitude as nu>0 in this own frame. The full
B-to-A force is

    (-alpha*U, nu-alpha*V).                            (6)

It has negative first component. If its second component were
negative, its point would be the lower-left B vertex. The exact full
torque would then be

    nu*(U-1-t)+alpha*(V-U)=0,

whose two terms are strictly negative. This is impossible.

There are precisely two surviving actual alternatives:

* The second component is zero. AB is B-owned West, with actual
  point (U-1,y), and the full force and torque equations give

      nu=alpha*V,
      |F_BA|=alpha*U,
      y=V*t/U,       0<y<V.                            (7)

  The original mean is this genuine side point; no endpoint is
  substituted for it.

* The second component is positive. AB is strict Northwest at the
  fixed B vertex

      Q=(U-1,V).

  Its full original coefficient relation is

      nu*(t-U+1)=alpha*V.                              (8)

  The factor t-U+1 lies strictly in (0,1), so (8) indeed retains
  the strict positive second component in (6).

Thus (7) is already an owned AB contact. The only still-free
possibility in (8) is a singleton at Q, distinct from the singleton
P. Moreover

    det((U,V),Q)=V!=0,

so Q is not collinear with B's actual radial leaf direction.

### 3.2. Aligned B

Since B owns n_BC, its real leaf direction is parallel or
perpendicular to that axis. It cannot be the positive axis because
H<d in (4). If it were the negative axis, H=-epsilon and the
absolute transverse coordinate of P would exceed one:

    t^2=d^2+1/4-epsilon^2=5/4+2*epsilon>1.

That is impossible in the actual unit transverse interval containing
the genuine leaf axis. Thus the leaf is perpendicular. Set
u=(s,-c) in the C frame. Since P.u=t>0, the real leaf direction
is u, not -u. In the actual frame (u,n_BC),

    B=[epsilon,d] times [H-1,H],
    0<=H<=1,       epsilon<t<d,
    P=(t,H).

The original leaf force is alpha*u, alpha>0, and the original BC
force is nu*n_BC, nu>0. Hence the actual B-to-A force is strictly
Southwest, at the fixed lower-left vertex

    Q=(epsilon,H-1).

Full torque gives

    nu*(t-epsilon)=alpha*(1-H),                        (9)

so H<1. Put w=1-H>0 and x=t-epsilon>0. The actual A near
point gives

    w^2<=epsilon*(x+sqrt(x^2+w^2)),
    w^2<=2*epsilon*t-epsilon^2
        <=d^2-1<121/3600.

Consequently

    49/60<H<1.                                        (10)

The original Q has nonzero vertical coordinate, so it is not
collinear with the genuine leaf direction. It is distinct from P.
AB cannot be B-owned in this aligned case.

## 4. The compatible preselection supplies the remaining A owner

Only the two strict B-vertex cases in Sections 3.1 and 3.2 remain.
If A does not own their actual AB normal, the physical contact
classification makes AB a free point-only vertex/vertex contact.
The original strict-point convention excludes a nonowned axis endpoint.

Apply the complete singleton true-S-three-force preselection of
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md, Section 4. Here the
two actual singleton points are Q on AB and P on BC. The latter is
fixed by the physical C vertex (3), even though B owns its side.
The actual BC normal m is a fixed B own axis and is not parallel
to the actual genuine leaf direction e. The actual Q is
noncollinear with e by Section 3.

For clarity, the necessary full-star determinant identity for a free
AB normal n is

    det(e,n)*det(P,m)-det(e,m)*det(Q,n)=0,
    det(W,n)=0,
    W=det(P,m)*e-det(e,m)*Q.

Noncollinearity gives W!=0. This identity excludes only finitely
many directions in the original free AB interval, independently of
the two C circle weights, every CD mean, and all equations at A,D.

The finite pose prelist includes these actual leaf/root/singleton
assignments before multiplier extraction. Its normal parameters at
Q and P are distinct; the BC direction is already a fixed own axis.
A matched opposite-pair parameter at Q therefore does not couple
this variation to BC. The same prelist is compatible with all
earlier open dense choices and with the open radial-pair restriction
in ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md.
Uncrossing and thinning retain the surviving normals and only add
already available side-endpoint atoms.

Thus the common compatible necessary certificate cannot retain a
free AB in either singleton case. A owns the actual normal there.
Together with (7), this proves that AB is owned by at least one
actual root throughout the whole stated two-corner physical mask.

## 5. Exact complete reduction and retained frontier

For every original high LCD.SS component with at least one two-corner
physical mask, rename the actual radial boundary unit as C by the
attachment symmetry and reflect as in Section 1. Then:

* CD is exactly (1a) or (1b), with its original mean.
* BC is the actual inner C corner (3), owned by B.
* Tilted B has exactly the West-owned mean (7) or the strict
  Northwest singleton (8); in the latter A owns AB.
* Aligned B has exactly the strict singleton (9)--(10), and A owns AB.
* Every true C2/D2 mask, individual zero weight and full A3/B3
  equation remains available to the later original caller.

In particular the original AB owner classification is now available
for every high physical mask: the unique/unique source handles that
mask, and this theorem handles at least one two-corner unit. Neither
source identifies a physically two-corner unit with a unique-corner
one, or puts its concurrence inside it without the appropriate
physical premise.

The both-two-corner mask is separately excluded by
ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md. The mixed
one-corner / two-corner mask still requires its whole remaining owner
cases. No full fine or coarse gate is claimed here.

This proof uses the same nine actual units, all original means and
full force/torque equations. There is no normal reselection after
extraction, shortened neighbor equation, numerical pose, compilation,
CI, remote action or shared-metadata change.
