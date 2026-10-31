# Independent full review: an open-origin S root at an owned near strip

Date: October 28, 2026 UTC. Reviewer: thin_d.

**Decision: PASS the complete local theorem and the stated conditional
three-family applications.** The target is
`OPEN_ORIGIN_S_ROOT_NEAR_STRIP_OWNED_SINGLETON_NORMAL_FORM.md`,
SHA256
`c98e9109ed299911d7c5fab5ef6cf16777fcc9eda74b3138aba57029e1d97a39`.
It supplies an exact necessary normal form, not a whole original gate.

## 1. Full reading and the real hypotheses

I read all seven sections and independently recalculated the force,
torque, support, norm and concurrence identities. I read the entire
actual weak-hub source used by the literal callers, and the operative
physical leaf, circle-mask, singleton and triangle inputs. Relevant
current pins are:

| Source | SHA256 |
| --- | --- |
| ONE_UNLOADED_RETURN_HUB_ACTUAL_WEAK_MOMENT_STRIP.md | 382e06b874e41cf582b17374a122c7e4f289472f00cd6d02d926b680f15c1ed5 |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b |

X is the actual open-origin unloaded root with exactly its genuine
S-leaf L and neighbors H,A. H has an actual near strip and owns the
original singleton HX normal; X does not own it. A is physically
boundary and the actual H--A contact is present. H's degree is arbitrary.
The radius restriction d=1+epsilon, 0<epsilon<1/60 is explicit.

The singleton convention is used legitimately: the original application
P is in the relative interior of H's side and is a strict minimum-normal
vertex of X. Thus the two inward X coefficients alpha,beta are both
positive. A shared side or an X-owned singleton is outside this theorem,
and is not silently lost from a full original family.

## 2. Entire genuine-leaf feature cover at X3

The aligned S-root feature is incompatible with O open in X because
its opposite side would have radial height d-1>0. Thus the original
leaf application is a strict X vertex.

At the HX application P, the actual occupied H tangent half-plane and
the strict inward X quadrant leave only two gaps, each narrower than
a unit's right-angle tangent cone. This forbids either other neighbor
containing P. The identical argument at the genuine radial S-leaf's
side-interior application forbids A sharing that vertex. These are
actual occupied-sector arguments, not extra contact assumptions.

For a leaf at the opposite X vertex, I recomputed the complete case
cover using the original force lambda*(a,b)-mu*(alpha,beta)+nu*m=0.
The mixed quadrant m_v<0<m_w gives

    nu*m_v=lambda*(b-a), mu*alpha=lambda*b,
    nu*m_w=mu*(beta-alpha),

so a>b and beta>alpha. The other mixed quadrant is the reflected
inequality. For the negative-v axis, the full actual mean parameter
0<t<=1 gives nu*t=lambda*(a-b) and mu*beta=lambda*b; hence a>b and
alpha<=beta. The negative-w axis gives the reflected result. Positive
axes fail the actual owned-axis triangle inequality; the two same-sign
strict vertex cones apply at the two already forbidden points.

Thus every feature yields (a-b)*(alpha-beta)<=0. Expanding the dot
product into the sums and differences of these unit coordinates proves
n.e_L<=(alpha+beta)/sqrt(2). The resulting bound

    h< -19/80 < -epsilon

is valid throughout d<61/60: sqrt(2)>4/3 implies
61/(60*sqrt(2))<61/80, and alpha+beta>=1 multiplies a negative
coefficient. This excludes the entire opposite-vertex leaf alternative.

The remaining leaf is therefore exactly the adjacent vertex P+v.
Naming this actual axis does not initially assume its closeness to n.

## 3. The complete narrow-angle algebra

For P=x*v-u*w, the open-origin property gives -1<x<0 and 0<u<1.
The genuine S relation and actual H support are

    (1+x)^2+u^2=(1+epsilon)^2,
    h=alpha*x-beta*u>=-epsilon.

These immediately give u>sqrt(2*epsilon), beta*u<epsilon,
beta<sqrt(epsilon/2)<1/10 and alpha>99/100. The squared support
inequality has positive sides; its exact expansion is

    u^2+2*beta*(alpha-epsilon)*u
       <=2*epsilon*(alpha^2+alpha)-beta^2*epsilon^2
       <4*epsilon.

The discarded middle term is positive, so u<2*sqrt(epsilon).
The leaf equation then gives x>-epsilon. No sign is lost by squaring.

For L0=beta*x+alpha*u, the exact identity

    alpha*L0=u+beta*h

gives L0>sqrt(2*epsilon)*(1-epsilon/2)>sqrt(epsilon), while x<0
gives L0<u<2*sqrt(epsilon). The actual positive HX moment then fixes
the stated handed assignment P=h*n-L0*Jn. It is not a reflection
performed after fixing the original moment sign.

## 4. The original A port and true X concurrence

The complete X3 equation makes m.w>0. Its positive-v alternative
would place the actual A point at P+v+w, whose n displacement from P
is alpha+beta>1. The strict support-span at that unchanged point would
put all of A strictly beyond H's actual support, contradicting HA.
The zero-v axis is excluded by the owned-axis triangle theorem.
Hence m.v<0<m.w and Q=P+w is forced.

The two actual HX and radial-leaf lines are independent. Substitution
of q=P+r0*n into the leaf line gives exactly

    r0=u/[beta*(1+x)+alpha*u]
       =u/(beta+L0)>0.

The full torque makes the original third line pass through the same
q. Thus m is the positive normalization of w-r0*n, and its positive
w component gives beta*r0<1. The denominator bounds yield

    2/3<r0<1/alpha<100/99.

These are derived from the true X3 only. H is not assigned a leaf,
A is not treated as unloaded2, and no circle resultant is substituted.

## 5. Physical A mask and every remaining HA normal

The actual Q has |Q.n|<1/10 and Q.Jn>0. If a physical circle corner
Z of A had Z.Jn<=0, expanding |Z-Q|^2 gives

    |Z-Q|^2>(R-1/10)^2>(19/10)^2>2,

contradicting the one actual unit's diameter. The strict inequality is
valid even if that corner has zero original circle weight.

I checked the norm identity

    |Q|^2-d^2=-2*(x+u)<0.

The exhaustive physical two-circle-corner classification is the radial
S rectangle whose every point has norm at least d. Hence A cannot have
two physical circle corners. Its given physical boundary status makes
it physically unique-corner, without a force-weight assumption.

The actual H-owned HX side and triangle HXA give N.n>=0. For the
strict downward HA cone, the actual H point D=(h,g-1) satisfies

    (D-Q).(w-r0*n)=beta*r0-1+alpha*(g-1+L0)<0.

Both strict terms follow from beta*r0<1 and the original relative
side-interior position of P, namely g-1<-L0. This contradicts D in
the actual A support half-plane. The South-axis alternative lies
entirely below g-1<=0 and contradicts A's positive-height circle point.

At the remaining horizontal endpoint N=n, every point of A would have
n projection at least h. The actual inward unit segment Q+[0,1]m lies
inside A for any minimum-m support feature. The inequalities

    r0-beta>17/30,
    beta*|w-r0*n|<3/10

put its endpoint Q+m strictly below h in n projection. This excludes
the horizontal endpoint, leaving exactly N.n>=0 and N.Jn>0.
All original side, vertex and mean endpoints have been covered.

## 6. Exact original callers and remaining gap

The actual weak-hub source proves the retained-domain near strip and
nonzero exceptional HX moment for the open-origin members of roof
AC.S, roof ABC.S and endpoint-fan234.S. Its private source/sink argument
uses the full torques despite a possible zero-moment H return; it does
not transfer a contradicted far-domain strict sign without a proof.
It also retains the real house transmitter, when present, and J4 in
the fan. Those are exactly the hypotheses needed here.

For either house, H=D is truly unloaded3. After the current normal-form
conclusion, its complete force makes its remaining H-to-C normal
strictly negative in both (n,Jn) coordinates. For the fan, H=J is
truly degree four: only the aggregate of the other two original
forces has that sign. The source explicitly preserves this distinction.

The theorem excludes no entire original family. Shared HX, X-owned
singletons, non-open-origin X and the remaining physical thin strip
still require their stated separate arguments. All nine units, their
actual circle, zero weights, original normals and means remain.

I found no gap or source revision needed. No numerical certificate,
angle subdivision, Lean run, CI or metadata edit is used by this review.
