# An intact petal cannot be balanced entirely by small-support external forces

Date: October 27, 2026.

**Status: accepted complete full-force theorem and adjacent-C4 load exit.**
Full root review: REVIEW_INTACT_SMALL_SUPPORT_EXTERNALS_ROOT_2026_10_27.md.
Separate independent review:
REVIEW_INTACT_PETAL_SMALL_SUPPORT_EXTERNALS_LEAF_PAIR_2026_10_27.md.
Both full-source/scope reviews pin the mathematical source before this
acceptance-only header edit.
No shared ledger or original gate is changed.

Keep the same original nine physical units and compatible selected
certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose H,U,V is an actual intact positive triangle, with U,V at
their true loaded positive degree two. Keep H's complete original
force system. Besides the two intact-petal forces, assume that H has
at least one other positive pair force, and that every such force has
its original outward H normal n_i and actual support satisfying

    h_H(n_i)<=epsilon.                                  (1)

**Theorem.** This entire original configuration is impossible. The
number, degrees, loads and physical identities of the other neighbors
are arbitrary. The actual normals and means are not replaced, and
each force keeps its own unchanged magnitude.

## 1. Every original outside normal belongs to one narrow cone

`ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md` puts O in int H and makes
H physically circle-clear. Thus every support h_H(n_i) is positive;
(1) implies epsilon>0 and d>1. If all four own side heights of H
exceeded epsilon, its support in every unit direction would exceed
epsilon: in own coordinates it is the sum of two positive side
heights multiplied by the absolute direction components, whose sum
is at least one. Therefore an actual own side has positive height
sigma<=epsilon.

The complete `INTACT_PETAL_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md`
now gives the unchanged actual chart

    H=[-sigma,1-sigma] x [-P,a],
    0<sigma<=epsilon<1/60,
    16/25<P<=11/15,
    a=1-P,       4/15<=a<9/25.                          (2)

For each original n_i, the support formula in (2) and (1) exclude
a nonnegative x component, since that would give support at least
4/15. Write

    n_i=(-c_i,s_i),       c_i>0,
    c_i^2+s_i^2=1.

The same support formula gives

    epsilon>=h_H(n_i)
       =sigma c_i+a max(s_i,0)+P max(-s_i,0)
       >=(4/15)|s_i|.

Hence every original normal has the strict bounds

    |s_i|<1/16,       c_i>15/16,
    |s_i|<(1/15)c_i.                                   (3)

Let its actual positive magnitude be beta_i, and set

    W=sum_i beta_i n_i.

There is at least one such force, so (3) gives

    W_x<0,       |W_y|<(1/15)(-W_x).                     (4)

This is a sum of the complete real outside pair forces. No outside
body or branch is turned into an artificial physical force atom.

## 2. The unchanged intact-petal resultant cannot point oppositely

In the exact shallow chart, the actual common petal side is the
bottom side. Write its two original applications and outward normals
as

    p_1=(-w,-P),       p_2=(z,-P),
    0<w<=sigma,        0<z<=1-sigma,
    n_1=(-s_1,-c_1),   n_2=(s_2,-c_2),
    s_1,s_2>=0,        c_1,c_2>0.                       (5)

These are the full actual common-side and strict straddling conclusions
of the shallow theorem and `ROOTED_END_TRIANGLE_ORIGIN_INTERIOR.md`,
Sections 1--5. All original shared means and normal-cone endpoints
remain. Let mu_1,mu_2>0 be their original magnitudes and put

    M=mu_1 n_1+mu_2 n_2=F_U+F_V.

In particular M_y<0. If the root normals are parallel, the full
parallel-root argument in the same origin theorem makes both actual
normals vertical downward. Then M_x=0.

Otherwise the genuine intact-root concurrence has the exact form

    q=-t M,       t>0,

with p_1,p_2 on their respective unchanged normal lines. This is
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Sections 2--3, as recorded
at the arbitrary-root scope in the origin theorem. Therefore

    det(p_2,n_2)
       =-t det(M,n_2)
       =-t mu_1 det(n_1,n_2)<0,

because det(n_1,n_2)=s_1 c_2+c_1 s_2>0 in this nonparallel case.
Equation (5) consequently gives

    -z c_2+P s_2<0,
    s_2/c_2<z/P<25/16.                                 (6)

It follows, including the possibility M_x<=0, that

    M_x=-mu_1 s_1+mu_2 s_2
          <(25/16)(mu_1 c_1+mu_2 c_2)
          =(25/16)(-M_y).                              (7)

The parallel case also satisfies (7), since M_x=0 and M_y<0.
This is a bound on the whole genuine intact resultant, obtained only
from its true two-tip equations and actual applications.

## 3. The complete original H equation is contradictory

H's physical clearance has already removed its circle force for a
geometric reason. Its full actual equation is exactly

    M+W=0.                                              (8)

Equations (4),(8) give

    M_x>0,       -M_y=|M_y|<(1/15)M_x.

Equation (7) instead gives

    -M_y>(16/25)M_x.

Since 16/25>1/15 and M_x>0, this is impossible. Both the parallel
and nonparallel petal domains, and every original outside-force
magnitude and support endpoint, have been included.

## 4. Near-neighbor and genuine-channel forms of the hypothesis

Two complete local ways to verify (1) are useful in larger original
graphs. Neither requires reducing the neighbor's degree.

First, if an actual positive neighbor K of H meets D_epsilon at k,
the original outward normal n satisfies

    h_H(n)<=n.k<=epsilon,

because the whole original K lies on the outward side of its
physical separator with H.

Second, suppose the actual H force enters a genuine normal channel
with one or more true unloaded degree-two internal bodies and a
contained actual far endpoint B. Let w>=1 be its real total width,
n its original channel direction and h its actual H support. The
full channel equations and the sharp contained-unit center bound
give

    B subset {z:n.z>=h+w},
    h+w+1/2<=n.c_B<=|c_B|<=d+1/2.

Thus

    h<=d-w<=d-1<=epsilon.                               (9)

This retains every real channel application and every actual side
or diagonal width. The far endpoint may have arbitrary original
degree, circle mask and additional forces. Equations (1) and (9)
do not assign a leaf equation to that endpoint.

Consequently an intact root cannot have every one of its other real
positive forces directed either to an actual near-origin neighbor
or into a genuine normal channel. The complete original list of
outside forces must meet this condition; one qualifying sublist is
not sufficient.

## 5. One entire adjacent-leaf C4 load alternative is excluded

In C2.34.b1, let the original triangle H,U,V be intact and let its
four-cycle be

    H-K-J-B-H,

with the sole genuine leaf at the adjacent K. The actual degrees
are H4,K3,J2,B2,U2,V2 and leaf degree one. Both arbitrary remaining
physical squares stay present.

K is an actual near-origin genuine leaf root. If B is unloaded,
the unchanged path H-B-J is a genuine normal channel. H's only
forces outside its intact triangle are precisely HK and HB. The
two alternatives in Section 4 verify (1) for both real forces,
and Sections 1--3 give a contradiction.

Thus the complete original domain with B unloaded is excluded,
including every S/D leaf type, every possible J load and physical
mask, and every original frame and mean. The cases with B loaded
and J either unloaded or loaded are not claimed closed here. No
fictitious triangle, force deletion, numerical pose, Lean build,
CI or remote action is used.
