# The owned S leaf excludes both parallel boundary frames in the North pair

Date: October 27, 2026.

**Status: complete original-domain proof, submitted for full root and
separate independent review.** This closes the last both-axis North/North
frame for B's owned far-axis genuine leaf. It keeps every original mean
and the full A3/B3/C2/D2 equations. Its exact scalar dependency is
NORTH_PAIR_OWNED_ROOT_SCALAR_SEPARATION.md.

## 1. Original component and actual North chart

Keep all nine actual squares and the positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

The actual roots A,B have genuine S leaves L,M. C,D each have exactly
one physical circle corner and are loaded. A alone owns the actual
AB normal. The prior complete one-owner leaf cover leaves A's
strict outer-lower leaf; this source concerns B's owned far-axis leaf.

Use the complete original contact reduction
ADJACENT_S_C4_OWNED_TILTED_LEAF_NORTH_CONTACT_REDUCTION.md,
SHA86b433cd94130623459d5cd0d0b5df3424f3a348750d996aa94ed3a29af53132.
It retains the actual North/North chart

    d=1+e, 0<e<1/60,
    R^2=(2+e)^2+1/4<=Q=1105/256,

    A=[-X,h] times [-v,1-v],
    X=1-h, X^2+v^2=d^2,
    |h|<=e, 0<k<v<13/50,
    P_AB=(h,-k),

    j=(s,-c), f=(c,s), c,s>0, c^2+s^2=1,
    B=[e,d] times [-w,1-w] in its actual (j,f) frame,
    h=e*s-w*c, k=e*c+w*s,
    0<w<3/20, p=c/s<3/10.

The real B leaf has inner point d*j. The two original outer
contacts, with their unchanged means, are

    AD North at (-t_A,1-v), t_A=X*k/v>0;
    BC f at (q,1-w) in B's frame,
    q=e+w/p=k/c.                                    (1)

The zero-depth B endpoint has already been excluded by the complete
contact reduction; it is not silently removed here. All original
circle masks and the three arbitrary completion units remain.

Assume in this frame that D owns the incoming North axis and C
owns the incoming f axis. The actual unique-corner high-port theorem
from Section 1 of ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md
then gives

    H=2-w, Z=sqrt(R^2-H^2)>1/2,
    C=[Z-1,Z] times [1-w,2-w] in (j,f),
    Z_C=Z*j+H*f;

    Y=sqrt(R^2-(2-v)^2)>1/2,
    D=[-Y,1-Y] times [1-v,2-v],
    Z_D=(-Y,2-v).                                   (2)

Both uses have the true degree two, unique physical corner and
other neighbor physically boundary required by that theorem.
No parallel-frame assumption is made about a body outside this
specific frame. In particular

    1/2<Z<19/20, H>37/20.                           (3)

The sharp upper radius also improves the root parameter:

    e<e0=31/1875,

because

    (2+31/1875)^2+1/4-Q=391/900000000>0.              (4)

The actual owned-root radius identity is exactly

    v^2=(1+e)^2-(1-e*s+w*c)^2.                      (5)

Thus the scalar lemma's complete base hypotheses hold.

## 2. Complete original CD owner cover

The compatible all-cycle owner theorem applies here: both root
nonleaf pairs are nonparallel, while C,D have unique physical
corners. It supplies an actual side-axis owner of CD before stress
extraction, without selecting any new shared-side mean.

Let g be the actual unit normal from D to C, with magnitude gamma>0.
The full D2 force equation is

    lambda_D*Z_D=nu_D*e_y-gamma*g,
    lambda_D,nu_D>0.

Its horizontal coordinate gives g_x>0. The available actual side
axes therefore leave East, j or f. The f case would make the full
C2 circle force parallel to f, contrary to its actual positive
Z coordinate in (2). Thus exactly two possibilities remain:

    g=East, owned by D;
    g=j, owned by C.                                (6)

For East, C's actual minimum-x point is its lower-left vertex.
For j, D's actual maximum-j point is its lower-right vertex.
The other body's full original side mean remains free until its
physical contact equality is used. These alternatives include the
actual side endpoints and use no fictitious three-body moment.

The proper-ray conclusion at the true unique-C tip also gives

    q>=((1-w)/(2-w))*Z>1/4+w.                       (7)

For completeness, the second strict comparison follows by using
R^2>17/4 and squaring positive sides. Its numerator is

    w*[7/4-(173/16)w+(19/2)w^2-2w^3]>0.

For 0<w<3/20 the bracket exceeds 971/8000, even after dropping
its positive quadratic term. No C mean has been reset to attain
the lower bound in (7).

## 3. D-owned East: the exact full C2 quadratic

The actual CD point is

    S=(Z-1)*j+(1-w)*f,

so equality with D's right side gives

    Y+s*Z+c*(1-w)=1+s.                              (8)

Its world height is y_S=s*(1-w)+c*(1-Z). The unchanged C2
force and torque equations give

    q*[H*s-Z*c]=Z*y_S.

Indeed the full circle force is nu_C*f+gamma*e_x, and the
actual two pair moments are nu_C*q and -gamma*y_S. No radial
point or side mean is chosen to obtain this identity.

Substituting the true owned-root mean q=e+w/p from (1) gives

    Z*(d-Z)*p^2+[Z-e*H]*p-w*H=0.                    (9)

Both leading coefficients are positive: Z<d follows from

    Z^2-d^2=-3/4+2e+4w-w^2<0,

and Z-eH>1/2-1/30>0. Thus the polynomial in (9) increases
strictly for nonnegative p.

Write z=c/(1+s)=p/[1+sqrt(1+p^2)]. We next prove exactly
the two strip bounds required for the scalar East inequality:

    9/10<z/w<2       if w<=1/25,
    9/10<z/w<3/2     if w>=1/25.                    (10)

## 4. Complete lower and upper strip bounds

For fixed w introduce only the auxiliary scalar polynomial

    Z_eta=sqrt(1/4+4eta+eta^2+4w-w^2),
    P_eta(x)=Z_eta*(1+eta-Z_eta)*x^2
               +[Z_eta-eta*H]*x-wH,
    0<=eta<=1/60.                                   (11)

At eta=e this is the original polynomial (9). Varying eta in
this comparison is not a physical motion or a reselection of any
normal, force or mean.

### Lower bound, all actual w

Set x=(9/5)w/[1-(81/100)w^2], the p corresponding to
half angle (9/10)w. We have x<3/10. As a function of Z,
the Z-dependent part of P_eta(x) has derivative

    x*[1+x*(1+eta-2Z)]>0

over 1/2<=Z<=19/20. Increase Z to 19/20 and 1+eta to
61/60, and discard the negative term -eta*H*x. Also set

    b=72000/39271,
    x/w<=b, x^2/w<3b^2/20, H>37/20.

Then

    P_e(x)/w
      <(19/300)*(3b^2/20)+(19/20)*b-37/20
      =-2354135317/30844228820<-3/40.

The increasing original polynomial therefore has its positive
root p>x. Since half angle increases with p, z/w>9/10.

### Upper bound when w<=1/25

Set x=4w/(1-4w^2), corresponding to half angle 2w.
Here x<1/6 and Z_eta<7/10 throughout (11). Direct differentiation
gives

    (d/deta P_eta(x))/x
      =[(2+eta)/Z_eta]*[1+x*(1+eta-2Z_eta)]
           +Z_eta*x-H
      >(20/7)*(14/15)-2=2/3>0.                     (12)

At eta=0, positivity of the quadratic term and Z_0>=1/2 give

    P_0(x)/w>4Z_0-H>=w>0.

Hence P_e(x)>0 and p<x, proving z/w<2.

### Upper bound when 1/25<=w<=1/10

Set x=3w/[1-(9/4)w^2], corresponding to half angle (3/2)w.
Throughout this range

    x<=120/391, 63/100<Z_eta<17/20, H<=49/25.

Expanding the derivative in (12) instead gives the exact lower bound

    (d/deta P_eta(x))/x
      >=40/17-49/25
          +(120/391)*(40/17-121/30+63/100)
      =11727/166175>0.                              (13)

At eta=0, 639/1000<Z_0<=4/5. The first strict inequality follows
from the exact squared reserve 79/1000000 at w=1/25.
Thus Z_0*(1-Z_0)>=4/25. Since x/w>=3 and x^2/w>=9w,

    P_0(x)/w
      >9*(1/25)*(4/25)+3*(639/1000)-49/25
      =73/5000>0.

Equations (13) and the increasing original polynomial give
p<x, hence z/w<3/2.

### Upper bound when w>=1/10

Use the same x. Here Z_e>4/5 and H<=19/10. Dropping the
positive quadratic term gives

    P_e(x)/w>3*(4/5-19/600)-19/10=81/200>0.

Again p<x. These ranges cover every actual w in (0,3/20),
including w=1/25 and w=1/10. This proves all of (10).

## 5. Finish the East interface

Apply the first complete scalar inequality to (4), (5), (10).
With F(x)=sqrt(Q-(2-x)^2), it gives

    F(v)+s*F(w)+c*(1-w)<1+s.

But the original R^2<=Q gives Y<=F(v), Z<=F(w), so the
actual contact identity (8) is impossible. Every original
East side-mean endpoint is included by that identity.

## 6. C-owned j: the complete other strip and exit

Now the actual CD point is the lower-right D vertex

    S=(1-Y,1-v).

Its equality with C's minimum-j side gives

    s*(1-Y)-c*(1-v)=Z-1.                            (14)

The full C2 equation, with the entire original CD side mean,
gives

    q*H/Z=S dot f=c*(1-Y)+s*(1-v).                  (15)

This also follows directly from its full force nu_C*f+gamma*j
and the unchanged torque nu_C*q-gamma*(S dot f)=0.

Since Y>1/2 and v>0, Cauchy--Schwarz gives

    S dot f<s+c/2<=sqrt(5)/2<9/8.

Using (3) in (15),

    q<171/296.

The actual q=e+w/p then gives p/w>296/171. Since
sqrt(1+p^2)<21/20,

    z/w>5920/7011>4/5.                              (16)

Conversely (7) gives

    w/p=q-e>1/4+w-e>7/30,
    z/w<p/(2w)<15/7.                                (17)

Thus the second complete scalar inequality applies at the actual
data. It gives

    s*[1-F(v)]-c*(1-v)>F(w)-1.

Since Y<=F(v), Z<=F(w), its left side is no larger than
s*(1-Y)-c*(1-v), while its right side is no smaller than
Z-1. This contradicts the exact actual contact equality (14).
The full C-owned CD side mean, including both endpoints, was
retained in (15); no midpoint or radial mean was imposed.

## 7. Exact original conclusion

The two actual side-owner alternatives in (6) exhaust this
both-incoming-axes frame. Both are impossible. Therefore the
entire owned-B-leaf, unique/unique North/North configuration
with C parallel to B and D parallel to A is excluded.

Together with the separately complete shared sources

    NORTH_PAIR_TILTED_C_AXIS_D_EXCLUSION.md,
    NORTH_PAIR_TWO_TILTED_BOUNDARY_TIPS_EXCLUSION.md,
    NORTH_PAIR_AXIS_C_TILTED_D_EXCLUSION.md,

this supplies all four boundary-frame exits for the literal
owned-root North caller. The other original BC features and
the original AD cover remain the previously accepted exact
contact reductions; they are not removed by a new force choice.

Every genuine leaf, original normal, actual mean, physical
corner, full true degree and all nine physical units survive.
The only finite coefficient certificate is the fully specified
exact rational scalar lemma. No sampled configuration, numerical
optimization, Lean compilation or CI is a premise of this proof.
