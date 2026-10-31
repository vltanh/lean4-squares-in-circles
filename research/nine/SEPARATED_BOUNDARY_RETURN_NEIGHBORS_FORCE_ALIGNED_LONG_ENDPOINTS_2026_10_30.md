# Separated boundary return neighbors force both long endpoints to align

Date: October 30, 2026 UTC.

**Status: complete proposed continuous hand proof, awaiting full independent
review of this frozen assembly. The entire tilted-long-endpoint branch is
excluded; the aligned sharp seven-body remainder is not declared closed.**

The new step couples the two actual endpoint joins. Each return square
contains a point one unit along its original contact normal from its
actual contact mean. If either long endpoint is tilted, full endpoint
force and torque balance constrain both normal directions strongly enough
that those two occupied points have distance strictly less than one.
This contradicts the actual set gap forced by any nonempty transmitting
run between the return squares.

## 1. Precise local theorem and the frozen endpoint reduction

Let actual unit squares with pairwise disjoint open interiors lie in the
disk centered at the unchanged origin with q=R^2<=Q=1105/256. Retain one
complete physical force-and-torque certificate. It contains a positive
channel

    A -- U -- V -- B

whose two internal bodies U,V are unloaded and have true positive degree
two in the whole retained graph. Their original full moment equations
hold. Choose the common signed channel normal as e_x by one rotation
about the disk origin.

Assume A and B themselves have true positive degree two. Their other
positive contacts are respectively with distinct actual squares D and C.
All four bodies A,B,C,D physically touch the containing circle. The whole
actual squares C,D lie in y>0, and

    dist(C,D)>=1.                                       (1)

All original contact points, means, normals and circle weights remain.
The other actual packing squares and all their restrictions remain too.
There is no bound on the full degrees of C,D. This local theorem itself
requires no planar embedding or lower radius bound, once the stated
above-side geometry has been established.

**Theorem.** Both A and B have an own side axis parallel to e_x.

The complete frozen input is

`LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md`,
SHA256 `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3`.

Its Sections 1--8 apply to these exact full endpoint stars. They prove
that the original long means are

    q_A=(s-1,t), q_M=(s,t), q_B=(s+1,t),
    |s|<1/60, |t|<=9/16,
    |y_A|+|y_B|<=1/8.                                  (2)

If either endpoint is tilted relative to e_x, the same source proves

    -9/16<=t<-1/2, y_A<0, y_B<0,                       (3)

and both actual return means are the upper-inner endpoint vertices,
with the complete strict inward/upward common-normal cones retained.
Neither endpoint may use its own upper-axis normal in this branch.
This includes an aligned endpoint when only the other endpoint is tilted.
No neighbor-owned or generic point-contact premise is introduced.

For a tilted right endpoint, its actual axes and points are

    u=(a,-b), v=(b,a), a^2+b^2=1, a>=b>0,
    q_B=(x,t), x=s+1,
    p_B=q_B+v,
    z_-=q_B+u, z_+=q_B+u+v.                            (4)

The source proves

    a+b<16/15, b<7/100, a>399/400.                     (5)

If the endpoint's transverse own-center coordinate is negative, z_- is
its unique physical circle corner. If that coordinate is zero, both
z_- and z_+ are physical circle corners with their original nonnegative
weights. The total circle resultant has negative y component. Reflection
in the y axis gives the left-endpoint version of every assertion.

We will assume some endpoint is tilted and derive a contradiction to (1).

## 2. Every tilted endpoint has a uniformly inward global return normal

Analyze the right endpoint in (4). Let its original return unit normal
be n. Its global y component is positive by the complete strict cone in
the frozen input. Let m be the original total circle vector
sum lambda*z. Then m_x>0 and m_y<0. These statements concern the total
resultant; individual physical circle weights have not been discarded.

Let the line through p_B with direction n meet y=t at (x0,t). Its
intersection exists because n_y>0. The full force and origin-moment
equations give

    x0=t*m_x/m_y.                                      (6)

For an explicit derivation, write the two pair magnitudes as mu,nu>0.
The equations are 2m-mu*e_x+nu*n=0 and
mu*t+nu*(p_B cross n)=0. Substitute
p_B cross n=n_y*x0-t*n_x. The force equations then reduce the moment
equation to 2m_x*t-2m_y*x0=0, proving (6).

Both possible circle corners have positive x coordinate. Therefore the
slope m_y/m_x is a convex combination of their slopes, using weights
lambda*z_x. It is at least the slope of z_-, namely

    (t-b)/(x+a).

This remains true for every permitted two-corner mask and every individual
zero weight. Since both this lower slope and m_y/m_x are negative, and
t<0, (6) gives

    x0 >= t*(x+a)/(t-b).

Put tau=-t>1/2. Because p_B=(x+b,t+a), the original global normal slope
satisfies

    H:=-n_x/n_y=(x0-x-b)/a
      >=[tau*(a-b)-b*(x+b)]/[a*(tau+b)].               (7)

In particular the right side will prove n_x<0; the global sign is not
assumed merely from a sign in the tilted own frame.

Here are convenient exact bounds, slightly weaker than (5):

    a-b>37/40, b<17/240, a>199/200, x<61/60.            (8)

The first follows from
(a-b)^2>194/225>(37/40)^2, whose final reserve is 19/2880.
The second follows by subtracting the first from a+b<16/15 and
dividing by two. The third follows directly from (5).

The numerator in (7) is positive under these bounds. Since a<=1,
we may replace its denominator factor a by one for a lower bound.
For fixed a-b,b,x, the resulting quotient increases with tau: its
derivative is b*(a-b+x+b)/(tau+b)^2>0. Thus tau>1/2 and (8) give

    H > [(1/2)(37/40)-(17/240)(61/60+17/240)]
          /(1/2+17/240)
      =7401/10960 >2/3,                               (9)
    7401/10960-2/3=283/32880>0.

Write the actual unit normal as n=(-alpha,beta). Then

    alpha>2/sqrt(13)>11/20, beta>0,
    alpha^2+beta^2=1.                                 (10)

The last rational comparison uses
4/13-(11/20)^2=27/5200>0. The reflected left normal has form
(alpha,beta) with exactly the same bound. This is a bound on the
original force normal, not on an independently chosen separator.

## 3. An elementary maximum-distance fact for two facing normal arcs

Put c0=11/20 and s0=sqrt(279)/20, so c0^2+s0^2=1. Let
Theta=acos(c0), which lies in (0,pi/2).

For A>0 and B<=0, the function

    F(theta)=(A-cos(theta))^2+(B+sin(theta))^2

has no interior maximum on [0,Theta]. Indeed

    F'(theta)=2*(A*sin(theta)+B*cos(theta)).

Its sign is that of A*tan(theta)+B, an increasing function. Any
interior critical point is consequently a minimum. The maximum is
at one of the two interval endpoints. The same statement applies
when B=0, in which case the function is nondecreasing.

In particular, for 2<=L<21/10, the maximum of

    (L-cos(theta_1)-cos(theta_2))^2
      +(sin(theta_2)-sin(theta_1))^2                    (11)

over both angles in [0,Theta] occurs at one of the four corners.
For each fixed angle the preceding derivative argument applies,
with A=L-cos(other)>0 and B=-sin(other)<=0.

Writing k=L-1, the largest corner value is

    1+k^2-(11/10)*k.                                  (12)

The other candidates are (L-2)^2 and (L-2c0)^2. The first is
smaller than (12) by 2(1-c0)(L-1)>0; the difference from the
second is 2(1-c0)(1+2c0-L)>0. This checks every angular endpoint
without an angle grid.

## 4. Both endpoints tilted: actual occupied points are less than one apart

Suppose both A and B are tilted, with independent parameters a_A,b_A
and a_B,b_B. Their original return means are

    p_A=(s-1-b_A,t+a_A),
    p_B=(s+1+b_B,t+a_B).                               (13)

Both pairs of axes satisfy (5),(8). Tight long supports and the center
diameter bound give the additional coupled width estimate

    (a_A+b_A)+(a_B+b_B)<31/15.                         (14)

Indeed the endpoint center x gap is 2+h_A+h_B and is strictly less
than 2M=91/30, so h_A+h_B<31/30. Multiplying by two gives (14).

Since each a_i>199/200, we obtain

    b_A+b_B<23/300,
    L:=2+b_A+b_B<623/300,
    |a_B-a_A|<1/200.                                  (15)

Let the original return normals from A into D and B into C be

    n_A=(alpha_A,beta_A), n_B=(-alpha_B,beta_B).

By (10), they are points of the two facing upper unit arcs used in
Section 3. First ignore the small height difference a_B-a_A in
p_B-p_A. Equations (11)--(12), with k<=323/300, give the squared
distance bound

    1+k^2-(11/10)k <=87739/90000 <(199/200)^2,          (16)
    (199/200)^2-87739/90000=5453/360000>0.

The expression increases for k>=1, justifying substitution of the
upper bound in (15). Restoring the vertical offset by the triangle
inequality and using (15),(16) gives

    |(p_B+n_B)-(p_A+n_A)|<199/200+1/200=1.             (17)

The actual inward-unit-normal chord puts p_A+n_A inside the original
square D and p_B+n_B inside the original square C. Hence (17)
contradicts dist(C,D)>=1. This excludes the entire doubly tilted
branch, including independent tilts and every two-circle weight mask.

## 5. The aligned endpoint in a mixed branch has a correlated normal and height

It remains to treat exactly one tilted endpoint. Reflect the whole
configuration in the y axis if necessary so A is aligned and B is
tilted. Put x=1-s, tau=-t>1/2 and Y=-y_A>0. Because the original
long mean lies on A's actual inward vertical side,

    tau<=Y+1/2, 0<Y<=1/8.

Define

    e=Y+1/2-tau, 0<=e<1/8,
    H=1-e,
    p_A=(-x,t+H), 59/60<x<61/60,
    tau+e=Y+1/2<=5/8.                                (18)

The strict inequality Y>0 follows from tau>1/2 and the actual side
interval; it is not a new load-mask assumption. Therefore A's lower
outer corner (-x-1,-Y-1/2) is its unique physical circle corner.
The complete endpoint force and moment equations, or the explicit
elimination leading to (6), give for its original normal
n_A=(alpha_A,beta_A) the exact slope

    h_A:=alpha_A/beta_A
        =[tau-x*e]/[(tau+e)(1-e)].                    (19)

All denominators are positive. The ratio increases with tau and
decreases with x. After setting tau=1/2 for a lower bound, it decreases
with e on [0,1/8]. Direct differentiation has numerator
tau*(tau-x-1+2e)-x*e^2<0 at tau=1/2. Consequently

    h_A>=358/525>2/3,
    358/525-2/3=8/525>0.                              (20)

The displayed value is obtained at tau=1/2, x=61/60, e=1/8;
enlarging to this closed parameter box is legitimate.

For the upper bound, rewrite (19) as

    h_A=[1-(x+1)e/(tau+e)]/(1-e).

Using x+1>119/60 and tau+e<=5/8 gives

    h_A<=[1-(238/75)e]/(1-e)<=1-2e.                   (21)

The last inequality follows after multiplying by 1-e>0 from
(13/75)e+2e^2>=0. Equality at e=0 is allowed.

Since n_A is a unit vector in the upper right quadrant,

    beta_A>=1/sqrt(1+(1-2e)^2)>2/3+e.                 (22)

For the strict comparison, the polynomial

    f(e)=(2/3+e)^2*(2-4e+4e^2)

is increasing on [0,1/8]. Its derivative has the positive factor
1-5e+12e^2, since 1-5e>=3/8 there. Its endpoint value is

    f(1/8)=9025/9216<1.

Squaring positive quantities proves (22). Combining it with H=1-e
gives the essential correlated estimate

    H+beta_A>5/3.                                    (23)

Equation (20) also gives alpha_A>11/20 and
beta_A<sqrt(279)/20<21/25. These are all consequences of the original
endpoint equations. Bounding the height and normal separately would
lose (23), which is why this mixed case needs its own argument.

## 6. Mixed branch: both possible extremal normal directions give distance below one

For the tilted B keep p_B=(s+1+b,t+a), with a>199/200 and b<17/240.
The base horizontal separation of the two actual means is

    L=2+b<497/240.

By (10), its original normal is n_B=(-cos(theta),sin(theta)) for
some theta in [0,Theta]. Write delta=a-H. The squared distance of
the two occupied normal-chord points is

    D(theta)^2=(L-alpha_A-cos(theta))^2
                +(delta-beta_A+sin(theta))^2.          (24)

Here A0=L-alpha_A>0 and B0=delta-beta_A=a-(H+beta_A)<0
by (23). Section 3 therefore proves that the maximum of (24) is
at theta=0 or theta=Theta. No assertion about the maximizing actual
packing pose is needed; this is an upper bound on an enlarged interval.

At theta=0, the horizontal coordinate difference is positive and
strictly less than 25/48. The vertical coordinate difference is
a-(H+beta_A), negative by (23), with absolute value less than

    1+21/25-199/200=169/200.

Consequently

    D(0)^2<(25/48)^2+(169/200)^2
           =1418821/1440000<1.                        (25)

At theta=Theta, the positive horizontal difference is strictly less
than 233/240. The vertical difference is a+s0-(H+beta_A). Using
a<=1, s0<21/25 and (23), it is less than 13/75. Using
a>199/200, s0>4/5 and H+beta_A<1+21/25, it is greater than
-9/200. Thus its absolute value is less than 13/75, and

    D(Theta)^2<(233/240)^2+(13/75)^2
               =1400489/1440000<1.                   (26)

Equations (24)--(26) give D(theta)<1 for the original actual normal.
Both tested points belong to the respective original return squares
by their inward unit-normal chords. This again contradicts (1).

The mixed branch is excluded, including the original aligned endpoint
height, its complete force balance and its actual vertex mean. Together
with Section 4, this proves the theorem: neither long endpoint is tilted.

## 7. Complete opposite-seven-cycle caller and precise remaining geometry

Consider the compatible physical positive cycle

    A -- U -- V -- B -- C -- W -- D -- A.

Assume U,V,W are unloaded of full true positive degree two in the same
complete force-and-torque certificate, A and B have full true positive
degree two, and A,B,C,D physically touch the containing circle. Extra
edges or attachments at C,D are permitted. Work in the inherited radius
window 79/40<=R<=sqrt(Q).

The complete return-side localization theorem, frozen SHA256
`c10361ea546b8e5681b4ac38c09b1b2e9b14fa0a2621c541f689857c73acbd1e`,
permits one common reflection so the whole actual squares C,D lie in
y>1/120. The original channel C--W--D has one signed normal by W's
complete two-force equation. Tight supports give dist(C,D)>=1,
irrespective of W's orientation. The long-channel and endpoint
hypotheses of Section 1 therefore all hold.

**Corollary.** In this entire opposite long/short seven-cycle family,
both A and B are aligned with the long normal. Every configuration
with either long endpoint tilted is excluded, across all internal
heights, actual contact means, return-square frames and circle masks.

The proof is a local pair-coupling theorem: it applies whenever the two
above-side boundary return neighbors have set distance at least one,
not only when that distance comes from a one-internal-body return.

The aligned case is retained. This conclusion does not align C,D or W,
does not make the direct joins vertical, does not identify the centers
of U,V with their force-line means, and does not create a solid row.
Both actual squares outside a seven-body component remain present.
The aligned and staggered record packings are preserved. The sharp
q>=Q completion/endpoint inequality remains a separate obligation.

## 8. Verification and source boundary

The entire endpoint reduction and its original normal/mean conventions
were read before this assembly. That frozen source proves the side
contact locus, all physical circle-mask alternatives, original force
line, strict sign, own-axis exclusions and the exact vertex reduction.
Sections 2--6 above supply the new coupled proof; they do not treat
those prior reductions as an already proved sharp lower bound.

The supporting-face chord is proved directly in Section 2 of the frozen
endpoint reduction and in the independent exact contact-lens source,
SHA256 `3e9a96293ae14e5ed3e9f2952c396cbef82d44ddd6a9643e54ab597a63e951e3`.
Its actual points p_A+n_A and p_B+n_B are retained throughout.

All angle maxima have a whole-interval derivative proof. All constants,
polynomial inequalities, strict margins and positive-squaring branches
are exact. There is no angular mesh, numerical pose search, altered
stress selection, deleted endpoint force, new packing certificate,
Lean compilation, CI or original ledger mutation in this argument.
