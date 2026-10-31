# Tilted long-endpoint return wrappers satisfy the sharp section profile

Date: October 30, 2026 UTC.

**Status: complete proposed continuous hand theorem, awaiting independent
full review.**

The result covers the actual boundary neighbor at the upper-inner vertex
of a tilted long-channel endpoint. A neighboring vertex gives a genuine
whole-square floor. A neighboring side may wrap below that floor, but
its actual section at height 5/4 still obeys the same strict one-sided
profile. The proof keeps the original force-line height and uses the
occupied length-four chord to pay for the endpoint's horizontal tilt.

No lower bound on the distance between the two return squares is used.
The complete original-normal force caller is stated separately from
the geometric profile lemma.

Put

    Q=1105/256, z=5/4, g(Y)=sqrt(Q-Y^2).

All squares are actual closed unit squares, with disjoint open interiors,
in the same disk centered at the unchanged origin.

## 1. Geometric parameter lemma for the entire side-wrapper interval

Suppose q=R^2 satisfies

    17/4 <= q <= Q.

Let a,b,s,t be real numbers satisfying

    a^2+b^2=1, a>399/400, 0<b<7/100,
    |s|<1/60, -9/16<=t<-1/2,
    (2+|s|)^2+t^2<=q.                                (1)

Define the actual point

    p=(x,f)=(s+1+b,t+a),
    k=z-f, d=g(f+1)-1.                               (2)

Let C be a physical-boundary unit in D_R. Suppose it has the actual
support chart

    n=(-alpha,beta), u=(beta,alpha),
    alpha,beta>0, alpha^2+beta^2=1,
    C=p+[0,1]n+[r-1,r]u, 0<=r<=1.                   (3)

Thus the original supporting line through p has strict northwest
normal n directed into C. The complete side-mean interval, including
both of its geometric endpoints, is allowed in (3).

**Theorem 1.** The full horizontal section of C at y=z lies strictly
between its horizontal supporting lines and is nondegenerate. If ell
is its actual left endpoint, then

    ell < g(f+1)-1.                                  (4)

No force equation, circle-weight choice, neighbor-normal replacement,
endpoint degree or whole-square floor is assumed in this geometric
lemma. In particular C may extend below y=f.

### 1.1 Exact uniform entry bounds

Equations (1)--(2) give

    87/200 < f < 1/2,
    59/60 < x < 163/150,
    3/4 < k < 163/200 < 7/8,
    7/16 < d < 51/100.                              (5)

For the lower floor use
399/400-9/16=87/200. For the upper floor use a<=1 and
t<-1/2. The upper x bound is 1+1/60+7/100=163/150.
The lower d bound follows from g(3/2)=23/16. For the upper d bound,

    (151/100)^2-[Q-(287/200)^2]=3667/160000>0,

so g(1+87/200)<151/100. Monotonicity of g gives the asserted bound.
Every argument of g used below is positive and strictly below sqrt(Q).

### 1.2 The actual section must exist

The point p belongs to C and f<1/2<z, so the lower horizontal support
is below z. Suppose the upper support were at or below z. The top
vertex in (3) has height f+beta+r*alpha, and hence

    beta+r*alpha <= k < 7/8.

Therefore beta<7/8 and
alpha=sqrt(1-beta^2)>sqrt(15)/8>7/16. Moreover

    r*beta <= beta*(k-beta)/alpha
           <= k^2/(4alpha) < 7/16.                  (6)

The complete original square would then satisfy

    -1/2 < X < 25/16, -5/8 < Y <= 5/4.              (7)

For its minimum x coordinate, use
x-alpha-(1-r)beta >= x-(alpha+beta)
>59/60-17/12=-13/30>-1/2.
For its maximum x coordinate, use (5)--(6) and

    25/16-[163/150+7/16]=23/600>0.

Its minimum height is at least f-alpha>87/200-1>-5/8.
The hypothetical upper support gives the remaining inequality in (7).

Every point in (7) has squared norm strictly below

    (25/16)^2+(5/4)^2=1025/256<17/4<=q,

with the displayed radius reserve 63/256. This contradicts C's actual
physical circle contact. Thus its upper support is strictly above z.
The full section is nondegenerate, and its relative open interval lies
in the original open square interior.

### 1.3 The complete two-edge section formula

Solving the unchanged two own-coordinate strips (3) on y=z gives

    ell=max(ell_1,ell_2),
    ell_1=x+(r-1-alpha*k)/beta,
    ell_2=x+(beta*k-1)/alpha.                         (8)

Indeed u.(X-x,k) lies in [r-1,r], while
n.(X-x,k) lies in [0,1]. The two lower bounds on X are exactly
the candidates in (8). Section 1.2 has already supplied nonemptiness,
so their maximum is an actual endpoint, not an artificial extension
of an empty slice.

## 2. The original upper corner controls the first edge

Let

    P=p+n+r*u,
    E=n.P=1-alpha*x+beta*f,
    T=1+alpha*z+beta*d.

P is the actual upper vertex of C. From (8),

    beta*ell_1=u.P-1-alpha*z.                         (9)

Actual corner containment gives u.P<=sqrt(Q-E^2). The square root is
real because E is a coordinate of an actual point in D_R, q<=Q.
Also T>0. Since

    (d+1)^2+(f+1)^2=Q,

direct expansion, using alpha^2+beta^2=1, yields the exact identity

    [T^2+E^2-Q]/alpha
      = 2(z-x)+2(zd-xf)beta
        +alpha*[z^2+x^2-d^2-f^2
                       -2(d+f)/(1+beta)].           (10)

Every term is controlled over the full domain (5):

    2(z-x)>49/150,
    zd-xf>=(5/4)(7/16)-(163/150)(1/2)
           =17/4800>0,                              (11)

and the bracket in (10) is strictly greater than

    25/16+(59/60)^2-(51/100)^2-1/4
               -2(51/100+1/2)=-59/90000.            (12)

Since 0<alpha<=1, even a negative bracket contributes more than
-59/90000 after multiplication by alpha. Thus

    [T^2+E^2-Q]/alpha
       >49/150-59/90000=29341/90000>0.                (13)

It follows that sqrt(Q-E^2)<T. Combining this with (9) proves

    ell_1<d.                                        (14)

This uses one original actual upper corner. It covers the entire
normal quadrant and every slider r without an angle subdivision.

## 3. The occupied long chord controls the second edge

Put D=x-d=x+1-g(f+1). The entry bounds give D>0. The unchanged
length-four chord constraint in (1) gives

    x+1=2+s+b <= 2+|s|+b
        <= b+g(-t)=b+g(a-f).

Consequently

    D <= b+g(a-f)-g(1+f)
       <7/100+g(A-f)-g(1+f), A=399/400.              (15)

The second inequality uses a>A, a-f=-t>0 and strict decrease of g
on positive arguments. It is an inequality for the actual original
coordinates, not a displacement of the force line.

For f in [87/200,1/2], the function

    S(f)=g(A-f)+g(1+f)

decreases. Its derivative is

    (A-f)/g(A-f)-(1+f)/g(1+f)<0,

because Y/g(Y) is strictly increasing for Y>=0 and A-f<1+f.
At the upper endpoint,

    S(1/2)>g(1/2)+g(3/2)
           >161/80+23/16=69/20.                     (16)

The strict radical comparison in (16) follows from

    Q-1/4-(161/80)^2=13/800>0.

Rationalizing the difference in (15), and using 1+A<2, now gives

    g(A-f)-g(1+f)
       = (1+A)(1-A+2f)/S(f)
       < (40/69)(1/400+2f)
       =1/690+(80/69)f.

Therefore

    0<D<L(f):=493/6900+(80/69)f.                     (17)

The scalar expression L(f)^2+(5/4-f)^2 is convex on the whole
closed floor interval. Its two exact endpoint values are

| f | L(f) | L(f)^2+(5/4-f)^2 | Strict reserve below one |
| --- | --- | --- | --- |
| 87/200 | 3973/6900 | 7585357/7617600 | 32243/7617600 |
| 1/2 | 4493/6900 | 23483837/23805000 | 321163/23805000 |

Both reserves are positive. Convexity and (17) prove throughout
the continuous domain that

    D^2+k^2<1.                                      (18)

Cauchy--Schwarz gives alpha*D+beta*k<1. Rearranging the second
candidate in (8) yields

    ell_2=x+(beta*k-1)/alpha<d.                      (19)

Equations (14),(19) prove Theorem 1. No sampled pose, numerical
minimizer or parameter mesh is a premise of this convexity estimate.

## 4. Complete physical vertex/side cover at a tilted endpoint

Let the actual right long endpoint B have vertices

    q_0=(s+1,t),
    q_0+u_B, q_0+v_B, q_0+u_B+v_B,
    u_B=(a,-b), v_B=(b,a),                           (20)

with the same actual parameters (1). Let its physical boundary
neighbor C meet its upper-inner vertex

    p=q_0+v_B=(x,f).

Assume the original unit contact normal from B into C is strict
northwest:

    n=(-alpha,beta), alpha,beta>0.                   (21)

B,C are both physical-boundary units. Every actual pose and the
original normal are retained.

**Theorem 2 (physical return profile).** The actual C section at y=z
is nondegenerate, lies strictly between its horizontal supports,
and satisfies

    ell_C <= g(f+1)-1.                              (22)

The inequality is strict whenever C wraps below y=f or has a
nonzero frame tilt. The reflected left-endpoint statement gives
the corresponding lower bound for the actual right section endpoint.

### 4.1 B's inward own side cannot support a boundary neighbor

Here is a complete geometric version of the face obstruction used
in this cover. In orthonormal own coordinates about the fixed circle
origin, suppose a boundary unit is

    [kappa-1,kappa] times [lambda-1,lambda],
    kappa-lambda>1, lambda>=1/2,
    kappa^2+lambda^2=q.

A contained unit on the opposite side of its inward face cannot touch
that face and physically reach the same containing circle.
If it touches at one of its own vertices, use that vertex.
Otherwise it has an own vertical side on the same line. Both such
side intervals have length one, so their nonempty closed overlap
contains an endpoint of the neighboring interval. Thus in every
case there is an actual neighbor vertex

    P=(kappa-1,y), |y|<=lambda

on the face. Both adjacent own unit-edge vectors from P have
nonpositive first coordinates. Each adjacent vertex has squared norm
at most

    q-2kappa+2lambda+2<q.

Their sum vector to the opposite neighbor vertex has first coordinate
at most -1 and second-coordinate magnitude at most one. That opposite
vertex has squared norm at most

    q-4kappa+2lambda+5<q.

The last strict inequality follows from kappa>lambda+1 and
lambda>=1/2. P itself is also strictly inside D_R. All four actual
neighbor vertices are therefore strictly inside, contrary to physical
boundary status.

For B in (20), write its own center coordinates as P_B,T_B:

    P_B=a(s+1)-b*t+1/2,
    T_B=b(s+1)+a*t+1/2.

The parameter bounds give

    P_B>35541/24000,
    |a*t+1/2|<=1/16,
    |T_B|<427/6000+1/16=401/3000.

For the middle estimate, a*t+1/2 ranges from at least -1/16
to strictly below 1/800. Consequently

    P_B-|T_B|>32333/24000>1.                         (23)

After reflecting the second own coordinate if necessary, take
kappa=P_B+1/2 and lambda=|T_B|+1/2. The boundary equality and every
face-obstruction premise hold. In particular -u_B cannot be a
common separating support normal from B into the boundary neighbor C.
This excludes that physical supporting halfplane, not an entire
vertex irrespective of its normal.

### 4.2 A neighbor vertex gives a genuine floor

Suppose p is a vertex of C. The cone of normals maximizing on B
at p is the closed right-angle cone with extreme rays v_B,-u_B.
The cone of normals minimizing on C at the same vertex is another
closed right-angle cone. They intersect at the original actual
normal (21).

Two closed circular arcs of equal length pi/2 with nonempty
intersection have an endpoint of the first arc in the second:
if neither endpoint belonged, the second could not intersect the
first without being strictly contained in its interior, which is
impossible for equal lengths. Hence v_B or -u_B is also a common
geometric support direction. Section 4.1 excludes -u_B, so v_B
minimizes on C at p.

The original n also minimizes there. Since b>0 and alpha>0,

    alpha*v_B+b*n=(0,alpha*a+b*beta)

is a positive multiple of e_y. Positive linear combinations preserve
the same minimizing point. Therefore the whole actual C satisfies

    C subset {y>=f}.                                (24)

This conclusion retains vertex/vertex contact and every boundary
case of the common-normal cones. The geometric auxiliary direction
v_B is not substituted for the original force normal n.

The complete unequal-floor section theorem, with f in (87/200,1/2),
now supplies the actual section and (22). It is strict for every
nonaligned C.

### 4.3 A neighbor-side interior is exactly the full wrapper

If p is not a vertex of C, it belongs to the relative interior of
one of C's sides. The original common support normal (21) is then
the unique inward own-axis normal of that side. Its unchanged
side coordinate gives exactly chart (3), with 0<r<1.

Theorem 1 supplies the actual section and the strict inequality (4).
Its geometric endpoints r=0,1 were included as well; thus no endpoint
of an original side-mean interval was lost in this cover.

These two alternatives exhaust every actual boundary neighbor and
prove Theorem 2. If C is wholly above y=f by either alternative,
the floor theorem applies directly. If it wraps below, the strict
side-wrapper proof applies without assigning it a false floor.

## 5. A full original-force caller for the strict global normal

The profile theorem above is geometric once (1),(20),(21) are present.
Here is a complete local force caller for (21) that uses no set gap
between the two return neighbors.

Keep a genuine positive long channel A--U--V--B. Its two internal
bodies are unloaded with true positive degree two and full angular
equations. Suppose the endpoints A,B also have true positive degree
two and their other original neighbors are actual physical-boundary
units wholly above the long axis. Every original circle weight and
application is retained.

The endpoints A,B themselves are physically boundary as well. For
example, if B had zero total circle load, its true degree-two
translational balance would propagate the same signed normal through
U,V,B to B's other boundary neighbor. The three actual internal
projection widths are each at least one. Their support telescoping
would give a center projection gap at least four between A and that
neighbor, contradicting the universal center bound |c|<91/60.
Thus B has positive total circle load. Reflection gives the same
conclusion at A. This argument uses their full retained stars and
does not infer physical clearance from a zero circle multiplier.

The frozen endpoint source
LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md,
SHA256 cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3,
then gives (20) and all of (1) whenever B is tilted. In particular its
original long means use the same s,t, its actual return point is p,
and its original own-frame return normal has positive global y
component. The length-four chord inequality is the unchanged
occupied-line statement, not a force-line height reset.

The long support gap also gives center separation at least three,
so at least one actual endpoint has center radius at least 3/2.
Its farthest-corner containment yields q>=17/4, supplying the
geometric lemma's lower radius bound.

For completeness, the global inward sign and a stronger slope bound
follow directly from the complete original endpoint equations.
The two possible physical circle corners are

    z_-=q_0+u_B, z_+=q_0+u_B+v_B.

If the endpoint transverse own-center coordinate is negative, only
z_- is a circle corner. At the zero coordinate both are circle
corners, and both original nonnegative weights remain. Its full
circle resultant m has m_x>0 and m_y<0. The latter is total vertical
force balance, not a sign claim about each separate circle atom.

Let the original return-normal line through p meet y=t at (x_0,t).
The full force and origin-moment equations give

    x_0=t*m_x/m_y.

Indeed, with original positive pair magnitudes mu,nu,
2m-mu*e_x+nu*n=0 and
mu*t+nu*(p cross n)=0. Using
p cross n=n_y*x_0-t*n_x eliminates the two pair forces and gives
2m_x*t-2m_y*x_0=0.

Both possible circle corners have positive x coordinate. Therefore
m_y/m_x is a convex combination of their slopes, with the original
nonnegative weights multiplied by their respective x coordinates.
It is at least

    (t-b)/(s+1+a).

This lower slope and m_y/m_x are negative. Since t<0,

    x_0>=t*(s+1+a)/(t-b).

Put tau=-t>1/2 and X=s+1<61/60. As p=(X+b,t+a),

    -n_x/n_y=(x_0-X-b)/a
       >=[tau*(a-b)-b*(X+b)]/[a*(tau+b)].             (25)

From the original a+b<16/15 bound and a^2+b^2=1,

    a-b>37/40, b<17/240.

The first comparison uses
(a-b)^2>194/225>(37/40)^2, with reserve 19/2880.
The second follows by subtracting a-b from a+b and dividing by two.
The numerator in (25) is positive. Replacing its denominator factor
a by one decreases the lower bound. The resulting quotient increases
with tau. Hence

    -n_x/n_y
      >[(1/2)(37/40)-(17/240)(61/60+17/240)]
                                    /(1/2+17/240)
       =7401/10960>2/3.                             (26)

The final reserve is 283/32880. In particular n_x<0<n_y, proving
the needed original normal (21). This derivation is the local part
of the previously frozen separated-return alignment proof, reproduced
here without that theorem's additional dist(C,D)>=1 hypothesis.

At a left tilted endpoint, reflect the entire picture in the y axis.
For other callers, such as a long endpoint whose other edge begins
a further transmitter channel, its actual upper-inner point and
strict global return-normal condition must be supplied from its
full original equations separately. The geometric Theorems 1--2
remain available once those exact premises are present; this
section does not assign a boundary neighbor to an unloaded body.

## 6. The coupled floor sum available to later assemblies

The force-free coupled endpoint estimate in
TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md,
SHA256 78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6,
uses the actual endpoint horizontal widths w_A,w_B. Put

    E=(w_A+w_B-2)/2, 0<=E<1/30.

It gives

    |y_A|+|y_B|<=1/8-E+(320/39)E^2.                  (27)

Whenever the unchanged endpoints have nonpositive center heights,
their actual highest horizontal supporting lines
f_i=y_i+w_i/2 therefore satisfy

    f_A+f_B>=7/8+2E-(320/39)E^2.                    (28)

For E>0 the excess above 7/8 is strictly positive, since
2-(320/39)E>2-32/117>0. These are actual support heights.
For a tilted endpoint in (20), f_B=t+a is exactly the height used
in (2). For an aligned endpoint, f_i=y_i+1/2.

The profile theorem proved here and the older aligned-endpoint
wrapper may thus be used at their respective actual endpoint
heights in one common horizontal section. Any subsequent proof
must still supply the actual order of the section intervals and
the required intervening occupied width. No whole-set distance
is inferred from a horizontal section gap in this source.

## 7. Inputs and verification boundary

Besides the two complete frozen endpoint sources explicitly pinned
above, the vertex-floor branch uses the complete theorem

UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md,
SHA256 abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94.

Its actual-section and equality scopes are unchanged. The wrapped
side branch is proved here in full; it does not import a narrower
aligned-endpoint profile as though the tilted endpoint were aligned.
The face obstruction and the original-normal slope calculation
are also printed in full.

All bounds are continuous analytic inequalities with exact rational
endpoint comparisons. This work used no numerical pose search,
parameter mesh, mean replacement, normal reselection, circle-mask
reduction, discarded original force, ledger mutation, Lean
compilation, CI execution, or remote publication.
