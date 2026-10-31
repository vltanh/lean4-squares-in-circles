# A triangle cannot carry short pendant paths at distinct roots

Date: October 26, 2026.
**Status: accepted complete theorem after full-source independent review in REVIEW_TRIANGLE_DISTINCT_SHORT_PATHS_GLOBAL_2026_10_26.md.** No shared ledger or original gate is changed here.

## 1. Exact graph and full statement

Work in the common compatible physical certificate in

    79/40 <= R <= sqrt(1105)/16.

The entire positive component has one triangle A--B--C--A. At each of
its three vertices there is either no bridge or precisely one pendant
path, of length one or two, ending in its genuine leaf. Assume at least
two different triangle vertices have paths, and at least one path has
length two. Every true degree, original normal, physical circle mask,
individual zero corner weight, actual shared-side mean, and all nine
physical squares are retained.

**Theorem.** This entire family is impossible. It includes the complete
path-length distributions (2,1), (2,2), (2,1,1), (2,2,1), and (2,2,2),
with every genuine S/D leaf and every original transmitter width.

This is a whole-component exclusion. No two-edge arm is replaced by
a leaf, and no already loaded body is treated as a transmitter.
The established direct-leaf theorems cover the cases with no length-two
path. The present theorem does not include a length-three path, whose
triangle root need not be circle-clear, or two paths at the same root.

Put

    d = sqrt(R^2-1/4)-1,     r = R-sqrt(2),
    epsilon = max(d-1,0),    kappa = 31/60.

The usual bounds give

    9/10 < d < 61/60,    0 <= epsilon < 1/60,
    r > 67/120 > kappa,    r < 7/10.

For a one-edge branch, its genuine leaf has direction e and application
radius r_L in {r,d}. Its root is physically circle-clear and meets
D_epsilon, by the radial leaf theorem.

For a two-edge branch X--U--L, the actual neighbor U of the loaded leaf
is physically circle-clear. Its exact positive degree two makes it an
original unloaded transmitter, with width w in {1,sqrt(2)}. The original
radial application at X is

    p_X = x e,       x = r_L-w,       X subset {e.z <= x}.       (1)

The D/diagonal alternative is excluded by the existing nonradial
off-origin point-contact convention. All remaining alternatives satisfy

    x <= d-1 <= epsilon,        |x| < kappa < r.                (2)

These are the full arm bounds in
TRIANGLE_THREE_BRIDGES_DISTINCT_ARM_EXCLUSION.md, Section1. In particular
X is physically circle-clear because it contains (1) of norm below r.
Every attached triangle root therefore meets D_kappa and is clear.

If a triangle vertex has no path, it has exact positive degree two and
is loaded: an unloaded transmitter cannot have two touching neighbors.
There is at most one such vertex under the stated graph hypotheses.

At each root let F_X be its full external resultant: the actual positive
circle resultant at an unattached vertex, or the original genuine leaf
resultant transmitted by its entire path. Thus F_X is nonzero, has zero
origin moment, and all three actual triangle equations give

    F_A + F_B + F_C = 0.                                      (3)

These three directions are distinct. They come from three distinct
physically boundary squares; the strict boundary-resultant direction
theorem in CYCLIC_GLOBAL_CONTINUATION.md, Section8, applies to all their
actual physical masks and weights. Equation (3) then makes them
noncollinear, since a line has only two unit directions.

The original directed triangle contacts have one common origin moment
H. This follows by summing the full actual moment equations, since every
external resultant just described has zero moment. No application mean
is reset in defining H.

## 2. The complete nonzero-moment domain

Suppose H != 0. Let A be any length-two root, rotate its genuine leaf
direction to e_x, and use x from (1). Let B be another attached root.
It meets D_kappa. Consequently its actual separating line from A, with
outward A-to-B normal n and application P, has

    h_A(n) = P.n <= kappa.                                   (4)

Indeed B lies in n.z >= P.n and contains a point of norm at most kappa.

The intact radial-triangle theorem RADIAL_TRIANGLE_CONCURRENCE.md applies
to the three true external resultants (3). If A's cycle pair is
nonparallel, its actual concurrence is

    q_A = q e_x,          q > 0,                              (5)

and each original port has the proper form P=q_A+ell*n, ell>=0.
The external force at A is its entire leaf resultant alpha*e_x,
alpha>0, because (2) already proved A circle-clear.

### 2.1. Every aligned A is excluded

In the aligned case write

    A = [x-1,x] times [l,l+1],       l<=0<=l+1,
    s = 1-x >= 1-epsilon.

If the AB normal is the left axis, its support is s. If it strictly
exposes a left vertex P=(-s,y), properness and (5) give

    n = (-s-q,y)/sqrt((s+q)^2+y^2),
    P.n = (s(s+q)+y^2)/sqrt((s+q)^2+y^2) >= s.                (6)

Squaring the positive quantities gives surplus
y^2(s(s+2q)+y^2)>=0. Both cases contradict (4), since

    s >= 1-epsilon > 59/60 > kappa.

A right-axis AB normal would make the other cycle normal horizontal
by the full vertical force equation, contrary to the nonparallel case.
For a top or bottom A-owned normal, the physical unit-triangle
nonobtuse-normal lemma makes the other normal's vertical component
have the same weak sign, so the actual positive vertical forces cannot
cancel. This includes all actual side means and their endpoints.

The only remaining AB feature is a strictly exposed right vertex.
Its normal has positive first coordinate and a nonzero vertical sign.
The full equation

    alpha*e_x + mu*n_AB + nu*n_AC = 0,      alpha,mu,nu>0,     (7)

then makes the AC normal strictly negative horizontally and opposite
vertically. It exposes the opposite left vertex. The physical
unit-triangle support-span lemma excludes two opposite strictly
exposed vertices when the two neighbors themselves touch.
Thus every aligned interface is covered.

### 2.2. Every tilted A is excluded

The rightmost point p_0=(x,0) is now the unique vertex of A. Write

    A = p_0 + [0,1]u + [0,1]v,
    u_x=-a, v_x=-b,       a,b>0,       a^2+b^2=1.

If q>x, both own coordinates of q_A relative to p_0 are strictly
negative. Every proper vector from q_A to an A port has both own
coordinates strictly positive. Thus both cycle normals strictly expose
the same far vertex p_0+u+v. Their nonparallel lines would concur there,
contradicting (5), since that vertex has negative first coordinate.
Therefore

    0 < q <= x.

The complete arm alternatives (1)--(2) force the S/side case and

    x = d-1 = epsilon > 0.                                  (8)

In the own frame the two coordinates of q_A are a(epsilon-q) and
b(epsilon-q), both in [0,epsilon). At the original AB port its proper
length obeys, by (4),

    0 <= ell = P.n_AB - q_A.n_AB <= kappa+epsilon < 8/15.       (9)

Every own-coordinate-maximum face is at distance greater than
1-epsilon>59/60 from q_A. Hence (9) places P on a minimum face or
their common near vertex, and both own components of n_AB are
nonpositive. The external direction e_x has both own components
strictly negative. Equation (7) consequently makes both own
components of n_AC strictly positive. Its actual port is the far
vertex P_F=p_0+u+v, with support

    h_A(n_AC) = |P_F-q_A| + q_A.n_AC
             >= sqrt(2)*(1-epsilon)-epsilon
             > 34/25 > 4/3 > d.                             (10)

Here sqrt(2)>7/5 and epsilon<1/60 suffice. But the actual contained
unit C beyond that support requires h_A(n_AC)<=d, by the sharp
contained-neighbor half-plane bound. This contradiction covers every
tilted root and all unchanged means.

### 2.3. The parallel A alternative

If A's cycle normals are parallel, they have the same outward sign:
opposite supports would separate B and C by A's positive width.
Equation (7) makes both normals west. Thus B lies in

    z_x <= min_A z_x <= x-1 <= epsilon-1 < -kappa,

contrary to its D_kappa intersection. This proof needs no concurrence
at A. Sections2.1--2.3 exhaust the entire H!=0 domain.

## 3. Zero moment when exactly two roots are attached

Now H=0. Suppose A and B have paths, with A's path of length two,
and C is the untouched loaded degree-two tip.

C's two force lines cannot be nonparallel with concurrence zero.
The full positive radial-concurrence lemma for a genuine loaded
degree-two square, as scoped in TRIANGLE_DISTINCT_LEAVES_DOMAIN.md,
Section2, uses actual unit neighbors and applies to all C masks.
Therefore C's pair is parallel. The complete parallel-boundary
classification makes it radial S or radial D, with both outward
cycle normals directed along its inner radial ray.

A radial D would put both actual applications at its one off-origin
inner vertex. The original selected nonradial point-normal convention
would make that point side-interior to both neighbors, whose inward
tangent half-planes overlap. Hence only radial S remains.

Rotate that S direction east. Its two genuine zero-moment applications
are both p=(d,0). At the side-interior point of C, the two neighboring
unit tangent cones must fill the left half-plane without overlap.
They are the two left quadrants. Therefore, after naming the upper
one A,

    A=[d-1,d] times [0,1],
    B=[d-1,d] times [-1,0].                                 (11)

If A's length-two branch was initially the lower one, reflect the
whole configuration first. The actual A-to-C force points east and
the actual A-to-B force points down. Their magnitudes are strictly
positive, so A's genuine external leaf direction points strictly
northwest. Its support on A is the unique northwest vertex

    p_A=(d-1,1).

But (1) gives p_A=x*e_A, and e_A has positive second coordinate.
Thus x>0 and x=|p_A|>=1, contradicting (2). This excludes H=0 for
the complete two-root families (2,1) and (2,2), without changing the
loaded C equation or a single original mean.

## 4. Zero moment when all three roots are attached

All three triangle bodies are now physically circle-clear and each
has one true external branch resultant. At most one cycle pair is
parallel, since two parallel pairs would make all three edge forces
and all three resultants in (3) collinear.

### 4.1. Each nonparallel root contains zero

At a nonparallel root, the two cycle lines pass through zero because
H=0. Their proper concurrence is therefore zero, and each actual port
is p=ell*n with ell>=0. If the root avoided zero, ell would be
positive and every such outward radial support would have norm
strictly greater than one. This is the own-frame outward-support
lemma in TREE_BODY_LOCALIZATION.md, Lemma F1.3; it has no load or
whole-tree hypothesis.

Its actual neighboring triangle root would lie beyond n.z=ell>1.
That is impossible because every attached root meets D_kappa and
kappa<1. Thus each nonparallel root contains zero.

### 4.2. If all three roots contain zero, a two-edge branch is impossible

For two interior-disjoint squares both containing zero, every actual
separating line passes through zero. Its zero-moment, normal-parallel
application must then be exactly zero. Thus all triangle ports are
zero whenever all three roots contain it.

At a length-two root A, both actual cycle normals lie in A's outward
normal cone at zero. By its full force equation their positive sum
is -alpha*e_A. The cone is convex, so -e_A is an outward normal at
zero. Hence A has minimum e_A-coordinate zero. Its opposite support
in direction e_A is its actual branch application x*e_A, and its
projection width is at least one. Thus x>=1, contrary to (2).

This argument includes both parallel and nonparallel cycle pairs,
origin side-interior and origin-vertex contacts, and every old mean.

### 4.3. The sole possible origin-avoiding parallel root

The remaining possibility has one parallel root K avoiding zero,
and the other two roots I,J containing zero. Rotate its genuine
external leaf direction east. The two K cycle normals are both west,
and their H=0 applications coincide at a point p=t*e_x on one actual
supporting face. Since I,J contain zero while K avoids it,

    t>0,              K subset {z_x>=t}.                    (12)

K's actual external application is x_K*e_x, where x_K is r or d for
a direct leaf and satisfies (2) for a two-edge arm. The two opposite
radial supports differ by K's projected width w_0>=1. Consequently

    x_K=t+w_0>1.

Only a direct S leaf can meet this inequality. Thus x_K=d>1.
The two opposite applications lie on one horizontal line. If the
horizontal direction were not an own axis of K, its two applications
would be opposite vertices, whose connecting radial line is a square
diagonal and whose width is sqrt(2). This is impossible since
w_0<d<sqrt(2). Hence K is aligned, w_0=1, and

    t=d-1=epsilon>0,
    K=[epsilon,d] times [b,b+1],       b<=0<=b+1.             (13)

No three-force body is falsely declared degree two here: both actual
cycle forces have the same proven application p, and the preceding
argument is the geometry of its two opposite supporting points.

### 4.4. The two remaining roots force an impossible far support

I and J both contain zero and p=(epsilon,0), so both contain the
whole segment [0,p]. They lie in z_x<=epsilon by their actual contacts
with K. Their interiors are disjoint. At p neither can have a tangent
cone containing the leftward ray in its interior, because the other
square contains that ray and has interior points arbitrarily close
to it. Thus p is a vertex of each square, with the leftward ray one
of its side rays. Their two right-angle tangent cones have opposite
vertical sides. Therefore, after naming the upper one I,

    I=[epsilon-1,epsilon] times [0,1],
    J=[epsilon-1,epsilon] times [-1,0].                       (14)

This also proves the claim when p is a K side endpoint. No interval
mean is chosen in obtaining (14).

The actual I-to-K force points east and the I-to-J force points down.
Their positive sum makes I's external leaf direction strictly
northwest. Its actual outward radial branch support is consequently

    P=(epsilon-1,1)=x_I*e_I.

Its positive second coordinate forces x_I>0. Every permitted short
branch has x_I<=d. However

    |P|^2-d^2
      =(1-epsilon)^2+1-(1+epsilon)^2
      =1-4epsilon>14/15>0.                                (15)

This is impossible. It includes both genuine direct leaf types and
every two-edge arm type. Thus (13) cannot occur either.

Sections4.1--4.4 exhaust every H=0 cycle configuration with all roots
attached. Together with Sections2--3 they prove the theorem.

## 5. Exact scope and remaining graph obligations

The proof uses the whole original component and three actual external
resultants. Every two-edge intermediate is proved unloaded from its
genuine leaf before its transmitter law is used. Every triangle root's
physical circle clearance is proved before omitting a circle force
from its equation. At parallel roots no concurrence is assigned.

The proof excludes every short-path distribution stated in Section1,
including the whole seven-, eight- and nine-body distributions with
all arbitrary completion squares left in place. No minimum-support
choice beyond the already compatible original certificate is needed.

A length-three path has a potentially loaded triangle root and is
outside this proof. A root carrying two pendant paths has a different
external equation and is outside it as well. Both distinctions must
remain explicit in any later coarse-cell assembly. The unrestricted
sharp radius and equality classification are not proved here.

No Lean compilation, CI, numerical pose sample or new coefficient
certificate is used in this argument.
