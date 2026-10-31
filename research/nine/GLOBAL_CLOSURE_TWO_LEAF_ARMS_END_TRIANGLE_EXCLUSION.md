# Two genuine leaf channels at one root exclude an intact end triangle

Date: October 26, 2026.
**Status: complete hand proof, accepted after full-source root and separate
independent reviews in REVIEW_TWO_ARMS_AND_D_WALL_ROOT_2026_10_26.md and
REVIEW_TWO_LEAF_ARMS_END_TRIANGLE_ROOTED_BLOCKS_2026_10_26.md.**
No ledger or original gate has been changed by this source.

Work with the common selected physical certificate and the same nine
actual squares, in 79/40<=R<=sqrt(1105)/16. All applications and means
below are their original ones. Let

    Q=1105/256, T=sqrt(R^2-1/4), d=T-1,
    epsilon=d-1, M=91/60.

The standard contained-unit center bound gives |c|<M, and d<61/60.

## 1. A force-free classification of two genuine pendant channels

Let A--U_i--L_i, i=1,2, be two distinct positive paths. Each U_i is
truly unloaded of exact positive degree two, and each L_i is a genuine
positive degree-one leaf. All five physical bodies are distinct. A may
have arbitrary other positive neighbors and circle weights at this stage.

The actual leaf classification gives a radial direction e_i and inner
application radius r_i=d for S, or r_i=R-sqrt(2) for D. The true
transmitter law gives width w_i in {1,sqrt(2)} and unchanged A application

    p_i=x_i e_i, x_i=r_i-w_i, A subset {e_i.x<=x_i}.          (1)

All side-channel slider and mean alternatives remain. The two directions
are distinct. Indeed two radial S leaves on one ray are the same physical
square, as are two D leaves; an S and a D on the same ray overlap in an
open neighborhood of a point on that ray, since their radial interior
intervals (d,d+1) and (R-sqrt(2),R) overlap in the stated radius window.

If x_i<0, p_i is the unique nearest point of A to zero: every a in A has

    |a| >= -e_i.a >= -x_i=|p_i|,

with equality only at p_i. Two negative x_i would consequently force the
same point and same e_i, already excluded.

Every combination other than S/side has x_i<-3/10. For D/side use
R<25/12 and sqrt(2)>7/5, obtaining x_i<-19/60. S/diagonal gives
x_i<61/60-7/5=-23/60, and D/diagonal is still smaller. A nonnegative
x_i therefore is necessarily S/side with x_i=epsilon<1/60. Such an
actual point of A has norm below1/60, so the other x_j cannot be negative
with magnitude greater than3/10. If both were S/side but epsilon<0,
both would be negative, which was just excluded.

It follows that the whole two-arm domain has

    R^2>=17/4, 0<=epsilon<1/60,
    both L_i radial S, both U_i side-normal,
    p_i=epsilon e_i.                                      (2)

### 1.1. Positive epsilon

Two distinct vertices of a unit square are at distance at least one,
whereas |p_1-p_2|<=2epsilon<1. Thus at least one application uses an
A side support. Take it to be e_1=(1,0). Its actual radial support foot
is (epsilon,0), and

    A=[epsilon-1,epsilon] times [b,b+1], b<=0<=b+1.

The other radial support at radius epsilon cannot be a vertex. A vertex
on the right side would need height zero and would repeat p_1; every
left vertex has norm at least1-epsilon>epsilon. It cannot be the
opposite side, whose radial support radius is1-epsilon, or the same
side, which has the single radial support foot p_1. It is therefore an
adjacent side. Reflect vertically to put e_2=(0,1). The complete root is

    e_1 perpendicular e_2,
    A=[epsilon-1,epsilon]e_1+[epsilon-1,epsilon]e_2.          (3)

This argument includes side-axis endpoints; after (3) the two positive-
epsilon support feet are in the relative interiors of their A sides.

### 1.2. The complete epsilon=0 endpoint

Now p_1=p_2=0. Distinct outward directions e_1,e_2 force zero to be a
vertex of A, since a side-interior point has only one outward normal.
Both directions lie in its closed right-angle outward normal cone.

At zero, each U_i either has an incoming side-interior point, and hence
occupies the open half-plane e_i.x>0 locally, or has a vertex there.
They cannot both have side-interior incidence: two such half-planes
would overlap unless their normals were opposite, impossible in that
right-angle cone.

If U_i has a vertex at zero, A--U_i cannot be a singleton vertex/vertex
contact with the channel normal on U_i's side-axis endpoint. The existing
selected strict point-normal convention excludes exactly that possibility.
The two squares must therefore share a positive side segment. Thus e_i
is an A side axis and U_i's tangent cone contains its inward-from-zero
ray e_i as a boundary ray, together with the common side ray into A.

If the other U_j is also vertex-incident, its same argument makes e_j
the other A side axis. If U_j is side-interior-incident, then e_j.e_i
must be zero: it is nonnegative in the right-angle cone, and strict
positivity would put points of int(U_i) near the ray e_i in the open
half-plane int(U_j), contradicting physical disjointness. The directions
are distinct, so the perpendicular alternative is the only one.

Consequently (3) holds at epsilon=0 as well, with every original incoming
mean and both shared-side endpoint alternatives retained. No generic
normal is changed after extraction.

## 2. A reusable corner-root obstruction for an intact end triangle

Let 0<=epsilon<1/60, s=1-epsilon, and d=1+epsilon as in the
initial radius definitions, and let the actual root be

    A=[-s,epsilon]^2.                                    (4)

Suppose A,B,C is an intact positive end triangle: B,C have their true
degree-two positive circle loads, and A may have any additional positive
forces. Write the actual two-tip circle resultant as

    F=F_B+F_C.

**Corner-root theorem.** If both coordinates of F are strictly negative,
this physical end triangle is impossible.

The proof retains every physical B/C mask, individual zero circle weight,
root side mean and actual root owner. Its inputs are the full intact-tip
equations and the physical end-triangle lemmas from
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Sections 2--4.

### 2.1. Every contained neighbor has support height at most d

For any actual root port p with outward unit normal n into B or C,
the neighbor is in {x:n.x>=n.p}. Its center radius bound and directional
halfwidth at least1/2 give n.p<=d. This is the sharp half-plane support
lemma in Section1 of the cited source; equality is allowed here.

The root's unique F-maximizing point is its southwest vertex

    P=(-s,-s),

because both F coordinates are strictly negative. In the nonparallel
root-force case, the end-triangle source supplies two facts with the
actual applications unchanged:

* One actual port maximizes F on A, and thus equals P.
* The two normal lines have common concurrence q=-t F/|F|, t>0,
  and every port p has p=q+a n with a>=0.

In particular q_x,q_y>0. At the port P its a is positive, its outward
normal is n=(-u,-v), u,v>0, u^2+v^2=1, and

    s(u+v)=n.P<=d,
    u+v<=d/s<61/59.                                    (5)

At epsilon=0, already d=1,s=1 and u+v>1 contradict (5). The following
argument also covers every epsilon>0 without subdividing its interval.

### 2.2. The corner normal is close to one side axis

Equation (5) forces min(u,v)<1/20. Otherwise the larger component is
at least1/sqrt(2)>7/10, giving uv>7/200 and

    (u+v)^2>107/100>(61/59)^2,

where the last comparison has numerator reserve367 after multiplying
by100*59^2. This contradicts (5). Exchange the two axes so that

    v<1/20, u>19/20, v/u<1/19.                         (6)

The actual normal line at P then gives

    (s+q_y)/(s+q_x)=v/u<1/19,
    q_x>18s>epsilon.                                  (7)

### 2.3. The other actual port lies on the same left side

Classify the root's four sides and four vertices using its proper-port
relation p-q=a n, a>=0. Because q_x>epsilon, no right-side point or
right vertex can occur: its proper-port first component would be
negative while its outward normal first component is nonnegative. A top
or bottom side interior would require p_x=q_x, outside the side.

The southwest vertex P has already been used. Two distinct normal lines
through q cannot use that same vertex, because then they would be the
same line; their force directions would be parallel. Thus the other
actual port is on the left side or at its northwest endpoint
P'=(-s,epsilon). This reasoning also shows q_y<=epsilon if the second
port exists; q_y>epsilon would exclude the northwest endpoint and every
left-side interior.

A left-side interior normal is exactly west. At P' the proper-port
normal has negative first coordinate, nonnegative second coordinate,
and

    |n_y|/|n_x|=(epsilon-q_y)/(s+q_x)
                <=epsilon/s<1/59<1/20.                    (8)

The same weak-zero relation includes its side-axis endpoint. Therefore
both actual tip normals satisfy n_x<-19/20 and |n_y|<1/20, and both
applications have first coordinate -s.

### 2.4. Both tip centers lie in one cap of diameter less than one

For a tip center c and its actual contact p, put w=c-p. Since p belongs
to that unit, |w|^2<=1/2. Since p minimizes n on that unit,

    n.w=h_tip(n)>=1/2.

Write w=h n+a Jn. Then h>=1/2 and a^2<=1/2-h^2<=1/4. The normal bounds
just proved give

    w_x <= -(19/20)(1/2)+(1/20)(1/2)=-9/20,
    c_x < -s-9/20 < -43/30.                            (9)

Every center also has |c|<M=91/60. Two points in this cap satisfy the
following elementary rectangular bound (no optimizing pose is assumed):

    |c_B-c_C|^2
      < (M-43/30)^2+4(M^2-(43/30)^2)
       =713/720<1.                                    (10)

Indeed each first coordinate is between -M and -43/30 and each absolute
second coordinate is below sqrt(M^2-(43/30)^2). But the inscribed open
radius-1/2 disks of two interior-disjoint unit squares force their center
distance to be at least1. This contradiction proves the nonparallel case.

### 2.5. The complete parallel case

Opposite parallel A normals would place B,C beyond opposite supporting
faces of A, separated by a positive unit width, so they could not touch.
Thus the parallel normals agree and point in direction F. Both coordinates
are strictly negative, so both actual applications are P=(-s,-s).
Their support inequality is again (5), hence (6) after exchanging axes.
The center estimate (9)--(10) applies to both tips directly. This includes
all force ratios and original circle masks; no concurrence is assigned
to a parallel force pair.

All alternatives are exhausted, proving the corner-root theorem.

## 3. The entire triangle with two two-edge arms at one root

Consider the exact positive graph on seven bodies

    A--B--C--A,
    A--U_1--L_1,
    A--U_2--L_2,

where B,C have positive degree2, U_i have positive degree2 and zero
circle load, and L_i are genuine leaves. Every other actual square
remains in the packing; in particular both additional physical squares
are retained without a restricted region or orientation assumption.

Section1 proves the complete original leaf/width/slider domain reduces
to (3). Its root is physically circle-clear: every point of (3) has
norm at most sqrt(2)max(s,epsilon)<=sqrt(2)<R. Each triangle tip is
loaded, since otherwise its degree-two opposite supports would separate
its touching neighbors A and the other tip.

Let alpha_i>0 be the actual transmitted force magnitude of arm i.
The exact root equation, or equivalently the force sum over the complete
component, gives

    F_B+F_C = -alpha_1 e_1-alpha_2 e_2.                    (11)

In the orthogonal actual frame of Section1 both coordinates of this
resultant are strictly negative. The corner-root theorem now excludes
the entire family, including the critical radius, every original side
mean and every physical boundary-mask endpoint.

The two U_i were not declared unloaded merely from a drawing. In the
original exact graph each L_i is a positive leaf and therefore loaded.
The radial bridge central-endpoint theorem makes its other endpoint U_i
physically circle-clear, since a loaded leaf is the outer endpoint of its
bridge. Thus both U_i are genuinely unloaded before Section1's transmitter
law is used. No positive circle force is deleted to invoke (11), and this
load join does not need a support-minimality assumption.

Consequently the **whole exact attachment graph**, not only its initially
unloaded subfamily, is excluded at the common selected pose.
It is the same-root pair of length-two pendant arms within C1.3.b4.
Other attachment graphs in that coarse cell remain open, as do the sharp
nine-square theorem and original equality reconstruction.
