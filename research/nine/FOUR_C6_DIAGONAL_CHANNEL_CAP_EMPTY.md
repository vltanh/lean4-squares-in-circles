# Every actual diagonal channel has an empty exterior pocket above radius two

Date: October 26, 2026.

**Status: complete whole-channel proof, accepted after full-source and
original-domain independent reviews in
REVIEW_DIAGONAL_CHANNEL_EMPTY_ROOT_2026_10_26.md and
REVIEW_FOUR_C6_DIAGONAL_CAP_EMPTY_GLOBAL_2026_10_26.md.**
No ledger is changed by this source.

Put Q=1105/256, s=1/sqrt(2), A=2+sqrt(2). Keep the entire original simple
positive cycle with at least three positively circle-loaded bodies, all
physical circle masks and individual weights, and an actual unloaded
degree-two diagonal transmitter W between original loaded endpoints X,Y.
Assume 2<=R<=sqrt(Q). The compatible diagonal convention and genuine
means are unchanged.

**Theorem.** The whole actual exterior X-W-Y pocket contains no additional
physical unit square of any orientation.

The proof covers physical radial endpoints and unique endpoints, and
retains the original strict side-interior applications. It uses no motion,
force deletion, newly selected certificate normal, or computational pose.
The SAT normals below are geometric separators for a putative extra;
they do not replace any original force normal.

## 1. Complete actual endpoint domain

DIAGONAL_CHANNEL_EXTERIOR_CAPACITY_ONE.md, Sections 1--2, supplies the
following unchanged geometry and strict height bound:

    X=[-a,1-a] times [b-1,b],
    Y=[c-1,c] times [d-1,d],
    a+c=A,       a^2+b^2=c^2+d^2=R^2,
    11/8<a,c<81/40,       b,d>=1/2,
    b-1<h<b,       d-1<h<d,       h>43/100.              (1)

The actual W center is (delta,h), delta=A/2-a=(c-a)/2. Its horizontal
and vertical half-diagonals are s. The two original channel applications
are (1-a,h),(c-1,h); these are relative-interior points of the actual
endpoint sides, as required by the compatible diagonal convention.

Both following inequalities hold on the whole domain, including radial
masks:

    h>=b(1-1/a),       h>=d(1-1/c).                      (2)

For a physical unique endpoint, this is precisely its proper concurrence
inequality on the actual horizontal force line. At a physical radial
endpoint the corresponding height is 1/2. Its right-hand side is then
less than (1/2)(1-40/81)=41/162<43/100<h. Thus no radial concurrence is
assumed to belong to its square.

The actual occupied crosscut and upper outer-circle arc give every whole
pocket extra E the inclusions

    E subset {y>=h},       E subset {-a<=x<=c}.           (3)

The second inclusion follows because that entire crosscut and its upper
circle arc have horizontal projection in [-a,c]; both endpoint circle
heights are positive. Apply the same compact-interior Jordan-region
argument as SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. These are whole-square
inclusions, not center-only assertions.

For a contained unit, its center lies in the disk of radius

    M=sqrt(R^2-1/4)-1/2 <91/60.                           (4)

## 2. The balanced endpoint family uses the existing complete geometric proof

Suppose a>b and c>d. The proof in
SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md, Sections 1--7, applies as a
geometric argument to (1)--(3). Its three-load alternating-cycle premise
was used only to obtain these displayed endpoint conditions and the
strict comparisons a>b,c>d. No other load equation, turn, or third body
enters its geometric SAT proof or its four closed-rectangle identities.

Here is the precise physical-mask endpoint check. If b,d>1/2, these are
exactly the geometric hypotheses written there. If b=1/2 or d=1/2,
that same proof remains valid directly: (2) has just been established
without assigning a unique mask; its endpoint bounds 10/7<a,c<2 and
h>2/5 remain strict; and every subsequent occurrence of a vertical
corner height uses the weak lower bound 1/2. In particular all four
polynomial identities in its Section 7 are already proved on closed
rectangles with lower height endpoint 1/2. The equality T-a=0 in its
Section 5 is explicitly allowed by its nonnegative squared factor
b^2-1/4. Its top-side mean uses h<b, which remains strict in (1).
Its auxiliary height M/sqrt(2)-1/2 is strictly greater than 1/2 when
that auxiliary construction is called here, because R>=2.

Thus the same full geometric proof, with these weak physical-height
endpoints retained, gives an empty pocket for the entire balanced family.
This is a direct check of its inequalities, not a limiting motion of
radial endpoints or a replacement of their circle weights.

It remains to prove the complementary asymmetric family. At least one
endpoint satisfies horizontal coordinate <= vertical coordinate. Both
cannot do so, since then A=a+c<=sqrt(2)R<3, whereas A>3.
Call the endpoint with horizontal <= vertical the tall endpoint, and
call the other one the short endpoint. Equal coordinates at the tall
endpoint remain included.

## 3. Uniform bounds for the complete asymmetric family

Write the tall corner as (alpha,beta), with alpha<=beta. Then

    11/8<alpha<=R/sqrt(2)<3/2,
    beta>=R/sqrt(2)>=sqrt(2)>7/5.

For the short endpoint, writing its horizontal and vertical coordinates
as a_s,b_s, respectively, gives

    a_s>389/200,       1/2<=b_s<3/4.                     (5)

Indeed a_s=A-alpha>=A-sqrt(Q/2)>389/200. To verify the final strict
radical comparison, square the positive numbers sqrt(2)+11/200 and
sqrt(Q/2); using sqrt(2)>140/99 leaves reserve 1087/2880000.
Then b_s^2<=Q-a_s^2<Q-(389/200)^2<9/16.

If X is the tall endpoint, its delta is positive and less than 1/3:

    0<delta=A/2-a<s-3/8<1/3.                             (6)

If X is the short endpoint, delta is negative and

    -delta=a-A/2>19/80.                                  (7)

For (7), use a>389/200 and A/2=1+s<1+99/140.
The original strict mean at the tall endpoint is especially useful:

    h>beta-1.                                           (8)

It is stronger than its proper-concurrence bound, since alpha<=beta.
For R^2>=17/4, (8) gives

    h>sqrt(17/8)-1>9/20.                                (9)

For the entire radius range, (1) still gives h>43/100.

## 4. Complete SAT cover for a putative whole extra

Take a separating side axis of W or E, directed from W toward E.
Its vertical component must be positive. For example, a nonpositive
vertical component and negative horizontal component, together with
E subset {y>=h}, would put all of E in x<=1-a. The slab (3) and minimum
horizontal unit width one then force E to be axis-aligned with horizontal
interval [-a,1-a]. Since h>b-1, its avoidance of X puts its bottom at
least at b. Its upper-left corner has squared radius at least
 a^2+(b+1)^2>R^2. The other horizontal sign is reflected; a downward
normal contradicts (3) already at W's lower vertex.

A purely upward separator puts E above h+s, so its center height is at
least h+s+1/2>91/60, contrary to (4). Reflect once if necessary. The
remaining W-to-E separator points strictly northwest.

Choose E's own axes as

    n=(u,v),       m=(-v,u),       u,v>=0,
    u^2+v^2=1,       w=u+v,       mu=max(u,v).            (10)

The E-owned northwest alternative uses its actual geometric side axis m,
with u,v>0. The W-owned alternative uses (-1,1)/sqrt(2), and permits
all closed endpoints in (10).

The X/E SAT cover, using (3), is exactly the following nonexclusive list:

    horizontal:       min_E x>=1-a;
    vertical:         min_E y>=b;
    E-owned northeast:min_E n.p>=u(1-a)+vb.              (11)

A northwest X/E separator exposes X's upper-left corner; because x>=-a
on E, it implies the vertical row. A southeast separator exposes its
lower-right corner; because y>=h>b-1 on E, it implies the horizontal row.
A southwest separator is impossible. These statements also cover all
side-axis endpoint cases, and do not assume contact between E and X.

### 4.1. The horizontal row is impossible in every case

Write c_E=(x,y). The horizontal row gives x>=1-a+w/2.
If W owns the northwest separator, then

    y-x>=h+a-1+mu,
    y+w/2>=h+w+mu>=h+2>R.

Here w+mu>=2; squaring gives
(2mu+nu)^2-4=nu(4mu-3nu)>=0 when mu>=nu>=0.

If E owns that separator, then

    -vx+uy>=-v delta+uh+s mu+1/2.

The top E vertex consequently has height at least

    h+v+[1+s(mu-v)]/u >=h+s+1>R.                         (12)

If u>=v, use 1/u>=1 and 1-sv>0. If v>=u, use v>=s and 1/u>=1.
Thus all horizontal alternatives are excluded, without a new mean.

## 5. The entire northeast row when X is tall

Here a<3/2, b>7/5, h>43/100, and 0<delta<1/3.
If both separators are owned by E, its farthest own-coordinate bounds are

    |n.c_E|+1/2 >= A1:=1+(1-a)u+bv,
    |m.c_E|+1/2 >= B1:=1+hu-delta v+s mu.               (13)

The lower quantities used next are positive, so their squared sum is a
legitimate lower bound for an actual E corner's squared norm.

For u>=v, use s>7/10 to obtain

    A1>1-u/2+(7/5)v,
    B1>1+(113/100)u-v/3.

On u^2+v^2=1, u>=v, put u=sqrt(1-v^2). Expand the squared sum, use
u>=1-v^2 and uv<=v, and obtain

    A1^2+B1^2 >47869/10000-v/50-(18/25)v^2
                 >=47869/10000-1/50-9/25>Q.             (14)

For completeness, before the harmless rounding of its quadratic
coefficient, that coefficient is
466/225-15269/10000-63/50, which is greater than -18/25.
The linear coefficient is exactly -1/50.

For u<=v,

    A1>1+(9/10)v>163/100,
    B1>1+(43/100)u+(11/30)v>=41/30.

Therefore A1^2+B1^2>(163/100)^2+(41/30)^2>Q.
This excludes both E-owned separators over the full orientation domain.

If W owns the northwest separator and u>=v, the exact original owner
comparison gives the E-owned northwest inequality as well. In detail,
with p0=u(1-a)+vb+1/2 and q0=uh-v delta+s u+1/2, the W-owned inequality
at p=p0 has q-bound above q0 by

    ((u-v)/w)[1+v(b-h)-s w]>=0.

Its q-bound increases with p. Since b>h and s w<=1, the comparison is
valid at all original face joins. The preceding E-owned proof applies.

If W owns the northwest separator and u<=v, use the actual top vertex
z=c_E+(n+m)/2. It satisfies

    n.z>=A1,
    (z_y-z_x)/sqrt(2)>=(h+a-1+2v)/sqrt(2).

A positive linear combination of these inequalities directly gives

    z_y>=w+(hu+bv)/w.                                   (15)

No closest-point claim is needed. Put t=u/v in [0,1]. If w>=6/5, the
right side exceeds 6/5+(43/100+7/5)/2=423/200>R.
If w<6/5, then t<11/25, and

    (hu+bv)/w > ( (43/100)t+7/5)/(1+t)
                 >3973/3600.

Thus z_y>7573/3600>21/10>R. This exhausts the northeast row at the tall
endpoint. Its vertical row is also impossible: a whole E above b>7/5
would have center height above 19/10>M.

## 6. The entire northeast row when X is short

Here a>389/200, a<81/40, 1/2<=b<3/4, and -delta>19/80.
Set

    h0=43/100 if R^2<=17/4,
    h0=9/20   if R^2>=17/4,
    H=h0+7/10.

The weak overlap at R^2=17/4 is harmless; (9) supplies the second row.

### 6.1. Both separators owned by E

The quantities in (13) obey

    A1>1-(41/40)u+v/2,
    B1>1+H u+(19/80)v             if u>=v,
    B1>1+h0 u+(15/16)v            if u<=v.              (16)

For u>=v and u>=19/20, the B1 bound alone exceeds R: its square
exceeds 17/4 in the first radius range and Q in the second. Otherwise
u<19/20 and the displayed A1 lower bound is positive.

Let F_H(v) be the squared sum of the first two lower bounds in (16),
with u=sqrt(1-v^2), 0<=v<=1/sqrt(2). It is strictly concave. To check
this explicitly, its positive u-linear coefficient is 2(H-41/40);
its negative uv coefficient has absolute value at most 1953/4000;
and its u^2 coefficient minus its v^2 coefficient is at least
1293516/640000. Since

    v(3-2v^2)/(1-v^2)^(3/2)<=4,

its second derivative is less than -2 throughout this interval.
Its minimum is therefore at v=0 or v=1/sqrt(2).
At v=0 the lower bound is

    (1/40)^2+(1+H)^2,

already above the appropriate radius bound. At the diagonal endpoint
put C0=H+19/80. The bound is

    2+((21/40)^2+C0^2)/2+(C0-21/40)sqrt(2).             (17)

Using sqrt(2)>140/99, its positive reserve above 17/4 for h0=43/100
is 451591/31680000, and its positive reserve above Q for h0=9/20
is 311/84480.

For u<=v, expand the squared sum of the first and third bounds in
(16), with v=sqrt(1-u^2). Its u-linear coefficient is at most -23/20,
its positive u^2-minus-v^2 coefficient is at most 159/1280, and its
uv coefficient is negative. As (uv)'=(1-2u^2)/v>=0 on this interval,
its derivative is strictly negative. Its minimum is again the common
endpoint u=v=1/sqrt(2), already covered by (17).

Thus every E-owned northwest/northeast combination is impossible.

### 6.2. The northwest separator owned by W

For u>=v, the exact owner comparison in Section 5 again gives the
E-owned northwest inequality, so Section 6.1 applies.

Assume u<=v. The actual top E vertex satisfies the two inequalities
preceding (15). If either lower projection exceeds R, containment
already fails. Otherwise their equality-line intersection z* is a
positive linear combination of the two unit normals, so every feasible
z has |z|>=|z*|. Here is the full positivity check.
The first coefficient is positive because

    A1-(R/sqrt(2))(v-u)
      =1+(1-a+R/sqrt(2))u+(b-R/sqrt(2))v>0.

Indeed 1-a+R/sqrt(2)>0, and if the second coefficient is negative the
whole expression is at least 1+b-R/sqrt(2)>0. The second closest-point
coefficient is positive because

    h+a-1+w+(a-1)u(v-u)-bv(v-u)>=h+a-1+1-b>0.

These use only (1),(5), not a unique circle mask at the short endpoint.
The intersection in ordinary coordinates is exactly

    z_x*=1-a+u-v+v(b-h)/w,
    z_y*=w+(hu+bv)/w.                                   (18)

Its first coordinate is negative and its second positive, throughout
a>=389/200, b<=3/4, h>=43/100, u<=v. Its squared norm increases with a
and with h. Thus replace a by 389/200 and h by 43/100 to get a lower
bound, retaining the full b and orientation intervals.

Put t=u/v. If t<=1/4, then v>24/25. Already the northwest projection
of z is greater than (659/200)/sqrt(2)>R, a contradiction.
For t>=1/4, at the comparison a,h the sum z_x*+z_y* is positive:

    z_x*+z_y* >=-103/200+2t/sqrt(1+t^2)+(7/50)/(1+t)>0.

For the last inequality, use 2t/sqrt(1+t^2)>=2/sqrt(17)>12/25
and (7/50)/(1+t)>=7/100. Consequently the squared norm increases with b, and may be bounded
below at b=1/2. The two resulting coordinates are

    X(t)=-189/200+(t-1)/sqrt(1+t^2)+(7/100)/(1+t),
    Y(t)=(1+t)/sqrt(1+t^2)+43/100+(7/100)/(1+t).

Their squared sum decreases on [1/4,1]. For an explicit derivative
check, write D=sqrt(1+t^2). Then half its derivative is

    [X(t)(1+t)+Y(t)(1-t)]/D^3
          -(7/100)[X(t)+Y(t)]/(1+t)^2.

The first bracket equals
-189(1+t)/200+43(1-t)/100+(7/50)/(1+t), and is at most -3/8.
The second bracket is positive by the preceding comparison. Thus the
displayed derivative is negative.

At t=1 the squared norm is

    (91/100)^2+(sqrt(2)+93/200)^2>Q,

with reserve at least 227411/5280000 using sqrt(2)>140/99.
This contradicts containment. The whole northeast row (11) is now
excluded for the short endpoint too.

## 7. A complete scalar inequality for the asymmetric short-endpoint vertical row

In this section X is short, so the opposite endpoint satisfies c<=d.
Let

    T=sqrt(R^2-1/4),       M=T-1/2,
    Y=b+1/2,              X0=sqrt(M^2-Y^2),
    D0=d-c>=0.

The radical X0 is real on the full present asymmetric domain. Indeed

    X0^2=a^2-T-b-1/4
        >(389/200)^2-121/60-1
        =49/64+11/15000.

Thus

    X0>7/8,       Y<5/4.                                (19)

We prove

    X0+Y<3s+D0.                                         (20)

Since h>d-1 and a+c=A, this immediately gives the stronger original-mean
inequality needed below:

    X0<h+a-1+s-Y.                                       (21)

### 7.1. The equal-coordinate tall endpoint is the adverse comparison

At fixed R, increase the short horizontal coordinate a from
A-R/sqrt(2) to its actual value. Then c=A-a, d=sqrt(R^2-c^2),
b=sqrt(R^2-a^2). The entire interval retains (5), c>11/8, d<8/5,
and b>=1/2. Define G=3s+(d-c)-Y-X0. Its derivative is

    G_a=1+c/d+(a/b)(1-Y/X0)
         >119/64-(81/20)(3/7)=277/2240>0.                (22)

Here (19) gives Y/X0<10/7. Thus it suffices to prove (20) at
c=d=t=R/sqrt(2).

At that endpoint

    a=A-t,
    b0=sqrt(t^2+2At-A^2),
    T=sqrt(2t^2-1/4),
    1/2<=b0<3/4.

Both sides to be squared are positive. Equation (20) is equivalent to

    F(t):=T+4At-2A^2+5-3s-(3sqrt(2)-2)b0>0.             (23)

### 7.2. One strong-convexity estimate proves (23) over the full interval

The exact second derivative is

    F''(t)=-1/(2T^3)+2(3sqrt(2)-2)A^2/b0^3>100.         (24)

Use T>19/10, b0<3/4, 3sqrt(2)-2>2 and A>17/5 for the last inequality.
The comparison interval containing the actual t and t0=47/32 retains
all those bounds.

At t0, the radicals simplify to

    T0=sqrt(2081/512),
    b00=sqrt(2081/1024-(17/16)sqrt(2)),
    F(t0)=T0+19/4-(29/8)sqrt(2)-(3sqrt(2)-2)b00.

The following fixed rational enclosures follow by squaring positive
numbers:

    1414213/10^6 <sqrt(2)<1414214/10^6,
    2016048/10^6 <T0<2016050/10^6,
    727752/10^6  <b00<727755/10^6.

They give

    F(t0)>742832129/10^11>7/1000,
    0<F'(t0)<1/10.

For a direct arithmetic check of the derivative, insert the same bounds
in F'(t0)=2t0/T0+4A-(3sqrt(2)-2)(t0+A)/b00. Its lower bound is
244130734963367/3667961049000000>0; its upper bound is less than 1/10
by 48544890238337/1455544655000000.

Now (24) and completion of one square give, for every actual t,

    F(t)>=F(t0)+F'(t0)(t-t0)+50(t-t0)^2
         >7/1000-(1/10)^2/200=139/20000>0.

This proves (23), then (20)--(21), over the entire continuous asymmetric
domain. No root sample, parameter grid or polynomial packet is used.

## 8. The short-endpoint vertical row has no northwest separator

Assume min_E y>=b. Its center lies in

    K={ (x,y):x^2+y^2<=M^2, y>=Y=b+1/2 }.

Put delta=A/2-a<0. The left endpoint of this center cap, relative to W,
is

    (-X0,Y)-(delta,h)=(-v0,u0),
    v0=X0+delta,       u0=Y-h.

The strict original means give u0>1/2. Equations (1),(5),(21) give

    u0<41/50,       u0+v0<sqrt(2),
    v0-u0<13/20<s.                                     (25)

For the last bound use v0<X0<sqrt((91/60)^2-1)<23/20 and u0>1/2.

The left cap endpoint satisfies every northwest support test with
strict excess less than 1/2. More explicitly, if v0<0, its excess over W's
support in r=(-sin theta,cos theta) is at most max(u0-s,0)<1/2.
If v0>=0 and u0-v0>=s, its distance to W's top vertex is at most
sqrt(2)(u0-s)<1/2. Otherwise (25) puts it either inside W or at distance
(u0+v0-s)/sqrt(2)<1/2 from W's upper-left edge.
Thus every northwest r has

    r.(-X0,Y)<h_W(r)+1/2.                               (26)

This point check extends to the entire cap K. Put theta0=arccos(Y/M).
For theta>=theta0, the cap support is attained at (-X0,Y), so (26)
already applies. For 0<=theta<=theta0, its support is M. On either side
of pi/4, the quantity h_W(r)+1/2-M is a positive-coefficient sine/cosine
combination plus a constant, hence concave. It suffices to check the
endpoints 0,theta0 and pi/4 if the latter belongs to the interval.
The first is strict because h+s+1/2>M. The second is (26).

For the possible pi/4 endpoint, Y<=M/sqrt(2). We claim

    h+a-1>sqrt(2)M-s.                                   (27)

If R^2<=17/4, then M<=3/2 and
h+a-1>sqrt(2)+(d-c)>=sqrt(2)>=sqrt(2)M-s.
If R^2>=17/4, the condition Y<=M/sqrt(2) gives
b<7/12<3/5. Hence

    a>sqrt(17/4-9/25)>197/100,
    c<sqrt(2)+3/100<1011/700.

Since

    17/4-(1011/700)^2-(1011/700+1/40)^2
       =10267/1960000>0,

we get d-c>1/40. But
sqrt(2)(M-3/2)<sqrt(2)/60<1/40. Thus (27) follows again from
h+a-1>sqrt(2)+(d-c).

Equation (27) is exactly h_W((-1,1)/sqrt(2))+1/2>M. Concavity now proves
h_K(r)<h_W(r)+1/2 for every northwest unit normal r. Every actual unit
E has support halfwidth at least 1/2, so no W-to-E separator can exist.
This excludes the entire remaining vertical row.

## 9. Whole-channel and original four-load consequences

Sections 4--8 exhaust every SAT owner, orientation, face join and actual
mean in the asymmetric endpoint family. Section 2 supplies the complete
balanced family, including physical radial height endpoints through the
explicit weak-endpoint check. These alternatives are exhaustive, so the
whole original diagonal exterior pocket is empty.

The theorem has no three-load alternating restriction and no extra
condition on the other original cycle channels. The actual circle masks,
load values and mean intervals remain throughout. It is stronger than
an exterior-capacity-one statement.

After independent full-source acceptance, apply this to either original
four-load bare-C6 orbit:

    U-A-V-B-D-C-U,       or       U-A-B-V-C-D-U.

The accepted central-capacity joins, including
FOUR_C6_LOADED_INTERMEDIATE_SIDE_PATH_DIAMETER.md, give at most one central
extra. Every side-channel cap has capacity one by
GENERAL_SIDE_CHANNEL_EXTERIOR_CAPACITY_ONE.md. If either U or V is
diagonal, its cap is empty by the present theorem, so the three actual
extras have total capacity at most two. This excludes the entire
side/diagonal, diagonal/side and diagonal/diagonal completion families
of both original four-load orbits at once.

Only the original both-side coupled allocation (1,1,1) remains in those
two parents. No entire four-load parent, cap parent, C6.ALL or coarse cell
is asserted closed by this source. No Lean compilation, CI, remote write
or shared-ledger change is performed here.
