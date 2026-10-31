# Every actual side-channel cap above radius two has a longer-than-quarter-turn inner arc per extra

Date: October 26, 2026.
Status: complete hand lemma, accepted after full-source root and separate
independent reviews in REVIEW_ARTICULATION_SPLITTING_AND_CAP_ARCS_ROOT_2026_10_26.md
and REVIEW_GENERAL_SIDE_CHANNEL_CAP_INNER_ARC_GLOBAL_2026_10_26.md.
No original gate is closed by this source alone.

Put Q=1105/256 and r=5/4. The two statements below have deliberately
separate scopes. The first is a force-free theorem about every unit square
in a circular cap. The second supplies its height premise for every actual
width-one channel in an entire multi-load simple positive cycle. Neither
asserts that the cap's free inner-circle interval has length at most pi/2.

## 1. Whole-orientation cap-arc theorem up to the target radius

Let E be any actual unit square contained in D_(sqrt(Q)). Suppose
E is wholly in {p:n.p >= H}, for a unit n and H>1/4.
Then E's open interior meets the circle |p|=r in one connected open arc
of angular length strictly greater than pi/4. The arc contains the radial
point r c/|c| of its actual center c.

This extends the radius range of
RADIUS_TWO_CAP_INNER_ARC_QUARTER_TURN.md. Here is a complete proof,
including the changed inner-face estimate.

Choose signs and order of E's own axes so that its actual center coordinates
are x>=y>=0. Write

    a=x+1/2, b=y+1/2, A=a-1, B=b-1,
    E=[A,a] times [B,b], q=a^2+b^2<=Q.

Thus a>=b>=1/2. Every point of E has norm at least H. Its nearest point
to the origin has coordinates (max(A,0),max(B,0)).

### 1.1. The complete inner-face case a>r

Here A>1/4. Since a^2<=Q-1/4=1041/256 and b<=sqrt(Q/2),

    A<41/40,       -1/2<=B<1/2,
    A^2+B^2 < (41/40)^2+1/4 =2081/1600 <25/16=r^2.

The first strict radical bound is sqrt(1041)/16<81/40; the second follows
from sqrt(Q/2)<147/100<3/2. Both follow by squaring positive quantities.

Set E0=A^2+B^2+sqrt(2) A B. For fixed q, put t=a+b. Expansion gives

    E0=(1-1/sqrt(2))q+t^2/sqrt(2)-(2+sqrt(2))t+2+sqrt(2).

This is convex in t. On the full fixed-q domain a>=b>=1/2, the extrema of
t occur at b=1/2 and a=b. Enlarging to this interval is valid even when
an endpoint fails a>r or the cap hypothesis.

At b=1/2, write A0=sqrt(q-1/4)-1. Since q>r^2+1/4=29/16,
1/4<A0<41/40. Using 1/sqrt(2)>7/10 gives

    E0=A0^2+1/4-A0/sqrt(2)
       <A0^2+1/4-(7/10)A0 <=933/1600 <25/32.

Indeed the last quadratic is convex; its values at 1/4 and 41/40 are
11/80 and 933/1600.

At a=b=v=sqrt(q/2), enlarge to 3/4<=v<=147/100. Then

    E0=(2+sqrt(2))(v-1)^2
       <=(7/2)(v-1)^2 <=15463/20000 <25/32.

The squared factor is convex and its larger endpoint value is
(47/100)^2. The final reserve is exactly 81/10000. Consequently the entire
inner-face domain satisfies E0<r^2/2.

Let

    alpha=arccos(A/r), beta=arcsin(B/r),
    gamma=arcsin(min(b/r,1)).

The full closed intersection with the inner circle is precisely the interval
[beta,min(alpha,gamma)]. The square has positive first coordinate, a>r,
and A^2+B^2<r^2 ensures beta>-alpha. Its open-interior intersection is the
corresponding open interval; b=r introduces no isolated point because
alpha<pi/2.

The inequality E0<r^2/2 is equivalent to

    (sqrt(2)A+B)^2 <r^2-B^2.

It implies sqrt(2)A+B<sqrt(r^2-B^2), irrespective of the sign of the
left-hand expression. Hence A<r cos(beta+pi/4). Since |B|<=1/2,
|beta|<pi/4, and the cosine comparison is on its decreasing interval.
Thus alpha-beta>pi/4.

If b<=r, then

    gamma-beta=arcsin(b/r)-arcsin((b-1)/r)
               >=2 arcsin(2/5)>pi/4.

The difference is nondecreasing on [1/2,r), because b>=|b-1|; continuity
includes b=r. The strict comparison follows from sin(pi/8)<2/5, or
2-sqrt(2)<16/25. If b>r, gamma=pi/2 and beta<pi/4 give the same strict
bound. Both possible interval lengths exceed pi/4.

### 1.2. The complete outer-face case a<=r

Here A,B<=1/4. If B<=0, the nearest-point norm is max(A,0)<=1/4,
contradicting H>1/4. Therefore

    0<B<=A<=1/4,    k^2=A^2+B^2>1/16,    k^2<=1/8.

The closed intersection is precisely

    [max(arccos(a/r),arcsin(B/r)),
     min(arccos(A/r),arcsin(b/r))].

Each of its four candidate upper-minus-lower differences exceeds pi/4.
The two opposite-face differences have the strip bound proved above.
The inner-inner difference is at least pi/2-2 arcsin(1/5)>pi/4,
since sin(pi/8)>1/4>1/5.

For the remaining outer-outer difference write

    L(A,B)=arcsin((1+A)/r)+arcsin((1+B)/r)-pi/2.

Fix k^2 and set B=sqrt(k^2-A^2), varying from A=B=k/sqrt(2) to the
original point. The sign of dL/dA equals the sign of

    (A-B)[(A+B-1/4)^2+(k^2-1/16)(A+B+1)],

which is nonnegative. This follows by comparing the two positive derivative
terms, squaring them, and using A^2+B^2=k^2. Continuity includes A=1/4
or B=1/4 where a derivative may be infinite. Thus

    L >=2 arcsin((1+k/sqrt(2))/(5/4))-pi/2
       >2 arcsin((4+1/sqrt(2))/5)-pi/2 >pi/4.

For the final strict comparison, the positive squared reserve against
sin^2(3pi/8) is (16-9sqrt(2))/100>0. These four differences prove a single
nonempty open interval of length greater than pi/4.

### 1.3. Radial center point

Every unit has projection halfwidth at least 1/2. Hence |c|>=H+1/2>3/4.
Its farthest corner also gives |c|^2+|c|+1/2<=Q, and therefore |c|<91/60,
since (91/60)^2+91/60+1/2-Q=31/57600>0. Consequently
|r-|c||<1/2. The radial point r c/|c| is strictly inside the actual incircle,
and thus belongs to the unique open arc already proved.

This proves the force-free cap-arc theorem on the entire radius interval.

## 2. Every actual width-one channel above radius two has height greater than 3/10

Now work with an entire actual simple positive cycle having at least three
loaded bodies, in 2<=R<=sqrt(Q), under the established physical normal and
embedding conventions. Let X and Y both have positive total circle load,
and let X-U-Y be one original channel with U a true
unloaded degree-two side-normal transmitter. Preserve all original positive
forces, endpoint masks, individual zero corner weights, actual application
means, and U's slider.

The proper channel and physical cap theorems give its actual frame

    P_X=(l,h), P_Y=(l+1,h), h>0,
    X subset {x<=l}, Y subset {x>=l+1}.

Every contained center has norm less than M=91/60. The projection halfwidth
of each actual endpoint square is at least 1/2. Thus

    l>1/2-M=-61/60,       l<M-3/2=1/60.

In particular -3/2<l<1/2. If l>=-1/2, then |l|<=1/2; if l<=-1/2,
then |l+1|<=1/2. Therefore one of the two unchanged endpoint applications
has horizontal coordinate of absolute value at most 1/2.

Each endpoint is a physical boundary square because it has positive total
circle load. If z is any actual circle corner on that same unit and P is
its application, then the unit's diameter gives

    |P| >=|z|-|P-z| >=R-sqrt(2)>=2-sqrt(2).

Apply this to the selected application, without changing it. Its common
height satisfies

    h^2 >=(2-sqrt(2))^2-1/4
         =23/4-4sqrt(2) >9/100.

The final comparison is sqrt(2)<283/200, with squared reserve
(283/200)^2-2=89/40000>0. Since h>0,

    h>3/10>1/4.

The argument does not require a unique endpoint mask, equal corner weights,
a particular support owner, or an endpoint concurrence inside its square.

## 3. Whole original-domain consequence and exact remaining obligation

The actual channel-cap theorem places every whole exterior extra E in
{y>=h}. Section 2 supplies h>3/10, so Section 1 gives each actual extra one
connected open inner-circle arc longer than pi/4, containing its radial
center point. It retains all physical masks and all original means.

Thus any two such extras require more than pi/2 of disjoint inner-circle
arc length. To exclude repeated cap occupancy one still must prove that
their actual occupied crosscut routes these arcs into a free interval of
length at most pi/2, or supply a separate coupled-occupancy obstruction.
That free-interval assertion is not proved by this source. In particular,
this lemma alone does not close the five-load C6 unique/unique side family.

This is a shared geometric input for every side channel in the stated
radius range. No finite coefficient packet, sampled orientation, Lean
compilation, CI, or change to an original gate is used.
