# An aligned S-leaf root cannot have two other boundary neighbors at d>=1

Date: October 27, 2026.

**Status: complete hand local theorem, submitted for full root and
separate independent review.** This uses the root's actual three-force
equation and the real S leaf. The two other neighbors may have
arbitrary true degrees, additional forces, physical circle masks and
individual zero circle weights. No coarse or fine label is changed.

Keep the same nine original interior-disjoint physical unit squares,
the common compatible selected certificate, and

    sqrt(17)/2 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<=epsilon<1/60,
    r=R-sqrt(2).

Suppose A is the genuine root of a positive S leaf L, and A has
true positive degree three. Its other two actual positive neighbors
B,D both physically touch the containing circle. Assume the real
S-leaf direction e is an own side axis of A.

**Theorem.** This entire original situation is impossible.

The proof retains all actual applications, including every side-mean
endpoint. It uses no force equation at B or D and no contact between
them. In particular it does not treat this three-edge star as an
actual positive triangle.

## 1. Original aligned chart and the full normal cover

Rotate the entire packing about its original origin so e=e_x. The
unchanged genuine leaf and root are exactly

    L=[d,d+1] times [-1/2,1/2],
    A=[epsilon,d] times [h-1,h],     0<=h<=1.

The actual leaf application is (d,0), and its positive root force
is alpha e_x, with zero origin moment. A is physically circle-clear
by the genuine radial-leaf theorem. Its full unchanged equation is

    alpha e_x+beta n_B+gamma n_D=0,
    alpha,beta,gamma>0.                                (1)

Its full origin-moment equation also retains those three forces.

Reflect the entire chart vertically to have 1/2<=h<=1. Every point
of a physical boundary unit has norm at least r, since it lies at
distance at most sqrt(2) from an actual circle corner of that unit.
Here

    r^2 >= 25/4-sqrt(34)>419/1000>1/4+1/3600,          (2)

using sqrt(34)<5831/1000. Consequently all points on A's left face
with height in [-1/2,1/2] are ineligible as boundary contacts.

No normal in (1) can point east. An actual unit beyond the support
x=d is necessarily the original radial S unit L: the sharp contained
unit support bound h<=d, including its equality case, is
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1. It has no degree
or load premise at that putative neighbor.

If h=1/2, the negative horizontal component required by (1) would
have its actual application on the whole ineligible left face.
Thus h>1/2. If both other normals were horizontal, they would both
point west; their actual application heights would both be strictly
positive by (2). Their strictly positive origin moments could not
sum to zero. Hence the two vertical components have strict opposite
signs. Name D so (n_D)_y<0.

If (n_D)_x<0, its actual A application is the lower-left vertex
(epsilon,h-1), ineligible by (2). If (n_D)_x>0, the application is
(d,h-1), a point in the relative interior of L's inner face because
-1/2<h-1<=0. An inward normal segment from an actual support point
of a unit square belongs to that square. A sufficiently short such
segment in direction n_D therefore belongs to D and enters int L,
which is impossible. This statement is valid also when the segment
is initially a boundary side of D: a closed-square point in another
unit's open interior forces open-interior overlap.

It follows that

    n_D=-e_y.

The complete equation (1) now gives

    (n_B)_x<0<(n_B)_y.

Thus B's actual root port is A's upper-left vertex, while D's is
an arbitrary actual bottom-face application:

    P_B=(epsilon,h),
    P_D=(x,h-1),       epsilon<=x<=d,
    D subset {y<=h-1}.                                 (3)

This is the complete parallel/nonparallel and support-owner cover.
It is the same local cover used in Section 2 of
FOUR_CYCLE_ALIGNED_S_ARTICULATION_EXCLUSION.md, re-established here
with no cyclic or other-neighbor equation in its premises.

## 2. Uniform exact bounds on the two unchanged ports

The actual boundary point P_B and (2) give

    h^2 >= r^2-epsilon^2
         >419/1000-1/3600>(647/1000)^2.

Put

    b=h-1,       t=h-1/2,
    D_0=61/60,   t_0=147/1000,   B_0=353/1000.

Then the whole original domain satisfies

    647/1000<h<=1,
    -B_0<b<=0,
    t_0<t<=1/2,
    1<=d<D_0.                                         (4)

Since P_D is also an actual boundary-unit point,

    x^2>=r^2-b^2
         >419/1000-(353/1000)^2>(27/50)^2.

The original x is nonnegative, so

    27/50<x<=d.                                       (5)

These are full interval bounds for the actual D mean. No contact
has been centered or moved.

## 3. The real S leaf supplies the complete lower-unit screen

First suppose D's maximum-y support is a side. Its actual frame
is aligned and

    D=[z,z+1] times [b-1,b].

The actual P_D gives x-1<=z<=x. Because -1/2<b<=0, the interiors
of D and L have overlapping vertical projections. Their horizontal
projections must therefore be disjoint. The alternative z>=d+1
contradicts z<=x<=d, so z+1<=d. Every corner of D then has

    |X|<D_0,       |Y|<1+B_0=1353/1000.

Its squared norm is less than D_0^2+(1353/1000)^2<17/4. Thus D
cannot physically touch the circle in this entire aligned case.

Suppose D's maximum-y support is its unique top vertex P_D. Its
complete tilted frame is

    D=P_D+[0,1](c,-s)+[0,1](-s,-c),
    c,s>0,          c^2+s^2=1.                         (6)

This parametrizes both possible tilts; c and s are not ordered.
If

    x+c<=d,                                           (7)

all its horizontal corner magnitudes are below D_0 and all its
vertical magnitudes are below B_0+sqrt(2). Therefore every corner
has squared norm less than

    D_0^2+(B_0+17/12)^2
      =37487981/9000000<17/4.                          (8)

Here sqrt(2)<17/12, and the exact reserve in (8) is
762019/9000000.

The only remaining case has x+c>d. Write g=d-x, so 0<=g<c.
The actual right downward edge P_D+u(c,-s) meets x=d at u=g/c.
Its height is b-gs/c. If that height exceeded -1/2, the edge
would enter the interior of the actual L immediately after that
crossing. Hence, including equality at L's inner lower corner,

    g s>=t c,
    x<=d-t(c/s).                                      (9)

This is an actual physical screen, not an assumed separator between
the two complete squares. In particular all tangencies and all
original point-contact endpoints remain allowed in (9).

## 4. Three of the tilted lower unit's corners have a large strict reserve

The corner P_D itself and its left adjacent corner

    P_D+(-s,-c)

have horizontal absolute coordinate below D_0 and vertical absolute
coordinate below 1353/1000. Both are therefore strictly inside the
circle by the same bound as in Section 3.

Consider the right adjacent corner

    (x+c,b-s).

Equation (9) gives

    x+c<=d+c(1-t/s).                                  (10)

For any t>1/8 and 0<s<1, c=sqrt(1-s^2), the whole-angle bound is

    c(1-t/s)<2/3.                                     (11)

For completeness, on its positive part the derivative vanishes
only at s^3=t; its maximum is
(1-t^(2/3))^(3/2). It is below (3/4)^(3/2)=3sqrt(3)/8<2/3
because t>1/8. On the nonpositive part (11) is immediate. This
checks the entire open angle range and both one-sided axis limits.

If s<=4/5, (4), (10)--(11) give the strict squared-norm bound

    (D_0+2/3)^2+(B_0+4/5)^2
      =37467181/9000000<17/4.                          (12)

If s>=4/5, then c<=3/5 and 1-t/s<=1-t<1-t_0. The corresponding
strict bound is

    [D_0+(3/5)(1-t_0)]^2+(1+B_0)^2
      =468767177/112500000<17/4.                       (13)

The positive reserves are 782819/9000000 in (12) and
9357823/112500000 in (13). Thus the right adjacent corner is also
strictly internal, in every original angle and screen-endpoint case.

## 5. A uniform concavity bound handles the remaining opposite corner

The last actual corner is

    Z=(x+c-s,b-c-s).                                  (14)

If c<=s, its horizontal magnitude is below D_0, so (8) applies
again. It remains that k=c/s>=1. Equations (4)--(5), (9) give

    1<=k<(D_0-27/50)/t_0=1430/441<13/4.              (15)

Its first coordinate is positive because x>0 and c>=s. Replacing
d by D_0 and t by t_0 increases its bound in (9), while replacing
b=t-1/2 by t_0-1/2 increases the absolute value of its negative
second coordinate. Therefore

    |Z|^2 <= F(k),

where the complete comparison function is

    F(k)=[D_0-t_0 k+(k-1)/sqrt(1+k^2)]^2
          +[t_0-1/2-(k+1)/sqrt(1+k^2)]^2.            (16)

The comparison uses the real coordinates monotonically and keeps
the full interval (15). It is not a mesh or a pose partition.

Write a=D_0+1/2 and b_0=D_0-1/2. Expanding (16) gives

    F(k)=(D_0-t_0 k)^2+(t_0-1/2)^2+2
          +2(a k-b_0)/sqrt(1+k^2)-2t_0 sqrt(1+k^2).

Direct differentiation yields

    F''(k)/2 = t_0^2-N(k)/(1+k^2)^(5/2),
    N(k)=3a k+(2b_0+t_0)k^2+t_0-b_0.                 (17)

On 1<=k<=13/4,

    N(k)>(9/2)k+(57/50)k^2-2/5>(1+k^2)^2/6.         (18)

Here is a short exact check of the second inequality. The difference
of its two sides has second derivative

    57/25-2/3-2k^2<0.

It is concave on that closed interval, so its minimum is at an
endpoint. Its values there are respectively 343/75 and
152999/38400, both positive. This proves (18) globally.

Also sqrt(1+k^2)<=sqrt(185)/4<7/2. Equations (17)--(18) imply

    F''(k)/2<t_0^2-1/21<-1/40,
    F''(k)<-1/20.                                    (19)

The exact reserve in the first strict comparison with -1/40 is

    1/21-t_0^2-1/40=21211/21000000>0.

At the interior comparison point k=2, direct substitution gives

    F(2)=(D_0-2t_0)^2+(1/2-t_0)^2+2
           +2(D_0+3/2-5t_0)/sqrt(5)<4241/1000,

    F'(2)=-2t_0(D_0-2t_0)
           +2(3D_0-1/2-10t_0)/(5sqrt(5)),
    -1/50<F'(2)<0.                                   (20)

These comparisons use only 559/250<sqrt(5)<2237/1000. To make
the arithmetic fully reviewable, the first displayed upper bound
before comparison is 4266766619/1006200000. The derivative lies
between -2705123/139812500 and -672961/34937500; those two rational
endpoints lie strictly between -1/50 and zero.

Integrate the uniform second-derivative bound (19), on either side
of 2, or complete the square in its Taylor upper bound. For every
original k in (15),

    F(k)<=F(2)+F'(2)(k-2)-(k-2)^2/40
          <=F(2)+10 F'(2)^2
          <4241/1000+1/250
           =849/200<17/4.                            (21)

Thus the last actual corner Z is strictly inside the circle as well.
The quantitative final reserve below 17/4 is at least 1/200. No
unproved numerical maximum, angle sample, or coefficient certificate
is a premise of this full one-variable inequality.

## 6. Conclusion and exact reusable scope

Every actual D corner is strictly inside D_R in every possible
frame: the aligned top face, both axis limits, the full tilted
screen alternatives, and the original mean endpoints have all
been included. Convexity therefore puts the whole actual D
strictly inside the containing circle. This contradicts its
physical boundary premise and proves the theorem.

Only A's genuine S leaf, full true degree-three force and torque
equations, and the physical boundary status of its two other actual
neighbors were used. Their mutual adjacency, degrees and other
forces were never used. Their original circle masks and every
individual zero weight remain, since the contradiction excludes
physical boundary contact rather than just positive circle load.

For the original opposite-root C4 with genuine S leaves at A,C
and positive block loads B,D, every aligned A or C at d>=1 is
therefore excluded. At d=1 a tilted genuine S root contains O in
its open interior, whereas the other genuine root contains O
closed. Those two distinct roots would overlap. Thus this local
theorem also supplies the entire critical opposite-S/S C4 exit.
The strict-high domain with both roots tilted retains a separate
obligation and is not declared closed here.

The same local theorem may be joined to another original graph
only after its true root degree three and both actual physical
boundary neighbors are established. Extra positive root forces
cannot be suppressed to fit it. No shared metadata, remote file,
Lean compilation, CI, physical pose or normal selection is changed.
