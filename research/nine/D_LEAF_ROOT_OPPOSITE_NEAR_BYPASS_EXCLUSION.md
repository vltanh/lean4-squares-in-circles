# A D-leaf root cannot have two boundary neighbors and a near-origin unit bypass

Date: October 27, 2026.

**Status: complete hand theorem and exact original mixed-leaf caller,
submitted for full root and separate independent review.** The local
theorem retains the D root's three actual forces. Its other three
units may have arbitrary degrees, weights and additional contacts.

## 1. Complete original domain

Keep all nine actual interior-disjoint unit squares, contained in the
original circle, with

    sqrt(17)/2<R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,   0<epsilon<1/60,
    r=R-sqrt(2),                   s=1-r.

Suppose an actual clear root A has true positive degree three: its
neighbors are a genuine D leaf L and two actual physical boundary
units B,D. Suppose a fourth actual unit C, distinct from A,B,D,L,
physically touches B and D and meets the closed disk D_epsilon.
Neither contact involving C is required to have positive stress.

**Theorem.** This entire physical and force configuration is impossible.

The proof uses the actual force and origin-torque equations only at
A. It makes no degree-two, circle-weight or concurrence assumption
at B,C,D. Every physical circle mask, zero individual weight, actual
shared-side mean and genuine vertex/vertex normal is retained.

Orient the actual D leaf east. Its unchanged root chart is

    A=[-s,r] times [h-1,h],       0<h<1,
    p_AL=(r,0),                  n_AL=e_x.

The strict transverse slider follows from the compatible genuine
D-leaf/root classification. The original D leaf has vertices
`(r,0),(r+1/sqrt(2),1/sqrt(2)),(R,0),
(r+1/sqrt(2),-1/sqrt(2))`.

In the strict-high domain the exact D margins give

    r>129/200>5/8,   s<3/8,
    r>1/2,          s>1/3,
    r^2-s^2>1/16.                                      (1)

For example the first bound follows from `R>103/50` and
`sqrt(2)<283/200`; the remaining bounds are those used in the
accepted D-root and shallow-side theorems. In particular both
horizontal margins of A are larger than epsilon.

Take an actual point of C in D_epsilon. It is outside int A,
since C and A are distinct interior-disjoint units. Therefore one
vertical margin of A is at most epsilon. Reflect vertically so

    0<h<=epsilon<1/60.                                 (2)

This reflection changes no physical body or mean.

## 2. The full three-force root equation leaves one west neighbor

The accepted force-free theorem
`D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md` applies to each actual
boundary neighbor B,D, since (2) is stronger than its `h<=1/4`
hypothesis. It says that every actual normal from A into either
boundary unit has nonpositive vertical component. This includes
all original owners and all shared-side mean endpoints.

Write the actual positive magnitudes as alpha,beta,gamma, and the
two unit normals as n_B,n_D. The full unchanged force equation is

    alpha e_x+beta n_B+gamma n_D=0.                    (3)

Its vertical component forces both normals to be horizontal. They
cannot both point east. A west contact has actual point `(-s,y)`
with `h-1<=y<=h`. Every point of a physical boundary unit has norm
at least r, so (1) gives

    y^2>=r^2-s^2>1/16.

Since `h<1/60`, its actual height must satisfy

    y<-1/4.                                           (4)

The origin moment of this west unit normal is
`det((-s,y),-e_x)=y<0`. The genuine radial D leaf has zero origin
moment. Hence two west normals would give a strictly negative
left side in A's full torque equation, which must be zero.

After interchanging B,D, their exact normals are consequently

    n_B=-e_x,      n_D=e_x,
    B subset {x<=-s},      D subset {x>=r}.             (5)

Let `P=(-s,y)` be the original A--B application, including the
original mean in a side contact. Equation (4) holds at this actual
point. No application height has been centered or reselected.

## 3. The physical bypass lies wholly above A

The contacts C--B and C--D and (5) imply that C's horizontal
projection contains the entire interval `[-s,r]`, of length one.
An interior-disjoint unit square with that projection property
must be separated from A in the vertical direction.

For completeness, this is the purely physical separating-axis
calculation from Section 4 of `UNIT_BYPASS_NORMAL_CHANNEL.md`;
it does not use a transmitter equation or a collinearity of
the two A applications. Let C's coordinate width be
`w=c+t`, where `c,t>=0` and `c^2+t^2=1`, and write its center
displacement from A as `(u,v)`. Projection containment gives

    |u|<=(w-1)/2.

Some own side axis of A or C separates the two squares. The
horizontal axis cannot do so because the projections overlap
in an interval of length one. If the vertical axis separates,
the required conclusion is already `|v|>=(w+1)/2`. Otherwise
a separating C side axis with absolute components `(c,t)` gives

    t |v| >= (w+1-c(w-1))/2 >= t(w+1)/2,

because

    (1-t)(w+1)-c(w-1)=2c(1-t)>=0.

Its vertical component t cannot vanish. Interchanging c,t handles
the other C side axis. Thus vertical projection separation always
holds, including all equality contacts and all tilted C frames.

It follows that C lies entirely in `y<=h-1` or entirely in
`y>=h`. The first possibility contradicts its actual point in
D_epsilon, since `h-1<-59/60<-epsilon`. Therefore

    C subset {y>=h}.                                  (6)

In particular its actual contact with B supplies a point of B
with height at least h. A positive gap between A and C causes no
problem and is not replaced by an invented A--C contact.

## 4. Every actual corner of the west boundary unit is strictly internal

We now use only the exact physical facts

    B subset {x<=-s},    P=(-s,y) in B,
    h-1<=y<-1/4,        max_y(B)>=h>0.                 (7)

First suppose B's maximum-x support is a side. Then B is aligned:

    B=[-s-1,-s] times [z,z+1].

The original P belongs to that side, so `z+1<=y+1<3/4`.
Its contact to C gives `z+1>=h`, hence `z>=h-1>-1`.
Every actual B corner consequently has `|x|<11/8` and `|y|<1`,
and therefore squared norm less than

    121/64+1=185/64<4<R^2.                            (8)

This includes positive-length side intersections and both actual
mean endpoints.

Otherwise the maximum-x support is the unique vertex P. The
complete tilted frame, with no orientation restriction, is

    B=P+[0,1](-c,t)+[0,1](-t,-c),
    c,t>0,               c^2+t^2=1.

Its highest vertex is `P+(-c,t)`. By (7),

    y+t>=h,       so y>=h-t.                          (9)

The four actual corners have the following strict bounds.

* At P, `|x|=s<3/8` and `|y|<1`, so its squared norm is
  less than `73/64<4`.
* At `P+(-c,t)`, its height is between h and `3/4`, while
  `|x|=s+c<11/8`. Its squared norm is less than
  `121/64+9/16=157/64<4`.
* At `P+(-t,-c)`, (9) gives `y-c>=h-(c+t)>-sqrt(2)`,
  while `y-c<0` and `|x|=s+t<11/8`. Its squared norm is
  less than `121/64+2=249/64<4`.
* At the opposite vertex `P+(-c-t,t-c)`, (9) gives
  `y+t-c>=h-c>-1`, and `y+t-c<3/4`. Thus `|y+t-c|<1`
  and `|x|=s+c+t<s+sqrt(2)<43/24`, using `s<3/8`
  and `sqrt(2)<17/12`. Its squared norm is less than

        (43/24)^2+1=2425/576<17/4<R^2.                (10)

Thus all four corners of the original B lie strictly inside the
containing circle in every frame. Convexity puts the whole square
strictly inside, contradicting its assumed physical circle contact.
This proves the local theorem.

## 5. Exact whole original C1.4.b2 caller

Take the original C4 in cyclic order A--B--C--D--A, with genuine
leaves at the opposite roots A,C. The complete load cover forces
B,D positively loaded; hence they are physical boundary units.
The actual roots A,C are clear and keep true positive degree
three, and both B,D keep their actual degree-two equations.
All three additional physical packing squares remain present.

Consider the complete mixed leaf orbit. By the genuine symmetry
exchanging A,C, put the D leaf at A and the S leaf at C. If
`d<=1`, the D root contains O openly and the S root contains O
closed, so they overlap. In the entire remaining domain `d>1`,
the genuine S root C contains its actual point `epsilon e_C`
and therefore meets D_epsilon. It physically touches both B,D.
Every premise of Sections 1--4 now holds at the true degree-three
root A with its original three forces.

This closes the entire existing fine family

    M6.B4L2.C4.OPPOSITE.LBD.SD.

It also independently contains the trivial D/D overlap exit.
The opposite-root S/S family is not claimed here. No degree is
lowered, no force is deleted, and no physical mask, side mean,
leaf direction or radius subinterval is sampled. No Lean
compilation, CI, numerical optimizer or remote mutation is used.
