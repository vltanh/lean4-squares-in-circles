# Exact two-square disk-cap capacity down to offset two fifths

## Theorem (arbitrary orientations)

For any `2/5<=h<=1`, if two pairwise interior-disjoint
unit squares lie entirely in

    D_R intersection {x>=h},

then

    R^2 >= (h+1)^2+1.                                (1)

Equality is possible only for the two parallel squares

    [h,h+1] x [-1,0],    [h,h+1] x [0,1].              (2)

These squares attain equality. No common frame is assumed in
the lower bound. This extends HUMAN_SHARP_CAPACITY_BOUND.md,
which treated only `2/3<=h<=1`. The proof below supplies
the missing whole-orientation common-point theorem; the
entire new interval is settled by finite rational sign
comparisons and trigonometric monotonicity.

## 1. A common point in a family of triangles

For `1/2<=k<=5/7` define the closed triangle

    T_k={(x,y): x>=0, x+k*|y|<=1+k}.

**Triangle theorem.** Every unit square contained in T_k
contains `w=(1/2,0)`. Every *non-axis-parallel* unit
square contains w in its **open interior**. The only
axis-parallel squares having w on their boundary are

    [0,1] x [-1,0],   [0,1] x [0,1].                   (3)

We now prove this complete statement. Reflect vertically,
and use square quarter-turn symmetry, to represent an
arbitrary square's frame as

    e=(c,s), f=(-s,c),   c=cos(theta),s=sin(theta),
    0<=theta<=pi/4.

Put L=c+s and D=c-s. Its horizontal half-width is L/2.
Its support half-widths along (1,k),(1,-k) are

    H_plus=(c+k*s+|k*c-s|)/2,
    H_minus=((1+k)*c+(1-k)*s)/2.

Define H=(H_plus+H_minus)/2,
d=(H_minus-H_plus)/(2*k), and
B=1+k-L/2-H. The square's center p must lie in
the closed triangle with vertices

    A=(1+k-H,d),
    U=(L/2,d+B/k),
    V=(L/2,d-B/k).                                  (4)

If the square fits, B>=0. Every requirement that w lie
inside it is one of four affine center inequalities

    |e dot(p-w)|<=1/2,    |f dot(p-w)|<=1/2.         (5)

It suffices to verify these inequalities at the
three vertices in (4), with strictness for theta>0.

The necessary formulas, obtained by direct substitution,
are

    s<=k*c:
      H=(1+k)*c/2,
      d=(1-k)*s/(2*k),
      B=1+k-(1+k/2)*c-s/2;

    s>=k*c:
      H=L/2, d=D/2, B=1+k-L.                         (6)

### 1.1 The negative e-coordinate is always strict

The smallest permitted center ordinate is

    V_y=-1/2-(1/k+1/2)*(1-c)+(1/k-1/2)*s.

For theta>0, it exceeds -1/2 because

    (1-c)/s=tan(theta/2)
      <=sqrt(2)-1<9/19
      <=(2-k)/(2+k).

Also every admissible center has p_x>=L/2>=1/2.
Therefore

    e dot(p-w)>=-s/2>-1/2                         (7)

for all non-axis-parallel frames. For theta=0
the weak inequality follows directly.

### 1.2 The regime s<=k*c

Here the greatest e-coordinate of p-w occurs
at A; the greatest f-coordinate occurs at U
and the least f-coordinate at V.

Put z=tan(theta), 0<=z<=k. At A an exact
calculation gives

    E(z):=e dot(A-w)
      =(k+1/2)/sqrt(1+z^2)
       -[(1+k)-(1/k-1)*z^2]/[2*(1+z^2)].

Differentiation yields

    E'(z)=z/(1+z^2)^2 *
      [k+1/k-(k+1/2)*sqrt(1+z^2)].                (8)

The bracket is strictly positive: AM-GM
gives k+1/k>=2, while
(k+1/2)*sqrt(1+z^2)
 <=(17/14)*(5/4)=85/56<2,
using k<=5/7<3/4.
Consequently E increases, and

    E(z)<=E(k)=(k+1/2)/sqrt(1+k^2)-1/2<1/2,      (9)

because k<3/4 implies (k+1/2)^2<1+k^2.

For the positive f-coordinate at U, the exact
expression is

    f dot(U-w)
      =(1+1/k)*c-c^2/k-c*s+s/2-1/2.             (10)

For theta>0 this is below 1/2 if and only if

    (1-c)*(c-k)<k*s*(c-1/2).

If c<=k, it is immediate. If c>k, use
1-c=s^2/(1+c), s<=k*c, and the inequality

    c*(c-k)/(1+c)<c-1/2,

which rearranges to c*(k+1/2)>1/2.
The latter follows from k>=1/2
and c>=1/sqrt(2)>1/2. Therefore (10)
is strictly less than 1/2.

Finally the negative f-coordinate at V is

    -f dot(V-w)
      =1/2-s/2+(1+1/k)*c*(1-c)
          +(1-1/k)*c*s.                            (11)

For theta>0 it is below 1/2 precisely when

    (1+k)*c*s/[k*(1+c)]
           <1/2+(1/k-1)*c.

Since s<=k*c and c^2/(1+c)<=c/2,
the left side is at most (1+k)*c/2.
The right minus that upper bound is

    1/2+[1/k-3/2-k/2]*c
      >=1/2-(16/35)*c
      >=3/70>0,                                   (12)

because 1/k-3/2-k/2 decreases in k
and equals -16/35 at k=5/7.
This proves all four strict inequalities
(5) in the first orientation regime.

### 1.3 The regime s>=k*c

Now the greatest e-coordinate and f-coordinate
occur at U, and the least f-coordinate at V.
Set

    g=cos(2theta)+sin(2theta)-c,
    j=cos(2theta)-sin(2theta)+s.

The three quantities to bound above by 1/2 are

    E_U=g/2+(s/k)*(1+k-L),
    F_U=j/2+(c/k)*(1+k-L),
    F_V=-j/2+(c/k)*(1+k-L).                      (13)

At fixed theta>0 each expression increases
strictly with k, because
(1+k-L)/k=1+(1-L)/k increases with k.

If theta<=theta0:=arctan(5/7),
increase k to k'=tan(theta)<=5/7.
This puts us at the boundary s=k'*c
of the first regime, whose strict
bounds have already been proved.
It remains to treat theta0<=theta<=pi/4
at the single endpoint k=5/7.

On this final interval we have the simple
rational comparisons

    s>=5/sqrt(74)>29/50,
    s<71/100, c<82/100,
    s^2>=25/74>1/3,
    s*c>=35/74>47/100,
    L>=12/sqrt(74)>139/100.                      (14)

For E_U at k=5/7, differentiation twice
using c'=-s, s'=c gives

    E_U''=(96*s^2+16*s*c-24*s+5*c-48)/10
          <[48+8-24*(29/50)+5*(82/100)-48]/10<0.

The first derivative at theta0 is

    E_U'(theta0)=(193/sqrt(74)-24)/10<0,

since 193^2<24^2*74. Thus E_U
strictly decreases in theta on this interval.
At the left endpoint it is the first-regime
boundary expression

    E_U(theta0)=17/(2*sqrt(74))-1/2<1/2,

because 17^2<4*74. Hence E_U<1/2 everywhere.

Next j is strictly decreasing:
j'=-2*sin(2theta)-2*cos(2theta)+c
 <=-2*(35/37)+1<0.
At theta0,

    j(theta0)=-23/37+5/sqrt(74)<0,

by the positive square comparison
25*37^2<23^2*74. Thus j<=0.
Using L>139/100 and c<=1,

    F_U<=c/k*(1+k-L)
      <(7/5)*(12/7-139/100)
       =227/500<1/2.                             (15)

For F_V at k=5/7, differentiating gives

    F_V'=(8*s^2+48*s*c-24*s-5*c-4)/10
      >[8/3+48*(47/100)
         -24*(71/100)-5*(82/100)-4]/10
       =13/1500>0.                                (16)

Thus F_V is strictly increasing, with maximum
at theta=pi/4. Direct substitution gives

    F_V(pi/4)=-9/10+19/(10*sqrt(2))<1/2,

because sqrt(2)>19/14, proved by squaring
positive quantities. This proves all three
strict upper bounds from (13). Together
with (7) this finishes the entire
non-axis-parallel orientation range.

### 1.4 Axis-parallel frames and boundary cases

At theta=0, the possible center triangle in
(4) has vertices

    (1/2+k/2,0), (1/2,1/2), (1/2,-1/2).

Every such axis-aligned square contains w.
It has w on its boundary only for the
two centers (1/2,+1/2) and (1/2,-1/2),
which give precisely (3). All other
allowed axis-aligned squares contain w
in their open interiors.

We have proved the triangle theorem
with its complete strictness and equality
classification. This uses no interval grid.

## 2. Transfer the common point to disk caps

Fix h in [2/5,1] and put

    k=1/(1+h),       R0=sqrt((h+1)^2+1).

Then k is in [1/2,5/7]. Any unit square
in D_R cap {x>=h}, where R<=R0,
satisfies the two disk-support inequalities

    x+k*y <=R*sqrt(1+k^2)
              <=h+1+k,
    x-k*y <=R*sqrt(1+k^2)
              <=h+1+k.

After translating the square horizontally
by -h, these place it inside T_k.
The triangle theorem forces it to
contain the fixed point (1/2,0);
in the original coordinates the point is

    w_h=(h+1/2,0).                                (17)

If two unit squares have disjoint open
interiors, they cannot both contain w_h
unless both have w_h on their boundaries:
an interior point of one cannot belong
even to the closed set of the other,
since an open neighborhood inside the
first necessarily meets the other's
open interior.

The triangle theorem therefore makes
both squares the two axis-parallel
boundary cases

    [h,h+1] x [-1,0],
    [h,h+1] x [0,1].

Both have a vertex with squared norm
(h+1)^2+1=R0^2. Thus containment implies
R>=R0, contradicting R<R0. At R=R0,
these two squares realize equality and
are the only possibilities.

If R>R0, inequality (1) is immediate.
This completes the exact sharp
arbitrary-orientation cap theorem.

## Role in the unrestricted eight-square problem

The enlarged offset interval [2/5,1]
covers **every** pair of exterior squares
whose whole-square separator is a
central side with signed threshold
h>=2/5. It is considerably broader
than the earlier interval [2/3,1].

For example, a central square C with
center side-normal coordinate t,
and two other squares wholly beyond
its positive side, must satisfy

    R^2>=(t+3/2)^2+1

whenever t+1/2>=2/5; this has
no orientation assumption on either
outer square.

The theorem does not count tilted
squares separated only on their
own oblique side axes, and does not
deduce the six directed candidate
separators in every packing.
The unrestricted sharp inequality
R8>=Rhat remains an unsolved
global step.
