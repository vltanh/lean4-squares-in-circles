# A uniform regular seven-square loaded ring cannot enclose three squares

This closes a restricted subcase of
[ALL_LOADED_COMPONENT_RINGS.md](ALL_LOADED_COMPONENT_RINGS.md). Suppose
all seven square frames have the same signed offset from their center
rays, after using the square frames' quarter-turn symmetry. Then the ring
cannot be a component of a
ten-square packing in squared radius at most `9/2` in the stated radius
window.

The common signed-offset hypothesis is not proved for a general
seven-loaded positive component. Equal radii and equal angular gaps
follow from it and the neighbor contacts, as shown below. This note does
not close the remaining nonuniform ring case.

## 1. The uniform contact family

Put

```text
h=pi/7, c=cos(h), s=sin(h),
A=c+s, B=c−s, k=cA/(2s).
```

By reflection and square symmetry, take the common frame offset
`0<=psi<=pi/4`. Consider the square with center `(r,0)` and edge vectors

```text
u=(cos(psi),sin(psi)), v=(−sin(psi),cos(psi)).
```

Every square is loaded in the same containing circle, so the equation
`R²=r²+r(cos(psi)+sin(psi))+1/2` makes all seven center radii equal.
For a successive center gap `2h_i`, the ring theorem gives
`pi/5<2h_i<2pi/5`. The separating-axis calculation below, with `h_i`
in place of h, gives the contact radius

```text
r=(1+t_i)/(2t_i(cos(psi)+t_i sin(psi))),
t_i=tan(h_i).
```

As a function of positive t this expression is strictly decreasing: its
derivative has the sign of
`−cos(psi)−(2t+t²)sin(psi)<0`. Thus all angular gaps are equal. Their
sum is `2pi`, so each is `2h=2pi/7`.

The next neighbor is therefore the rotation through `2h`. The
support sum in the first square's v-direction is

```text
H=(1+cos(2h)+sin(2h))/2=c(c+s)=cA.
```

The center displacement has projection
`2r s cos(h−psi)` in that direction. This is the largest absolute
projection among the two squares' four edge-normal directions. Indeed,
apart from signs, the corresponding factors are

```text
cos(h−psi), sin(h−psi), cos(h+psi), sin(h+psi),
```

and the first dominates on the stated interval; for the last comparison
use `(c−s)(cos(psi)−sin(psi))>=0`. Because the neighbors touch, the
separating-axis condition therefore gives exactly

```text
r=k sec(h−psi).                                    (1)
```

The containing squared radius of the loaded square is

```text
q=r²+r(cos(psi)+sin(psi))+1/2.
```

With `x=tan(h−psi)`, this becomes the exact quadratic

```text
q(x)=k²(1+x²)+k(A−Bx)+1/2.                         (2)
```

For later use, set

```text
C=r cos(psi)=k(c+sx),
S=r sin(psi)=k(s−cx).
```

The center's own-frame coordinates are `(C,−S)`. The incoming contact
is the own-frame lower-left corner. The outgoing contact lies on the
upper side, at offset `(xi,1/2)` from the center, where

```text
xi=−2ksx−cos(2h)/2+cs.
```

It varies strictly from `−1/2` to `1/2` as psi varies from zero to
`pi/4`. For `0<psi<pi/4`, the contact is therefore a side-interior/vertex
contact with a unique separating normal. At the two endpoints it is a
vertex/vertex contact; those endpoints are treated separately below.

## 2. Interior offsets: stress forces the unique stationary member

Suppose `0<psi<pi/4`. Vary psi smoothly in the uniform contact family
(1), with q given by (2). Every positive ring contact retains zero
normal relative velocity, and each loaded circle vertex has squared
norm q. Each square has a unique farthest vertex in this open interval.

Apply the physical certificate's force-and-torque balance to this virtual
motion. Contact work cancels, and the circle-force work is minus a
strictly positive constant times `q'`. Thus `q'=0`. This virtual-work identity uses the original
unique contact normals. It does not require feasibility with respect to
zero-weight contacts elsewhere in the packing.

Since x varies strictly with psi, (2) now forces

```text
x=B/(2k),
r²=k²+B²/4,
q=k²+kA+1/2−B²/4.                                 (3)
```

The elementary bounds in Section 3 give `cot(h)<21/10`. At `psi=0`,
the squared radius is

```text
q_0=cot²(h)/4+cot(h)+5/4 < 1781/400 < 9/2.
```

The stationary value in (3) is smaller still. Thus both this stationary
member and the endpoint `psi=0` are strictly subcritical. The
center-radius reduction forces all three remaining centers below one,
and the physical-ring theorem places their entire squares in its inner
region. This justifies the three-square hole requirement used below.

The resulting values are approximately `psi=.281857057` and
`q=4.216251575`; these decimals are descriptive, not premises.
At this member the exact own-frame quantities simplify to

```text
C=(cot(h)+cos(2h))/2,
S=sin(2h)/2,
xi=1/2−cos(2h).                                   (4)
```

## 3. Exact area of the stationary hole

For the stationary member, the inner boundary follows each square's full
left edge from the incoming lower-left corner to its upper-left corner,
then follows its upper edge to the outgoing contact. The top segment
has length `xi+1/2=1−cos(2h)`.

These pieces form a simple polygon: each body's boundary path is simple,
and different bodies meet only at the specified neighboring contact
points. Replacing the corresponding center-to-contact paths of the
physical ring by these boundary paths is a homotopy inside the loaded
squares, all of which avoid the origin. The new polygon therefore still
has winding number one about zero. Along its full left edge the square
lies to the right of the upward-directed path, and along its top segment
the square lies to the right of the rightward-directed path. Thus all
loaded-square interiors are outside this positively oriented polygon.
Its bounded region is precisely the central free hole. It need not be
star-shaped about zero. The three remaining squares meet `B(0,1/2)` in
their interiors and cannot cross a loaded body, so their interiors must
lie in this same hole.

In own coordinates, the two oriented edge contributions to the shoelace
sum are

```text
C−1/2,
(S−1/2)(xi+1/2).
```

Rotations preserve the cross product. Summing over seven squares and
using (4) gives the exact hole area

```text
Area = (7/4)[cot(h)+(sin(2h)−2)(1−cos(2h))].        (5)
```

Here is a short rational upper bound. Write `z=cos(2pi/7)`. The usual
seven-angle sum gives

```text
8z³+4z²−4z−1=0.
```

This polynomial is increasing on `[1/2,1]`. Its values at `3/5` and
`5/8` are `−29/125` and `1/64`, respectively, so

```text
3/5 < z < 5/8,
sin(2h)<4/5,
cot(h)=sqrt((1+z)/(1−z))<sqrt(13/3)<21/10.
```

Equation (5) consequently gives

```text
Area < (7/4)[21/10−(6/5)(3/8)] = 231/80 < 3.
```

The three remaining interior-disjoint unit squares, which the physical
ring theorem puts in this hole, have total area three. They cannot fit.

## 4. The two vertex-contact endpoint families

The virtual-work differentiation in Section 2 is deliberately not used
at `psi=0` or `psi=pi/4`, where contact-normal uniqueness fails.

At `psi=pi/4`, (1) gives

```text
r=cot(h)/sqrt(2),
R=(cot(h)+1)/sqrt(2)>3/sqrt(2),
```

because `z>3/5` implies `cot(h)>2`. This endpoint lies outside the target
radius range.

At `psi=0`, the outgoing contact is the upper-left corner. The inner
boundary consists of seven full unit sides and is a regular heptagon.
Its circumradius is

```text
1/(2sin(h)) < 2/sqrt(3) < 5/4.
```

The first inequality follows from `z<5/8`, which gives
`sin²(h)=(1−z)/2>3/16`. But three unit squares cannot lie in a disk of
radius `5/4`: their optimal radius is `5sqrt(17)/16>5/4`, by the
repository's hand proof of the
[three-square theorem](https://github.com/vltanh/lean4-squares-in-circles/blob/4bea747b3efa13c869b956cb28435efaf21526fa/docs/proof/06-three.md).
Thus the radial-side endpoint cannot contain the three inner squares
either.

All members of the common signed-offset family compatible with a
physical positive stress are now excluded as ten-square completions.
General seven-loaded rings may have unequal frame offsets; their
classification remains open.
