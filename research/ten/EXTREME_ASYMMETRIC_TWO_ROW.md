# Every permitted asymmetric two-row core has capacity at most nine

**Handoff status:** independently reviewed hand proof for the stated core
family. The unrestricted four-inner-center case remains open.

The quarter-unit restriction on the upper offsets in
[ASYMMETRIC_TWO_ROW_COMPLETION.md](ASYMMETRIC_TWO_ROW_COMPLETION.md) can
be removed. In the origin-centered disk of squared radius `9/2`, suppose
four core squares are axis-parallel with centers

```text
(-1/2,-t), (1/2,-t), (-b_L,1-t), (b_R,1-t),
0<t<=5/12,       b_L+b_R>=1,
b_L^2+(1-t)^2<=1,  b_R^2+(1-t)^2<=1.
```

Then at most five additional unit squares fit, even with arbitrary
individual orientations. No assertion is made that a general four-square
core admits this two-row description.

Use the notation of the preceding manuscript:

```text
r=sqrt(1+1/sqrt(2)), A=(sqrt(17)-1)/2,
h=1/2-t, z=3/2-t, g=b_L+b_R-1,
gamma=acos(1/r), t_0=2^(-1/4)-1/2.
```

The hypotheses automatically give

```text
3/16<b_L,b_R<13/16,
z>=13/12>27/25, h>0.
```

Indeed both absolute upper offsets are at most `sqrt(95)/12<13/16`,
and their sum is at least one. In particular both are positive.
The unit-disk clearance argument from Section 1 of the preceding manuscript
still applies verbatim, so every additional center has norm `1<u<=A`.

## 1. The lower noncrossing case needs no quarter-offset hypothesis

Suppose `t<=t_0`. As proved in the preceding manuscript, `t<7/20`, so

```text
b_i<19/25, b_i>6/25, z>23/20.
```

The only places where the earlier proof used `b_i>=1/4` were to ensure
that each retained upper-quadrant trace has positive length and that each
outer vertical edge has coordinate magnitude greater than `2/3`.
Both properties follow from these stronger bounds in the current case:

```text
b_i+1/2>37/50>2/3,
(b_i+1/2)^2+z^2>(37/50)^2+(23/20)^2>r^2.
```

The inward corners remain inside the test circle. The endpoint formulas,
six-arc count, bound `g<=sqrt(2)-1`, and upper-sector center-clearance
contradiction are unchanged. Thus the lower noncrossing case is excluded.

For `t>t_0`, the earlier theorem already applies if both b values are at
least `1/4`. By reflection it remains only to treat

```text
t>t_0,       3/16<b:=b_R<1/4,       b_L>=1-b>3/4.
```

Here `g<1/4+13/16-1=1/16`.

## 2. Three retained core arcs force three squares into one large gap

Ignore the small upper-right square's trace entirely. Retain the
upper-left square's second-quadrant trace and the two lower traces.
The upper-left trace is

```text
[pi-beta,pi-alpha],
beta=asin(z/r),       pi/4<beta<3pi/8,
0<alpha<pi/8.
```

To justify these bounds, `z=3/2-t<2-2^(-1/4)<6/5<H=(1+sqrt(2))/2`,
using `2^(-1/4)>4/5` and `sqrt(2)>7/5`.
Thus the top edge supplies the upper endpoint beta. The inner vertical edge
would supply an angle greater than `3pi/8`. At the lower endpoint, the
horizontal-edge bound is less than `pi/8`; the outer vertical edge also
gives less than `pi/8`, since
`b_L+1/2>5/4>r cos(pi/8)=H`.

The lower traces have the same endpoints as before, with
`delta=asin((t+1/2)/r)>gamma`. The three enlarged complementary gaps are:

```text
left:    alpha+gamma<pi/2,
bottom:  pi-2delta<3pi/4,
large:   pi-beta+gamma<pi.
```

They can hold at most one, two, and three connected arcs of angle at least
`pi/4`. Consequently six additional squares would require three in the
large gap. Lift its angles to

```text
[-gamma,pi-beta].                                      (1)
```

## 3. No additional center lies in the central upper sector

The center-clearance estimates in Sections 3 and 4 of
[ASYMMETRIC_TWO_ROW_COMPLETION.md](ASYMMETRIC_TWO_ROW_COMPLETION.md)
apply to any additional center with polar angle in

```text
[beta,pi-beta].                                        (2)
```

They depend only on that angular condition and the following bounds,
all valid here:

```text
1<u<=A<25/16,  27/25<z<H<5/4,
b_i+1/2>11/16>2/3,
g<1/16<4/25.
```

Outside the two outer top corners the endpoint estimates give distance
less than `1/2` from the core. Over either upper horizontal interval the
vertical distance is less than `193/400`. In the middle opening the
squared distance is strictly below

```text
(2/25)^2+(193/400)^2=38273/160000<1/4.
```

Thus (2) is impossible for an additional center.

The radial test-circle point of every additional center lies in that
square's open inscribed disk. A square whose connected arc is in (1)
therefore has its center angle in (1), and the exclusion of (2) strengthens
this to

```text
-gamma<=arg(x,y)<beta.
```

In particular `x>0` and

```text
y>-9/8,       y<25/16.                                (3)
```

For the lower bound use `gamma<pi/4` and
`A sin(gamma)<25/(16sqrt(2))<9/8`.

## 4. A rectangle contained in the core forces a right-cap square

The core contains the solid rectangle

```text
J=[b-1/2,b+1/2] x [-t-1/2,z].
```

Its upper half is the small upper-right square; its lower half lies in
the lower pair's solid rectangle. The origin is in J's interior.
Let S be one of the required large-gap squares.

The separating-axis theorem supplies a weak separator between S and J
normal to an edge of either rectangle. Coordinate separation can put S
only to the right of J. Indeed its center has x>0 while J's left edge is
negative. Above J would require `y>=z+1/2>25/16`. Below J would require
`y<=-t-1<-5/4`, using `t>t_0>1/4`, contrary to (3).

For an oblique separator, the support point of J is one of its four
corners. Neither left corner is possible. Its x-coordinate is negative,
and the outward normal's x-component is negative, so the center's
horizontal contribution to the support inequality is negative. Its
vertical contribution is less than `1/2` in absolute favorable direction:
at the top use `y-z<25/16-13/12<1/2`; at the bottom use
`-t-1/2-y<9/8-t-1/2<3/8`. The required center-to-support-line distance
is at least the square halfwidth `1/2`, a contradiction.

Only the two right corners remain. Move S inward along the separator
normal until its inner edge contains the chosen corner q. This preserves
disk containment because the corner's outward support value is positive.
The corner belongs to the inner edge segment; otherwise a coordinate
separator already exists. These are the elementary translation facts in
Section 1 of
[GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md).

We use its Section 3 corner lemma in its algebraic form: at a corner with
positive absolute coordinates `(a,d)`, if

```text
(3/2-a)^2+(3/2-d)^2<=1,
```

then an obliquely separated unit square in `D_(9/2)` lies strictly beyond
the coordinate line of distance `1/2` corresponding to its dominant
outward normal component. The relevant corner coordinate must exceed
`1/2`. The proof uses only the displayed bound on the auxiliary vector,
not the presence of an actual core center at that vector.

At the upper-right corner `(b+1/2,z)`, this auxiliary vector is
`(1-b,t)`. Its squared norm is at most

```text
b_L^2+t^2<=2t<=5/6<1.
```

A predominantly rightward normal therefore puts S in `x>1/2`.
A predominantly upward normal is impossible. For such a unit normal,
the corner's normal projection is at least

```text
min(z,(b+1/2+z)/sqrt(2))>17/16.
```

Here `z>=13/12>17/16` and
`(b+1/2+z)/sqrt(2)>(11/16+13/12)/(3/2)=85/72>17/16`.
The two outer-edge vertices would then give a maximum squared norm
strictly greater than

```text
(1+17/16)^2+1/4=1153/256>9/2.
```

At the lower-right corner `(b+1/2,-t-1/2)`, the auxiliary vector is
`(1-b,1-t)`, of squared norm at most
`b_L^2+(1-t)^2<=1`. Both relevant absolute corner coordinates exceed
`1/2`. The corner lemma therefore puts S wholly in `x>1/2` or wholly in
`y<-1/2`, according to the dominant normal component. Outward translation
back to the original S preserves the asserted coordinate half-plane.

The second alternative cannot occur for a large-gap square. On the test
circle, the cap `y<=-1/2` meets the angular interval (1) only in
`[-gamma,-pi/8]`, of length `gamma-pi/8<pi/8`. It cannot contain S's
connected arc of angle at least `pi/4`.

Thus every large-gap square lies wholly in the right cap `x>=1/2`.

## 5. The necessary triple contradicts cap rigidity

The sharp three-square cap theorem
[THREE_SQUARE_CAP.md](THREE_SQUARE_CAP.md) says that three squares in
this cap force, among their members, the axis-parallel square centered
at `(1,1)`. That square overlaps the upper-right core square centered at
`(b,1-t)`: their horizontal center difference is `1-b<1` and their
vertical difference is `t<1`.

Therefore at most two large-gap squares can exist. Section 2 requires
three if six additional squares fit, a contradiction. This excludes the
extreme asymmetric crossing case and completes the stated two-row theorem.
