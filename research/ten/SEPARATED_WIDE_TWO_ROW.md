# Separated two-row cores over the full displacement interval

**Status:** independently reviewed hand proof (2026-10-29). The displayed
core hypotheses remain essential; no unrestricted lower bound is claimed.

Suppose a packing in the origin-centered disk of squared radius `9/2`
contains four axis-parallel unit squares centered at

```text
(-a,-t), (a,-t), (-b_L,1-t), (b_R,1-t),
1/2<=a<=1/sqrt(2),       0<t<3/2-2^(-1/4),
b_L+b_R>=1,
b_L^2+(1-t)^2<=1,  b_R^2+(1-t)^2<=1.
```

Then at most five additional unit squares fit, even with arbitrary
independent orientations. In particular the entire packing has at most
nine squares.

This combines the displacement extension in
[WIDE_DISPLACEMENT_TWO_ROW.md](WIDE_DISPLACEMENT_TWO_ROW.md) with the
separated lower pair in
[SEPARATED_LOWER_TWO_ROW.md](SEPARATED_LOWER_TWO_ROW.md). The proof below
checks the interaction of the two extensions explicitly. It uses the
already established arc, corner, and cap lemmas and does not use a radial
count certificate. It is a conditional theorem for this exact two-row
core; no general four-inner-square normal form is asserted.

Write

```text
r=sqrt(1+1/sqrt(2)), A=(sqrt(17)-1)/2<25/16,
h=1/2-t, z=3/2-t, d=a-1/2,
gamma_a=acos((a+1/2)/r), gamma_0=acos(1/r),
t_0=2^(-1/4)-1/2,
t_*=r/sqrt(2)-1/2=(sqrt(2+sqrt(2))-1)/2.
```

The upper-center constraints imply
`t>=1-sqrt(3)/2>1/8`. Also

```text
0<=d<=1/sqrt(2)-1/2<1/4,
pi/8<=gamma_a<=gamma_0<pi/4,
(a+1/2)^2<=r^2-1/4.
```

The latter two bounds follow from
`r*cos(pi/8)=1/2+1/sqrt(2)`.

## 1. Every additional center has norm greater than one

Put `B=sqrt(2t-t^2)`. The displacement upper bound gives `t<2/3`,
because `2^(-1/4)>5/6`. Hence

```text
1/2<=B<sqrt(8/9)<19/20,
1-B<=b_L,b_R<=B.
```

The two lower horizontal intervals cover `[-1,1]` except for the
middle opening `[-d,d]`. For a unit-disk point below height `h`, its
horizontal miss from this union is at most `d<1/4`, and its vertical
miss below the common bottom is at most
`max(1/2-t,0)<3/8`. Its squared distance from the lower pair is therefore
less than

```text
(1/4)^2+(3/8)^2=13/64<1/4.
```

Above `h`, the upper pair has middle opening at most `2B-1`, and each
outer end misses the interval `[-1,1]` by at most `B-1/2`.
The horizontal miss is thus at most `B-1/2<9/20`, and the vertical miss
above the common top is at most `max(t-1/2,0)<1/6`. Its squared distance
from the upper pair is less than

```text
(9/20)^2+(1/6)^2=829/3600<1/4.
```

Every point of the closed unit disk is consequently within distance
strictly less than `1/2` of the core. The open inscribed disk of any
additional square forces its center norm `u` to satisfy `1<u<=A`.
The center-radius arc theorem therefore gives each additional square one
connected test-circle arc of angle at least `pi/4`. Its radial test-circle
point lies in the square's open inscribed disk, since `|r-u|<1/2`.

## 2. Small displacement: the arc count remains valid

Assume first `t<=t_*`. Use the exact constants established in Section 1
of [WIDE_DISPLACEMENT_TWO_ROW.md](WIDE_DISPLACEMENT_TWO_ROW.md):

```text
t_*<17/40,       2/11<b_L,b_R<9/11,
z>43/40,        b_i+1/2>15/22>2/3.
```

The lower squares' upper outside corners lie inside the test circle,
because their squared norms are at most `r^2-1/4+h^2<r^2`.
Their inner corners are also inside: their squared norms are less than

```text
d^2+(t+1/2)^2<1/16+(37/40)^2=1469/1600<1.
```

If the lower outside bottom corners are on or inside the test circle,
the lower squares have no positive-length trace, and `t<=t_0` because
`a+1/2>=1`. The noncrossing argument in Section 1 of
[EXTREME_ASYMMETRIC_TWO_ROW.md](EXTREME_ASYMMETRIC_TWO_ROW.md) uses only
the upper core and exterior additional centers; it applies unchanged.

Otherwise the lower traces have the same endpoint formulas as before,
with `gamma_a` in place of `gamma_0` and

```text
delta=asin((t+1/2)/r)>gamma_a>=pi/8.
```

First suppose both upper offsets are at least `1/4`. Their retained
quadrant arcs have endpoints `[alpha_R,beta_R]` and
`[pi-beta_L,pi-alpha_L]`, as in
[ASYMMETRIC_TWO_ROW_COMPLETION.md](ASYMMETRIC_TWO_ROW_COMPLETION.md).
Their positivity and endpoint inequalities continue to hold by the
constant table in the wider-displacement proof. The four complementary
gaps have angles

```text
pi-beta_L-beta_R,
alpha_L+gamma_a,
pi-2delta,
alpha_R+gamma_a,
```

and capacities at most one, two, two, and two. Both side gaps cannot
contain two arcs: that would make both `alpha_i` outer-vertical-edge
endpoints and imply

```text
b_i+1/2<=r*sin(gamma_a)<=r*sin(gamma_0)=2^(-1/4),
```

contrary to `b_L+b_R>=1`. Thus six additional squares require an upper-gap
square and a side gap containing two. The latter forces one `b_i<=t_0`.
The middle opening is then bounded by

```text
g=b_L+b_R-1<41/120+9/11-1=211/1320<4/25.
```

The required upper gap gives `z<=H=(1+sqrt(2))/2` and
`beta_L=beta_R=asin(z/r)`. The upper-sector clearance proof in Sections 3
and 4 of the asymmetric manuscript, with the wider-displacement constants,
excludes its required square. In detail the horizontal center bound is
less than `9/10`, the outer-corner endpoint bounds remain less than
`1/2`, and the middle-opening squared clearance is less than

```text
(2/25)^2+(39/80)^2=39049/160000<1/4.
```

None of these upper-sector estimates depends on `a` or on the lower pair
touching. This closes the ordinary crossing case.

## 3. Small displacement: the virtual slot remains inaccessible

It remains, after reflection, to consider a crossing lower pair with
`b:=b_R<1/4`. Then `b_L>3/4`, and its center constraint implies

```text
t>1-sqrt(7)/4>1/3,
z<7/6<H,
g<1/4+9/11-1=3/44<4/25.
```

Retain the upper-left quadrant arc and the two lower traces. The former
has endpoints `[pi-beta,pi-alpha]`, with

```text
beta=asin(z/r),       pi/4<beta<3pi/8,
0<alpha<pi/8.
```

The three complementary gaps have capacities one, two, and three:
their angles are `alpha+gamma_a<pi/2`, `pi-2delta<3pi/4`, and
`pi-beta+gamma_a<pi`. Thus six additional squares would require three
in the large gap `[-gamma_a,pi-beta]`.

The same upper-sector clearance bound just used, now with `g<3/44`,
excludes every additional center angle in `[beta,pi-beta]`. The radial
test-circle point therefore puts the center `(x,y)` of each required
large-gap square in

```text
-gamma_a<=arg(x,y)<beta,
x>0,       -9/8<y<25/16.                           (1)
```

Consider the virtual rectangle

```text
J=[b-1/2,b+1/2] x [-t-1/2,z].
```

Its upper half is the upper-right core square. Its lower half is covered
by the lower pair except for the open slot

```text
G=(-d,d) x (-t-1/2,h).
```

For `d=0` there is no slot. For `d>0`, the two slot sides belong to the
lower squares, and its whole top belongs to the upper-right square:
`b-1/2<-1/4<-d` and `b+1/2>d`.

Suppose the interior of a large-gap square `S` contained a point `p` of
`G`. Its center `c` lies outside the closed slot, whose squared point
norms are less than `1469/1600<1`. The circumradius gives

```text
0<x<d+1/sqrt(2)<=sqrt(2)-1/2<11/12.
```

Together with (1) and `tan(gamma_a)<=2^(-1/4)<17/20`, this yields

```text
y>=-x*tan(gamma_a)>-187/240>-5/6>-t-1/2.
```

The segment from `p` to `c` stays inside `S` and above the slot bottom.
It must exit the slot through its side or top, hence through a point of
an actual core square. Such a point cannot lie in `S`'s interior, even
if it is on the core boundary, since a neighborhood would meet the core
interior. This is a contradiction. Openness also excludes interior points
of `S` on the uncovered slot bottom. Every other point of `J` is in the
actual core. Thus `S` has interior disjoint from all of `J`.

Now apply the corner-separator argument of Section 4 of
[EXTREME_ASYMMETRIC_TWO_ROW.md](EXTREME_ASYMMETRIC_TWO_ROW.md), with the
constant replacements of the wider-displacement proof. Its assumptions
are exactly disjointness from `J`, (1), `t>1/4`, and the upper-center
constraints. The upper-corner auxiliary vector has squared norm at most
`2t<17/20<1`; the lower-corner vector has squared norm at most one.
Left-corner separators are impossible because the favorable vertical
distance is less than `1/2`, and a predominantly upward separator is
impossible because its support projection exceeds `17/16`.

Consequently `S` lies wholly in `x>1/2` or wholly in `y<-1/2`.
The latter cap meets its available angular interval only in
`[-gamma_a,-pi/8]`, of length at most `gamma_0-pi/8<pi/8`, so cannot
contain its arc of angle at least `pi/4`. All three required large-gap
squares would therefore lie in `x>=1/2`.

The sharp three-square cap theorem then forces an axis-parallel square
centered at `(1,1)`. It overlaps the upper-right core square at `(b,1-t)`,
because `1-b<1` and `t<1`. This contradiction closes the extreme crossing
case, proving the theorem for `t<=t_*`.

## 4. Larger displacement needs only three retained arcs

Now assume `t_*<t<3/2-2^(-1/4)`. Section 1 already proves that all
additional centers are exterior. At least one upper offset is at least
`1/2`; reflect to make it `b_L`. Retain its upper-left quadrant trace
and the two lower traces.

The lower upper outside corners are inside the test circle because
`|h|<1/6` and `(a+1/2)^2<=r^2-1/4`. The lower inner corners are also
inside, since

```text
d^2+(t+1/2)^2<1/16+(7/6)^2=205/144<r^2.
```

Their outside bottom corners are outside: `t+1/2>r/sqrt(2)` and
`a+1/2>=1` give squared norm greater than `1+r^2/2>r^2`.
Thus their trace endpoints use `gamma_a` and

```text
delta=asin((t+1/2)/r)>pi/4.
```

The retained upper-left trace has endpoints

```text
[pi-beta,pi-alpha],       0<=alpha<=gamma_0<beta<pi/2.
```

Indeed its outward top corner is outside because `b_L+1/2>=1` and
`z>2^(-1/4)`. Its inward top corner has squared norm at most
`5/2-t-b_L<=2-t<r^2`; the inward bottom corner is also inside.
The outer vertical-edge lower-angle bound is at most `gamma_0`, and any
positive bottom-edge bound is smaller than `gamma_0`. If `h<=0`, quadrant
clipping contributes zero instead. Both upper-angle bounds exceed
`gamma_0`: the top-edge bound because `z>2^(-1/4)`, and the inner
vertical-edge bound because `b_L-1/2<1`.

The complementary gaps have angles

```text
alpha+gamma_a<=2*gamma_0<pi/2,
pi-2delta<pi/2,
pi-beta+gamma_a<pi.
```

Their capacities are at most one, one, and three exterior arcs,
respectively. Hence at most five additional squares fit. Together with
the small-displacement argument, this proves the full stated theorem.

## Verification scope

All threshold and clearance comparisons above are explicit rational or
quadratic-radical inequalities. This is a hand proof assembled from the
two separately reviewed extensions, with their interaction checked here.
Lean formalization and kernel verification have not been performed.
