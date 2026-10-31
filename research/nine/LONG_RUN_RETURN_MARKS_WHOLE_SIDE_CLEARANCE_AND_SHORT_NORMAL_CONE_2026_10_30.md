# A long run puts every return mark on one side and confines every short-return normal

Date: October 30, 2026 UTC.

**Status: complete proposed hand family theorem, awaiting independent
review. No original closure or ledger flag is changed here.**

The result uses the actual geometry of one long run and the circular
order supplied by a compatible physical cycle embedding. It localizes
whole return-marked squares, not only their centers. A second conclusion
restricts a supported run between any two return marks without imposing
a common square frame. The unresolved sharp seven-body terminal is
stated separately at the end.

## 1. Geometric statement

Let actual unit squares have pairwise disjoint open interiors and lie
in a disk centered at O of radius

    79/40 <= R <= sqrt(Q), Q=1105/256.

Let a simple actual contact cycle admit a compatible physical embedding:
the original center-to-contact strands can be made noncrossing by
arbitrarily small changes in their junction disks and strand tubes,
respecting the incident square sectors. This is the physical premise
of `UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md`,
not a premise of abstract graph planarity alone.

Mark at least three cycle bodies, all of which physically touch the
containing circle. Suppose one marked-to-marked run is precisely

    A -- U -- V -- B,

with four distinct actual bodies, two unmarked internal bodies, and
one signed unit normal n supporting all three actual contacts from
A toward B. No common-normal condition is required on the rest of
the cycle for the first conclusion. Call every mark other than A,B
a **return mark**.

**Theorem 1 (whole-square return-side localization).** Choose n as the
x direction, with the disk center still the origin. One of the two
choices of sign for the perpendicular y direction makes every return
marked square T satisfy

    (c_T)_y > 43/60,
    T is contained in the open halfplane y>1/120.          (1)

All return marks use the same sign. No chosen contact point, force
line or origin-containment premise for the cycle is needed.

**Theorem 2 (short-return normal cone).** For any two return marks C,D,
any unit direction m satisfying

    m.(c_D-c_C) >= 2                                    (2)

has

    |m.n_perp| < |m.n|.                                 (3)

Thus its unoriented angle to the long normal n is strictly less than
45 degrees. In particular (3) holds for every actual common-normal
run between C,D with at least one internal unit, since its support
identity gives a center projection gap at least two. This applies
whether that run is the displayed return arc or another actual path.

These are geometric conclusions. In a physical stress caller,
unloaded true-positive-degree-two internal bodies provide common
normals by translational force balance. Marked bodies may retain
arbitrary additional positive edges, circle weights and original
means. Torque is not needed for either theorem.

## 2. Exact long-endpoint localization

Put M=91/60 and L=89/60. Every contained unit center has norm less
than M, because its farthest-corner squared norm is at least

    |c|^2+|c|+1/2,
    M^2+M+1/2-Q=31/57600>0.

Write the endpoint centers in the long-normal frame as

    c_A=(-X_A,y_A), c_B=(X_B,y_B).

Actual support telescoping, with each internal width at least one,
gives

    n.(c_B-c_A) >= 2+h_A(n)+h_B(n).

The force-free coupled endpoint theorem in
`TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md`,
Sections 2--3, therefore supplies

    L<X_A,X_B<M,
    |y_A|+|y_B|<=1/8.                                   (4)

It retains both endpoint tilts and all their physical boundary cases.
The support halfwidths h_A,h_B are their actual own-frame halfwidths;
neither endpoint is replaced by an aligned square.

Each endpoint center direction is within five degrees of its signed
long axis. Indeed its deviation is less than

    arctan((1/8)/L)=arctan(15/178)<pi/36.                (5)

Here is an exact elementary check of the last comparison. We have
15/178<3/35, and the tangent triple-angle identity gives

    tan(3*arctan(3/35))=5499/20965<4/15
                                  <2-sqrt(3)=tan(pi/12).

The final inequality follows from 3<(26/15)^2. The triple angle is
in (0,pi/2), so monotonicity proves (5). Consequently A's direction
is within pi/36 of the negative x axis and B's is within pi/36 of
the positive x axis.

## 3. All return center directions lie in one thirty-five-degree sector cut

Use the following two complete geometric facts from Section 3 of
`UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md`:

1. Any two physical circle-touching unit centers have minor angular
   separation strictly greater than 40 degrees throughout this radius
   interval. The input is a whole closed radius-5/4 arc lying in the
   actual open square interior.
2. In the compatible embedded cycle, the marked cyclic order is the
   actual marked-center angular order, up to reversal. The proof uses
   actual disjoint square arcs and circle spokes; it does not assume
   the origin is inside the cycle.

A and B are consecutive marks on their long run. Every other mark
therefore belongs to the complementary A-to-B arc in the actual
center order. Choose the y sign so that this arc goes from the
direction of B near zero to the direction of A near pi through
the upper halfplane. Equations (5) and the strictly greater than
40-degree gaps from the first and last return marks to B,A give,
for every return center direction theta,

    7*pi/36 < theta < 29*pi/36,
    35 degrees < theta <145 degrees.                    (6)

For an intermediate return mark the same bounds follow because it
lies between the first and last in this angular interval. If there
is only one return mark, its separation from both A and B gives
both bounds directly. In particular no return mark is assigned to
the opposite halfplane by a choice made separately for that body.

## 4. From angular localization to whole-square clearance

Every physical circle-touching unit has center radius at least

    r >= R-1/sqrt(2) >= 79/40-1/sqrt(2),                 (7)

by its actual circle corner, whose distance from its center is
1/sqrt(2). From (6),(7), each return center has

    y > (79/40-1/sqrt(2))*sin(7*pi/36).

Concavity of sine between 30 and 45 degrees gives

    sin(7*pi/36) >= (2/3)*sin(pi/6)+(1/3)*sin(pi/4)
                   =1/3+sqrt(2)/6.

Hence

    y > (79/40-sqrt(2)/2)*(1/3+sqrt(2)/6)
       =59/120+13*sqrt(2)/80
       >863/1200
       >43/60.                                         (8)

The penultimate inequality uses sqrt(2)>7/5; the last has exact
reserve 1/400. This proves the center assertion in (1).

Every point of a unit square is within 1/sqrt(2) of its center.
Moreover 1/sqrt(2)<17/24 since 288<289. Thus every actual point p
of every return marked square satisfies

    p_y >43/60-17/24=1/120.                              (9)

This proves the whole-square assertion, including every side and
vertex, and completes Theorem 1.

## 5. Width of the actual return-center cap

All return centers belong to the same open circular cap

    |c|<M, c_y>H, H=43/60.                              (10)

Set K=sqrt(M^2-H^2). Then

    K^2=134/75 < (27/20)^2,
    K<27/20.                                            (11)

Suppose a unit direction m in (2) had vertical component at least
as large in absolute value as its horizontal component. Reversing
and horizontally reflecting coordinates for this width estimate,
write m=(a,b) with

    0<=a<=b, a^2+b^2=1.

For the closed cap |c|<=M, c_y>=H, the maximum of m.c is at most M.
Its minimum is at least -aK+bH. To see the latter directly, write
c_y=z. Then

    m.c >= -a*sqrt(M^2-z^2)+b*z,

and the right side is increasing for H<=z<=M, so its minimum is
the value at H. Therefore the cap's width in m is at most

    M+a*K-b*H
      <= M+(K-H)/sqrt(2)
      < 91/60+(19/30)/sqrt(2)
      < 91/60+19/42
      =827/420 <2.                                     (12)

Here a<=1/sqrt(2)<=b, (11) gives 27/20-H=19/30, and
sqrt(2)>7/5 gives the next strict comparison. The final reserve
is 13/420. The width is invariant under reversing m and under
horizontal reflection, so the estimate applies to every direction
with |m_y|>=|m_x|. It contradicts (2), proving Theorem 2.

For a genuine supported return path with at least one internal unit,
telescoping the unchanged contacts gives

    m.(c_D-c_C)=h_C(m)+h_D(m)+sum internal widths >=2.

This proves the advertised channel caller without using internal
torque, proper endpoint concurrence or a common endpoint frame.

## 6. The remaining opposite long/short seven-cycle terminal

Consider the seven-body cycle

    A -- U -- V -- B -- C -- W -- D -- A,

whose four marks are A,B,C,D and whose unmarked bodies U,V,W are
unloaded of true positive degree two. The long run is A-U-V-B;
the opposite short run is C-W-D; B-C and D-A are the two actual
direct joins. In a compatible physical certificate, Theorem 1 puts
the whole squares C,D on the same strict side of the long diameter,
and Theorem 2 puts the short normal within 45 degrees of the long
normal. The two actual direct joins are still present, and every
other physical square in a nine-body packing is retained.

**Still unproved here:** the sharp implication R^2>=Q from this
opposite long/short geometry with its actual direct joins and all
endpoint tilts, means and full endpoint balances. After the separate
diagonal-short exclusion, the remaining transmitter W is side-normal.
That fact and (3) do not imply that its frame agrees with the long
frame. A proof still has to combine the two actual direct joins with
the coupled long-endpoint height/tilt budget (4). It may not assume
vertical separation of either joined pair, a common horizontal seam,
equal internal center heights or a force line through an internal
center.

The following exact equality packing from
`UNRESTRICTED_THREE_SQUARE_CAP.md`, Section 7, shows why those stronger
normal forms cannot be inserted as conclusions of the geometry:

| Bodies | Actual aligned centers |
| --- | --- |
| A,B | (-3/2,1/16), (3/2,1/16) |
| U,V | (-1/2,1/5), (1/2,1/5) |
| D,C | (-1,-15/16), (1,-15/16) |
| W | (0,-4/5) |
| Two further units | (-3/5,5/4), (3/5,5/4) |

All nine actual squares fit in the disk of squared radius Q, with
pairwise disjoint open interiors. A,B,C,D physically touch its circle.
The displayed seven-body cycle consists of actual contacts and admits
the compatible side-contact embedding. Both supported runs have
horizontal common normals. For the long run, one may choose actual
contact points (-1,0),(0,0),(1,0); for the short run choose
(-1/2,-4/5),(1/2,-4/5). These means satisfy force and moment balance
on their respective internal transmitters if equal positive forces
are used; no full endpoint stress is asserted by this local choice.

The long internal heights 1/5 differ from the endpoint height 1/16.
The middle short square W has top height -3/10, so the lower triple
is not wholly below the sharp cap ceiling -7/16. The same source
proves that this equality packing has no sharp triple cap in any
direction. The new theorems preserve it: C,D are strictly on one
side of the diameter and the short normal has relative angle zero.

## 7. Frozen dependencies and verification boundary

| Source | SHA256 | Used content |
| --- | --- | --- |
| `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md` | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` | Force-free long-gap center and coupled-height bounds |
| `UNIFORM_MARKED_CYCLE_ANGULAR_BUDGET_AND_NINE_BODY_CYCLE_EXCLUSION_2026_10_30.md` | `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be` | Complete forty-degree center separation and physical marked-center order, Section 3 |
| `UNRESTRICTED_THREE_SQUARE_CAP.md` | `b1359fcb446d93a534dc19dc7582edc5e8067300109810369621e47989ecf77b` | Exact staggered equality witness and no-universal-triple-cap diagnostic, Section 7 only |

The new estimates are whole-domain geometric arguments with exact
rational comparisons. They do not alter a physical pose, contact mean,
stress selection or graph degree. No numerical pose search, finite
packing certificate, Lean compilation, CI run, original ledger mutation
or remote publication is a proof premise or claimed action here.
