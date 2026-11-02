# The bounded-inner-height case supplies a routed triple with central floor 109/930

November 2, 2026. Hand proof. No Lean, CI, mathematical script, or
sampled angular cover is used in the derivation.

Let nine physical unit squares with disjoint open interiors lie in the
closed disk of squared radius Q=1105/256. Suppose four form an actual
horizontal projection chain
\[
                      M_0<_xM_1<_xM_2<_xM_3,
\]
and suppose the inner main centers satisfy
\[
                        |y_{M_1}|,|y_{M_2}|<7/20.        \tag{1}
\]
Both (1) hold, in particular, when the two side columns are full and
their main squares occupy the middle markers, by the recovered 7/20
main-height theorem and the physical marker-order theorem.

## 1. Every outsider lies wholly above or wholly below a fixed central band

The unrestricted outsider-strip theorem gives |x_F|<13/12 for all five
outsiders. Assign an outsider in x>=0 to M2, one in x<=0 to M1,
with either assignment permitted at x=0. The physical inner-clearance
theorem gives a vertical center gap exceeding 97/100 from its assigned
main. Since the two main heights differ by less than 7/10, the outsider
is therefore above both inner centers or below both.

Call these alternatives upper and lower. Every upper outsider has
\[
                  y_F>-7/20+97/100=31/50.                 \tag{2}
\]
Every lower outsider satisfies the reflected inequality. In particular,
upper outsiders are above both outer main centers as well, since the
endpoint height budget gives |y_M0|,|y_M3|<=1/8.

Each outsider lies horizontally between the two outer main centers.
Choose an adjacent pair of mains bracketing its horizontal center.
Their contained aligned squares have halfwidths g_i=1/(4h_i).
The exact adjacent-proxy barrier gives, for an upper outsider,
\[
 y_F-h_F\ge\min(y_i+g_i,y_{i+1}+g_{i+1})-G_i/2,           \tag{3}
\]
where G_i is the horizontal gap between the two aligned proxies.
This barrier uses physical disjointness, and permits unequal main heights
and oblique outsider separators.

The actual four-chain span gives G_1<1/30 for the central pair and
G_0,G_2<1/15 for the two outer pairs. For inner mains g_i>15/31,
and hence
\[
 y_i+g_i>15/31-7/20=83/620.
\]
For outer mains the proved endpoint budget gives
g_i-|y_i|>221/600>83/620. Therefore every upper outsider satisfies
\[
                     y_F-h_F>83/620-1/30=187/1860.        \tag{4}
\]
Every lower outsider lies wholly below -187/1860, by reflection.
These are whole-square bounds, not merely bounds on centers.

## 2. The upper/lower occupancies are exactly three and two

Every upper outsider lies in the strip [187/1860,sqrt(Q)]. Its height
is strictly less than 87/44, because
\[
 \sqrt Q<187/90,
 \qquad 187/90-187/1860=11033/5580<87/44.
\]
The first squared comparison has numerator reserve 1564; the final
fraction comparison has difference 1/30690.

The physical strip theorem in
`HORIZONTAL_STRIP_PAIR_CENTER_GAP_HAND_PROOF.md` consequently gives
\[
                      |x_F-x_G|>4/5                     \tag{5}
\]
for any two upper outsiders. It retains both arbitrary orientations.
The same is true for any two lower outsiders.

There cannot be four upper outsiders, since (5) would give center span
greater than 12/5, while all centers lie in |x|<13/12, a strip of width
13/6<12/5. The same holds below. Since there are five outsiders, the
two populations are exactly three and two. Reflect y if necessary so
that there are three upper outsiders.

Order those three by center x-coordinate and denote them L,C,R. Applying
(5) to each adjacent pair, together with |x|<13/12, yields
\[
 x_L<-31/60,\qquad |x_C|<17/60,
 \qquad x_R>31/60.                                      \tag{6}
\]
Thus L lies beyond the left inner main, C lies between the two inner
mains, and R lies beyond the right inner main. The two lower physical
outsiders remain present; none was discarded in this extraction.

## 3. The central unit has the stronger whole floor 109/930

Because x_C lies strictly between the two inner main centers, the
central-pair version of (3) applies to C with G_1<1/30. Using (1),
\[
 \boxed{y_C-h_C>-7/20+15/31-1/60=109/930.}                \tag{7}
\]
The outer shoulders retain their whole floors greater than 187/1860.
In particular, the central floor in (7) exceeds 7/60, since
109/930-7/60=1/1860>0.

This is the stronger central floor required by the extended joint-support
shoulder terminal. It follows from the central proxy gap and should not
be replaced by the weaker outer-pair estimate (4).

## 4. Exact scope of the terminal caller

The extraction proves an actual horizontal four-chain, a physical routed
upper triple obeying (4), (6), and (7), and both remaining lower squares.
It does not assert horizontal projection separation within the triple.
It also does not assert that each shoulder is actually above its matched
outer main in vertical projection.

The endpoint transfer theorems now supply a larger, precisely
stated terminal caller. Suppose, for each matched pair (M0,L) and
(M3,R), at least one of the following holds independently:

1. The shoulder is actually above its matched endpoint in vertical
   projection.
2. There is an upward physical separating unit normal n=(c,s),
   with s>=|c|, owned by a side axis of that outer main.
3. There is an upward physical separating unit normal n=(c,s),
   with s>=|c|, owned by the shoulder, and pointing horizontally
   outward: c<=0 on the left and c>=0 on the right.

The physical supports in the two oblique alternatives are essential;
neither alternative follows just from vertical center order. Horizontal reflection
changes the sign of c on the right but preserves the stated condition.
An actual vertical separator need not be owned by the main, so the
first alternative remains explicitly available.

Under these alternatives the containing squared radius is at least Q.
Here is the full join, including the direction of the two remaining
physical separators. Every upper center lies between 31/50 and
rho=91/60 in height, so its height difference from any other upper
center is less than
\[
                  91/60-31/50=269/300<1.                 \tag{8}
\]
Every unit square contains its centered radius-1/2 disk. Thus the sum
of the support halfwidths of two units in a unit direction is at least
one. For two upper units ordered from left to right, a separating
normal directed toward the right-hand unit cannot have nonpositive
horizontal component: its center projection would then be at most
the absolute vertical center difference, contradicting (8). The
separating-axis theorem therefore supplies normals proportional to
(1,z_L) from L toward C and (1,z_R) from C toward R, for finite real
z_L,z_R. This accounts for every sign and every finite slope; it does
not impose an actual horizontal projection comparison.

For a downward shoulder-to-central transfer use
`ENDPOINT_OWNED_OBLIQUE_DOWNWARD_CENTER_TRANSFER_HAND_PROOF.md`;
for an upward transfer use
`ENDPOINT_OWNED_OBLIQUE_UPWARD_TRANSFER_HAND_PROOF.md`.
For alternative3 use the corresponding
`SHOULDER_OWNED_OUTWARD_DOWNWARD_TRANSFER_HAND_PROOF.md` or
`SHOULDER_OWNED_OUTWARD_UPWARD_TRANSFER_HAND_PROOF.md` instead.
If an endpoint pair uses alternative1, use the original vertical
version of the appropriate transfer instead. The whole central floor
(7) supplies 7/60; the shoulders satisfy the required side columns
by (6) and the outsider strip. For a mixed pair in which the upward
endpoint uses only alternative1, the actual-vertical mixed theorem
uses |x_C|<29/60, already supplied by (6). If its endpoint uses
alternative2 or3, the stronger owner reserve handles every upward slope
directly. The downward reserve is valid in all three alternatives.
The complete independent choice of endpoint alternatives and all four
central slope signs is written in
`MATCHED_SHOULDER_ENDPOINT_OWNER_UNION_HAND_PROOF.md`.

The paired center-cost theorem handles two downward transfers. The
shared central-orientation estimate and the upward shoulder reserves
handle two upward transfers. The retained common central height and
orientation handle the two mixed signs. Each join contradicts strict
subcritical containment, using the actual-four adjusted span at
least2 and the same physical central square on both sides.

At q=Q all shoulder-to-central slopes must vanish. Any selected
nonvertical selected endpoint normal also makes the appropriate bound
strict. Hence the equality case under these premises supplies the
actual parallel three-chain L<_xC<_xR and routes to the existing
physical4+3 sharp terminal. No unrestricted equality classification
is asserted.

Consequently any remaining subcritical configuration satisfying (1)
must have at least one matched endpoint pair for which none of the
alternatives above holds. To make the remaining direction classification
explicit, for the left matched pair its center differences satisfy
\[
  2/5<x_L-x_{M0}<1,\qquad y_L-y_{M0}>31/50-1/8>0.       \tag{9}
\]
The first bounds follow from |x_L|<13/12, x_L<-31/60,
and -91/60<x_{M0}<-89/60. A unit separator toward L with
nonpositive vertical component would therefore have center projection
strictly below one, impossible for the two contained radius-1/2 disks.
Every such physical separator is upward. The reflected reasoning
applies on the right. Section4 of the endpoint-owner union further
excludes every outward nearly horizontal axis using
149/(120sqrt(2))<1. An outward nearvertical axis is covered by
alternative2 or3. Consequently the remaining endpoint pair must
have only strictly inward separating axes, with no main-owned
nearvertical separator and no actual vertical comparison. Its
inward shoulder-owned and nearly horizontal main-owned domains remain.
Those are genuine remaining caller obligations. No coordinate cover
or finite pose enumeration was introduced here.

The note proves this extraction and its exact constants. Unrestricted
A.2 and global equality are not declared closed.
