# Radial/radial side transmitters are transversely free of all physical boundary core bodies

**Status: complete hand geometric theorem, frozen for independent review.**
This is a theorem about the original physical bodies and their complete
touching relations, including zero-weight contacts. It does not assert that
a transmitter is free of other circle-clear bodies.

## 1. Original setting and conclusion

Work in
\[
             \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1.1}
\]
Use the existing compatible selected physical certificate whose entire
positive component is a simple cycle with at least three loaded bodies.
All true degrees, original circle masks, individual circle-weight endpoints,
actual shared-side means, other components, and additional physical squares
remain.

Let \(X-U-Y\) be three consecutive vertices of this original cycle.
The body \(U\) is an unloaded true-degree-two side-normal transmitter;
\(X,Y\) are loaded and each has two physical circle corners. Their two
nonnegative individual circle weights may include a zero weight. The
word *core* below means a body of this original simple cycle, and
*boundary* means physical circle contact, independently of loading.

**Theorem.** In the actual channel frame, let \(N\) be its outward
unit normal and \(g\) its directed force normal from \(X\) toward \(Y\).
Then:

1. \(U\) has strict physical clearance from the containing circle.
2. Every actual contact of \(U\) with any physical boundary core body
   has a common separating normal parallel to \(g\).
3. Consequently every sufficiently small translation of \(U\) in
   either direction \(+N\) or \(-N\) preserves its containment and
   its nonoverlap with **all** physical boundary core bodies.

This applies simultaneously to any finite collection of such
radial/radial side transmitters: arbitrary sufficiently small transverse
translations preserve every pair involving one of those transmitters and
a fixed physical boundary core body, as well as all their individual
circle constraints. Contacts among moving transmitters, with other
circle-clear core bodies, or with additional physical squares must still
be checked.

The theorem does not require the remaining cycle channels to be short,
side-normal, or radial. It uses no secondary minimum. At an original
\((R,\Phi)\) minimum, its combination with the existing inward-blocker
routing theorem is stated in Section 6.

## 2. Exact original radial/radial channel

Put
\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \phi=\arctan\frac1{2d}.
\tag{2.1}
\]
The complete radial support cover and exact radial/radial channel
calculation in [R], Sections 1, 7 and 8, give, without changing either
actual application,
\[
 P_X=(-\tfrac12,d),\qquad P_Y=(\tfrac12,d),\qquad
 g=(1,0),\quad N=(0,1).
\tag{2.2}
\]
Both applications are strict inner vertices of their radial endpoints
and lie in the relative interiors of the respective opposite sides
of \(U\). Thus the actual transmitter is
\[
 U=[-\tfrac12,\tfrac12]\times[b-\tfrac12,b+\tfrac12],
 \qquad d-\tfrac12<b<d+\tfrac12.
\tag{2.3}
\]
In particular its transverse mean has not been centered or replaced.

The actual endpoint center directions lie at angles
\[
 \arg c_X=\arg N+2\phi,\qquad
 \arg c_Y=\arg N-2\phi.
\tag{2.4}
\]
The physical channel-order theorem [F], Sections 3 and 5, identifies
the outward arc between them as the actual consecutive loaded-center
arc across \(X-U-Y\). Its length is \(4\phi<\pi\).

For clarity, the exact estimates needed below are recorded here:
\[
 \frac9{10}<d<\frac{61}{60},\qquad
 R-\sqrt2>\frac{14}{25},\qquad
 \frac{\pi}{7}<\phi<\frac{\pi}{6}.
\tag{2.5}
\]
The first two are also proved in [R]. At the lower radius endpoint,
\[
 R^2-\tfrac14\ge\frac{5841}{1600}>
 \left(\frac{19}{10}\right)^2.
\]
At the upper endpoint,
\[
 R^2-\tfrac14\le\frac{1041}{256}<
 \left(\frac{121}{60}\right)^2,
\]
whose cross-multiplied strict margin is \(496\).
Moreover \(\sqrt2<283/200\), since \(80089>80000\), so
\(79/40-\sqrt2>14/25\).

Here is a self-contained exact proof of the angle estimate, also
used in the already accepted all-radial center-gap theorem.
The upper bound follows from \(d>9/10>\sqrt3/2\).
For the lower, \(d^2<(61/60)^2<25/24\), so
\[
 \tan\phi>\frac{\sqrt6}{5}.
\]
Set \(\theta=\arctan(\sqrt6/5)\in(0,\pi/4)\). The sign of
\(\sin7\theta\) is the sign of
\[
 7-35\frac6{25}+21\frac{36}{625}-\frac{216}{15625}
                  =-\frac{3191}{15625}<0.
\]
Since \(0<7\theta<7\pi/4<2\pi\), this gives \(7\theta>\pi\).
Therefore \(\phi>\theta>\pi/7\), proving (2.5).

Equation (2.3) now proves the strict circle clearance directly:
\(b>d-\tfrac12>0\), and the maximum squared corner norm of \(U\) is
\[
 \frac14+(b+\tfrac12)^2
       <\frac14+(d+1)^2=R^2.
\tag{2.6}
\]
This includes every physical circle mask of the original transmitter:
the conclusion is that such a transmitter actually has no circle corner.

## 3. All physical boundary core centers lie in the inward open half-plane

We need the physical order of **all** boundary core bodies, including
ones with zero total circle multiplier. This does not follow by merely
listing the loaded bodies, so we give the precise order argument.

By [P], Section 6, the selected embedded simple cycle has a disjoint
exterior spoke from every physical boundary core center to one of its
actual circle corners, whether or not that corner carries positive
weight. The annular-order lemma in [F], Section 3, therefore identifies
the order of these chosen corners on the containing circle with their
vertex order on the embedded cycle.

One can transfer this corner order to center directions without any
assumption on the circle weights. Put \(\rho=5/4\). For every physical
boundary square \(W\), its center \(c\) satisfies
\[
 |c|\ge R-\frac1{\sqrt2}>\frac54.
\tag{3.1}
\]
Indeed \(1/\sqrt2<29/40\). The centered-arc theorem [A] puts
\(\rho c/|c|\) in \(W^\circ\). Join that point radially to \(c\),
then join \(c\) to the chosen circle corner \(z\). These are disjoint
crosscuts of the annulus \(\rho\le |p|\le R\), one for each boundary
square: their interiors lie in disjoint square interiors.

To check that the second segment stays strictly outside the inner
circle, write the square in its own orthonormal frame. A farthest
corner has signs agreeing with the corresponding center coordinates
(with either sign permitted at a zero coordinate), so
\[
 c\cdot(z-c)=\frac12\bigl(|c\cdot u|+|c\cdot v|\bigr)>0.
\]
Thus \(|c+t(z-c)|\) strictly increases for \(t\ge0\), and is already
larger than \(\rho\) at \(t=0\). The radial first segment is also
in the annulus. The corner endpoints are distinct, by physical
circle-point unshareability. Annular order for these disjoint
crosscuts proves that the chosen circle-corner order is exactly
the center-direction order.

Combining the two annular-order statements gives the original
cycle order for **all** physical boundary core centers. Since the
path \(X-U-Y\) has no other vertex and \(U\) is circle-clear by
(2.6), no other physical boundary core center direction lies on the
outward arc of length \(4\phi\) in (2.4).

Now let \(W\ne X,Y\) be any physical boundary core body.
The centered-arc pair consequence [A] gives minor center separation
strictly greater than \(2\pi/9\) from each of \(X,Y\).
Represent directions relative to \(N\), with the outward endpoint
directions at \(-2\phi\) and \(2\phi\). The direction of \(c_W\)
belongs to the complementary arc, and the two separation bounds give
\[
 2\phi+\frac{2\pi}{9}
   <\arg_N c_W
   <2\pi-2\phi-\frac{2\pi}{9}.
\tag{3.2}
\]
Each displayed oriented gap is at least its corresponding minor gap,
so this inference does not assume that the two complementary subarcs
are shorter than \(\pi\).

Finally,
\[
 2\phi+\frac{2\pi}{9}>
 \frac{2\pi}{7}+\frac{2\pi}{9}
 =\frac{32\pi}{63}>\frac{\pi}{2}.
\]
Consequently
\[
                       \boxed{c_W\cdot N<0.}
\tag{3.3}
\]
The same proof applies to any other physical boundary square whose
center direction is independently known to lie outside the outward
radial/radial endpoint arc. No such order is asserted for unrestricted
additional squares here.

## 4. Exact exclusion of top and bottom contacts

Fix a body \(W\) as in Section 3. Every point \(p\in W\) is within
\(1/\sqrt2\) of \(c_W\). Therefore (3.3) gives
\[
                 p\cdot N<\frac1{\sqrt2}.
\tag{4.1}
\]
By (2.3), every point on the top face of \(U\) has height
\[
 b+\tfrac12>d>\frac9{10}>\frac1{\sqrt2}.
\]
Thus \(W\) cannot meet the top face, including its endpoints.

For the bottom face split at the exact value \(b=2/3\).

**If \(b\ge2/3\), there is no contact anywhere.** By (3.1),
(3.3), and \(b>0\),
\[
 \begin{split}
 |c_W-bN|^2
 &=|c_W|^2+b^2-2b(c_W\cdot N)\\
 &>\frac{25}{16}+\frac49
   =\frac{289}{144}>2.
 \end{split}
\tag{4.2}
\]
Touching unit squares have center distance at most \(\sqrt2\):
pass through an actual common point and use each circumradius
\(1/\sqrt2\). Equation (4.2) therefore excludes all contact.

**If \(b<2/3\), no bottom-face point belongs to a boundary square.**
By (2.3) and \(d>9/10\),
\[
 -\frac1{10}<b-\frac12<\frac16.
\]
A point on the whole bottom face has the form
\(p=(x,b-\tfrac12)\), \(|x|\le1/2\), and hence
\[
 |p|^2<\frac14+\frac1{36}=\frac5{18}
                         <\left(\frac{14}{25}\right)^2.
\tag{4.3}
\]
The final cross-multiplied comparison is \(3125<3528\).
On the other hand, if \(z\) is any actual circle corner of \(W\),
then every \(p\in W\) satisfies
\[
 |p|\ge |z|-|z-p|\ge R-\sqrt2>\frac{14}{25}.
\tag{4.4}
\]
This excludes the entire bottom face, including both corners.
The proof uses physical boundary contact only, not a positive weight.

In either range, any remaining intersection \(U\cap W\) must lie
in the relative interior of a vertical side of \(U\). At such a
contact, the supporting line of that side is a common separating
line for the two convex squares with disjoint interiors. Its normal
is parallel to \(g\). Translation of \(U\) by any multiple of \(N\)
leaves this separating inequality unchanged.

The two original endpoints \(X,Y\), omitted from (3.3), already
have precisely these horizontal common separators by (2.2):
\(X\subset\{x\le-1/2\}\), \(Y\subset\{x\ge1/2\}\).
Thus every actual boundary core contact, including all zero-weight
ones, has the stated separator.

## 5. Bilateral local motion and simultaneous use

There are finitely many physical bodies. Every boundary core body
not touching \(U\) has positive distance from \(U\), so its
nonoverlap survives all sufficiently small translations in either
direction. Every actual boundary core contact has just been supplied
with an unchanged horizontal separator. Strict circle clearance (2.6)
also survives both signs of a sufficiently small translation.
This proves all three assertions of the theorem.

For several radial/radial side transmitters, apply the same argument
to each original channel frame. Fix every boundary core body.
Choose the translations uniformly small using the finitely many
strict clearances. Then all circle constraints and all moving/fixed
boundary-core pairs remain feasible simultaneously. This conclusion
allows different signs and rates on different transmitters.

It supplies no automatic feasibility at a contact between two moving
bodies or between a moving transmitter and a fixed circle-clear body.
Those constraints remain the original physical constraints, with
their complete sets of common separators. In particular, a
nonconsecutive core transmitter can genuinely block another one's
individual inward motion. The theorem does not charge those blockers
as distinct or remove them from a collective motion.

## 6. Canonical inward-blocker consequence

At an original \((R,\Phi)\) minimum, [B] applies to the present
radial/radial side channel, since either radial endpoint suffices for
its hypotheses. It produces an additional actual inward blocker.
An extra-body blocker is central in the original physical pocket
decomposition. The other alternative is a nonconsecutive core body.

The present theorem removes **every physically boundary core body**
from that latter alternative. Therefore every actual inward blocker
of this radial/radial side transmitter is either

- a nonconsecutive, physically circle-clear, unloaded true-degree-two
  core body; or
- an actual central additional square.

The physical zero-weight boundary masks have been excluded
geometrically, rather than silently treated as clear transmitters.
For a no-long simple cycle on at most seven core bodies, the existing
central-capacity theorem used in [B] bounds the total central
completion by one. The same possible central square may touch several
transmitters, and actual circle-clear transmitters may block each other.
Neither alternative is discarded by this result.

The theorem is a simultaneous geometric restriction on an entire
original family. It does not close the remaining mixed short C7
completion cases, change a checked flag, prove the unrestricted
nine-square bound, or transfer a canonical motion to every
equal-radius packing.

## 7. Frozen direct inputs

The displayed arguments are hand geometry and exact arithmetic.
These are the operative source pins; [B] is needed only for Section 6.

| Label | Complete source | SHA-256 |
| --- | --- | --- |
| [R] | RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md | 2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e |
| [F] | SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md | 5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635 |
| [P] | PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| [A] | CENTERED_INNER_ARC.md | fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5 |
| [B] | RADIAL_SIDE_TRANSMITTER_INWARD_BLOCKERS_ARE_CENTRAL_OR_NONCONSECUTIVE_CORE_BODIES_2026_10_30.md | 017f05bfc067cb2dff2cfb10d8a16bcb2236c78cfa1eb6a5f06cfdc2badf729e |

