# Complete normalized (1,4,0) actual-cone-four occupancy closure

Complete hand proof, independently reviewed, 5 November 2026. This proof
retains all nine original unit squares and all their physical pair
constraints. It uses neither the central singleton-floor certificate nor
any other interval exclusion table.

Put Q=1105/256, r=sqrt(Q), rho=91/60, l=29/60, u=13/12.

## 1. Fixed whole-domain statement

Consider nine independently oriented original unit squares in the
centered closed Q-disk with pairwise disjoint open interiors. Four of
them form an actual horizontal projection chain M0<_x M1<_x M2<_x M3,
and the same consecutive centers also satisfy the positive horizontal
cone comparisons. Assume their adjusted endpoint span satisfies

    D=x3-x0-h0-h3>2.                                  (1)

The other five originals have normalized column count (L,C,R)=(1,4,0),
using x<=-l, |x|<l, x>=l. There is also a designated disjoint outsider
horizontal cone three-chain L<_c P<_c R. Its letters are fixed original
squares, and its links need not be actual projection separations.

These hypotheses are impossible. In particular, they exclude this
normalized count in any strict subcritical nine-square counterexample:
common center expansion preserves the actual and cone chains, gives
closed-disjoint units at Q, and makes the endpoint span strictly greater
than two. The count in this theorem refers to those normalized positions.
Horizontal reflection treats the complete count (0,4,1).

The only additional hand inputs used below are:

* The actual-four localization, inset and physical center-clearance
  results retained in the active source collection.
* The high central-endpoint lemma in [ACTUAL_FOUR_230.md](ACTUAL_FOUR_230.md), Sections 1--4.
* The upper-column separation lemma in [FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md), Section 2.1:
  two originals with center heights at least 3/5 have horizontal center
  gap greater than l.
* The upper central pair replacement theorem in
  [UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md](sources/UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md):
  if two upper central originals have horizontal gap at most 1/2,
  the higher one has whole floor greater than 2807/24000>1/10.
* The two-low-main theorem in [ACTUAL_FOUR_CENTRAL_BOUNDS.md](ACTUAL_FOUR_CENTRAL_BOUNDS.md), Section 1:
  y1<=-3/5 and y2<=-23/60 exclude every original central below both,
  with the reflected variants.
* The original central-strip pair cap in
  [TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md](sources/TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md): two originals
  centered in [-l,l] cannot both lie wholly above 9/20, or wholly below
  -9/20 after reflection.
* The completed widened five-square cap in [FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md).

Every invocation retains its original physical squares and frames.

## 2. Placement and a common vertical choice

Every outsider lies in |x|<u. Every selected cone edge has horizontal
gap at least the sum of its two original inset halfwidths, hence at least
1/sqrt(2)>7/10. The selected middle P is central, and the triple cannot
be wholly central because its span is at least sqrt(2)>2l. Since there
is no right-side outsider, its selected R is central and its selected L
is the unique original left-side outsider. As in the direct horizontal
calculation in [ACTUAL_FOUR_230.md](ACTUAL_FOUR_230.md),

    -23/60<x_P<-13/60<0,
    19/60<x_R<l,
    -u<x_L<-11/12.                                  (2)

Every central outsider is above both inner mains or below both. Indeed,
the correlated inset bounds x1+g1>-1/60 and x2-g2<1/60 make its
horizontal residual relative to each inset less than 1/2. Its half-unit
disk then gives vertical gap greater than g_i>15/31 from each main.
Its own-half gap is greater than 59/60. A center between the main
heights would therefore require

    |y2-y1|>59/60+15/31>31/30,

contradicting the main cone comparison.

Choose the common vertical reflection putting P above both mains.
In fact its vertical gaps from both mains exceed 3/4: its horizontal
gaps are below 9/10 and g_i>12/25, so its contained disk gives
(12+sqrt(46))/25>3/4.

The selected L must be above M1. Otherwise its own-half clearance would
give y_P-y_L>3/4+97/100>22/15, contrary to the cone bound
x_P-x_L<22/15. The selected R must be above M2: the contrary would
give y_P-y_R>3/4+59/60>2l while x_R-x_P<2l. The general central
routing just proved therefore places R above both mains as well.

The same physical endpoint argument used in [ACTUAL_FOUR_230.md](ACTUAL_FOUR_230.md)
gives the high original shoulder

    y_L>27/40>3/5.                                  (3)

For completeness L is above M1, so y_L>-139/120+97/100=-113/600.
Its horizontal center gap from M0 is less than 3/5. Their disjoint
half-unit disks give |y_L-y0|>4/5. The lower alternative would put
y_L<1/8-4/5=-27/40, a contradiction; the upper alternative gives (3).

The four original central squares include the upper P,R. The other two
are each upper or lower in the exhaustive routing sense above. Thus
there are exactly three possible vertical counts: four upper; three
upper and one lower; or two upper and two lower.

## 3. A high selected middle already supplies the complete terminal

If y_P>3/5, the central-endpoint hand lemma gives y_R>3/5. Its Section 3
also proves the stronger intermediate conclusion

    y_P>y_L>17/20.

This intermediate conclusion is independent of the assumed low-R
contradiction used later in that lemma. Since h_P<=1/sqrt(2)<3/4,

    y_P-h_P>17/20-3/4=1/10.

Consequently the three distinct originals L,P,R and the original outer
main endpoints satisfy the five-square cap. It gives D<=2, contrary to
(1). Every surviving configuration in the rest of this proof therefore
satisfies the single closed condition

    y_P<=3/5.                                       (4)

No separate bad-floor or selected-link predicate is imposed.

## 4. Four upper central originals

Every upper central center has

    -7/40<y<rho,

by y_i>-139/120 and its own-half central clearance 59/60. There cannot
be three such originals in one closed horizontal half of the central
strip. Order their centers by height. Their two adjacent vertical gaps
are each at least sqrt(1-l^2), while the total available height span is
less than 203/120. This is impossible because

    1-l^2-(203/240)^2=587/11520>0.

Four upper central originals must therefore have exactly two strictly
negative and two strictly positive x-coordinates. A zero coordinate would
belong to both closed halves and would force three in one of them.

Each same-half pair has horizontal gap less than l<1/2. Apply the hand
replacement theorem to each pair. Let U be the higher negative original
and B the higher positive original. Both have whole floors greater than
2807/24000, so B has center height greater than 3/5. The three distinct
originals L,U,B satisfy the five-square cap, contradicting (1).

This closes the entire four-upper alternative, including every possible
vertical order of the two additional originals.

## 5. Three upper and one lower central original

We first record the closed-height version of the consequence of the
two-low-main theorem: in the presence of an original central G below
both mains, at most one upper central original can have center height
at most 3/5.

If two such units A,B are in a common closed horizontal half, their
horizontal gap is at most l and their heights belong to (-7/40,3/5].
Their squared center distance is then strictly less than

    l^2+(31/40)^2=12013/14400<1,

contradicting their original half-unit disks.

Otherwise their horizontal signs are opposite. Their own-half physical
clearances imply y1<-23/60 and y2<-23/60. The two-low-main theorem,
applied with the retained original G, forces both y1>-3/5 and y2>-3/5.
Applying the own-half clearances again puts

    23/60<y_A,y_B<=3/5.

Their horizontal gap is at most 29/30 and their vertical gap is less
than 13/60. Their squared center distance is therefore less than

    (29/30)^2+(13/60)^2=3533/3600<1.

This is another incircle contradiction. A center on x=0 was already
covered by the common-closed-half alternative. The closed boundary
y=3/5 is thus included in the consequence.

Now apply this fact to the present three upper originals. By (4), P is
the unique possible one with height at most 3/5. The other two originals,
including selected R, have heights greater than 3/5. Since two high
central centers cannot lie in the same closed horizontal half by the
upper-column theorem, R is positive and the third upper original U is
strictly negative.

P and U have horizontal gap less than l<1/2, and U is the higher one.
The replacement theorem makes the whole floor of this original U
greater than 2807/24000. Thus L,U,R satisfy the five-square cap and
contradict (1). This closes the complete three-upper/one-lower alternative.

## 6. Two upper and two lower central originals

The upper originals are precisely the selected P,R. Let G,H be the
two distinct original central squares below both mains. We use (4) and
P's actual negative central position from (2).

Its own-half clearance from M1 gives

    y1<y_P-59/60<=-23/60.                            (5)

For the other main, the correlated right inset bound and (2) give

    (x2-x_P)-g2<1/60+23/60=2/5.

P is above M2. Its original half-unit disk therefore forces

    y_P-y2>g2+sqrt(1/4-(2/5)^2)=g2+3/10,
    y2<3/10-15/31=-57/310.                          (6)

Every lower central original V with x_V<=0 has own-half clearance
from M1, and hence

    y_V<y1-59/60<-41/30.

Every lower central V with x_V>=0 has own-half clearance from M2,
and hence

    y_V<y2-59/60<-2171/1860.

At x_V=0 both statements are valid. Since every physical unit has
h_V<=1/sqrt(2)<17/24, these give respectively

    y_V+h_V<-41/30+17/24=-79/120<-9/20,
    y_V+h_V<-2171/1860+17/24=-569/1240<-9/20.

Thus both unchanged originals G,H lie wholly below -9/20 and have
central centers. The hand central-strip pair cap, reflected vertically,
excludes them. This closes the entire two-upper/two-lower alternative.

Notice that no general singleton-floor theorem is used: the selected
middle's specific horizontal placement and the surviving center-height
condition (4) provide the two main-height bounds (5)--(6) directly.

## 7. Complete coverage and scope

The common vertical choice makes selected P,R upper. The other two
central originals are each upper or lower, and Sections 4--6 cover all
three resulting counts. Section 3 first disposes of every y_P>3/5;
the complement y_P<=3/5 is retained throughout the remaining proof.
All central sign-zero faces, equality at the center-height threshold,
physical frame orientations, original separator owners and original
contacts remain included.

The only result involving a lower central beyond basic physical
clearance is the independently hand-proved two-low-main theorem in the
three-upper case. No central singleton-floor certificate or half-width
numerical theorem has been imported. The four-upper and two-upper
alternatives are direct physical callers of already hand-proved caps.

Therefore no normalized original-nine configuration in the complete
stated (1,4,0) domain exists. Reflection closes (0,4,1). This is a
whole occupancy theorem under the actual-and-cone main chain and the
designated outsider cone triple. It does not assert the unrestricted
nine-square lower bound or resolve the remaining occupancies.
