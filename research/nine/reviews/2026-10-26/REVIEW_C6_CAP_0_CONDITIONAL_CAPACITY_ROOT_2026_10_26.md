# Root review: conditional capacity one for the entire remaining pocket 0

Date: October 26, 2026.

**Result: PASS as a conditional geometric theorem. The original-orbit
coordinate hypotheses remain unproved, and no allocation is retired.**

I independently read SIX_CYCLE_REMAINING_CAP_0_CONDITIONAL_CAPACITY_ONE.md
and checked the loaded coordinates against the accepted exact
three-parameter reconstruction. The theorem retains the entire cap,
arbitrary extra orientations and every actual transmitter slider.

The sharp contained-unit center bound gives |e|<23/16 when R<=2.
Cap containment gives y<=-H-1/2<=-1. The open inscribed radius-1/2
disk of any actual extra makes distance(e,S_i)>=1/2 a necessary
condition. This relaxes the geometric exclusion and does not move
or replace the physical extra.

From a^2+b^2<=4 and b>=6/5 one obtains a<=8/5. Since a>=3/2,
the possible center lies to the right of the left edge of S0.
Its vertical distance from S0 is less than19/80, so the disk
condition forces x>1-a+7/16>=-13/80. The radical comparison
1239>1225 is strict and correct.

For S1 I checked the own coordinates
xi=X(x-(2-a))+Y(y+H) and
zeta=Y(x-(2-a))-X(y+H). The stated coordinate hypotheses imply
2/5<=2-a<=1/2, 3/5<=Y<2/3, Y/X<8/9. Cauchy's inequality gives
zeta<1; the previously proved lower x bound and cap condition give
zeta>-1/15. The upper estimate xi<53/100 remains correct also
when x-(2-a) is negative, as the source separately explains.

If xi were nonnegative, distance(e,S1)<1/15 would contradict the
necessary disk condition. Thus xi<0, and its full distance formula
forces -xi>sqrt(221)/30>49/100. The exact positive squared reserve
is491/90000. Solving for x, with the known signs of y+H and X,
gives x<173/240. When H>=23/16 there is already no center; the
remaining sign use H<23/16 is therefore legitimate.

Every feasible extra center is consequently in one rectangle of
width53/60 and height7/16. Its squared diameter is exactly
55969/57600<1, with reserve1631/57600. Two physical unit squares
with disjoint interiors have disjoint open inscribed disks and
therefore center separation at least one. This proves the stated
entire-cap capacity bound, including independent orientations and
all circle-contact masks.

To apply it to the full remaining mixed110 outgoing-share0 orbit,
one must still prove the original inequalities R<=2, a>=3/2,
b>=6/5, H0>=1/2 and3/4<=X<=4/5. The source explicitly keeps
these as outstanding hypotheses. The seven completion allocations,
all original gate counts and the unrestricted theorem remain open.
No numerical box, root-isolation assertion, Lean compilation or CI
is a premise of this review.
