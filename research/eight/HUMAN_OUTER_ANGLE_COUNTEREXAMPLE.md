# Exact counterexample: outer square centers need not be 45 degrees apart

Two interior-disjoint unit squares fit inside the radius-two disk, both with center norm greater than one, and with center rays separated by an angle strictly smaller than pi/4. The proof is rational arithmetic.

Put r=1327/1000; c=8319/11681; s=8200/11681. Then c^2+s^2=1, 0<s<c. Let both squares use the same orthonormal frame
e=(12/13,5/13), f=(-5/13,12/13).
Take centers P=(r,0) and Q=(r*c,r*s).

Their angular separation is arctan(s/c)<pi/4, and both centers have norm r>1. The projection of Q-P onto f exceeds the sum of the squares' half-widths:
f dot (Q-P)-1 = 103067/15185300 > 0.
Thus a line perpendicular to f strictly separates them.

For a unit square centered at p with frame (e,f), the largest squared vertex norm is |p|^2+1/2+|p dot e|+|p dot f|. At P it equals
51951077/13000000 < 4.
At Q it is strictly smaller: its support term is r*(7*c+17*s)/13, whereas the support term at P is 17*r/13, and
17-(7*c+17*s)=944/11681>0.
Their center norms are equal. Therefore every vertex of both squares lies strictly inside the radius-two circle. Convexity then contains the whole squares.

This disproves the assertion that exterior squares whose centers have norm at least one must have center-angle separation at least pi/4. It does not contradict the valid private-center-ray theorem or the weaker pi/8 angular bound. The counterexample must not be used as an eight-square packing or a counterexample to the conjectured optimum.
