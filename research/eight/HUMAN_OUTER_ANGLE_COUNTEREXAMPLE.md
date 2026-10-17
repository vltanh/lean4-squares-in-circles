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


## Sharper obstruction at the exact search ceiling

Even the assertion that two outer-center directions must be **strictly**
more than `pi/4` apart is false below the rational eight-square ceiling
`sqrt(9789)/50`.

Put `t=pi/8`, `e=(cos t,sin t)`, `f=(-sin t,cos t)`, and
`L=cos t+sin t`. Choose two unit squares of common frame `(e,f)`
and centers

    P=(L,0),     Q=L*(cos(pi/4),sin(pi/4)).

The center directions differ by exactly `pi/4`.
The identity `2L sin(t)=sin(2t)+1-cos(2t)=1` gives

    Q-P=f.

Thus the two squares have disjoint open interiors and share a whole
side. Their farthest squared vertex norms are equal, because both center
directions make the same unsigned angle t with e; they are

    L^2+1/2+L*(cos t+sin t)
      =2*L^2+1/2
      =5/2+sqrt(2).

This is strictly less than the rational construction ceiling
`9789/2500`: the comparison is `sqrt(2)<3539/2500`, proved
by `2*2500^2=12500000<12524521=3539^2`.

Hence a **strict pi/4 exterior-center pair gap** cannot hold even
at the proved small-radius search ceiling. A seven-square circle budget
must retain the central obstacle or more refined pair-state information.
