# Independent review of the unit-height aligned endpoint blocker

November 4, 2026. **Accepted as a local physical theorem and equality terminal.**
This review does not close an original cell or a mask. The previously accepted
`1/8` blocker and all of its sources remain unchanged.

The reviewed hand proof is
`a_family/other_masks/unit_height_blocker_packet/UNIT_HEIGHT_ALIGNED_ENDPOINT_BLOCKER_HAND_PROOF.md`,
SHA256 `376fdc879e70e9ed200ac1a56bdacd822e56bd2c440cb76ac41b107a2eba86d3`.
Its exact companion has SHA256
`f5ee0eef2b5a29c59007e4088e3fd059cd37cd45d1238e12f90bbd461f833da1`.
The separate `review_unit_height_blocker.py` imports neither that companion nor
a numerical solver. Its rational identities and polygon projection controls
supplement the continuous geometric argument below.

## Physical statement and the occupied strip

The statement concerns actual aligned unit squares at
\(D=(1,0)\), \(X=(0,v)\), and \(G=(1/2,-1)\), with the entire closed
interval \(0\leq v\leq1\). The hypothetical fourth original square has
center \((x,y)\), folded frame \(a\geq b\geq0\), \(a^2+b^2=1\),
halfwidth \(h=(a+b)/2\), and \(j=(a-b)/2\). The hypotheses preserve the
original cone \(d=1-x\geq|y|\) and strictly weak comparison
\(d<h+1/2\). No center disk condition replaces physical nonoverlap.

Incircle separation and the cone give \(d\geq1/\sqrt2\), while strict
weakness gives \(x>1/2-h>-1/2\). The strip
\((1/2,1)\times(-3/2,1/2)\) lies in the union of the closed aligned
squares D and G. Its horizontal seam is handled correctly: any closed point
of C inside this open strip has nearby interior points of C still in the
strip, and some are off the seam. Such a point lies in the interior of D or
G. Consequently C cannot even have a boundary point in the open strip.

The boundary version at horizontal coordinate 1 is also valid. A strict
segment point from a rightmost C vertex toward its center enters horizontal
coordinates below 1 because \(x<1\), retains both strict vertical bounds,
and is in the interior of C. A further sufficiently small perturbation avoids
the seam. This deals explicitly with the diagonal-frame contact case.

## Exhaustive continuous cases

For \(x\leq0\), both opposite top and bottom vertices of C lie strictly
inside X's horizontal strip. The lower horizontal margin follows from
\(x-j+1/2=(x+h-1/2)+(1-a)>0\). The upper margin can be zero only at
\(x=0,j=h=1/2\), which contradicts the same strict weak inequality.
The open segment joining these opposite vertices lies inside C. Thus its
vertical interval cannot overlap the open vertical interval of X. This
forces either \(y+h\leq v-1/2\) or \(y-h\geq v+1/2\).
The cone and strict weakness exclude the second alternative strictly, even
at \(v=0\). The first implies \(y+h\leq1/2\), retaining \(v=1\).

Here \(b>0\), since \(b=0\) and strict weakness would force \(x>0\).
Either chirality's actual rightmost vertex therefore satisfies
\(1/2<x+h<1\) and
\(-3/2<y\pm j<1/2\). The upper vertical bound is strict by \(b>0\);
the lower is strict by the original weak-comparison margin. This vertex is
in the occupied open strip, a contradiction. The argument also treats side
faces by choosing their displayed endpoints.

For \(x>0,y\geq0\), C–D incircle separation yields
\(y^2-x^2\geq2x(1-x)>0\), hence \(x<y\leq1-x\). For every
\(v\in[0,1]\), convexity in v gives
\(|y-v|\leq\max(y,1-y)\leq1-x\). C–X squared center distance is
then at most \(x^2+(1-x)^2=1-2x(1-x)<1\), contradicting their
physical incircles.

For the remaining case \(x>0,y<0\), a rightmost C vertex lies in
\((1/2,1]\times(-3/2,1/2)\). Its horizontal upper bound follows from
\(h\leq1/\sqrt2\leq d\), and its strict vertical bounds follow from
the cone, \(x>0\), \(y<0\), and \(j\leq1/2\). The boundary-strip
argument above includes horizontal coordinate 1 and the horizontal seam.
These cases exhaust every permitted physical C frame and center.

## Sharpness and strictness

The displayed half-angle family is valid for the entire rational interval
\(0<t\leq2/5\), not only the sample controls. The denominators are
positive; \(a\geq7/10\), \(a>b>0\), and
\(0<\varepsilon=b^2/100\leq1/200\). The endpoint numerator reserves
are exactly \(7/25\) and \(1/25\). The continuous cone reserve satisfies
\(d-y=a-\varepsilon(1+b/a)\geq69/100>0\).

The identity \(a d+b y=1/2+h\) gives actual C-owned-axis contact with
D for C's frame \((a,-b),(b,a)\). Meanwhile
\((1/2+h)-d=b\varepsilon/a>0\), so the original horizontal comparison
is strictly weak. X–C have exact vertical separation equal to the sum of
their physical halfwidths. G–C exceed that separation by
\(1-a+\varepsilon>0\). The other three aligned pairs separate on the
coordinate axes. Thus the family is physically valid and has
\(v=1+b+\varepsilon>1\) tending to 1. The four-square control is local;
it makes no claim of fitting the full nine-square Q disk.

At \(v=1\), aligned C at \((0,0)\) is a physical contact control with
horizontal gap exactly 1. This confirms that the original strict weak CD
predicate is essential; replacing it by a closed inequality would make the
claimed blocker false.

The independent evaluator verifies thirteen rational-function identities,
two distance polynomial identities, all three uniform parameter reserves,
and 36 physical pair checks using vertices and edge-normal projection
intervals. Those finite controls test algebra and the stated boundary
examples; the continuous case proof above is the exclusion proof.

## Permitted caller attachment

Once a separately accepted row/cap equality argument aligns X,D,G, gives
\(x_D-x_X=1\), and fixes
\(G=(x_D-1/2,y_D\pm1)\), the closed hypothesis
\(|y_X-y_D|\leq1\) suffices for this blocker. Common vertical reflection
places G below D. Aligned X–G then have horizontal gap 1/2; their signed
vertical gap is \(v+1\in[0,2]\), so physical nonoverlap forces
\(v+1\geq1\), hence \(v\geq0\). All endpoint faces are retained.

The new lemma does not supply the preceding row inequality, cap equality,
or global routing of the nine originals. Those hypotheses must be checked
in each use. It requires neither actual BC, a large CD height gap, nor a
preselected G side, but it does require the actual C→D cone and strict CD
weakness. No original-cell or mask closure is credited here. No Lean, Lake,
or CI was run.
