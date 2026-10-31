# Root review: empty radial-incident cap from an actual adjacent circle vertex

Date: October 26, 2026.

**Result: PASS for the full local theorem, its two-corner equality
case and its stated conditional one-radial allocation consequence.**

I independently read SIX_CYCLE_RADIAL_ADJACENT_CIRCLE_CORNER_CAP_EMPTY.md
and checked its actual radial port, cap-routing, unit-square support
threshold and near-corner prerequisites against their original sources.

## 1. The original channel and extra contact feature are preserved

The real reserve-one transmitter fixes P=(d,1/2), g=(-c,s), Q=P+g.
The outward cap normal N=(s,c) has height h=ds+c/2. The condition
z=Q+v with v an actual unit side is an explicit additional feature;
it does not move a shared mean or turn an opposite corner into an
adjacent one. Every actual mean endpoint already satisfying it is
included. The radial corner weights are unrestricted.

## 2. A single exact scalar identity proves the strict case

I re-expanded |Q|^2 and obtained precisely
R^2-2d(1+c)+s. The circle equality therefore gives

\[
 z\cdot v=d(1+c)+(1-s)/2>0.
\]

At a physically unique circle corner, the other actual adjacent
vertex is strictly inside the circle. Its inward side direction w
has z dot w>1/2, so perpendicularity gives z dot v<sqrt(R^2-1/4)=d+1.
The resulting inequality 2dc<1+s is exactly equivalent to
2d(1-s)<c, using c>0 and (1+s)(1-s)=c^2. Thus h>d on the
entire domain. There is no numerical endpoint or sign packet.

The cited pocket-routing theorem contains every entire exterior
unit in the actual cap of height h. The exact contained-unit support
threshold is d. Their combination therefore excludes the complete
pocket for arbitrary extra-square orientations and physical masks.

## 3. The physical two-corner equality is not discarded

With a second actual circle corner the same argument gives h>=d.
If equality holds, both original applications have squared norm
d^2+1/4, lie on the line N dot x=d, and differ by the unit tangent g.
Their tangential coordinates must therefore be -1/2 and 1/2.
The cap threshold's unique equality square has their exact segment
as its inner side.

The complete radial support cover places P strictly inside the
original transmitter side. The unchanged transmitter equations place
Q at the same strict transverse coordinate on its opposite side.
Their midpoint is therefore in the transmitter's open interior.
An open neighborhood across the cap line intersects the equality
square's interior, which contradicts physical nonoverlap. This
argument works for every original slider and does not require a
positive multiplier at either circle corner.

## 4. Exact whole-subfamily consequence

If both radial-incident unique applications are adjacent vertices,
both corresponding exterior pockets are empty. They also satisfy
the previously reviewed near-corner premise. In the retained
strictly obtuse radial branch, the complete central free union then
has capacity at most one. The right-turn branch keeps its separate
accepted classification and exclusion.

Consequently at least two of the three actual extras must be in the
remaining unique-to-unique exterior pocket. The source correctly
does not claim a capacity bound for that pocket or close the full
one-radial original gate. Opposite vertices and non-endpoint shared
means keep their original obligations. All nine squares, true
forces, means, masks and individual zero-weight endpoints remain.
No Lean compilation, CI or numerical proof premise was used.
