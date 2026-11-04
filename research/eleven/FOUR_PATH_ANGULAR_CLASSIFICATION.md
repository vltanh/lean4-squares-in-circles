# Four-body transmitting stress paths have a discrete radius

This note concerns an extracted **full-angle** stationary stress, with the
definitions and hypotheses of `SPARSE_MINIMIZER_STRESS.md`. Suppose its
positive pair graph is the path `0-1-2-3`, and only its two endpoints have
positive circle weights. The two internal vertices are unloaded. Then,
under `q<=49013/10000`, necessarily

    q = 17/4.

An independently proved lower bound `q>17/4` for eleven squares therefore
excludes this entire stress class. This note does not supply that auxiliary
lower bound, assume the three radial core squares are the same as a stress
core, or classify paths whose internal vertices carry circle weights.

## One common transmission normal

Balance at each unloaded degree-two vertex implies that, orienting the path
from 0 to 3, all three selected separator normals are one unit vector n and
all three aggregate pair weights equal the same beta>0. Let

    h_i = max_(w a centered corner of square i) n dot w.

Each edge is tight and gives `n dot (p_(i+1)-p_i)=h_i+h_(i+1)`.
Every selected normal is a signed own axis of one of its two bodies.

Call a frame parallel when one of its axes is parallel to n. Every edge has
at least one parallel endpoint. Thus two adjacent vertices cannot both have
nonparallel frames. At a nonparallel body the support corner in direction n
is unique, its supporting width is smooth in its angle, and that body owns
neither incident separator. The derivative is the usual derivative of its
width; no support-vertex cusp or contact-point interpretation is used there.

## Every nonparallel frame is at 45 degrees

For an unloaded internal nonparallel body, angular stationarity reads

    2 beta * d(h_i)/d(theta_i) = 0.

In any open quadrant of its frame coordinates, the support width is
`(|cos(theta)|+|sin(theta)|)/2`. Its only stationary nonparallel orientation
is the diagonal orientation, making an angle of 45 degrees with n.

Consider a nonparallel endpoint, say the left endpoint 0. Its total circle
weight A is positive, and its center balance is

    2 sum_w alpha_w (p+w) = -beta*n.                 (1)

If only one farthest corner has positive weight, call it w. Its absolute
position is `p+w=-sqrt(q)*n`. The farthest-corner condition in each square
coordinate forces w to be the corner opposite the support corner in
direction n: for a coordinate sign epsilon, it says
`epsilon*(p+w)_coordinate>=1/2`. Therefore w is the negative of that
support corner. Since `beta=2A sqrt(q)`, its corner angular derivative
is `beta*h_i'`, while its sole pair contributes another `beta*h_i'`.
Angular stationarity gives `2 beta*h_i'=0`, again the 45-degree frame.

The remaining possibility is positive weight on two farthest corners.
The center must lie on a frame axis; write `p=-rho*u`, with rho>1/2, after
choosing the axis direction. The inequality rho>1/2 follows already from
the auxiliary bound `q>1469/400`, since
`q=(rho+1/2)^2+1/4`. Choose the sign of the perpendicular frame axis so that
`n=c*u+s*v` with c,s>0. Reflecting the angular coordinate if necessary
changes both derivatives by the same sign and does not change stationarity.
The two farthest corners are `-u/2+v/2` and `-u/2-v/2`. If their weight
difference is delta, the v coordinate of (1) gives `delta=-beta*s`.
Their combined angular derivative is `rho*delta=-beta*rho*s`.
The pair-width derivative is `beta*(s-c)/2`. Their sum equals

    beta*((1/2-rho)*s-c/2) < 0,

contradicting angular stationarity. If the center is instead on the other
axis, the same computation gives
`beta*((rho-1/2)*c+s/2)>0`, also impossible. Thus no nonparallel endpoint
can use two positively loaded farthest corners. The right endpoint follows
by reversing n and the path.

Every frame is therefore parallel (P) or diagonal (D), and adjacent D
frames are forbidden. The half-widths are respectively 1/2 and sqrt(2)/2.

## Exact endpoint projections

At a parallel endpoint, (1) forces the transverse center coordinate to be
zero: a nonzero transverse coordinate makes every farthest corner have a
strictly same-sign transverse absolute coordinate. Its outward support
projection is therefore `sqrt(q-1/4)` in magnitude. At a diagonal endpoint,
the unique loaded farthest corner is on the ray through n, so its outward
support projection is `sqrt(q)` in magnitude.

Write `L=2 sum_i h_i`, the total projected width of the four bodies. Summing
the three tight separator equalities gives these exact alternatives:

| Endpoint types | Radius equation |
| --- | --- |
| P,P | `2 sqrt(q-1/4)=L` |
| P,D or D,P | `sqrt(q-1/4)+sqrt(q)=L` |
| D,D | `2 sqrt(q)=L` |

If all frames are P, then L=4 and `q=17/4`.

If a D frame occurs and the endpoints are P,P, then `L>=3+sqrt(2)` and
`q>=3+3sqrt(2)/2>51/10>U`. If the endpoints are P,D, then
`L>=3+sqrt(2)` and

    q = (L/2+1/(8L))^2
      > L^2/4+1/8
      >= 23/8+3sqrt(2)/2
      > 199/40 > U.

Here `sqrt(2)>7/5` supplies the rational strict comparison. Finally, D,D
endpoints require at least two D frames, hence `L>=2+2sqrt(2)` and
`q>=3+2sqrt(2)>29/5>U`. All nonparallel alternatives are excluded.

The conclusion is a finite exact terminal classification for this specified
stress path. Physical completion by the other seven squares is still
required, and its impossibility follows only after adding a valid
eleven-square lower bound strictly greater than 17/4.
