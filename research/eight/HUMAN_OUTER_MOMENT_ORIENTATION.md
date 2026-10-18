# Every outer contact has a uniformly positive circular moment

## Statement and scope

Let a packing of unit squares lie in the closed disk D_R centered at zero,
where R<=2. As in HUMAN_OUTER_CENTER_VISIBILITY.md, a square is called
outer when its center has norm at least one.

Order two touching outer squares S,T so that their common contact direction
is counterclockwise from the center direction of S and clockwise from that
of T, on the intervening arc of length less than pi. The private-ray theorem
in that note guarantees this order. Let z be any point of S intersection T,
and let n be any unit separating normal directed from S toward T. Then

    z cross n > 1/20.                                    (1)

In particular every actual outer contact, not merely a positively stressed
one, has strictly positive moment in the circular order. The assertion holds
for every available separating normal and every point of a contact segment.
It requires neither contact with the containing circle nor an assumed stress.

The consequence for physical stresses is an exact scalar flux equation on
the induced outer graph. It identifies the signed inner attachments needed
by each positively stressed outer path. It is not the sharp radius bound
for eight squares.

## 1. Bounds on the centers at a common contact

For a square with center p and orthonormal frame e,f, its largest squared
vertex norm is

    |p|^2 + |p dot e| + |p dot f| + 1/2.

Since |p dot e|+|p dot f|>=|p|, containment with R<=2 gives

    |p| <= (sqrt(15)-1)/2 < 29/20.                       (2)

The last strict comparison is sqrt(15)<39/10, verified by squaring.
Every point of a unit square is within distance 1/sqrt(2) of its center.
Thus at a common point z of two outer squares,

    |p_S-z|^2<=1/2,       |p_T-z|^2<=1/2,
    |p_S|>=1,             |p_T|>=1.                     (3)

Put r=|z|. The triangle inequality gives

    r>=1-1/sqrt(2)>2/7>0.                               (4)

For the strict rational comparison use 1/sqrt(2)<5/7, whose squared
comparison is 49<50.

Use the orthonormal coordinates u=z/r and v=Ju, with
J(x,y)=(-y,x), and write

    p_S=a_S u+b_S v,       p_T=a_T u+b_T v.

Expansion of (3) gives, for either i=S or i=T,

    2r a_i >= |p_i|^2+r^2-1/2 >= r^2+1/2,
    a_i >= r/2+1/(4r) >= 1/sqrt(2) > 7/10.             (5)

The penultimate inequality is the identity
(r-1/sqrt(2))^2>=0, divided by 2r. Together with (2), this yields

    |a_T-a_S| < 29/20-7/10 = 3/4.                       (6)

Also, since both centers are within 1/sqrt(2) of z,

    |p_T-p_S|<=sqrt(2).                                 (7)

All these bounds concern actual points and centers; no contact multiplier
has been introduced.

## 2. The separating normal points forward in angle

Here is the precise angular input from HUMAN_OUTER_CENTER_VISIBILITY.md.
Each outer square has an angular shadow of length at most pi/2 and contains
its own center direction in the relative interior of that shadow. Its shadow
omits the other outer center direction. At a common point the two shadows
meet. Consequently the contact direction is strictly between the two center
directions, on their intervening arc of length less than pi.

This same ordering holds for every point of their common contact set. In the
coordinates u,v above it implies

    b_S<0<b_T,       Delta_b:=b_T-b_S>0.                 (8)

Write n=alpha u+beta v, so alpha^2+beta^2=1. Since n separates touching
squares, the center displacement has the exact support projection

    n dot (p_T-p_S)=h_S(n)+h_T(n)>=1,                    (9)

where h_S,h_T are the centered support functions. The lower bound follows
because a unit square has half-width at least 1/2 in every unit direction.
The normal need not be a side normal of either square for (9).

If beta<=0, then (6), (8), and (9) would give

    1 <= alpha(a_T-a_S)+beta Delta_b
       <= |a_T-a_S| < 3/4,

a contradiction. Thus beta>0. Keeping the positive term in that calculation,

    beta Delta_b > 1/4.

Equation (7) gives Delta_b<=sqrt(2), hence

    beta > 1/(4sqrt(2)).                                (10)

Since z=r u, its moment is z cross n=r beta. Equations (4) and (10) now give

    z cross n > 1/(14sqrt(2)) > 1/20.                   (11)

The last comparison follows from 400>392. This proves the theorem over the
whole stated geometric domain, including R=2.

## 3. Consequence for a physical stress

Choose a physical stress as in HUMAN_CONTACT_EQUILIBRIUM.md. For each actual
outer contact oriented in circular order, let Lambda>=0 be its combined
contact multiplier. If Lambda>0, its effective contact point z is in the
common contact segment. Define its directed moment flux by

    tau=Lambda (z cross n).

For Lambda=0 define tau=0. The theorem gives

    Lambda>0  if and only if  tau>0,
    tau>Lambda/20 whenever Lambda>0.                    (12)

Thus there are no zero-moment positive edges between outer squares and no
reversed moment edges there. Averaging endpoint forces on a contact segment
cannot cancel the moment, because (1) holds throughout that segment.

Consider an outer vertex i, with predecessor and successor in circular
order. Set tau_(i-1)=0 or tau_i=0 if the corresponding outer edge is absent
or has zero stress weight. Let M_i be the sum of the moments about zero of
all forces on i from inner squares, meaning squares of center norm less
than one. Circle reactions have zero moment about zero. Therefore physical
moment balance is exactly

    tau_i-tau_(i-1)=M_i.                                (13)

The sign convention is worth checking: the predecessor exerts positive
moment +tau_(i-1) on i; i's force from its successor has moment -tau_i.
Adding the inner moments gives tau_(i-1)-tau_i+M_i=0, which is (13).

No circle-contact hypothesis is needed at vertex i. In particular (13)
continues to hold at an outer square with zero circle multiplier and at
one that is strictly inside the containing circle.

## 4. What a positively stressed outer path needs from the inner squares

Take one maximal run of positive outer edges in a path component, and name
its vertices consecutively v_1,...,v_k, k>=2. At the two ends the adjoining
outer fluxes outside the run are zero. Summing (13), or using it at the ends,
gives

    M_(v_1)=tau_1>0,
    M_(v_k)=-tau_(k-1)<0,
    sum_(j=1)^k M_(v_j)=0.                              (14)

Consequently its first vertex has at least one inner contact exerting
strictly positive moment, and its last has at least one inner contact
exerting strictly negative moment. These contacts have positive weight.
Merely having an actual inner attachment, or a positively weighted radial
attachment with zero moment, cannot supply (14).

At any internal vertex with M_i=0, the two neighboring positive fluxes
are equal. In particular a run with no internal inner moments transmits
one constant nonzero flux. If an entire outer contact cycle has M_i=0
at every vertex, all its fluxes are equal: either all are zero or every
edge has positive weight and the same positive moment flux.

The induced outer graph is a union of paths and isolated vertices, or a
full cycle, by HUMAN_OUTER_GRAPH_REDUCTION.md. Equations (12)--(14) therefore
cover all of its stressed edges. They do not identify the inner square at
one end with the inner square at the other, do not identify actual degree
with positive-stress degree, and do not rule out a vertex isolated in the
outer graph but attached to inner squares.

## 5. Remaining role in the eight-square argument

The new fact is the fixed, quantitatively separated sign at every outer
contact. One no longer needs to search over orientations of moment flow
along the outer graph. The open radius-bound problem is still to control
the inner attachments and the two long-cycle geometries quantitatively.
Equation (13) is a necessary equilibrium relation, not the five projected
inequalities of the sharp conditional theorem. No unrestricted equality
R8=Rhat is inferred here.
