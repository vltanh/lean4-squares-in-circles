# Eight-square candidate: five outer corners and a tilted two-square chain

Status: exact geometric reduction for a specified construction family; the stationary values below are numerical discovery data. This is NOT a global lower bound for arbitrary eight-square packings.

## Sources and correction to the initial picture

Friedman's table attributes the 1.97877+ construction to David W. Cantrell (March 2002): https://erich-friedman.github.io/packing/squincir/ . Decimal centers and half-edge vectors of a near-matching layout are publicly displayed at https://minmaxarena.com/en/problems/tilted-squares-in-circle/p05-n8-v2 . The equations below were reconstructed independently from those coordinates.

The layout has six squares in one orientation and two in another. It is not a rigid eight-vertex boundary ring: several squares/coordinates have slack. Do not assume uniqueness or that all eight squares touch the circle. In particular, a valid representative can have the central and top squares at heights 7/20 and 27/20, without circle contact.

## Exact parametrization

Let q be squared radius and let y be the vertical coordinate of the bottom-right corner of the right-lower square. Write c=cos(t), s=sin(t), e=(c,s), f=(-s,c). Define positive square roots

    x1 = sqrt(q-y^2),
    x2 = sqrt(q-(y+2)^2),
    x3 = x2-3,
    y3 = sqrt(q-x3^2),
    y4 = y3-2,
    x4 = -sqrt(q-y4^2).

Four outer corners are

    P1=(x1,y),       P2=(x2,y+2),
    P3=(x3,y3),      P4=(x4,y4).

Their norm squares all equal q. Their consecutive projected differences are respectively 2 vertically, 3 horizontally, and 2 vertically. Set

    h1 = c*x1+s*y-2-c,
    h2 = -s*x4+c*y4-1-s,
    P5 = h1*e+h2*f.

The remaining circle equation is

    F(q,y,t) = h1^2+h2^2-q = 0.                 (1)

The centers of the right-lower, right-upper, upper-left, left-middle, and lower-left tilted squares are respectively

    A=P1+(-1/2,1/2),  B=P2+(-1/2,-1/2),
    D=P3+(1/2,-1/2),  E=P4+(1/2,1/2),
    H=P5+(e+f)/2.

A second tilted square can be placed at G=H+e. The two remaining axis-parallel squares can be placed at

    C=(B.x-1,7/20),    T=(B.x-1,27/20).

A small nonzero displacement of G in the f direction is also possible; taking zero makes the construction simpler.

Equation (1) places a fifth corner on the circle. The two extra separation identities are

    e dot (P1-P5) = 2+c,
    f dot (P4-P5) = 1+s.

They encode the two tilted squares' longitudinal chain to A and their transverse separation from E. A/B and D/E have unit vertical center separation, while B and D are two units apart horizontally. C and T fit in the intervening column. The remaining containment/separation inequalities must still be verified; a contact diagram alone does not prove them.

## Stationary solution recovered

Solving F=F_y=F_t=0 at high precision produces

    q = 3.91553413751747532651970441708409057685792562985694532794956855
    y = -0.92065667800760613174687416238175921326112677841885877376659827
    t = 0.123637086521587971034510545083858069146303698142254164146654124
    R = 1.97877086533976321492995738414223876309061826189010616650182.

This agrees numerically with the previously quoted Cantrell radius. The equations, not these rounded decimals, should be used for an eventual exact definition. Substituting tan(t/2) turns the trigonometric part into rational functions, so an algebraic formulation is available.

Representative centers (rounded for inspection, not a certificate):

    A = ( 1.2515494337, -0.4206566780)
    B = ( 1.1584788605,  0.5793433220)
    C = ( 0.1584788605,  0.3500000000)
    T = ( 0.1584788605,  1.3500000000)
    E = (-1.4021226910, -0.0454020590)
    D = (-0.8415211395,  0.9545979410)
    G = ( 0.2459535367, -0.9065755718)
    H = (-0.7464131298, -1.0298979102).

A through F in a generic eight-variable array should not be confused with the F function above. The names in this note are A,B,C,T,E,D,G,H.

## What this proves and what it does not

The equations exactly explain the near-record candidate and reduce its contact construction to three variables. Numerical stationarity does not establish existence of an exactly isolated solution, local optimality, or global optimality. Required next steps are a verified construction, an exact fixed-family lower-bound/certificate argument, and a genuinely global structural reduction covering other orientations/contact patterns.
