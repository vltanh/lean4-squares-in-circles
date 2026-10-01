# A global central-square reduction for eight squares

**Intermediate certificate theorem, not a proof of the optimum.**

At squared radius at most 98/25, an interior-disjoint packing of eight unit squares has exactly one square whose OPEN interior contains the disk center. The proof below uses an exhaustively verified rational interval certificate for a two-square marker lemma. It is currently computational, not yet humanized. This is permitted by the revised research instruction; no Lean formalization is attempted.

## 1. Sorted exterior states and a new marker

Set the circle center to the origin. For a square whose open interior does not contain the origin, choose one of its four oriented side frames so that its center has coordinates (a, sigma*u), with sigma in {-1,1}, a>=1/2, 0<=u<=a. Containment implies

    (a+1/2)^2+(u+1/2)^2 <= 98/25.

Consequently 1/2<=a<=3/2 and 0<=u<=1. Define

    ell(a,u) = min(11u/10, 3/5+4u/7-3a/8, 3/4).

On this whole rectangle 0<=ell<=3/4. The marker direction is the frame angle plus sigma*ell. These coefficients were discovered by numerical pair experiments, then verified on the full continuum by the certificate. They are not transplanted n=7 conclusions.

## 2. Pair statement

For two admissible states (a,u,sigma), (A,v,tau) whose markers have directed gap g in [0,4/5], write

    d = g+sigma*ell(a,u)-tau*ell(A,v),
    X = A*cos(d)-tau*v*sin(d),
    Y = A*sin(d)+tau*v*cos(d),
    H = (|cos(d)|+|sin(d)|)/2.

The certificate proves ALL FOUR inequalities

    a+1/2-X+H > 0,
    1/2+sigma*u-Y+H > 0,
    1/2-a+X+H > 0,
    1/2-sigma*u+Y+H > 0.                    (2.1)

Thus the squares cannot be separated on either axis of the first frame. Reverse the pair and reflect the coordinate frame: the states become (A,v,-tau), (a,u,-sigma), the marker gap remains g, and the relative phase formula is unchanged. The same four universal inequalities also rule out separation on either axis of the second frame.

The separating-axis theorem for rectangles now implies that the interiors intersect. Therefore two interior-disjoint exterior squares have marker distance strictly greater than 4/5 radians.

## 3. The circle budget

If all eight squares avoided the origin in their open interiors, all eight markers would be pairwise distinct and pairwise farther apart than 4/5. Ordering them on the circle, at least one consecutive gap is at most 2*pi/8=pi/4<4/5, a contradiction. The last numerical inequality follows already from pi<16/5.

Hence one square contains the origin in its open interior. Interior-disjointness makes it unique. Notice that this is stronger than merely finding closed containment: states with a=1/2 are included in the certificate, so boundary containment does not escape the argument.

## 4. What the verifier checks

`verify_exterior_markers.py` starts, for each of the four sign choices, with the complete rational box

    a,A in [1/2,3/2], u,v in [0,1], g in [0,4/5].

A terminal box is discarded only if an admissibility constraint is impossible throughout it, or if exact rational lower bounds prove all four margins in (2.1) strictly positive. Otherwise it is bisected into two closed half-boxes. On successful termination their union covers the original box.

Labels are bounded by interval evaluation of their affine branches. The relative phase always lies in [-3/2,23/10]. Sine and cosine at rational endpoints use alternating Taylor bounds: degrees 17/19 for sine and 16/18 for cosine. Possible extrema at +/-pi/2 are conservatively included using 3/2<pi/2<8/5; cosine's possible maximum at zero is included exactly. On this phase interval cosine has no other extremum.

For a coefficient alpha in [al,ah] and x in [xl,xh], the minimum of alpha*x+|x|/2 occurs at one of the four rectangle corners or at x=0. This supplies a rigorous bound for each cosine/sine contribution without dropping its correlation with the square width.

Floating point is used ONLY to choose splits and decide when to attempt an exact check. It never accepts a terminal box: every acceptance is rechecked using Python Fraction arithmetic. A node/depth limit raises an error rather than claiming a certificate.

## 5. Executed exact checks

All four cases completed:

| sigma | tau | Nodes | Empty leaves | Positive leaves | Maximum depth |
| --- | --- | --- | --- | --- | --- |
| +1 | +1 | 17715 | 2178 | 6680 | 28 |
| +1 | -1 | 29647 | 3701 | 11123 | 24 |
| -1 | +1 | 20881 | 2753 | 7688 | 27 |
| -1 | -1 | 15679 | 2099 | 5741 | 27 |

For every row, nodes = 2*(empty leaves + positive leaves)-1. Every positive leaf has a strictly positive exact rational margin. The different-case asymmetry is an implementation/search-order feature, not a mathematical assumption.

This establishes the certificate-level pair lemma over the full state domain, not just a finite sample of states. The verifier and its arithmetic soundness argument still deserve independent review, as any unformalized computer-assisted proof does.

## 6. Next mathematical problem

Normalize the unique central square and analyze the seven exterior squares and their mutual separators. This reduction does not force Cantrell's contact graph, does not exclude all smaller radii, and does not assert that the seven exterior states all lie on the far-corner circle. Those remain separate tasks.
