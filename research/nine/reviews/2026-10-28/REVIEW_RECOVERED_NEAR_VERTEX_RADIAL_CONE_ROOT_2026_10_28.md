# Independent review of the recovered near-vertex radial cone step

Date: October 28, 2026 UTC. Reviewer: root continuation.

## Exact manuscript and review scope

The source is
`RECOVERED_NEAR_VERTEX_LOWER_HOUSE_SEVEN_TWENTY_FIFTHS_EXCLUSION.md`,
SHA256
`1cad5d0e0d8d54dcd57cb4604150f4d08f02e39c7dbd388e31017f776b1fda62`.
It is a newly reconstructed manuscript, not the historical near-vertex
source at either old hash. I read the complete reconstruction and here
independently verify Section 6.1, including every premise it imports
from Sections 5 and 6. The separate cycles review covers the full
physical feature, topology, and mask assembly. This record does not
give whole-family credit without the entry and assembly proofs.

**Verdict at this exact pin: PASS for the entire unique-corner radial
cone step in Section 6.1.** No normal, support owner, application,
circle coefficient, or square position is replaced.

## Complete scalar and physical check

The port is the actual point P of the true loaded degree-two square T,
with unchanged incoming unit normal n. The prior interface supplies

    P=u*n-r*Jn, 59/60<u<=d<61/60, 0<r<7/25.

The full proper-concurrence lemma, applied with the real physical
boundary neighbor D, supplies

    Q=P+ell*n=lambda*Z,
    ell>=0, 0<lambda<=1,

in the unique physical circle-corner mask. Z is the actual radius-R
corner of T. Neither strict ell nor strict lambda<1 is assumed.

Suppose T does not own n. Then P is its unique minimum-n vertex.
The exact reserves

    (127/120)^2-(61/60)^2-(7/25)^2=2901/360000>0,
    17/4-(247/120)^2=191/14400>0

show that each adjacent vertex has norm at most |P|+1<247/120<R.
P itself also has norm below R. Thus the sole possible actual circle
corner is the opposite vertex, with w=Z-P and |w|=sqrt(2).

The concurrence equality, without changing its original point, gives

    w=A*P+B*n,
    A=(1-lambda)/lambda>=0, B=ell/lambda>=0.

The pair A,B cannot both vanish, because |w|=sqrt(2). Since u>0,

    P.w=A*(u^2+r^2)+B*u>0.

Direct expansion, with no squaring sign ambiguity, gives

    (P.w)^2-u^2*|w|^2
       =A^2*r^2*(u^2+r^2)+2*A*B*u*r^2>=0.

Consequently P.w>=sqrt(2)*u. The actual circle radius therefore obeys

    R^2=|P+w|^2
       =|P|^2+2+2*P.w
       >=u^2+2+2*sqrt(2)*u
       >(59/60+7/5)^2
       =1105/256+78559/57600.

This contradicts the declared radius ceiling. The endpoint cases
lambda=1 or ell=0 remain included whenever consistent with w; none
is silently discarded. The contradiction forces T to own the original
normal. The two-corner physical mask is a different branch of the
source and is not replaced by this unique-corner argument.

## Independence and boundary of the review

Cycles disclosed that it authored the historical general cone lemma
and helped reconstruct this short step. This root review independently
checked the displayed expansion, its signs, the physical opposite-
vertex reduction, and all rational reserves. The source's Section 6.1
is self-contained; no lost historical port-gap source is required.

Exact rational arithmetic was used only to check printed reserves.
No sampled configuration, angle mesh, Lean compilation, CI, or
unrestricted optimality assertion is involved.
