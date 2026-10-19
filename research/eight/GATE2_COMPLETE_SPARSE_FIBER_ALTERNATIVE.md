# Gate 2: complete sparse alternatives for every fixed n=8 fiber

2026-10-13. Depends on the actual-square model in
`GATE1_ORDERED_RATIONAL_GLOBAL_MODEL.md`. This closes a proof-mechanism
gate, **not** the unrestricted radius inequality.

## 1. Fixed-fiber notation

Fix the seven relative frame parameters z and one signed true SAT owner
for each of the 28 pairs. Let o_iv be the four actual vertex offsets of
square i and write each chosen directed separator as

    A_e p = n_e dot (p_j-p_i) >= w_e,   w_e >= 1.

Here p has 16 center coordinates. All normals are unit true square axes.
The fiber minimizes q subject to these 28 affine inequalities and

    |p_i+o_iv|^2 <= q      (32 genuine disk constraints).

The value is denoted q_min(z,W), with value +infinity for an empty fiber.

## Theorem A — a complete separator alternative, with at most 15 edges

Exactly one of the following holds:

1. The directed separator system is feasible.
2. There are lambda_e>=0, not all zero, with

       sum_e lambda_e A_e = 0.

   Consequently 0 >= sum_e lambda_e w_e > 0 would be required.

If alternative 2 holds, a certificate exists supported on at most **15**
chosen pair edges. On a support-minimal certificate using m square labels,
the bound improves to 2m-1. Its undirected support graph is connected,
has no bridges, and has no vertex of degree one.

### Elementary proof of completeness

All rows A_e lie in the 14-dimensional subspace annihilating common
translations of the eight centers. Let C be their finite convex hull.

If 0 belongs to C, its convex coefficients give the stated certificate.
If 0 does not belong to C, let b be the point of C closest to zero.
Then b is nonzero and the minimum-norm property gives

    A_e dot b >= |b|^2 > 0       for every e.

A sufficiently large positive multiple of p=b therefore satisfies
A_e p >= w_e for every e. This proves the alternative without an
assumption about strict feasibility or a numerical LP.

A representation of zero as a convex combination can be reduced to at
most 15 rows: if more remain in dimension 14, an affine dependence permits
adjusting the nonnegative coefficients until one vanishes, preserving
both their sum and their weighted vector sum. Repeat. Restricting to m
labels gives dimension at most 2m-2 and bound 2m-1.

For a support-minimal certificate, disconnected components would each
balance separately, contradicting minimality. A bridge is impossible:
sum all node force equations on one side of its cut; the sole remaining
force is a nonzero positive multiple of its unit normal. The degree-one
case is included. QED.

**Quantifier warning:** these are *separator infeasibility* forces with
no circle terms. The no-bridge conclusion is not a theorem about physical
contact stresses, which may include disk forces and radial leaves.

## Theorem B — attainment and an optimal dual with at most 17 constraints

If the directed separator system is feasible, its radius minimum is
finite and attained. There are nonnegative multipliers on at most
**17 total constraints**, counted across the 32 disk vertices and 28
chosen pair separators, giving an exact optimal dual value q_min.
No frame genericity or positive disk weight at every square is assumed.

### Attainment and strict feasibility

Choose feasible centers. Scaling their centers by a factor alpha>1 makes
every separator strict, since w_e>=1. Taking q sufficiently large makes
all disk inequalities strict. This is a Slater point.

The fiber has a finite feasible objective. Below that objective the
vertex-average identity bounds every center. Closedness then gives
attainment of its infimum.

### A direct multiplier argument

At an attained optimum x*=(p*,q*), consider the objective gradient and
the gradients of all active constraints, expressed as functions <=0.
A direction making all these scalar products strictly negative would
improve the objective and satisfy all constraints for a sufficiently
small positive step. Such a direction cannot exist.

The same finite convex-hull alternative used above therefore gives a
nonnegative dependence among the objective gradient and active constraint
gradients. Its objective coefficient is strictly positive: otherwise,
dotting with the direction from x* to a Slater point would give a strictly
negative sum equal to zero. Here convexity gives a strictly negative
scalar product for each active constraint gradient. Normalize the
objective coefficient to one. These are the stationarity and
complementarity multiplier equations.

Now express the negative objective gradient as a nonnegative combination
of active constraint gradients in R^17. A support-minimal such conical
representation has at most 17 vectors: if more are present, a linear
dependence allows subtracting a suitable multiple of it from the
positive coefficients until one vanishes, without making any coefficient
negative or changing the represented vector. This proves the count.
The q-coordinate of stationarity still forces the disk multipliers to
sum to one. QED.

## 3. The explicit dual, including zero disk-anchor squares

Let mu_iv>=0 be disk multipliers with sum_{i,v} mu_iv=1 and let
lambda_e>=0 be separator multipliers. Define

    m_i = sum_v mu_iv,
    a_i = sum_v mu_iv o_iv,
    c_i = sum_{edges leaving i} lambda_e n_e
          - sum_{edges entering i} lambda_e n_e,
    B_i = 2a_i+c_i.

For m_i>0 put Psi_i=|B_i|^2/(4m_i). When m_i=0, require c_i=0 and set
Psi_i=0. In that case all mu_iv=0, hence a_i=B_i=0 as well.

The exact center-independent lower bound is

    D = 1/2 + sum_e lambda_e w_e - sum_i Psi_i.        (D)

Indeed, subtract the nonnegative weighted true separator gaps from the
weighted disk-vertex squares. The result is

    1/2 + sum_e lambda_e w_e
        + sum_i [m_i |p_i|^2 + B_i dot p_i].

Completing the squares proves q>=D. If m_i=0 but c_i is nonzero, this
expression is unbounded below in p_i and is NOT a finite dual bound.

For the optimal multipliers in Theorem B, stationarity gives
B_i=-2m_i p_i*. Complementarity makes the weighted gaps vanish.
Consequently (D) equals the actual q_min. This establishes exact dual
attainment, including free zero-anchor centers, by the preceding
finite-dimensional argument.

## Theorem C — positive-anchor regularization has a quantitative loss bound

Start with any valid dual data and choose 0<epsilon<1. Set

    mu_iv^epsilon = (1-epsilon) mu_iv + epsilon/32,
    lambda_e^epsilon = (1-epsilon) lambda_e.

Every disk vertex weight is now positive and every m_i^epsilon>=epsilon/8.
Since the four offsets of each square sum to zero,

    a_i^epsilon = (1-epsilon)a_i,
    c_i^epsilon = (1-epsilon)c_i,
    m_i^epsilon = (1-epsilon)m_i + epsilon/8.

It follows that

    D_epsilon >= (1-epsilon)D + epsilon/2.            (R)

### Proof

When m_i>0,

    Psi_i^epsilon
      = (1-epsilon)^2 |B_i|^2 / (4m_i^epsilon)
      <= (1-epsilon) Psi_i.

When m_i=0, both old and new B_i vanish, so both penalties are zero.
Substitute these inequalities in (D). More precisely the nonnegative
regularization reserve is

    D_epsilon - [(1-epsilon)D+epsilon/2]
      = sum_{m_i>0} ((1-epsilon)epsilon Psi_i)/(8m_i^epsilon).

This is an identity, not a sampled continuity assertion. QED.

The 17-constraint support bound concerns an exact optimal dual before
regularization. Adding 32 positive vertex weights need not preserve
that sparsity; no simultaneous claim of both properties is made.

## Theorem D — every strict fiber exclusion has a rational, stable witness

Fix any real threshold tau. At a fixed z,W, the assertion

    q_min(z,W) > tau

is equivalent to the existence of rational nonnegative dual multipliers,
with **all 32 disk weights positive** and summing exactly to one, for
which D(z,W)>tau. Such a witness remains valid on a relative open
neighborhood of z in the closed ordered simplex.

### Proof

For a nonempty fiber use the attained optimal dual from Theorem B.
Apply (R) with epsilon sufficiently small to retain D_epsilon>tau.
All anchor denominators are then strictly positive.

For an empty separator fiber use Theorem A's balanced lambda, and set
mu_iv=1/32. Then a_i=c_i=0 after multiplying lambda by any positive scalar
s, so D=1/2+s sum_e lambda_e w_e tends to infinity. Choose s giving a
strict margin over tau.

In both cases continuity in the weights allows rational approximations,
preserving nonnegativity and the exact simplex normalization sum mu=1,
while retaining the strict margin. The latter simplex has dense rational
points in its relative interior. Zero separator weights can remain zero.

For these fixed rational weights the Gate 1 formulas make D a continuous
rational function of z with positive denominators. Thus D>tau persists
in a relative open neighborhood, including at z ties or z=0/1. One may
choose a rational threshold b with tau<b<D(z,W), and a sufficiently small
rational box on which D>b. Direct rational interval arithmetic can
certify that strict inequality after sufficient local refinement.

Conversely, weak duality gives q_min>=D>tau. QED.

### What compactness does and does not supply

For a compact set K of angle/word pairs **already proved** to satisfy
q_min>tau everywhere, these neighborhoods have a finite subcover.
This is a conditional termination statement. It does NOT establish that
the entire domain has q_min>=q_*, nor that a chosen complement of a local
pose neighborhood has a strict gap.

At a genuine equality fiber q_min=q_*, no strict certificate D>q_* can
exist. Such fibers require a non-strict sharp inequality, potentially
with zero anchor weights, and separate equality-aware arguments.

## Theorem E — the exact scope of local-to-fiber propagation

Fix z,W. Suppose a feasible pose p0 has squared radius q0 and is a local
radius minimum among the genuine square packings in that fixed fiber.
Then q_min(z,W)=q0 globally over all centers in the fiber.

Proof: if another feasible point (p1,q1) had q1<q0, convexity would make
((1-t)p0+t p1,(1-t)q0+t q1) feasible for every 0<t<1. For t arbitrarily
small its centers are arbitrarily close to p0 and its objective is
strictly smaller than q0, a contradiction. QED.

In particular, the existing local sharpness theorem propagates to every
**exact reference-angle** owner fiber which actually contains its
reference packing. This is stronger than a pose-local statement at those
fixed frames. It does NOT establish a positive-width angular terminal:
the interpolation argument requires both endpoints in the SAME convex
fiber. Nearby frame angles and all slider endpoints need their own
uniform hypotheses.

## Gate exit

**Gate 2 passes.** Every fixed fiber has a complete alternative: a sparse
separator contradiction, or an attained exact sparse optimal dual.
Zero anchors are handled, strict rational witnesses are locally stable,
and the limit of local-to-fiber propagation is explicit.

**Still open:** a globally exhaustive, usable reduction of all orientation
and owner families; sharp inequalities for all its survivors; unrestricted
R_8>=R_*; and global equality. Proceed to Gate 3A, not directly to another
isolated angular-box certificate.
