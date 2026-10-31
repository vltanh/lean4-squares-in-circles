# Root review: exact C6 channel compatibility and three-parameter reconstruction

Date: October 26, 2026.

**Result: PASS for the full equivalence and both reconstruction
directions, with every stated physical condition retained.** This
is an exact reduction of equations, not an exclusion of their roots.

I independently read the complete
SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md and
checked it against the original shared-support functional and the
accepted remaining one-share physical domain.

## 1. Three residual identities are exact

With v=-Ju, one has F dot v=(JF) dot u and
v cross F=u dot F=u cross JF. Thus each actual local contribution
to the weighted channel dot sum is RD-E, while its original torque
is -u cross(K+JF)=0. Telescoping gives exactly

\[
 \sum r_i=-C,\qquad \sum f_i\cdot r_i=V,
 \qquad \sum f_i\times r_i=0.
\]

These identities hold before any channel residual is set to zero.
The actual direction u=(K+JF)/|K+JF| is the unchanged local
positive-support and torque direction. No numerical rank argument
or artificial force equation is present.

If r0=C=V=0, then r2=-r1 and both the dot and cross products of
F2=f1-f2 with r1 vanish. The strict original turn makes F2 nonzero;
the elementary norm identity forces r1=r2=0. Conversely all three
channel vectors zero imply all five displayed scalar equations.
Closure and virial alone are correctly not called sufficient.

## 2. The surviving physical chart and positive circle branch agree

I checked the mixed110 outgoing-share0 chart, its E1^2 constant 2,
the bit-zero g2 direction, the shared torque ell=1-q(s0-c0), and
the virial numerator 2+p+q(1+h0)+E1+E2.

For an original core, z0=(-a,-b) and z1=(A,-B). The actual channel0
components give a=2+X+Y-A and H=B-X+Y=b-1+ell. Its original force
signs select b=+sqrt(R^2-a^2); no physical second branch is dropped.
Shared torque gives ell=kappa(a-b)>0, so a>b>1/2 and a>1.
The original force f2 is therefore recovered exactly by
(1-kappa a,-kappa b), with kappa=ell/(a-b)>0.

## 3. The converse reconstructs the same local equations

For every retained admissible parameter tuple (R,p,c1), the formula
F0=kappa z0 gives its actual positive circle-force direction and norm.
The shared mean is unchanged because q(s0-c0)=1-ell. Directly,

\[
 K_0+JF_0=(0,-\kappa(a+b)),\qquad
 E_0=\kappa(a+b)=1+q(s_0+c_0)>0.
\]

Thus u0=(0,-1) is exactly its local support direction. The other
two units use their original local formulas. Their actual ports have
p0+=(-a+1,-H) and p1-=(2-a,-H), so channel0 is identically one.
The residual equivalence then proves that Cx=Cy=V=0 supplies both
remaining channel vectors in full.

The c2 and s2 formulas respect the original turn sum. The further
inequality H>b(1-1/a) is exactly equivalent to c0>0, after
multiplication by the positive a-b. It is a valid necessary physical
height bound, not an added restriction.

## 4. What has and has not been reduced

The source explicitly retains every original circle mask, vertex
containment, singleton/shared contact set, genuine mean endpoint,
transmitter interval and all nine-square nonoverlap constraints.
The ell=1 endpoint is retained initially and excluded only by the
accepted closure contradiction. Normalizing by mu0 divides by an
original strictly positive force and loses no force ordering.

The result replaces six channel components by five scalar equations,
then solves two of them exactly to leave three scalar equations in
three parameters. It does not assert isolated roots, root uniqueness,
a numerical bounding box or a completion-capacity theorem. The seven
remaining exterior/central allocations and full original completion
gate stay open. No original gate count or coefficient packet changes.
No Lean compilation, CI or numerical proof premise is used.
