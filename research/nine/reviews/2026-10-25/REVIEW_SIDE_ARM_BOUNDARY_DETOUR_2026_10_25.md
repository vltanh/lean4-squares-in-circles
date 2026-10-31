# Independent review: a side arm cannot return through a boundary detour

Date: October 25, 2026. Reviewer: root, independently of the author.

**Verdict: PASS.** `SIDE_ARM_BOUNDARY_DETOUR_EXCLUSION.md` proves a
whole-radius, arbitrary-root-degree arm/channel obstruction and closes
the original gate `M6.B4L2.C4.CHAIN.LBC.S_SIDE`. It adds no coefficient
certificate or new checklist ID.

## 1. Exact original arm and channel premises

I checked the full arm/load cover in
`FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md`, Section 1 and Section 3.1.
The genuine S leaf L has its actual inner application at d*e, where
d=sqrt(R^2-1/4)-1. Its true degree-two unloaded side transmitter U has
reserve one. The original torque/normal-channel identity therefore
places the actual application on the block root A at (d-1)*e.

The source does not claim that A itself has a genuine leaf. U is
retained as a physical square with its real contact means and original
degree two. A may have arbitrary other forces.

For another actual normal channel from A to C, with reserve w>=1,
the source keeps its exact supporting half-planes and actual support
alpha. The sharp contained-unit center bound gives

    alpha+w+1/2 <= n dot c_C <= |c_C| <= d+1/2,
    alpha <= d-w <= d-1.

This uses neither a load nor an assumed circle contact at C. Every
directional halfwidth is at least one half. The stated maximum-corner
identity and its resulting center bound are correct for independent
square frames.

## 2. Complete lower-radius argument, including all equalities

If delta=d-1<0, the actual point delta*e in A gives

    alpha >= delta*(n dot e) >= delta.

The second inequality has the correct direction because delta is
negative. Together with the preceding upper bound this forces
alpha=delta, w=1, and n=e. The last conclusion uses delta<0, not a
claim at delta=0.

Every center/halfwidth bound is then equality. In particular
c_C=(d+1/2)*e and the halfwidth in direction e is one half.
The unit-square width identity forces e to be a side axis. Hence the
entire occupied C is the unique radial S square

    [d,d+1]*e+[-1/2,1/2]*Je,

which is exactly the original L. Distinct physical unit squares cannot
have identical interiors. Thus the second channel is impossible for
d<1, even without a boundary detour. No unproved local motion or
assumption about C's original circle multiplier is used.

## 3. The upper-radius transfer uses the actual general theorem

For d>=1, the original point (d-1)*e gives
dist(0,A)<=d-1=max(d-1,0). I read Theorem 4.1 and its proof in
`FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md`. Its hypotheses are exactly
this central-disk condition, the true channel support inequalities
with reserve at least one, and a physically circle-touching common
neighbor of its endpoints. Its proof does not require a genuine leaf
at A, positive degree two at A or C, or positive weight on the detour
contacts. The source explicitly covers longer channels with the same
support equations.

The narrow-shadow proof used in this transfer has R>=sqrt(17)/2,
which follows here from d>=1. Its strict contact norm, cap slope and
boundary-shadow estimates therefore apply in their full stated radius
range. In particular the endpoint d=1 is assigned to this argument,
and no equality value falls between the two cases.

## 4. Complete original gate join

The original cyclic order is A--B--C--D--A, with the real arm
A--U--L and block-load representative BC. The S/side arm gives the
required point on A. D is a true unloaded degree-two body; its channel
is A--D--C. The full load cover even forces its reserve to one through
the bypass B, although the new theorem only needs reserve at least one.
B is positively loaded and hence physically boundary, and it actually
touches both A and C. C and L are distinct original bodies.

These premises hold for every original mean, orientation, physical
circle mask, individual zero circle-weight endpoint and remaining
packing square in the entire representative. Its reflected load
placement is already included by the original C4 symmetry. No force
at A is deleted and no higher-degree body becomes a transmitter.

Thus exactly the stated existing gate closes. The complete C4 arm
parent and coarse C1.4.b2 remain open through their other original
load/width alternatives. The stronger local theorem may be reused
only after checking its actual arm/channel/detour hypotheses.

No numerical sample, computational certificate, Lean compilation,
CI or workflow dispatch was used in this review. The global theorem,
original equality and older prerequisite-chain audit remain open.
