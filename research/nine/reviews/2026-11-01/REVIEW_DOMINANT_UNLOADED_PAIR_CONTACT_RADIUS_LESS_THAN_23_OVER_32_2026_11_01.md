# Independent review: the dominant contact lies within 23/32 of the disk center

Date: November 1, 2026 UTC. Reviewer: four_chain continuation.

**Decision: PASS the complete new quadratic longitudinal estimate,
simultaneous two-point localization and all stated local conclusions.**

The frozen target is
`DOMINANT_UNLOADED_PAIR_CONTACT_RADIUS_LESS_THAN_23_OVER_32_2026_11_01.md`,
SHA-256 `493a2b6cbac1849798ef42aace682583e33770aafb6d9200c95505cb6d8e15dc`.
I read the entire source and independently reconstructed the new
directional-error identity, exact rational comparisons, midpoint
argument and zero-residual endpoint.

Authorship boundary: I constructed the earlier sharp support-torque
kernel and the existing disk-point restatement in the cited C4 source.
That frozen input already has its separate clean full review by
module_universal. I did not construct the present quadratic longitudinal
estimate or simultaneous-midpoint improvement. This review accepts
those new arguments independently at that retained prior input boundary;
it does not present my own earlier kernel as independently audited by me.

## 1. The retained local disk points have the exact hypotheses needed

At either original unloaded endpoint, all remaining positive forces
are retained in the residual magnitude r. The complete translation
gives z >= d-r and the exact two-vector identity gives the stated
delta bound. Each original residual application is a support point
for its own normal, so the already accepted torque bound by r applies
at the same original pair application p, including every side mean.

The unit support segment puts p-n in the first unit and q+u in its
immediate actual distinguished neighbor. Consequently s >= -u.n,
lambda > 0 and 0 < k <= 1. The printed y_A is a convex combination
of two original disk points, not a substituted contact. The full norm
error follows from the exact lambda identity and retains its zero
case. The constant 2924/925 < 19/6 is correct.

No lower radius, full-cut size, planar selector or four-cycle graph
appears in these local inputs. Their extraction from the accepted
source does not import its unrelated original C4 hypotheses.

## 2. The pair-direction error is genuinely quadratic

With c=u.n=-1+delta^2/2, direct expansion of the unchanged disk point
gives

    epsilon_A.n = 3delta^2/2-delta^4/4+k v (Ju.n).

The first term is nonnegative for delta<1. Also Ju.u=0, so
|Ju.n|=|Ju.(u+n)| <= delta. Combining this with the full moment
bound and 0<k<=1 proves the absolute directional estimate

    |epsilon_A.n|
      <= [ (3/2)(26/25)^2+(26/25)(40/37) ] t_A^2
      = (317590/115625)t_A^2 < 3t_A^2

when t_A>0, and zero when t_A=0. The weak bound by 3t_A^2 therefore
holds at every endpoint. Applying the same argument at B with its
local normal -n preserves the absolute estimate in direction n.
No transverse sign, common frame or support owner has been assumed.

## 3. Both original disk points are used simultaneously

For m=(y_A+y_B)/2 and w=(y_B-y_A)/2, the two directional errors
give

    w.n >= 2-(3/2)(t_A^2+t_B^2) >= 2-3T^2/2 > 0.

Thus |w| has that lower bound. The exact parallelogram identity for
the two unchanged disk points gives

    |m-O|^2+|w|^2 <= R^2 <= Q.

This proves the displayed square-root bound for |m-O|. The same
errors give |p-m| <= (19/12)T. Their combination is precisely the
parameter-dependent bound claimed in Theorem (1), with the actual
same p at both endpoints. The radicand is positive in this entire
range and, as the source observes, is also certified nonnegative
by the geometric inequalities themselves.

## 4. Exact constants and endpoints

For every actual 0<=T<3/40,
2-3T^2/2 > 6373/3200. The printed square and subtraction are correct:

    6373^2=40615129,
    Q-(6373/3200)^2=3584871/10240000<9/25.

Therefore |m-O|<3/5, while |p-m|<19/160. Their sum is exactly
23/32. At T=0 both errors vanish, m=p, and the sharper closed bound
|p-O|<=sqrt(Q-4)=9/16 follows directly. No false strict inequality
at a zero residual is needed anywhere in the proof.

## 5. Complete scope

The result applies to an actual unloaded pair with one distinguished
original neighbor force at each endpoint and total residual ratio
below 3/40, at arbitrary remaining degrees and loads of all neighbors.
All original physical normals, support means and circle coefficients
remain. It neither manufactures that residual ratio for a new caller
nor supplies an unproved distant terminal. The direct triangle and
other open original families are correctly left for separate proofs.

The accepted C4 source and its independent review remain frozen.
This new local improvement introduces no canonical packing, lower-radius,
graph-cut or normal-selection premise. All mathematics in this review
was checked by hand. The SHA identifies document bytes only; no
mathematical script, numerical sample, interval certificate, Lean,
build, CI, ledger change or remote mutation was used.
