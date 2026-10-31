# A support-point radius inequality forces exact unit-square alignment

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed force-free general hand theorem and literal
side-channel reductions, frozen for separate full independent review.
No original whole-family or coarse-cell closure is claimed.**

The general theorem has no force, degree, contact owner, circle-contact
mask, or fixed radius-window premise. It is an inequality for one actual
unit square in its actual containing disk. Its applications preserve all
original units and all original applications and side means.

## 1. Exact general support-point theorem

Let K be an actual unit square contained in the closed disk of radius R
about the unchanged origin. Let n,m be orthonormal directions. Suppose K
lies in n.X>=h and its actual minimum-n support contains the point

    S=h*n+z*m, h>0.

If K is not parallel to the n,m axes, it has a unique minimum-n vertex,
which must be this same S. Then an actual opposite corner Z satisfies

    |Z|^2>(h+1)^2+(1-|z|)^2.                         (1)

Consequently

    R^2<=(h+1)^2+(1-|z|)^2                           (2)

forces K to have sides parallel to n,m. The support point in this
conclusion can be any original vertex, contact point or shared-side mean;
no point is chosen or moved.

For the proof, use the actual n,m coordinates about the original circle
origin. At a genuinely tilted minimum-n vertex, the two inward unit axes
have n components c,s>0 with c^2+s^2=1. Their transverse components have
opposite signs. Put

    k=c+s>1, q=|c-s|<1, k^2+q^2=2.

The actual opposite vertex has coordinates (h+k,z+delta), where
|delta|=q. Therefore

    |Z|^2
      >=(h+k)^2+(|z|-q)^2
       =(h+1)^2+(1-|z|)^2
          +2*h*(k-1)+2*|z|*(1-q)
       >(h+1)^2+(1-|z|)^2.

The last inequality is strict because h>0 and k>1. This proves (1)
and its contrapositive (2), including equality in the radius comparison.
Neither a derivative nor a numerical orientation cover is used.

The pointwise inequality (1) permits every real z. For a convenient
uniform consequence, if 0<=b<=1 and |z|<=b, then
(1-|z|)^2>=(1-b)^2. Hence

    h>=h_0>0, |z|<=b<=1,
    R^2<=(h_0+1)^2+(1-b)^2                          (3)

also forces actual alignment.

## 2. Two complete high-radius support intervals

Throughout R^2<=1105/256, either of the following closed support-point
conditions suffices for the same conclusion:

    h>=1,       |z|<=7/16;                          (4)
    h>=59/60,   |z|<=1/3.                          (5)

For (4), the right side of (3) is exactly

    4+(9/16)^2=1105/256.

For (5), its strict reserve is

    (119/60)^2+(2/3)^2-1105/256
       =3551/57600>0.

Thus the first condition includes its exact radius/support/transverse
endpoint, and the second includes the full displayed closed rectangle.
Both concern the actual support point and the unchanged circle origin.
They cover a whole continuous set of orientations and positions without
using any force equation or physical circle-contact assumption.

In particular (4) strengthens the support-point lemma used in
OPEN_ORIGIN_S_ROOT_NORTH_RETURN_PARALLEL_HUB_SIDE_AND_DOUBLE_CORNER_REDUCTION.md:
its interval |z|<=1/3 is contained in |z|<=7/16. The previously frozen
source and its proof remain unchanged.

## 3. Literal application to the full side channel with a triangle bypass

Retain the entire actual graph and force hypotheses of
SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md:

    edges AB,BC,CD,DA,AT,DT;
    B is unloaded true degree two;
    C is loaded true degree two with neighbors B,D;
    D is unloaded true degree three with neighbors A,C,T;
    T physically touches the circle;
    A and T may have arbitrary other true forces and degrees.

Use its original high-radius chart about the unchanged circle origin:

    d=1+epsilon, 0<=epsilon<1/60,
    B=[h,h+1] times [b,b+1],
    P_AB=(h,q), P_BC=(h+1,q), b<=q<=b+1,
    A subset {x<=h}, C subset {x>=h+1},
    max_D y<=b<=q,
    -epsilon<=h<=epsilon.

Every point displayed is its original actual application or mean.
The complete positive-mean theorem proves q>0, with all its zero-moment
and parallel-force endpoints included. The incoming support height of
the real C is

    h_C=h+1>=1-epsilon>59/60.

Apply (5) to C at its unchanged point P_BC. This gives the full
necessary alternative

    0<q<=1/3  ==>  C is parallel to the actual B channel;
    C tilted relative to B  ==>  q>1/3.             (6)

This does not assume C owns the incoming normal. Ownership in the
small-q domain follows from the actual alignment just proved.

The original house-hub TC.S and TC.D callers of the positive-mean
source satisfy precisely this local graph, with true A4/T2/D3/B2/C2/L1.
They retain their genuine leaf and all nine physical squares. The
theorem here adds no new root-origin, leaf-axis, A3 or T2 premise to
the general local implication. Each literal caller must still supply
the displayed actual near-origin channel bound, exactly as in that
accepted source.

## 4. A still smaller channel mean forces the full physical two-corner mask

In the same complete channel, suppose

    0<q<=59/238.                                    (7)

This lies within the interval in (6), so C is parallel to B and has
its actual minimum-x side at h_C>59/60.

If C's two original pair normals are parallel, their complete
classification in the positive-mean source gives the genuine radial S
shape. The radial D alternative has inward support R-sqrt(2)<41/60,
contrary to h_C>59/60. Oppositely directed parallel forces were excluded
there using the actual circle point and real neighbor-width obstruction.
Both original applications and magnitudes remain distinct data.

Otherwise the two pair normals are nonparallel. The complete conditional
proper-concurrence argument in Section 2 of that source applies without
assuming either of C's actual neighbors is boundary. It gives

    q_C=P_BC+ell*(1,0), ell>=0,
    q_C=tau*F_C, tau>0.

Assume C has just one physical circle corner Z. Since its actual x
interval is [h_C,h_C+1] with h_C>0, its circle corner is on the far
side and has transverse coordinate of absolute value at least 1/2.
The positive transverse coordinate q of q_C forces that coordinate
to be positive. Write

    Z=(h_C+1,L_C), L_C>=1/2,
    q_C=t*Z, t>0.

The actual normal component gives t>=h_C/(h_C+1). Hence

    q=t*L_C>=h_C/[2*(h_C+1)]
      >(59/60)/[2*(119/60)]=59/238,

contrary to (7). Every unique physical mask is excluded.

Therefore C has its full physical two-circle-corner radial rectangle.
The parallel-force row gives the same conclusion. In either row,
equality of the two corner radii centers its real transverse interval:

    C=[d,d+1] times [-1/2,1/2],
    h_C=d, h=epsilon.                              (8)

The two original nonnegative circle weights are not set equal. Either
individual zero weight is retained, their total stays positive, and
both original positive pair forces of the true C2 remain. A physical
two-corner shape is not substituted by a force leaf or transmitter.

This is a necessary-domain reduction, not an exclusion of the remaining
radial C, large-q aligned C, or tilted q>1/3 domain.

## 5. Exact operative pins and preservation

| Source | SHA256 | Exact use |
| --- | --- | --- |
| SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md | 5a1607a588e45d0702c46c3d74074561f31109dccc0b8f94c665991cd4a9f5ee | Complete literal channel, full positive mean, conditional nonparallel properness, and complete parallel C classification |
| UNIT_BYPASS_NORMAL_CHANNEL.md | db073cd024a4f2e763e7cd0a21bf5cb6a2a8be67069f3f9d3aff638b8a40b258 | Actual unloaded B2 channel and genuine D bypass with original unit reserve and unchanged means |
| OPEN_ORIGIN_S_ROOT_NORTH_RETURN_PARALLEL_HUB_SIDE_AND_DOUBLE_CORNER_REDUCTION.md | 63a4f444aa098ba450321380aaea39e2a136f5dc1aabf94eab8d8b6b6d55d789 | Earlier narrower support-point lemma strengthened by (4), without rewriting that source |

Sections 1--2 are self-contained physical geometry and use no imported
force proof. Sections 3--4 use exactly the complete hypotheses and proof
parts stated above. All nine actual squares, original true degrees,
full positive forces and torques, selected normals, actual applications,
shared means and endpoints, circle masks and zero individual weights
remain. No original ID or checkbox is added, removed, reordered or changed.
No numerical pose search, Lean compilation, CI or workflow was performed.

