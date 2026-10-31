# Compatible shared-BC block selection excludes a free HC return

**Status: complete finite pre-extraction selection argument; root author review and separate independent full saved-source, direct-prerequisite and selection-pipeline audits passed.**

Work in the original radius window 79/40<=R<=sqrt(1105)/16, with the actual H--A--B--C--H positive component and intact H--X--Y--H petal. Retain true H4/A2/B2/C2, every original positive force, circle weight, physical square and shared application mean.

A is a negative unique endpoint, HA is an H-owned singleton, and AB is an A-owned left singleton. The small-coordinate and tilt theorems give the actual B frame

    T=(x,beta), x=a-1>1/2,
    e=(-c,s), f=(-s,-c), c,s>0, c²+s²=1, det(e,f)=1,
    B=T+[0,1]e+[0,1]f,
    z_B=mathsf A e-mathsf B f=(X,Y),
    mathsf A>0, mathsf B>0, Y=beta+s>0.

Here T is the fixed physical singleton AB point. The actual outward normal from B toward A is m=e_x, a fixed axis of A. The original B concurrence is (beta/Y)z_B. If BC is B's f-owned side, its unchanged aggregate application S satisfies

    S·e=beta*mathsf A/Y, S·f=1-mathsf B.                 (1)

Equation (1) is the original B2 concurrence statement in NEGATIVE_H_OWNED_LEFT_SINGLETON_SIDE_RADIAL_EXIT.md. The present theorem concerns the genuine positive-length shared BC alternative and a physically unique C. That source excludes every physically radial C from this feature before the present selection is used.

**Theorem.** A compatible finite normal choice, imposed with the existing normal conditions before multiplier extraction, ensures that no surviving true B2/C2 shared block in this entire domain has a free singleton HC. Every original shared BC mean and its endpoints are retained. This is a selection implication, not a closure of the entire left-singleton return family.

## 1. The complete physical shared-C frame

A genuine shared BC side forces C's actual axes to be e,f. Its minimum-f coordinate is 1-mathsf B, and its maximum-f coordinate is 2-mathsf B. The bound mathsf B<5/4 from Section 2 of the radial-exit source applies at the actual physical point. Thus 2-mathsf B>3/4 and the far f-coordinate is positive.

C has a unique physical circle corner. Its proper C2 concurrence, supplied by its physical boundary neighbor B, has e-coordinate S·e>0. Since that concurrence is a positive multiple of the actual unique circle corner, that corner's e-coordinate is positive. Write

    z_C=Ue+Vf, U>0, V=2-mathsf B>0, U²+V²=R²,
    C=[U-1,U]e+[V-1,V]f.                            (2)

This identifies the original physical pose. No transverse C position, BC mean or force has been chosen. Every physical contact point of a free singleton HC is a fixed vertex K of C. It cannot be the circle vertex z_C.

## 2. Two virtual-work identities on the actual B/C block

Use J for counterclockwise rotation by pi/2 about the true circle origin. Consider the circle-tangent translations

    w_B=Jz_B, w_C=(mathsf A/U)Jz_C.                  (3)

They have zero work against their respective original circle forces. Their normal components on the shared BC interface agree exactly:

    f·w_B=mathsf A=f·w_C.

Consequently all internal BC work cancels for every original shared-side mean. There is no hypothesis that that mean lies in an interior subinterval.

A second virtual motion rotates both original B and C about the true origin at the same unit angular velocity, keeping every other body's velocity zero. Each circle force again has zero work. The two velocities agree at every point of the shared interface, so the internal BC force cancels with its unchanged application and moment.

Suppose a surviving free HC singleton has actual outward C-to-H unit normal r, fixed physical point K, and positive pair magnitude nu. Let mu>0 be the original AB magnitude. The true B2 and C2 equations imply the two identities

    mu(m·w_B)+nu(r·w_C)=0,
    mu det(T,m)+nu det(K,r)=0.                     (4)

These are linear combinations of the full genuine force and torque equations. H, A, the petal and every other physical square remain in the certificate; their additional forces are not set to zero. The test velocities on those bodies happen to be zero.

Eliminating the unchanged positive magnitudes from (4) gives

    r·W=0,
    W=(m·w_B)JK-det(T,m)w_C
     =-Y JK+beta*(mathsf A/U)Jz_C.                 (5)

Indeed m=e_x, m·Jz_B=-Y and det(T,m)=-beta. Both coefficients are fixed by the original physical geometry of this candidate block.

## 3. The coefficient W cannot vanish in a surviving block

At either noncircle corner adjacent to z_C, one has det(K,z_C)=-V or U in the positively oriented e,f frame. These quantities are nonzero. Since Y>0, the two vectors JK and Jz_C are independent, so W is nonzero.

At the remaining opposite corner K=(U-1)e+(V-1)f,

    det(K,z_C)=U-V.

Thus W could vanish only if U=V. In that case U=R/sqrt(2)>1 and

    K=(1-1/U)z_C,
    |K|=R-sqrt(2).

Substituting this K into (5), W=0 is exactly

    beta*mathsf A/Y=U-1.                           (6)

But (1), (2) and (6) would make the actual original BC mean equal K:

    S=(U-1)e+(V-1)f=K.

This is physically impossible. The common-point bound for two circle-touching units is strict:

    p in B intersection C  =>  |p|>R-sqrt(2).

It is the boundary-neighbor argument used in FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md, Section 1, and GENERAL_FIXED_TIP_NORMAL_SELECTION.md. Equality in the unit-diameter and triangle inequalities would force the two units to share the same containing-circle corner, which is forbidden. It applies to every actual point of the shared interval, including an endpoint-valued mean.

Therefore no surviving original block in this domain has W=0. The zero-coefficient exception has been excluded using the original mean, rather than silently discarding the opposite-corner or radial-diagonal pose.

## 4. One compatible finite choice before extraction

Prelist all ordered physical A,B,C,H quadruples in the fixed original packing with:

* unique physical B and C circle corners;
* a genuine physical shared B/C side and its actual parallel frames;
* a singleton external AB contact T with an A-owned normal m;
* a free external HC candidate at a fixed physical C vertex K.

Include all physical candidates, even if they do not occur in an initially considered positive support, and all possibilities needed by physical uncrossing. In the relevant positive-e, positive-f C charts, compute W from the physical quantities in (5). The candidate pair means remain unrestricted. No extracted multiplier is used in defining this finite list.

For each entry with W nonzero, exclude the proper line r·W=0 from its open free-normal cone. This removes only finitely many directions from each relevant open cone. It is compatible with the previously imposed strict, fixed-tip and shared-block conditions by the same finite open-dense intersection argument as NEGATIVE_H_OWNED_SHARED_LEFT_MIDDLE_EXCLUSION.md, Section 2.

Entries with W=0 are not assigned an impossible normal condition. Section 3 shows that any surviving true B2/C2 certificate for such an entry would force its unchanged mean S to a physically forbidden common point, so that entry cannot survive.

Make this common finite choice before multiplier extraction and before the physical uncrossing/thinning pipeline. Every possible physical shared pair and external candidate was already prelisted. Uncrossing retains preselected surviving normals and their actual contact data; thinning only deletes edges. The resulting certificate therefore satisfies all earlier conditions and this additional one simultaneously.

A surviving free HC return would have to satisfy (5) by its true equations, while its preselected normal was chosen off that line. This contradiction excludes the complete free-return alternative. No positive extracted normal is subsequently rotated, removed or reassigned.

## 5. Exact consequence and limits

After the common pre-extraction choice, every surviving HC return for this original shared-BC feature is H-owned, C-owned or genuinely shared. The theorem retains all original offsets, physical corner masks, actual application means and zero individual weights that enter the surrounding component. True B2 and C2 are essential.

The complete owned-return geometry is proved in NEGATIVE_H_OWNED_LEFT_SHARED_RETURN_EXCLUSION.md. The full positive-component/completion contradiction retains its separate open obligations. This source does not close a coarse cell, replace H4 by a smaller force equation, transfer the result to a K3 junction, or identify an original equality packing. No Lean compilation or CI is run.

