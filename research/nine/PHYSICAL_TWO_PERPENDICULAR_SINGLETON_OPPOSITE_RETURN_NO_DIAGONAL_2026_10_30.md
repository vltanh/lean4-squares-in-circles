# The whole opposite-return family also excludes a diagonal N

Date: October 30, 2026. **Complete proposed original-feature theorem with an
exact finite certificate; independent audit and compiled Lean are deferred.**

Together with
`PHYSICAL_TWO_PERPENDICULAR_SINGLETON_WHOLE_SIDE_RETURN_EXCLUSION_2026_10_30.md`,
this leaves only an **opposite-D-vertex return with side N** in the original
physical-two West/strict, A-owned perpendicular-singleton L135 feature.
The whole original D02.L135 row remains open. No original checkbox changes.

**Reusable scope.** B and C may have arbitrary original positive degrees,
loads, further forces and physical contacts. The displayed B2/C2 stars below
are only the literal L135 caller. The proof uses their original AB/DC support
owners, deduced from the unchanged full A3/D3 singleton stars, and the true
unloaded N2 interface; it never uses a shortened B or C equilibrium equation.
The whole result therefore also excludes this feature inside larger positive
components with arbitrary attachments at B,C. The exact A3,D3,V2,N2 stars,
initial common-selector and incident-diagonal premises remain essential.

## 1. Retain the original chart and every true star

Use the entire original chart and original selected certificate of Section 1
of the companion side-return theorem. All nine squares, original forces,
means, masks and the same initial incident-diagonal avoidance remain. Keep

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C},

with unloaded A3,D3,N2 and loaded V2,B2,C2. The parameters retain

    h=(c,-s), e=(s,c), a^2+b^2=c^2+s^2=1,
    D0=1-a+Hs>0, N0=1-Hc+b>0,
    u=ac-bs, y=as+bc,
    r=gamma/mu=N0/D0,
    K=P-h+N0*e,
    f_B=(-D0*h+N0*e)/sqrt(D0^2+N0^2).

The original opposite-D-vertex return has

    L=Q+v+w,
    q=gamma/nu=(u-y)/b>0.                              (1)

In particular its original D-to-C normal is strict at the opposite actual D
vertex, not a D side mean. The full V,A,D moments give

    b*(H-1/2)*N0=(d*s+c/2)*(u-y)*D0.                  (2)

The complete continuous slider-gain source
`PERPENDICULAR_SINGLETON_COMPLETE_CONTINUOUS_SLIDER_GAIN_AND_OPPOSITE_TWO_FIFTHS_EXCLUSION_2026_10_29.md`
has already excluded the whole b>=2/5 range. Its proof includes the joining
endpoint. The full-star return-ratio source excludes q>=18/5. Thus any
remaining original opposite return satisfies

    0<b<2/5, q<18/5, 0<s<2/3,
    1/2<H<=1, 9/10<d<61/60.                         (3)

Here s<2/3 follows from the existing c>3/4 exit; sqrt(7)/4<2/3.

## 2. A diagonal N forces perpendicular original endpoint axes

The physical AV and AD intersections are the original genuine singletons at
two distinct relative-interior A side points. The A-to-B force has strict
own components (-mu,gamma), so AB is a singleton at A's opposite corner K,
distinct from those two points. Consequently all three original A contacts
are distinct physical singletons.

At D the original DV point Q and AD point W are adjacent distinct D vertices.
The present DC point L is the opposite vertex to Q, distinct from both.
All three contacts are physical singletons. The original full D force has
strict positive components along v,w here; this is exactly the opposite
return in (1).

Apply the **existing initially common** theorem
`GENERAL_UNLOADED_THREE_DISTINCT_SINGLETON_PORTS_HAVE_NO_FREE_NORMAL_SELECTION.md`
to these unchanged full true-three stars. This is the same pre-extraction
selection hypothesis used in the published owner cover. No new normal is
selected after the graph, loads or contacts are known. It gives:

- B owns its original inward normal bvec=f_B at K.
- C owns its original inward normal -cvec at L, where

      cvec=(c*h+(s+q)*e)/sqrt(c^2+(s+q)^2).

K is on B's actual minimum-bvec side; L is on C's actual maximum-cvec side.
The respective normal components are nonzero, and neither A nor D could own
these strict corner normals. This is the reason the original singleton
selector is needed; arbitrary force directions alone would not imply owners.

If the unchanged N is a diagonal transmitter, its full two-force equations
give T-U=sqrt(2)*n for the actual BN,CN applications. The original incident-
diagonal avoidance forces both T and U to be relative-side-interior points
of B and C. Therefore B and C both own n and have parallel actual frames.
Their original own axes bvec,cvec must be parallel or perpendicular.

In the actual A frame, bvec has coordinates proportional to (-D0,N0),
whereas cvec has coordinates proportional to (c,s+q). All four displayed
scalar magnitudes are positive, so their determinant is strictly negative.
They cannot be parallel. Hence necessarily

    bvec.cvec=0,
    N0*(s*b+u-y)-c*b*D0=0.                           (4)

All multiplications here use positive b,D0 and vector norms; no zero-force
or side-mean endpoint has been discarded. On (4), their **directed** axes are

    bvec=(-D0*h+N0*e)/sqrt(W0),
    cvec=(N0*h+D0*e)/sqrt(W0), W0=D0^2+N0^2>0.       (5)

## 3. Exact whole-domain cover gives two strict support projections

The unchanged support difference simplifies to

    Delta=K-L=-(D0-b)*h+(1+a)*e.

The following two polynomial-radical comparisons hold at every original
opposite return satisfying the diagonal-ownership equality (4):

    (D0-b)*D0+(1+a)*N0 > sqrt(W0),
    -(D0-b)*N0+(1+a)*D0 > sqrt(W0).                    (6)

By (5), these are precisely

    Delta.bvec>1, Delta.cvec>1.                         (7)

The full finite interval certificate uses the closed rational domain

    s in [0,2/3], b in [0,2/5], H in [1/2,1], d in [9/10,61/60],
    a=sqrt(1-b^2), c=sqrt(1-s^2).

Every original point is contained, including all limiting endpoint faces
needed for a closed cover. The exact replay has **1,873 nodes**, **937 leaves**,
and maximum depth **17**:

| Leaf | Exact contradiction or conclusion | Count |
| --- | --- | ---: |
| `q_positive` | u-y<=0 contradicts (1) | 10 |
| `return_ratio` | 5(u-y)-18b>=0 gives the already excluded q>=18/5 | 3 |
| `full_torque` | Equality (2) has a fixed nonzero sign on the box | 218 |
| `endpoint_axes_not_orthogonal` | Equality (4) has a fixed nonzero sign | 228 |
| `B_point` | The actual contained B point K+f_B would be outside its circle | 304 |
| `both_support_projections_gt_one` | Both inequalities (6) hold throughout | 174 |

The B-point predicate, dyadic interval operations, outward square-root
rounding and full binary closed-box coverage are exactly the proved rules
in Section 3 of the companion theorem. Only the original full-torque equality,
root b interval and the perpendicular-axis equality/terminal inequalities
differ. The certificate declares its own distinct kind and root domain.

Data and replay:

    certificates/physical_two_perpendicular_opposite_diagonal.json
    ../../scripts/n9_physical_two_opposite_diagonal_certificate.py

All comparisons are integer/rational, and no leaf is a sampled sign. No
subdivision-limit branch is accepted as a proof. Both generation and full
replay terminate successfully, in under one second in this environment.

## 4. A four-row rectangle argument closes every diagonal direction at once

This last argument is independent of the circle and all force magnitudes.
Suppose two actual unit squares have perpendicular own axes bvec,cvec, with
K a minimum-bvec point of B and L a maximum-cvec point of C. A diagonal
transmitter N with both endpoint normals owned by B,C would have

    T-U=sqrt(2)*n,
    T a minimum-n point of B, U a maximum-n point of C,
    n in {bvec,-bvec,cvec,-cvec}.

The four original alternatives have the following complete support bounds:

| n | Necessary bound on Delta=K-L | Reason |
| --- | --- | --- |
| bvec | Delta.cvec<=1 | (K-T).cvec<=1, (T-U).cvec=0, (U-L).cvec<=0 |
| -bvec | Delta.bvec<=-1-sqrt(2) | K and T are on opposite B sides; U is C's minimum-bvec point |
| cvec | Delta.bvec<=1 | (K-T).bvec<=0, (T-U).bvec=0, (U-L).bvec<=1 |
| -cvec | Delta.cvec<=-1-sqrt(2) | U and L are on opposite C sides; T is B's maximum-cvec point |

Each bound is a whole-unit rectangle bound and includes every original side
mean or endpoint. They contradict (7) in every row. The diagonal N is
therefore impossible over the **entire original opposite-return domain**.

## 5. Complete feature consequence and remaining boundary

The original perpendicular-singleton D contact has exactly the adjacent,
side and opposite returns. The adjacent return was already excluded in full.
The companion theorem now excludes the **whole side return**, for both
possible unloaded-N transmission types. This theorem excludes diagonal N
in the **whole opposite return**. Therefore any surviving instance of this
complete physical-two perpendicular-singleton feature must have

    opposite D return, and N a side transmitter.

This conclusion retains c>3/4, b<2/5, q<18/5 and every original force,
physical circle corner, individual coefficient and actual completing unit.
Whole-data reflection transports the result to the opposite V coefficient
endpoint. It does not assert that the remaining side-N row is realizable.

Loaded N in D02.L1345 does not satisfy the unloaded transmission dichotomy
and is not excluded. The other original AD owners, the two-strict-inner-tip
physical feature, unique-V families and the entire original D02 load rows
still have their stated obligations. This source changes no original ledger
flag and does not promote uncompiled code to a Lean theorem.

Replay:

    python scripts/n9_physical_two_opposite_diagonal_certificate.py \
      --verify research/nine/certificates/physical_two_perpendicular_opposite_diagonal.json
