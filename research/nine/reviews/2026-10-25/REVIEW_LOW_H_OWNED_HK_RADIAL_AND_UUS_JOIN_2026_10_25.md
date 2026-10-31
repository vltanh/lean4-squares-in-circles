# Independent review: the H-owned HK radial return and entire UUS diamond join

Reviewer: high_radius_review. Date: October 25, 2026.

**Verdict: PASS.** The complete new source proves that the original
H-owned-n HK row is impossible for physical radial B, for every actual
KB/HB owner and every original mean and individual radial-weight endpoint.
It also excludes both B masks when c_H dot n>=0. The latter is a proved
restriction on the remaining unique-B row, not its whole exclusion.

The full previously accepted HK owner cover and negative-HA owner join
then justify closing exactly the two existing UUS gates listed in
Section 5. No new gate, full UUU closure or coarse-cell closure follows.

## 1. Exact new source and direct prerequisites reviewed

The hashes below identify the complete saved texts read for this review.
The new source is frozen at its pre-acceptance status. A later status-only
edit does not change the mathematical text audited here.

| Source | SHA-256 |
|---|---|
| LOW_DIAMOND_H_OWNED_HK_RADIAL_AND_NONNEGATIVE_PROJECTION_EXCLUSION.md | 2ef7b77631d8ce15c54c64913f7253adab4dfb644f47575caabcc92c6bef1e10 |
| LOW_DIAMOND_H_OWNED_HK_RETURN_FAN.md | 08cfe890aad8748eecf87f50df7e7da43d1f99c3038627dd40ea914f7679a655 |
| NEGATIVE_H_OWNED_UPPER_LEFT_DIAMOND_HK_CONTACT_FAN.md | 037a24079e9305f82dafd3dbeede62dbef12204cb0c759e6f3ebd09a02cf8d45 |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | e94305229333f45afdbd94e6dddf08485e62005a865afe697759cc36161cf753 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac |
| BOWTIE_CELL_CLOSED.md | 41fec95f68f153d4417651a556cdc65352a6e3f97d32f8f99c561dfb6282b772 |

I read the complete new source and the complete direct fixed-tip and
triangle-normal inputs, and checked the end-triangle pressure theorem
at its actual arbitrary-degree-root scope. The complete original HK fan
and the accepted H-owned-HK return fan were also read. In particular their
strict side-interiority, actual upper-g K corner, h>0, F>1, E>v, d<u,
and exhaustive left-side/upper-left-vertex KB cover are applicable to
exactly the row used here. They do not replace the original HK normal
by an auxiliary separator.

## 2. Full nonnegative-cn branch

The source correctly preserves the actual center projections

    N=V dot n, J=V dot j,
    cn=N-1/2, cj=J+w-1/2.

I rederived that negative A pressure gives cj>0 when cn>=0, because
z_A dot n>0 and z_A dot j=-(av-bu)<0. The genuine H5 force equation
contains the two original parallel n forces and the unchanged petal
resultant. Combining those vectors in the force equation is legitimate;
their two distinct applications P,V are not combined in a torque equation.
The strict petal pressure therefore forces c_H dot ell<0.

The physical triangle theorem at H gives ell dot n>=0. Its zero case
would be ell=-j and is excluded by the strict actual K/H lower-support
gap. Thus ell dot n>0 and ell dot j<0. The HB point is consequently
the fixed physical front/bottom vertex Y=V-(1-w)j. Since Y_f>X,
the entire KB=-f side, including every shared mean, is impossible.

The remaining actual KB point is the fixed K vertex Q=(X,W). I checked
the exact distance identity

    |Q-Y|^2=1+2E(1-w)+(1-w)^2>1.

This establishes two distinct fixed applications before generic
selection is invoked. When B is unique, the selected fixed-tip theorem
then excludes free normals at its genuine B2 star. Since the original
KB normal is strictly within K's upper-left vertex cone, B owns it.
No shared B mean is treated as a fixed point, and the coincident radial-D
exception is excluded by the strict distance bound.

For radial B, no unique-tip selection is used. Its two possible squared
vertex norms are q and q+1-2sqrt(q-1/4). With z_K=(F,W), F>1, W>1,
the actual Q satisfies

    q+1-2sqrt(q-1/4) < |Q|^2=q+1-2F < q.

Thus Q is not a radial B vertex. It must be in the relative interior
of a B side, and the original KB normal is again B-owned. This argument
uses the physical mask and is independent of the individual circle weights.

At B the triangle-normal theorem gives ell dot k>=0. I separately
checked both endpoints of this implication:

* If ell dot k>0, every minimum-ell support point of B belongs to its
  minimum-k unit side. Hence Y,Q lie on that same side and have distance
  at most one, contradicting the displayed strict distance. A side
  endpoint or relative-interior mean is included in this support argument.
* If ell dot k=0, the strict sign ell_f>0 and k_f<0<k_g give ell=-Jk.
  In the common B side frame, Q=I+t ell and Y=I+t' k with t,t' in [0,1].
  Thus Q_f-Y_f=t ell_f-t' k_f>=0, whereas the actual H/K geometry gives
  Q_f-Y_f=-d(1-w)<0. No zero or endpoint value of t,t' is omitted.

This proves the complete cn>=0 exclusion for both physical masks,
including cn=0. It never assigns a K2 equation to the true K3 body.

## 3. Full nonpositive-cn branch and strict whole-H norm bound

Now 0<N<=1/2. I independently expanded the actual corner relation

    z_K=z_A-e_x+tau f+g,
    z_K dot j=E+v-(av-bu)-tau d=J+E-d.

The strict full-row bounds a<2, b>3/5, E>v, d<u and tau<1-v give
z_K dot j>u(v-2/5)>0. If J<=0, the true circle equation would imply

    q=(N+E+d)^2+(J+E-d)^2
      <=1/4+sqrt(2)+2<15/4<q0,

so J>0. Every square and all K forces remain; this argument selects
no circle weight and needs no K concurrence.

I also rederived the exact A2 line intersection

    C_A=P+(c/E)n=T-(u/E)g.

It is on A's original radial force line. Its ordinary first coordinate
is positive, so its scalar multiple of z_A is positive. Since adding
n does not change j projection and z_A dot j<0, this yields P dot j<0.
Using V=P+r0 j gives r0-J>0. Therefore the two distinct original
boundary-square contacts P,V straddle the n axis strictly. This is
where the genuine A2 relation enters the norm proof.

Let rho=R-sqrt(2) and x=rho^2. Every point of any unit square touching
the circle has norm at least rho, by the unit-square diameter and the
triangle inequality. Applying this to P in A and V in K, with their
common n coordinate N and opposite j signs, gives

    J>=b0, r0-J>=b0, b0=sqrt(x-N^2)>0.

The radicand sign is independently established by x>5/16 and N<=1/2.
Since r0<1, these two separate inequalities imply b0<1/2 and x<1/2.
Putting k0=sqrt(x-1/4) gives

    1/4<k0<N<=1/2, k0<=b0<1/2.

All inequalities at equality-capable endpoints were checked: N=1/2
and b0=k0 are allowed, whereas w>0 and r=r0+w<1 remain strict.
Those two actual offset inequalities put H's complete j interval
strictly inside (b0-1,1-b0). Its n interval is [N-1,N]. Consequently
every point Z of the whole closed H satisfies

    |Z|^2 < (1-N)^2+(1-b0)^2.

This is a whole-square estimate, not merely a center or contact estimate.
The algebraic product identity

    (N b0)^2-k0^2/4=(N^2-k0^2)(1/4-N^2)>=0

uses exactly N^2+b0^2=k0^2+1/4. It gives N+b0>=k0+1/2, and hence

    |Z|^2 < 1/4+(1-k0)^2 < 13/16.

The final strict bound follows from k0>1/4. The only physical inputs
after true A2 were the unchanged contacts P,V and the actual H offsets;
there is no hypothesis on the HB/KB owner, selected force or mean in
this part of the proof.

For radial B every point has norm at least sqrt(q-1/4)-1>91/100.
Its squared norm therefore exceeds 8281/10000>13/16, contradicting
the existence of any actual HB point. Both original radial weight
endpoints remain, because this final contradiction is physical.

The independent standard-Fraction arithmetic check reproduced all
new rational margins, including

| Comparison | Exact positive reserve |
|---|---:|
| (99/70)^2-2 | 1/4900 |
| (157/280)^2-5/16 | 149/78400 |
| q0-15/4 | 241/1600 |
| q0-1/4-(191/100)^2 | 101/40000 |
| (91/100)^2-13/16 | 39/2500 |

It also checked 79/40-99/70=157/280 and 1/4+(3/4)^2=13/16.
All sign arguments and identities above were reconstructed directly,
without numerical pose samples or a coefficient table.

## 4. Complete original UUS owner and radius join

UUS here is the physical mask in order **(K,A,B)**: K,A are unique
and B has two physical circle corners. The complete boundary-path
resultant theorem BOUNDARY_THREE_PATH_RESULTANT_CONE.md, Section 3,
retains true K3 and H5 and makes at least one of A,B negative at H.
Radial B has strict positive pressure at H for every original individual
weight, so the negative unique endpoint is the actual A. This is not
a relabeling of the degree-three K as a degree-two body.

For HA, the accepted whole-window physical-triangle tip-owned theorem
excludes every A-owned singleton and every genuine shared HA mean.
The complete free-HA join uses the existing fixed-tip theorem when AK
is a singleton, the full LOW free/shared diamond-return theorem when
AK is shared, and the HIGH free-endpoint theorem including q=17/4.
Thus H-owned singleton HA is the only original remaining owner.

The ordered negative-endpoint fan then has exactly the two A axes and
the strict upper-left A vertex. Every A-owned left singleton is excluded
by NEGATIVE_H_OWNED_LEFT_DIAMOND_SINGLETON_EXCLUSION.md, including its
small-coordinate and HIGH joins. The entire shared-left feature is
excluded by NEGATIVE_H_OWNED_DIAMOND_SHARED_LEFT_EXCLUSION.md. The upper
axis, singleton or shared, puts K in y>=b while the original H satisfies
max_H y<=b-1+ru<b, contradicting physical HK. The strict upper-left
vertex has two distinct fixed applications on the true A2, so compatible
selection makes the original AK K-owned, with its original side offset.

The complete HIGH upper-left theorem already excludes q>=17/4. For
q<17/4 the full accepted HK contact fan has the following exhaustive
selected-normal and mean cover:

| Entire original HK type | Complete exclusion used |
|---|---|
| K-owned g singleton, d>0, r=r0, delta>delta0 | The full parallel-HK NEAR/SIDE pair, reviewed in REVIEW_PARALLEL_HK_2026_10_25.md |
| Free n/g junction, d>0, r=r0, delta=delta0 | The complete LOW_DIAMOND_FREE_HK_NEAR/SIDE/OUTER_RETURN_EXCLUSION join, reviewed in REVIEW_FREE_HK_DIAMOND_2026_10_25.md |
| K-owned f singleton, d<0 | The full f-interface root-projection and RADIAL_RETURN_EXCLUSION assembly, reviewed in REVIEW_LOW_F_INTERFACE_2026_10_25.md |
| Genuinely shared f=n interval, d=0 | The same f-interface assembly, with the complete unchanged original mean interval |
| H-owned n singleton, d>0, delta=delta0, r>r0 | The new reviewed sign split: cn>=0 by H5/support, cn<=0 by whole-H/radial-B separation |

This cover retains the entire free-normal interval in the junction row
and the entire original mean interval at d=0. The new proof does not
substitute an endpoint normal into either row. The two signs cn>=0
and cn<=0 cover the final H-owned row with no gap at zero. Every original
LOW/HIGH radius and their common q=17/4 boundary is therefore covered.

I checked the complete source statements and genuine-degree scopes of
the previously accepted whole-owner joins and reread the applicable
reviewed assemblies. This is a new exact scope/join audit; it does not
claim to repeat every arithmetic proof in the older prerequisite chain.

Additional source hashes used in this scope audit are:

```text
84041bef56dc918eb8362db48e9ec5967c5476fdd89e8bff540e9422f3d62ec2
BOUNDARY_THREE_PATH_RESULTANT_CONE.md
c3e242cd9047efe023c7277d88ad11f3536d825d21f99cb423ddce9bbac22833
LOW_DIAMOND_F_INTERFACE_RADIAL_RETURN_EXCLUSION.md
11fa5a3584421761952a3d0e839eecf8e77f6e6a426a6b62d87a13667959e3c4
LOW_DIAMOND_FREE_HK_NEAR_RETURN_EXCLUSION.md
1031229479cd311cc3fed5edb9ee3e37c053d7fd93db57e6d392afe6df57cc29
LOW_DIAMOND_FREE_HK_SIDE_RETURN_EXCLUSION.md
65f7be64c560e84b188d01d4b095386b10f432560e109b0d59c67853d1b43c77
LOW_DIAMOND_FREE_HK_OUTER_RETURN_EXCLUSION.md
9e2fdef3694bd4e1bfbfd6266563f814a0bce3ce7bb0eb519f395a3cb6870c43
HIGH_RADIUS_TRIANGLE_TIP_PRESSURE_AND_DIAMOND_FAMILIES.md
2a3b2c6d16ccb651100f0d8d904e015f107e448a2dd621d23e57732f984feebd
NEGATIVE_UNIQUE_TRIANGLE_TIP_OWNED_EXCLUSION.md
09a40b2202eb5b0348aaffdf9bd3325eb72130b807c617ad1c94d466a40c268f
NEGATIVE_FREE_SHARED_DIAMOND_RETURN_GEOMETRY.md
59c7a729b87b9a262e97253e8ad4946522b99c750255081a5423641fc7ed6aa8
NEGATIVE_H_OWNED_LEFT_DIAMOND_SINGLETON_EXCLUSION.md
8e1ccbb96507c7aed7ba1562d1262b9a8f59088ff50157a76fb77a62fe0eebce
NEGATIVE_H_OWNED_DIAMOND_SHARED_LEFT_EXCLUSION.md
```

## 5. Precisely two existing gates may close

After accepting the new source, the complete join above justifies closing
exactly these two existing original IDs:

1. M6.TB4.DIAMOND_HUB.NEGATIVE_OWNER.H_OWNED.UUS.LOW.AK_K_OWNED
2. M6.TB4.DIAMOND_HUB.LKAB.UUS

The corresponding HIGH leaf and all other UUS negative-owner alternatives
were already closed. No new ID is introduced. The remaining physical UUU
mask must retain its true H5/K3/A2/B2, all nine squares, actual HK n owner,
negative cn, original KB/HB owners and shared means, and both surviving
KB features. The UUU leaf, whole negative-owner parent, LKAB parent,
diamond-hub orbit and larger coarse cell remain open.

No Lean compilation, CI, numerical sample, changed force or reset mean
is a premise of this review. The result is a complete hand proof and
whole-family assembly at the scopes stated above, not a claim that the
entire PR or unrestricted nine-square theorem is finished.
