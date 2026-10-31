# A large central side offset excludes the whole high top return

Date: October 27, 2026.  
Author: topology_final.

**Status: complete fresh analytic local theorem, frozen for a full independent review.** The actual central side position is retained throughout. The theorem permits either sign of the root's small horizontal coordinate and covers the entire singleton/shared top-contact partition. H and K have arbitrary degrees. The only two-force equation used is the true loaded C2. No computational exclusion certificate is introduced.

## 1. Full actual domain

Let H,K,C be pairwise interior-disjoint unit squares contained in the same origin-centered disk. Both K and C physically touch its circle. Assume

    17/4 <= R^2 <= 1105/256,
    d=sqrt(R^2-1/4)-1 < 61/60,
    R<25/12,
    -1/60<=h<=1/60, 89/120<G<1,
    H=[h-1,h] x [G-1,G], W=(h,G), |W|<d.

The actual central HK is a K-owned singleton at W, with its unchanged actual normal and square

    U=(c,s), V=(s,-c), c,s>0, c^2+s^2=1,
    n_HK=U,
    K=W+[0,1]U+[-a_0,1-a_0]V,
    0<c<1/10, 7/8<=a_0<1.                    (1)

Thus W is in the relative interior of K's actual minimum-U side. The interval for a_0 is a hypothesis on that actual side position, not a choice of its representative.

C has one physical circle corner z_C, positive total circle load, and precisely the two positive pair forces HC and CK. The actual HC normal from H to C is E2. Keep both physical possibilities: a strict lowest C vertex in the relative interior of H's top side, or a positive-length shared side with its whole unchanged actual force mean. The actual CK force, application, physical type and owner are unrestricted initially.

Use the existing compatible physical certificate: when both incident C contacts are physical singletons at distinct fixed points, its original simultaneous unique-circle fixed-point selection supplies an actual side owner. This is a pre-multiplier selection, not a new normal choice after a force or a mean is known. A local application outside that framework may instead provide that resulting actual owner premise directly. No singleton selector is applied to a variable shared mean.

**Theorem 1.1.** The complete local configuration above is impossible.

The theorem has no force law at H or K and imposes no physical circle mask at K. It preserves all their other neighbors, every original shared mean, and all additional physical squares in any original caller.

## 2. Actual proper C2 and both low K corners

Orient w from C to K. Let T be the actual HC point or mean, and Z the actual CK point or mean. With the actual positive magnitudes, the C2 force and proper concurrence give

    kappa*z_C=omega*E2-gamma*w,
    kappa,omega,gamma>0,
    q_C=r*z_C=T+ell*E2 in C,
    Z-q_C=ell_K*w,
    0<r<=1, ell>=0, ell_K>=0.                (2)

The boundary-neighbor version of Lemma 2.1 in the complete present triangle-chain source applies because K physically touches the circle. Physical uniqueness at C identifies its radial resultant with the same z_C and puts its concurrence in C. A positive dilation beyond its unique circle corner is outside the square, so r<=1. The offsets are kept nonnegative; their zero endpoints are not discarded.

The two minimum-U K corners are W-a_0 V and W+(1-a_0)V. Their distance from W is at most one. Since |W|<d,

    |W-a_0 V|<d+1<R,
    |W+(1-a_0)V|<d+1<R.                      (3)

The last strict comparison is exact from R^2=(d+1)^2+1/4. Any physical K circle corner must consequently be one of

    K_1=W+U-a_0 V,
    K_2=W+U+(1-a_0)V.                        (4)

No K circle corner or weight has been selected in advance.

## 3. Shared HC: the actual mean still forces the left circle corner

Suppose HC has positive physical shared length. Then

    C=[l,l+1] x [G,G+1],
    T=(x_0,G), h-1<=x_0<=h<=1/60.            (5)

The lower C corners cannot touch the circle, since G>0 makes their vertically adjacent upper corners strictly farther from zero. The unique circle corner is on the top side. Physical uniqueness also makes the magnitude of its horizontal coordinate strictly greater than 1/2; this follows by comparing the two top corners.

By (2), r*(z_C)_x=x_0 and r*(G+1)=(q_C)_y>=G. Since G>1/2, one has r>=G/(G+1)>1/3. If x_0>0, the actual top-right circle corner would therefore give

    x_0=r*(z_C)_x>1/6>1/60,

contrary to (5). If x_0=0, the same positive r would give a zero horizontal circle coordinate, also impossible. Hence x_0<0 and

    z_C=(l,G+1), l<-1/2.                     (6)

This is why the shared branch works for positive h as well. Its conclusion uses the actual proper mean and the full side interval; no mean is moved to the left half-plane.

The horizontal component of the true C2 force in (2) gives w_x>0. The physical H-K-C triangle at C's owned CH side, whose outward normal is -E2, gives w_y<=0.

If w_y<0, C's actual maximum-w support is its bottom-right vertex at height G. Because w.V>0, the minimum-w K support is W-a_0 V, W-a_0 V+U, or the whole side between these points according as w.U is positive, negative or zero. Every one of those points has height at least G+a_0 c>G. No physical contact is possible.

Thus w=E1. Its minimum support on K is the actual point W-a_0 V. Equality of the actual horizontal supports forces

    l+1=h-a_0 s,
    z_C=(h-a_0 s-1,G+1).                    (7)

This covers the entire initially allowed w cone and every original shared HC mean. CK has not been assigned a preferred physical type or owner.

## 4. Shared HC: both possible K circle corners are dominated

For the actual corner (7), direct expansion gives

    D_1=|z_C|^2-|K_1|^2
       =-2h(1+c)+1+2a_0 s-a_0^2 c^2
          +2G(1-s-a_0 c),

    D_2=|z_C|^2-|K_2|^2
       =-2h(1+c+s)+2G(1-s+c)
          +2a_0(1+s-Gc)-a_0^2 c^2.          (8)

All estimates below use the complete signed h interval. For D_1, the possible negative h term is greater than -11/300, the quadratic term is greater than -1/100, and

    2G(1-s-a_0 c)>-2c>-1/5.

Dropping the positive 2a_0 s therefore gives the uniform strict reserve

    D_1>1-11/300-1/100-1/5=113/150>0.        (9)

For D_2, its first term is greater than -7/100, its second term is positive, and 1+s-Gc>1-c>9/10. Using a_0>=7/8 yields

    D_2> -7/100+(7/4)(9/10)-1/100
        =299/200>0.                         (10)

Thus both actual candidates (4) have norm strictly less than |z_C|=R. The other two K corners were already strictly inside by (3). This contradicts K's physical boundary contact and excludes the entire shared-HC branch. No K force equation or K uniqueness is used.

## 5. Singleton HC: the sign of the actual contact is derived

Now suppose HC is a physical singleton. Its actual point T is a strict minimum-height C vertex in the relative interior of H's top side. Write

    T=(t,G), h-1<t<h,
    C=T+[0,1]e+[0,1]f,
    e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1.     (11)

The point T cannot itself be a circle point shared by H and C. The opposite C corner cannot be the physical circle corner either. Indeed, if z_C=T+e+f has height Y, then Y>G and (2) gives r>=G/Y, r<=1 and T_x=r*(z_C)_x. Therefore

    2=|z_C-T|^2
      <=(1-G/Y)^2 R^2
      <=(R-G)^2
      <(161/120)^2<2,                       (12)

with final squared reserve 2879/14400. This complete argument does not assume a sign of t.

If t>=0, then h>0 and 0<=t<h, so |T|<=|W|<d. Both adjacent C corners would have norm less than d+1<R. Along with (12) and the impossible shared T, there would be no physical C circle corner. Consequently t<0.

Put t=-z. The actual singleton domain is now

    z>0, 0<z+h<1.                            (13)

The adjacent T+f cannot be a circle corner: its minimum-e coordinate is T.e=zq+Gp>0, whereas comparison with its adjacent vertex in the +e direction would require that circle coordinate to be at most -1/2. Thus the actual unique circle corner is

    z_C=T+e=(-z-q,G+p).                       (14)

The sign and the circle candidate have been derived on the whole signed-h domain, not imported from a nonpositive-h theorem.

## 6. The full C circle, angle and actual proper-ray identities

Set

    A=Gp+zq>0, B=zp-Gq.

The actual circle coordinates and physical uniqueness give

    B>1/2,
    R^2=(A+1)^2+B^2=(z+q)^2+(G+p)^2,
    A<d<61/60,
    G=Ap-Bq<dp-q/2.                          (15)

If q>=39/100, then p<=sqrt(8479/10000)<921/1000, so

    dp-q/2<14827/20000<89/120,

contradicting the actual G lower bound. The two squared/height reserves are 341/1000000 and 19/60000. Hence the whole domain satisfies

    0<q<39/100, p>23/25.                      (16)

The proper line in (2) now fixes the actual concurrence as

    q_C=[z/(z+q)]z_C,
    ell=B/(z+q)>0.                           (17)

In particular the two actual C applications cannot coincide. If they did, the two nonparallel actual contact lines supplied by proper C2 would concur at T, contrary to (17). Thus when CK is also singleton, the original compatible fixed-point selector applies to the actual distinct singleton applications and supplies a side owner. Its coincident radial exception is not deleted. Shared CK already has a physical side owner and keeps its whole actual mean.

Define

    F=z(p-q)-Gq-q^2
     =B(1-pq)-(A+1)q^2.

The full bounds in (15)--(16), together with p<=1-q^2/2, give

    F>J(q)=1/2-q/2+q^3/4-(121/60)q^2.

The derivative J'=-1/2+3q^2/4-(121/30)q is negative on the complete interval [0,39/100]; even the larger bound -1/2+3(39/100)^2/4 is negative. Therefore

    F>J(39/100)=52379/4000000>0.               (18)

This is one whole-interval inequality, not a finite contact-angle computation.

## 7. Every CK side owner and actual support is retained

The f component of the actual force equation (2), using z_C.f=-B, gives w.f>0. The entire actual C support is consequently

| Sign of w.e | Actual C support |
| --- | --- |
| Negative | T+f |
| Positive | T+e+f, of height greater than G+1 |
| Zero | w=f and the entire maximum-f side |

In the first row the unchanged proper-ray displacement is exactly

    (T+f)-q_C=(p,-F/(z+q)),                   (19)

which is strictly rightward and downward by (18). No auxiliary force line is substituted.

If C owns CK, w.f>0 leaves only its own normal w=f. The actual physical H-K-C triangle at that owned C side would require

    f.(-E2)=-q>=0,

which is impossible. This removes the entire C-owned CK class, including every shared CK mean. There is no assumption that the incoming HC is also C-owned: the triangle theorem requires only the outgoing owned side and the actual other supporting normal.

The remaining CK is a K-owned singleton. The physical triangle at K, whose other outward normal is -U, gives w.U>=0. All actual K axis alternatives are therefore U,V,-V; -U is excluded. Both zero-dot alternatives V and -V are kept.

For w=U, if w.e>0 the C support has height greater than G+1, whereas K's entire minimum-U side has height at most G+a_0 c<G+1. If w.e=0 then w=f, already excluded by the physical C-side triangle. If w.e<0, (19) makes w strictly downward, contrary to U_y=s>0.

For w=-V, one has w.e=sq+cp>0. If w.f<=0 the actual force projection is already impossible; otherwise C's support again has height greater than G+1. K's minimum-(-V) side has maximum height

    G-(1-a_0)c+s<G+1,

so this whole axis is impossible too.

Thus the only surviving actual normal is w=V. Its C support is T+f since V.e=-sq-cp<0. It must lie on K's actual minimum-V side. For the original side parameter zeta,

    T+f=W-a_0 V+zeta U,
    0<zeta<1,
    zeta*s=q-a_0 c,
    z+h=p-(c/s)q+a_0/s.                     (20)

All divisions are safe because s>0. The strict side parameter is the actual singleton convention; none of the final estimates requires a newly chosen point or mean.

## 8. The actual large offset contradicts the whole contact relation

Equation (13) says z+h<1. Apply it directly to the same actual relation (20):

    a_0<s(1-p)+cq
       <2/25+39/1000
       =119/1000.                            (21)

The second strict inequality uses s<1, p>23/25, c<1/10 and q<39/100. It contradicts the whole original offset premise a_0>=7/8, with exact gap

    7/8-119/1000=189/250>0.                  (22)

There is no need to estimate the final K circle angle or subdivide the remaining slope. The actual relative-interior inequality at H and the actual side position at K already disagree uniformly.

Sections 3--4 exclude shared HC; Sections 5--8 exclude singleton HC across every original CK physical type, side owner and application. They prove Theorem 1.1 on its entire stated signed strip and actual offset interval.

## 9. Exact logical scope and present inputs

The complete local theorem is broader than the parallel-root caller that motivates it. It requires only the displayed actual H,K geometry, boundary K, true physically unique C2, the actual top HC and the existing compatible singleton convention. H and K keep arbitrary other forces, masks and degrees. All additional physical units remain.

The whole actual central offset a_0 is retained through both branches. The proof uses no K2 or H3 law, no false B-C triangle sign, no replacement of a variable mean, no post-stress normal selection, and no assumed nonpositive h. The possible positive mean and nonnegative lowest point at C are explicitly excluded from the actual proper geometry before using a left circle chart.

The following complete present originals are the only logical inputs:

| Complete source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual force/moment laws, strict singleton convention and unchanged shared means |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Complete boundary-neighbor proper C2 with physical unique C and non-strict offsets |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical circle-corner comparisons and impossibility of a shared containing-circle point |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual H-K-C side-normal implications, including all zero-dot endpoints |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing simultaneous selection at the proved distinct fixed C singleton applications |

The accepted nonpositive-h high-corner theorem motivated some comparisons. Its hypotheses are not extended by assertion: all needed shared/positive-point signs, complete owner branches and new offset inequalities are reproduced above. No missing earlier artifact is a premise.

Exact polynomial and rational checks accompany the new source. They validate whole displayed identities and fixed reserves; the complete physical cover is the proof above. The source still requires an independent full review of every actual support/mean branch and its original caller before adoption. No original gate, ledger, remote file, Lean source or CI workflow is changed, and no computational exclusion certificate is added.
