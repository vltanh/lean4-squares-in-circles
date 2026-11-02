# Every distinct upper central extra has a good whole floor

November 2, 2026. A complete six-variable computer-assisted table, with
an independent directed-integer replay and the original-square reduction
below. The final acceptance counts and audit are recorded in Section 8.
No Lean, Lake, or CI. This is a component theorem, not a whole-mask claim.

## 1. Statement and retained originals

Retain an original closed-Q `010/11` configuration, where Q=1105/256.
Write A,B,C,D for the original main chain and L,P,R for the original
selected short chain. Keep every independent original frame, corner and
physical pair. Orient vertically so P is above both inner mains, L is
above B and R is above C, using the accepted common routing. Let U be an
additional original central square, distinct from A,B,C,D,L,P,R, with

    |xU| <= ell = 29/60,             yU >= yP.

**Theorem.** The original U has `yU-hU>1/10`.

In the low-P-floor domain, the completed upper-extra ordering theorem
makes every unselected upper central original a valid U. The present theorem cannot
be applied with U=L or U=R: it uses both original U/L and U/R physical
pairs. The unused ninth original remains arbitrary and physical. No new
cone comparison to U is assumed.

Reflect horizontally, reversing both marked chain labels and their
coordinates together, so x=xP>=0. Put Z=-xL and X=xR. The original
cone gaps and the contained half-unit center disks give

    0 <= x <= 1129/3000,   19/60 <= Z <= 13/12,
    7/10 <= X <= 13/12,    DL=Z+x,  DR=X-x,
    DL,DR > 707/1000.

These are closed enlargements of the original strict bounds. Every
selected frame is written independently as

    aS=1/sqrt(1+tS^2), bS=tS*aS, hS=(aS+bS)/2, kS=(aS-bS)/2,
    (aS,sS*bS), (-sS*bS,aS),  tS in [0,1], sS in {-1,+1}.

All eight sign triples are retained. Write p=hP, l=hL, r=hR.

## 2. A bad U floor bounds the same original P from above

Suppose contrary to the theorem that yU-hU<=1/10. Equal U/P heights
are impossible, since their horizontal gap is at most ell+x<1. Thus
U>P. The accepted support bound for independently oriented original
unit squares is `|cU-cP|>=1+|hU-p|`. For u=hU this gives

    yP <= u+1/10-sqrt((1+|u-p|)^2-(ell+x)^2)
       <= p+1/10-sqrt(1-(ell+x)^2).                 (1)

The last inequality is exact: for delta=|u-p| and 0<=D<1,

    sqrt((1+delta)^2-D^2) >= delta+sqrt(1-D^2),

as squaring nonnegative quantities leaves
`2*delta*(1-sqrt(1-D^2))>=0`, and u-delta<=p. This eliminates U's
frame only after bounding its actual original P/U pair.

The published `WIDE_MAIN_UPPER_CENTRAL_HEIGHT_HAND_TABLE.md` applies
to the actual P and proves yP>-7/40, independently of the selected
short bits or any additional outsider. Hence the initial P interval is

    Pminus=-7/40,
    Pplus=min(p+1/10-sqrt(1-(ell+x)^2), actual P corner upper bounds).
                                                               (2)

This removes all main-frame parameters from the table. No original main
is assumed aligned. For the endpoint resources below we simply discard
the nonnegative original surplus V=etaB+etaC; this is a relaxation of
the complete original configuration.

## 3. Original shoulder resources and heights

For S=L,R keep the accepted unrestricted pair toll

    tauS=max(2*bS, 6*bS-(27/2)*(1-aS)).

The original endpoint contributions A0=-xA-hA and A3=xD-hD obey
A0+A3>=2+V and each Ai<61/60. Dropping V>=0 from the two original
endpoint/shoulder caps supplies the necessary lower bounds

    AL=max(59/60,157/184+(27/92)*(X-r)+tauR/46),
    AR=max(59/60,157/184+(27/92)*(Z-l)+tauL/46),

and the five nonnegative resources

    61/60-AL, 61/60-AR,
    1+l+r-Z-X-(2/27)*(tauL+tauR),
    l+451/810-Z-(2/27)*tauL,
    r+451/810-X-(2/27)*tauR.                       (3)

These refer to the same original L,R frames used in all later corners
and pair constraints. They do not add the tolls of different theorems
on a single pair.

Let J=29927/30000. For either actual endpoint, its inset contains the
rectangle with horizontal interval [503/480,937/480] in the reflected
right-hand coordinates and vertical interval [-c,c], where

    c=max(4421/12000,
          1-sqrt(Q-(min(Astar,61/60)+J)^2)).        (4)

Here Astar is AL or AR. On the necessary domain (3), the clipping does
nothing. Outside it, (4) is only a well-defined scalar extension. This
is the previously audited original endpoint rectangle: it follows from
that endpoint's outward corner, hE+kE>=J and hE+gE>=1.

For a shoulder at absolute horizontal coordinate z>=3/5 the original
upward routing and this rectangle give the lower height

    c+hS-loss,
    loss=max(0,tS*(kS+503/480-z))          for local sign +,
    loss=max(0,(503/480-z-kS)/max(tS,t0))  for local sign -.
                                                               (5)

Use t0=1/16 for L, t0=1/4 for R. The left local sign is -sL; the
right local sign is sR. The complete coordinate-owner and physical-owner
argument, including the zero-slope faces, is Section 5 of
`WEAK_MIDDLE_TWO_WEAK_SHORT_MAINHEIGHT_QUARTER.md`; it does not use
that paper's main-height conclusion. The denominator floors are valid
because below the relevant t0 the numerator of the positive part is
negative.

Use (5) for R throughout, and for L when Z>=3/5. When Z<=3/5, use
instead Lminus=-1/4. Indeed the original B band and Z in [19/60,3/5]
give |xL-xB|<1/4. Since L>B and yB>-6/5, their center disks give

    yL > -6/5+sqrt(15)/4 > -1/4,

where the last positive-square reserve is
`15/16-(19/20)^2=7/200`. This covers the entire low-Z domain.

The upper heights Lplus,Rplus come from the actual signed corners.
For example at positive abscissa z,

    U+(z,h,k)=min(sqrt(Q-(z+k)^2)-h,sqrt(Q-(z+h)^2)+k),
    U-(z,h,k)=min(sqrt(Q-(z+h)^2)-k,sqrt(Q-(z-k)^2)-h).

Use U_(-sL) for L and U_sR for R. The independent checker retains all
four actual corners, which can only strengthen these necessary bounds.

## 4. The same P height belongs to both original short pairs

First apply, in this order, the finite cone contractions

    Pminus=max(Pminus,Lminus-DL,Rminus-DR),
    Pplus=min(Pplus,Lplus+DL,Rplus+DR),
    Lminus=max(Lminus,Pminus-DL), Lplus=min(Lplus,Pplus+DL),
    Rminus=max(Rminus,Pminus-DR), Rplus=min(Rplus,Pplus+DR).       (6)

Every update preserves the actual original heights. An empty interval
is a legitimate rejection; no convergence of an iteration is presumed.

For an original pair i,j define its exact support sum

    sigmaij=(1+|ai*aj+si*sj*bi*bj|
                +|sj*ai*bj-si*bi*aj|)/2.

All four genuine owned axes have this same support. For positive
horizontal gap D, intersect the necessary vertical interval with [-D,D],
calling its endpoints Eminus,Eplus. Each selected original pair requires
the following six quantities to be nonnegative:

    Eplus-Eminus,
    D-707/1000,
    hi+hj-D,
    D-1/(4hi)-1/(4hj),
    max over original owner axes n and E in {Eminus,Eplus}
        |nx*D+ny*E| - sigmaij,
    D^2+max(Eminus^2,Eplus^2)-sigmaij^2.             (7)

The two physical pair rows retain all owned axes, both directions,
both vertical orders and the exact weak-link upper halfwidth bound.
No owner or chirality is inferred from numerical optimization.

For the additional shared-height test keep both vertical orders for
each selected pair, giving four combinations. Their center-distance
gaps are

    rL=sqrt(max(0,sigmaLP^2-DL^2)),
    rR=sqrt(max(0,sigmaPR^2-DR^2)).

In each combination apply the corresponding height order contractions
(for example P>L implies Pminus>=Lminus+rL and Lplus<=Pplus-rL),
then (6), in that order, twice. Keep the same updated P interval in
both links. Recompute the three interval lengths and the three
height-dependent entries of (7) for each pair. Also restrict its signed
vertical interval to [rij,infinity) or (-infinity,-rij] according to
the chosen order. These are additional necessary restrictions on the
same actual heights, not independently chosen heights for each pair.

## 5. Eliminate U only against these same retained heights

For one of the four updated combinations write Pminus=P0 and let
H=1/sqrt(2)+1/10. The assumed bad U floor gives yU<=H. Put

    G=max(0,H-P0), d0=sqrt(max(0,1-G^2)).

The P/U center disks imply that xU belongs to the union of

    I0=[-ell,min(0,x-d0)],
    I1=[0,min(ell,x-d0)],
    I2=[max(0,x+d0),ell].                           (8)

If P0>H, d0=1 makes all intervals empty since ell+x<1. If G>=1,
the d0=0 formula merely weakens the necessary domain. Shared zero
and distance boundary faces belong to both adjacent intervals.

For I=[v0,v1] define the three maximum horizontal gaps to the retained
originals, and their necessary vertical clearances,

    dP=max(|v0-x|,|v1-x|),    cP=sqrt(max(0,1-dP^2)),
    dL=max(|v0+Z|,|v1+Z|),   cL=sqrt(max(0,1-dL^2)),
    dR=max(|v0-X|,|v1-X|),   cR=sqrt(max(0,1-dR^2)).             (9)

The published wide-main low-side theorem supplies one further original
consequence. If I is nonpositive and Z>=ell, a bad upper central U
forces the original L to have yL>=3/5; otherwise L would be a true low
left-side original above B, making U's floor good. If I is nonnegative,
the same theorem forces yR>=3/5. Here R is always a true side original.
Thus strengthen the corresponding existing shoulder lower height to
3/5. Do not impose the left strengthening in the central-L root.

Call these strengthened bounds LL and RR; retain the same upper bounds
Lplus,Rplus. For each of the four U/L,U/R height orders start with

    Uminus=P0+cP, Uplus=H.

For U>L increase Uminus to at least LL+cL, while for U<L decrease
Uplus to at most Lplus-cL. Apply the analogous original R inequality.
Retain both equality orders whenever a clearance is zero. The maximum
of these four Uplus-Uminus values must be nonnegative for an actual U
in I. Take its minimum with v1-v0, Lplus-LL and Rplus-RR; finally take
the maximum over I0,I1,I2. Call this necessary quantity CU.

For each original L/P,P/R order combination take the minimum of CU,
the three updated interval lengths, and its six updated physical-pair
rows from Section 4. The maximum over all four combinations is ZU.
Every original bad U therefore implies ZU>=0. All copies of L,P,R in
this calculation are the same original squares. In particular a shoulder
cannot use different heights to avoid P and U.

## 6. Fixed roots and exact coverage

There are six live coordinates

    (tP,tL,tR,x,Z,X),

with the first three in [0,1], x in [0,1129/3000], X in [7/10,13/12],
and the three left-coordinate intervals

    [19/60,29/60], [29/60,3/5], [3/5,13/12].

For each of the eight sign triples use all three intervals, giving
24 closed rational roots. The central-left root deliberately omits
the low-side contrapositive even at its boundary Z=ell; this is a sound
weakening. All original angle and shared coordinate faces are retained.

The 21 scalar channels, in their exact code order, are the three height
interval lengths, the five resources (3), six rows (7) for L/P, six
for P/R, and ZU. Every original counterexample has all 21 quantities
nonnegative. A negative upper bound on any channel excludes a complete
box. Exact midpoint children have closed union equal to the parent.

The six-variable final format contains no dummy original main parameter
and no assumed main orientation. Its checker reconstructs these roots
and every midpoint from integer dyadic indices, not floating coordinates.

## 7. Conclusion

The finite forest excludes every original counterexample from Sections
1-6. Hence U's whole floor exceeds 1/10. In the low-P-floor domain,
combining this with the independent ordering theorem shows that every
unselected original upper central square is
strictly higher than P and has good whole floor. It may therefore be
used as the central original in the widened five-square cap when two
distinct high original shoulders have separately been supplied.

This does not turn a central selected L into an unselected U, and does
not eliminate the remaining lower-side or mixed lower-central cases.

## 8. Exact acceptance record

The complete forest has 24 roots, **2,263,632 strict leaves**,
**4,527,240 nodes**, maximum depth **35**, and empty frontier. The
separate directed-integer checker uses 48-bit outward intervals, signed
128-bit intermediate products, integer square-root enclosures, and exact
rational root reconstruction. The final normalized six-coordinate forest
is replayed directly; floating discovery does not certify any leaf.

The least positive replay reserve is **43026615/2^48**. In lexicographic
order of the independent signs (sP,sL,sR), the leaf counts for the three
Z intervals in Section 6 are:

| sP | sL | sR | Central-left interval | Low-side interval | Raised-side interval |
|---:|---:|---:|---:|---:|---:|
| -1 | -1 | -1 | 291 | 560 | 45,234 |
| -1 | -1 | +1 | 1,105 | 9,420 | 703,409 |
| -1 | +1 | -1 | 259 | 550 | 33,100 |
| -1 | +1 | +1 | 904 | 7,218 | 481,963 |
| +1 | -1 | -1 | 256 | 542 | 51,876 |
| +1 | -1 | +1 | 1,223 | 9,482 | 521,697 |
| +1 | +1 | -1 | 289 | 552 | 34,218 |
| +1 | +1 | +1 | 3,205 | 10,834 | 345,445 |

The immutable gzip certificate is `bad_upper_extra_floor_cover.json.gz`.
Its decompression was checked byte-for-byte against the complete exact
replay's original JSON; this lossless packaging does not claim another
arithmetic replay. Both the original and gzip-bound reports are retained.

| Artifact | SHA-256 |
|---|---|
| Delivered gzip | `0cf9e12c82007b36e93b2567e6c512c96f2ea625b22c8f234dcddc45693d8c41` |
| Completely replayed JSON | `2310c4ca47fd55b733abb873d4bd7363dc568b3b5e9c86a1789e31fdb6f46979` |
| Independent C++ checker | `461a05d87dba9aca9b4963e09c4a4d5553c5c9a56825ab36fa0497cf212714c9` |
| Independent wrapper | `6593a160dffecd9679adfca4ad5bea7f5631dbdc959d6c56f56950aa92a928df` |

`DISTINCT_UPPER_EXTRA_FLOOR_INDEPENDENT_REVIEW.md` separately audits the
original-square reduction, all 21 channels, signed owners, finite
contractions, code, and complete tree structure. Six damaged controls
were rejected, including a false whole-root scalar leaf sent directly
to the exact engine. No human or proof-kernel verification is claimed.
