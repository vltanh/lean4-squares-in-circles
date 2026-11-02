# No original lower-side extra in the weak-middle low-floor domain

November 2, 2026. **Complete physical hand/table proof with full independent
exact replay: all128 fixed roots,27,552,502 strictly rejected leaves and no
frontier.** Independent physical/formula review: PASS. No Lean, Lake or CI.

## 1. The original caller and target

Keep all nine original physical unit squares of the fixed `010/11`
predicate in the closed disk Q=1105/256. The main originals are A,B,C,D;
the selected outsider cone triple is L,P,R. The outer main comparisons
are actual, the middle main and both selected short comparisons are weak,
and all five marked center comparisons are horizontal cone comparisons.
Use the accepted upward routing so P is above B,C, L is above B, and
R is above C. Suppose

    yP-hP <= 1/10.                                    (1)

The target conclusion is:

> No original outsider in the right closed side strip can be below C,
> and no original outsider in the left closed side strip can be below B.

This statement concerns the original side units, not substitutes. The
selected side endpoints are already above their assigned mains by routing;
any hypothetical lower side unit is necessarily one of the other originals.
No selected short comparison is transferred to it.

Reflect horizontally and reverse both marked chains together so x=xP>=0.
Put zL=-xL and zR=xR. The original centered half-unit disks and the original
cones give each selected horizontal gap at least 1/sqrt(2)>707/1000.
Consequently

    0 <= x <= 1129/3000,   19/60 <= zL <= 13/12,
    7/10 <= zR <= 13/12.                              (2)

Let S be a hypothetical lower-side original, M its assigned original inner
main, epsilon the sign of its side (left=-1,right=+1), and sM its global
folded chirality. Keep the original halfwidth h=hM. The two completed
lower-side inputs give

    1/2 <= h < 31/50,      yM > T(h),                 (3)

where

    f(h)=-(2/3)h+max(0,min((h-1/2)/6,(27/50-h)/3))+1/400,
    F+(h)=-331/1000-(9/20)(h-1/2)-(7/4)(h-1/2)^2,
    F-(h)=-1/3,
    T(h)=max(f(h),F_(epsilon*sM)(h))                    if h<=57/100,
    T(h)=max(f(h),F_(epsilon*sM)(h),3h-211/100)          if h>=57/100.

Both closed pieces are valid at h=57/100. The sources are
`LOWER_SIDE_MAIN_PAIR_HEIGHT_BRIDGE.md` and
`SIGNED_LOWER_SIDE_HEIGHT_ENVELOPE.md`; the former uses the independently
established yB,yC<-1/4 and the other original main's full endpoint budget.
It narrows only the assigned main M. It does not narrow the other main by
an unsupported transfer.

## 2. Original frames, circle heights and endpoint resources

For j=L,P,R retain independent slopes tj in [0,1] and chiralities sj:

    aj=1/sqrt(1+tj^2), bj=tj*aj,
    hj=(aj+bj)/2, kj=(aj-bj)/2.

For M set g=1/(4h), eta=h+g-1, k=sqrt(1/2-h^2), a=h+k, b=h-k.
Its original coordinate band is

    [g-1/60,61/60-h]       if epsilon=+1,
    [h-61/60,1/60-g]       if epsilon=-1.             (4)

Use all four original circle corners to bound each original selected
height from above. In explicit signed form, for nonnegative z,

    U+(z,H,K)=min(sqrt(Q-(z+K)^2)-H,sqrt(Q-(z+H)^2)+K),
    U-(z,H,K)=min(sqrt(Q-(z+H)^2)-K,sqrt(Q-(z-K)^2)-H).

Then Pplus=min(hP+1/10,U_sP(x,hP,kP)), Lplus=U_-sL(zL,hL,kL),
and Rplus=U_sR(zR,hR,kR). The independent checker reconstructs all four
corners; the two displayed corners are sufficient for the producer.

Retain each original shoulder toll

    tauj=max(2bj,6bj-(27/2)(1-aj)).

The original endpoint pairs and adjusted main span supply the necessary
lower endpoint contributions

    AL=max(59/60,157/184+(27/92)(zR-hR)+tauR/46)+eta,
    AR=max(59/60,157/184+(27/92)(zL-hL)+tauL/46)+eta.

The following five rows must be nonnegative:

    61/60-AL, 61/60-AR,
    1+hL+hR-zL-zR-(tauL+tauR)/(27/2)-(92/27)eta,
    hL+451/810-zL-(92/27)eta-tauL/(27/2),
    hR+451/810-zR-(92/27)eta-tauR/(27/2).            (5)

These are the already reviewed universal pair resources, with only
eta<=V retained from the full two-main budget. They do not assume a good
central floor or a high shoulder and do not invoke the final cap.

For a raised shoulder z>=3/5 and its matched lower endpoint contribution
Astar, define

    c=max(4421/12000+(32/9)eta,
          1-sqrt(Q-(min(Astar,61/60)+29927/30000)^2)),
    q=503/480-z.

Its original endpoint contains the corresponding raised inset rectangle.
The exhaustive rectangle/original-square owner calculation gives

    Y >= c+H-max(0,t*(K+q))                         for local sign +1,
    Y >= c+H-max(0,(q-K)/max(t,t0))                 for local sign -1.  (6)

The local sign is -sL on the left and sR on the right. Use t0=1/16 for L
and 1/4 for R. The original sign/zero-angle complements are covered by
the established inequalities k(1/16)>503/480-3/5 and
k(1/4)>503/480-7/10. The min in c extends the scalar formula outside the
necessary domain AL,AR<=61/60 without changing its physical value.

Use (6) for R throughout and for L when zL>=3/5. On the other closed
left root zL<=3/5 one has |xL-xB|<6/25 from the full wide-main bands.
The original center disks then give yL-yB>97/100, since
1-(6/25)^2-(97/100)^2=3/2000>0. Since yB>-6/5, the valid weaker bound
Lminus=-1/4 applies on that entire root. This step also covers a selected
L whose center is in the central strip.

## 3. The original assigned main raises the same original P

For an actual pair of signed frames f,g, its exact common support on any
genuine owned axis is

    sigma(f,g)=(1+|af*ag+sf*sg*bf*bg|
                 +|sg*af*bg-sf*bf*ag|)/2.

It is at least1+|hf-hg|. For M/P let dx range over x minus the original
main band (4), with endpoints dlo,dhi and D=max(|dlo|,|dhi|). The actual
horizontal gap is below9/10; P is above M. Consequently every possible
actual separator is one of the four upward original owners

    n=(sM*a,b), (-sM*b,a), (sP*aP,bP), (-sP*bP,aP).

Define

    Cphysical=min_n [sigma(M,P)-max(nx*dlo,nx*dhi)]/max(ny,1/40),
    Cinset=g+min(hP,
       min over P's two upward owners
        [1/2+g*|nx|-max(nx*dlo,nx*dhi)]/max(ny,1/40)),
    Cradial=sqrt(max(0,sigma(M,P)^2-D^2)).

For the physical owner, sigma>=1 and |nx|<=1, so its numerator is
at least1-D>1/10. For the inset owner, its numerator is at least
1/2-(D-g)>1/10. The checker may therefore clamp both lower numerators
to1/10. A positive denominator floor only weakens these positive-ratio
bounds. The main inset has no horizontal or downward separator because
D-g<2/5. These are the
complete signed physical, inset and center-distance consequences already
reviewed for the original 21-row profile reduction. They preserve the
same original M side and chirality. Thus

    Pminus=T(h)+max(Cphysical,Cinset,Cradial).           (7)

Intersect the three selected height intervals using only the two original
cones. With DL=zL+x and DR=zR-x, the following ordered updates are valid:

    Pminus=max(Pminus,Lminus-DL,Rminus-DR),
    Pplus=min(Pplus,Lplus+DL,Rplus+DR),
    Lminus=max(Lminus,Pminus-DL), Lplus=min(Lplus,Pplus+DL),
    Rminus=max(Rminus,Pminus-DR), Rplus=min(Rplus,Pplus+DR).

They never change an original frame or choose independent copies of P.

## 4. The first 21 necessary rows

The first rows are the three height-interval widths, 1/30-eta, and the
five endpoint rows (5). For each original selected pair i->j use its
positive horizontal gap D and the actual height bounds to define

    Elo=max(jminus-iplus,-D), Ehi=min(jplus-iminus,D).

The six further rows for that pair are

    Ehi-Elo, D-707/1000, hi+hj-D, D-gi-gj,
    max over all four owned axes n and E in {Elo,Ehi}
          |nx*D+ny*E| - sigma(i,j),
    D^2+max(Elo^2,Ehi^2)-sigma(i,j)^2.

Each is necessary. The weak-bit boundaries are retained outward and no
vertical order between P and either shoulder is prescribed. Both signs
of every genuine original owner are present.

## 5. The two original selected owners share one P height

There is a useful stronger check within each interval box. For a horizontal
cone comparison, a true separating owner can be normalized to point into
the positive x half-plane: rotating a left-pointing owned axis by a right
angle toward the cone does not decrease its center projection and leaves
both square supports unchanged. The complete normalized owner list is

    (ai,si*bi), (bi,-si*ai), (aj,sj*bj), (bj,-sj*aj).   (8)

For each owner, its original inequality gives a necessary interval of
allowed E=yj-yi after intersecting the original cone and height bounds.
A zero vertical component either satisfies its horizontal inequality or
excludes that owner. For a positive component divide its necessary lower
numerator by its upper component; for a negative numerator use the lower
positive component. If the denominator interval reaches zero and the
numerator's lower bound is nonpositive, impose no extra bound. All these
operations only enlarge each actual owner's feasible E interval.

For an L/P owner interval [eL-,eL+] and a P/R owner interval [eR-,eR+],
the same actual P height must belong to

    [Pminus,Pplus]
      intersect [Lminus+eL-,Lplus+eL+]
      intersect [Rminus-eR+,Rplus-eR-].                (9)

A pair with an empty E interval is excluded. If all16 owner pairs in(9)
have a strictly empty intersection, the whole parameter box is excluded.
This is one terminal type, numbered21 with zero-based indexing.

## 6. Positive-weight cancellation preserves the actual M/P owner

The final terminal retains the same actual upward M/P normal n in both
selected shoulder checks. For an original shoulder S=L or R, direct its
original selected-pair normal m from P toward S. Its physical inequality is

    mx*(xS-x)+my*(yS-yP) >= sigma(P,S),

and the original M/P inequality is

    nx*(x-xM)+ny*(yP-yM) >= sigma(M,P), ny>=0.

When my>=0, multiply the second inequality by my and the first by ny,
then add. The same actual yP cancels exactly:

    (my*nx-ny*mx)*x + ny*mx*xS - my*nx*xM
      +ny*my*(yS-yM) >= my*sigma(M,P)+ny*sigma(P,S).    (10)

All multipliers are nonnegative. Bound the right shoulder height yS by
its original circle/cone upper bound, yM from below by T(h), and the same
xM by (4). This yields a necessary nonnegative row for the chosen owners.
It is independent of choosing a new P height for each pair.

If n and m are both P-owned, their determinant in(10) is exactly0 or±1,
since P's two original axes are orthonormal. The checker uses that exact
identity, including aligned faces. For other owner pairs it retains the
complete original signed determinant with outward arithmetic.

When my<0 the usual original P/S projection row is retained instead of
using an impermissible negative multiplier. In every case the original
projection row is also required. For each of the four actual M/P owners,
require its own M/P projection row and at least one of the four normalized
owners on each selected side. If every M/P owner fails this necessary
combination, the box is excluded. This is terminal22. The same actual M
chirality, P frame and P height occur throughout(7)--(10).

## 7. Fixed finite coverage and acceptance state

The seven continuous variables are

    (tP,tL,tR,x,zL,zR,h).

The fixed roots are the Cartesian products of the ranges(2), the three
closed slope ranges[0,1], the two left pieces[19/60,3/5] and[3/5,13/12],
and the two main-width pieces[1/2,57/100] and[57/100,31/50]. Keep all32
independent choices of(sP,sL,sR,sM,epsilon). Thus there are exactly128
closed roots, including every original aligned frame and every shared face.
Their lexicographic order is the five signs, then width piece, then left piece.

`discover_lower_side_coupled.cpp` is an untrusted floating producer. It
records only exact midpoint split coordinates and selected rejection rules.
A complete accepted tree must retain both children of every split, reject
every leaf strictly, and leave no frontier. The immutable archive
`computer_assisted/lower_side_no_extra_forest.zip` contains128 unchanged
per-root gzip files,128 unchanged raw exact replay reports and128 unchanged
discovery records. It uses ZIP_STORED, so the gzip certificate bytes are
identical to those independently replayed before packaging.

The standalone `verify_lower_side_exact.cpp` reconstructs each rational
root, every dyadic midpoint, all23 necessary rules and every original
signed frame. It imports no producer code. Its directed integer kernel,
with48-bit fractional endpoints and128-bit exact products, is inherited
from the previously audited independent main-height checker; the new
physical formulas and root union are reconstructed separately. Radicals
are bracketed by integer square roots with checked squared endpoints.
The standard-library byte-binding wrapper `replay_lower_side_roots.py`
checks complete per-root structure, counts and hashes. A final forest
acceptance must include all128 distinct fixed roots exactly once.

### Complete fixed table

The following entries count terminal leaves, not sampled configurations.
“Narrow” means h in[1/2,57/100], “wide” means h in[57/100,31/50],
“low” means zL in[19/60,3/5], and “raised” means zL in[3/5,13/12].
Every entry is a complete binary tree whose rational root is reconstructed
by the independent checker.

| `(sP,sL,sR,sM,epsilon)` | narrow h, low zL | narrow h, raised zL | wide h, low zL | wide h, raised zL |
|---|---:|---:|---:|---:|
| `(-,-,-,-,-)` | 36,229 | 3,064,446 | 24,854 | 804,543 |
| `(-,-,-,-,+)` | 105 | 437 | 150 | 689 |
| `(-,-,-,+,-)` | 12,729 | 219,955 | 2,893 | 25,712 |
| `(-,-,-,+,+)` | 411 | 6,652 | 323 | 11,341 |
| `(-,-,+,-,-)` | 3,071 | 2,162,706 | 2,547 | 169,441 |
| `(-,-,+,-,+)` | 65 | 274 | 79 | 377 |
| `(-,-,+,+,-)` | 1,350 | 79,197 | 714 | 10,175 |
| `(-,-,+,+,+)` | 159 | 5,386 | 94 | 8,225 |
| `(-,+,-,-,-)` | 16,949 | 314,830 | 10,309 | 251,218 |
| `(-,+,-,-,+)` | 59 | 423 | 88 | 631 |
| `(-,+,-,+,-)` | 6,515 | 88,184 | 1,711 | 15,903 |
| `(-,+,-,+,+)` | 188 | 4,091 | 142 | 5,508 |
| `(-,+,+,-,-)` | 1,995 | 96,963 | 1,488 | 51,885 |
| `(-,+,+,-,+)` | 41 | 263 | 55 | 349 |
| `(-,+,+,+,-)` | 964 | 27,226 | 497 | 6,103 |
| `(-,+,+,+,+)` | 90 | 2,616 | 57 | 3,838 |
| `(+,-,-,-,-)` | 3,888 | 59,059 | 1,529 | 25,736 |
| `(+,-,-,-,+)` | 104 | 10,275 | 37 | 394 |
| `(+,-,-,+,-)` | 3,354 | 44,470 | 1,588 | 13,683 |
| `(+,-,-,+,+)` | 184 | 94,099 | 219 | 35,545 |
| `(+,-,+,-,-)` | 4,174 | 159,842 | 1,670 | 112,042 |
| `(+,-,+,-,+)` | 154 | 400,039 | 43 | 527 |
| `(+,-,+,+,-)` | 4,999 | 104,064 | 3,429 | 36,850 |
| `(+,-,+,+,+)` | 343 | 10,105,270 | 429 | 1,646,008 |
| `(+,+,-,-,-)` | 5,096 | 38,946 | 2,134 | 20,867 |
| `(+,+,-,-,+)` | 190 | 8,564 | 55 | 580 |
| `(+,+,-,+,-)` | 4,509 | 29,433 | 2,288 | 11,722 |
| `(+,+,-,+,+)` | 347 | 54,672 | 460 | 34,653 |
| `(+,+,+,-,-)` | 7,337 | 88,464 | 3,470 | 70,558 |
| `(+,+,+,-,+)` | 419 | 240,325 | 68 | 847 |
| `(+,+,+,+,-)` | 8,422 | 61,842 | 5,728 | 27,280 |
| `(+,+,+,+,+)` | 1,804 | 5,403,470 | 2,596 | 974,801 |

The complete forest has128 roots, **27,552,502 leaves**,55,104,876 total
nodes, maximum total split depth63, and zero unresolved leaves. Every leaf
has a strictly negative exact upper bound. The smallest positive rejection
reserve is

    3357953 / 2^48 > 0,

attained in root125. Terminal21 supplies18,249,807 leaves and terminal22
supplies12,334; all23 terminal counts are recorded in the manifest and
aggregate replay report. Counts alone are not the certificate: the archive
retains every split and leaf tag, and each raw report binds the exact bytes
that were replayed.

### Separate replay, source binding and controls

`lower_side_no_extra_independent_replay.json` aggregates the128 completed
independent exact replays. `lower_side_no_extra_manifest.json` pins all128
compressed and uncompressed certificates, all128 raw replay reports, the
raw discovery records, the final exact source and the original byte-binding
wrapper. The full replay used the final checker source below:

    checker source SHA256:
    5211852f38acfa94c3d80d29559042bcb346d9d1751c0c5015152fc0ecc6a424
    replayed executable SHA256:
    cd9e51c1328120fe1e45a1fd5c533eca5fa9f172a906fb883b59f0ea729593c0
    immutable archive SHA256:
    a76663f6e8d46af76b5820197e68dacf6ed17deb75792d6cb93d5e6223cb3d90

The entire delivered C++ source was compiled again with
`g++ -O3 -std=c++17`; the resulting executable was byte-identical to the
one used for every full replay. This is recorded by
`lower_side_no_extra_build_binding.json`, with a repeatable binding script.
The producer and its portable driver are supplied separately; neither is
imported by an exact checker.

Eleven deliberately invalid streams were rejected by the final exact
binary. They include false whole-root height, shared-P and cancellation
terminals, unknown axes/rules, omitted children, truncated/trailing bytes,
invalid counts and out-of-range roots. Their exact payload identities and
rejection reasons are in `lower_side_no_extra_negative_controls.json`;
`check_lower_side_forest_controls.py` repeats them.

A fresh complete replay from only the delivered archive, manifest, wrapper
and exact C++ source is available with:

```sh
python3 computer_assisted/verify_lower_side_forest.py --jobs 2
```

The wrapper compiles the delivered source and checks every leaf of every
fixed root. Its optional `--identities-only` mode instead checks the archive,
the preserved raw reports and their aggregate. The saved
`lower_side_no_extra_archive_identity_check.json` records that packaging
check. It is explicitly not a second arithmetic replay.

The separate physical and code review is
`NO_LOWER_SIDE_INDEPENDENT_PHYSICAL_CODE_REVIEW.md`. It checks the original
frame/root union, all23 necessary channels, zero-angle owner alternatives,
the shared P height, positive-weight cancellation and exact determinant
identities. These physical reductions plus the complete exact finite table
establish the target. No Lean kernel or external CI acceptance is asserted.

## 8. Original-domain conclusion

A hypothetical original lower-side S supplies its actual assigned M,
side, chirality and h, and hence(3). The same actual selected originals
supply one point in one of the128 complete roots and every necessary
row or owner alternative above. A complete strictly rejected forest is
therefore a contradiction. Horizontal reflection covers the other side.
No statement is made here about an upper opposite-side extra or a lower
central original; they remain physical cases for the complete mask assembly.
