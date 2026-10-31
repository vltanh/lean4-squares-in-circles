# Independent full review: four-sevenths whole-unit support cap

Date: October 28, 2026 UTC. Reviewer: sole-UT continuation.

**Disposition: PASS at the exact hashes below.** I did not author or
contribute to the new cap proof. I independently read its entire source,
read the entire cited older roof source, checked the whole geometric
argument and both orientation endpoints, and verified every displayed
exact rational reserve. This review is separate from root's review and
does not rely on its conclusions.

## 1. Exact reviewed sources

| Source | SHA256 |
| --- | --- |
| UNIT_SUPPORT_CAP_FOUR_SEVENTHS_UNIFORM_BOUND.md | 0b7e13116e4da9136d9cb55ed73da22005b59ec74c3a713f675ddb5c1a33c606 |
| UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md | 2b90b565591b3c9bbc30c2c1af48cf117771b96bbc58ad81441f9e99497067d6 |

The second file's unchanged scope is the older shared-root roof chart,
its full actual H3 support deduction, and the original North-XA bound.
The new source does not modify its bytes or claim to replace its other
proofs. This review makes no new full transitive audit claim about the
older root and selection prerequisites.

## 2. Whole geometric domain and orientation cover

The theorem concerns an actual unit K contained in D_(sqrt(1105/256))
and wholly in x<=-1. The selected highest corner admits the two actual
inward axes (-c,-s),(s,-c), with c,s>=0 and c^2+s^2=1. This includes
c=0 and s=0: for a horizontal highest side one chooses the endpoint
with the indicated two inward directions. Both the highest height and
the whole square are retained.

The actual extreme horizontal corners give x+s<=-1 and width c+s.
Containment gives the lower horizontal support at least -sqrt(Q), so
c+s<=sqrt(Q)-1<13/12. The concavity argument on the entire interval
where c,s>=1/10 correctly forces min(c,s)<1/10. No intermediate angle
or possible side-support equality is omitted.

The highest-corner chart is a geometric description of the actual unit,
not a conversion of an original contact mean into a corner. There are
no force or load premises to be checked in this part of the proof.

## 3. Complete s-small comparison

Assuming y>=4/7 and 0<=s<1/10, the corner Z+u has negative horizontal
coordinate at most -(1+s+c) and positive height at least 4/7-s.
Thus squaring these coordinate bounds is legitimate. The inequality
c>=1-s^2 is valid on the full interval. Independent expansion gives

    (2+s-s^2)^2+(4/7-s)^2
      =4+16/49+s*(20/7-2s-2s^2+s^3).

The final parenthesis is strictly positive on [0,1/10), while the
constant 4+16/49 already exceeds Q. Therefore the aligned endpoint
s=0 is excluded by the same strict radius reserve rather than being
lost by division by s. This proves y<4/7 throughout this domain.

## 4. Complete c-small comparison

For 0<=c<1/10, s>99/100 and the actual highest corner has x<-199/100.
Containment therefore gives |y|<3/5. This conclusion does not require
y to be positive.

On the alleged closed subinterval c>=1/20, the strict bound
s>159/160 gives the actual corner Z+u both x<-327/160 and
y<-63/160. Both coordinates have their needed negative signs before
squaring. Its squared norm exceeds Q, so that entire subinterval is
impossible, including c=1/20.

On the remaining 0<=c<1/20, one has s^2>399/400 and hence s>399/400.
The actual highest corner has x<-799/400. Its norm is too large if
y>=4/7, with the stated strictly positive reserve. The endpoint c=0
is included and the proof uses no division by c. Reflection in the
original horizontal axis then supplies min_K y>-4/7 for the entire
closed body. Convexity, or maximization on the actual corners, passes
the extreme-height conclusions to every point of K.

## 5. Invariant statement and actual roof caller

The orthogonal frame x=-n.z, y=f.z preserves the circle origin and
square geometry. Thus an actual whole-unit minimum support n.z>=h>=1
meets the theorem literally. The stated invariant conclusion follows
without translating the unit or replacing it by its supporting line.

For M=(-s,-t), with s,t>=0 and s^2+t^2=1, the original vertical
coordinate is t*(e.z)+s*(f.z), where e=(s,t), f=(-t,s). The proof keeps
e.z<=-1. If s>0, the strict transverse estimate gives z_y<4/7;
if s=0, z_y<=-1 gives the stronger result directly. Both axis endpoints
and h=1 are therefore present.

I checked the older roof source's Section 2 chart and Sections 3--4
before accepting the stated substitution. In that actual shared-XH
domain H is the full unloaded H3 with its original East HX force.
The real H-X-A triangle and weak HA moment leave N=East, North, or
strict Northeast. The complete positive H3 force makes the HC normal
West in the East case, or strict Southwest otherwise. In the first
case its actual minimum support at C is 1-h>1. In the second, the
unchanged weak HC moment gives q0>=A0*kappa and hence

    h_C=(A0+q0*kappa)/sqrt(1+kappa^2)
         >=A0*sqrt(1+kappa^2)>1,

with A0=1-h>1. This is the required whole-unit minimum-support
orientation. It is not inferred from zero load or from the position
of a single point.

For North-XA, the actual A has min_A y>=1-b>89/120. Combining it with
the new strict whole-C cap gives a gap strictly greater than
89/120-4/7=143/840. This uses no B equation. It therefore applies to
both stated roof AC and ABC shared-root domains at their original
premises, while preserving unloaded B in AC and loaded B in ABC.
No reserve-one transmitter, fake circle clearance, or shortened
loaded A3/C2 equation is introduced. The fan's H4 is outside this
literal old H3 caller, as the old source already states.

## 6. Exact arithmetic checked independently

| Displayed comparison | Exact positive difference |
| --- | --- |
| (25/12)^2-Q | 55/2304 |
| 99-(59/6)^2 | 83/36 |
| 4+16/49-Q | 127/12544 |
| (199/100)^2+(3/5)^2-Q | 591/160000 |
| 99/100-(159/160)^2 | 63/25600 |
| (327/160)^2+(63/160)^2-Q | 199/12800 |
| (799/400)^2+(4/7)^2-Q | 4/30625 |
| 89/120-4/7 | 143/840 |

I also checked the polynomial expansion in Section 3. Exact Fraction
arithmetic was used only to verify these printed identities and
reserves. The written continuous orientation cover supplies the proof;
there is no numerical square-pose certificate.

## 7. Acceptance boundary

The complete proposed support theorem, its invariant consequence and
the limited actual roof strengthening all pass. The source correctly
claims zero new original fine or coarse credit and does not exclude
the remaining roof configuration merely from vertical separation.

All original units, circle masks, actual support means, true degrees
and full equations are retained wherever a caller uses them. No Lean
compilation, CI, workflow, sampled pose, normal reselection, shared
ledger edit or remote write was performed in this review.
