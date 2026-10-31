# A dominant unloaded contact pair has a central original application

Date: October 31, 2026. Hand proof; no mathematical program, Lean, or CI.

## 1. Precise statement

Let actual closed unit squares with disjoint open interiors lie in the
closed disk of radius R about O, where R² ≤ Q = 1105/256. Retain one
physical positive contact certificate, including every original force,
its actual application or shared-side mean, and every torque equation.

Let A and B be two selected-circle-unloaded squares with a direct positive
contact of magnitude d > 0, unit normal n from A to B, and common original
application p. At each of A and B distinguish exactly one other positive
force, of magnitude z_A or z_B. Call these distinguished forces exits;
their first physical neighbors, not any compressed fictitious endpoints,
are used below. Let r_A and r_B be the sums of the magnitudes of ALL the
remaining forces at A and B. In particular no small force is deleted.
Assume

    (r_A + r_B)/d < 2/29.                         (1)

**Theorem 1.** Every original common application p of the displayed pair
obeys

    |p| < 15/16.                                  (2)

The statement permits arbitrary remaining degrees, shared contacts,
endpoint-valued means, and real degree-two transmitters on an exit arm.
The centers and orientations of every actual square stay unchanged.

**Corollary 2.** For every actual unit square Z in the same disk,

    dist(p,Z) < 469/240 < 2.                       (3)

Consequently this complete original force feature is incompatible with
any separately proved full-cut inequality dist(p,Z) ≥ 2. This corollary
is a closing mechanism, not an assertion that every module has such a
cut or that the unrestricted nine-square theorem is already proved.

## 2. Elementary support and center bounds

If p is a maximum support point of a unit square in a unit direction n,
then p−n belongs to that square. To see this, write its own coordinates
as [−1/2,1/2]² and n=(a,b), a²+b²=1. A coordinate with a>0 starts at
1/2 and subtracting a stays in the interval; for a<0 it starts at −1/2;
for a=0 it stays unchanged. The other coordinate is identical. The
minimum-support version says that q+n belongs to the square.
These statements include every point of a supporting side.

The farthest corner of a contained unit square with center c gives

    |c|² + |c| + 1/2 ≤ Q.

Indeed its exact squared radius is |c|²+1/2+|c·u|+|c·v|, and the last
two terms sum to at least |c|. Since

    (91/60)² + 91/60 + 1/2 − Q = 31/57600 > 0,

every actual center satisfies |c| < M = 91/60. No nine-body count or
circle-mask premise is needed for this elementary bound.

## 3. One endpoint: the full force and moment equations

Work first at A. Let the distinguished exit have outward unit normal u
and original application q on A. Write z=z_A, r=r_A and t=r/d. The
complete unloaded equation is

    d n + z u + sum_k μ_k v_k = 0,     sum_k μ_k = r.

Thus |d n+z u| ≤ r, |d−z| ≤ r, and z ≥ d−r > 0. With
δ=|u+n|, the exact identity

    |d n+z u|² = (d−z)² + d z δ²

implies

    δ ≤ t/sqrt(1−t) ≤ sqrt(29/27)t < (28/27)t     (4)

when t>0; at t=0 all these quantities vanish. Here t<2/29 by (1),
and (28/27)²−29/27=1/729>0.

Take moments about the ORIGINAL application p. The force on AB has zero
moment about p, so the entire torque equation gives

    z det(q−p,u) = −sum_k μ_k det(q_k−p,v_k).

Every p and q_k lies in A, whose diameter is sqrt(2). Consequently

    |det(q−p,u)| ≤ sqrt(2)r/z
                    ≤ (99/70)(29/27)t.             (5)

The last inequality uses sqrt(2)<99/70 and z/d≥1−t>27/29. For r=0
the determinant is exactly zero. All original torque terms are retained.

Decompose q−p=s u+v Ju. Then |v| has the bound (5). Because p−n lies
in A and q maximizes u on A,

    s = u·(q−p) ≥ −u·n.

Put λ=1−u·n. The exit's immediate actual neighbor contains x=q+u,
by the minimum-support segment lemma. Both p and x lie in the disk.
Moreover s+1≥λ>0. The point

    y = p + [λ/(s+1)](x−p)
      = p + λu + [λ/(s+1)]v Ju

therefore lies in the SAME disk by convexity. This auxiliary point is
used only for a disk estimate; it is not asserted to belong to a square
or to create a new physical contact.

Since u·n=−1+δ²/2, direct expansion gives

    |λu+2n|² = δ²(4−3δ²/4) ≤ 4δ².

Hence (4)–(5) imply

    |y−(p−2n)| ≤ 2δ+|v|
      ≤ [56/27 + (99/70)(29/27)]t
       = (6791/1890)t < (18/5)t                    (6)

for t>0, and the error is zero when t=0. The simple rational comparison
is 6791<6804. This proves the claimed error estimate without evaluating
an angle, searching a pose, or neglecting a positive coefficient.

## 4. Combine both endpoints

Apply the same proof at B, with its pair normal −n and the SAME original
application p. It supplies y_A,y_B in the disk and nonnegative errors
ε_A,ε_B such that

    |y_A−(p−2n)| ≤ ε_A,
    |y_B−(p+2n)| ≤ ε_B,
    ε_A+ε_B ≤ (18/5)(r_A+r_B)/d < 36/145 < 1/4.

The last strict comparison is 144<145. Therefore

    |p−2n| ≤ R+ε_A,       |p+2n| ≤ R+ε_B.

Squaring, adding, and dividing by two gives

    |p|²+4 ≤ Q + R(ε_A+ε_B) + (ε_A²+ε_B²)/2
            < Q + R/4 + 1/32.

Use R<25/12, which follows by squaring from Q<625/144. Then

    |p|² < Q + 25/48 + 1/32 − 4
           = 667/768
           < 675/768 = (15/16)².

This proves Theorem 1 with a positive rational reserve of 1/96 in the
last comparison. No equality configuration is lost by a limiting force.

## 5. Point-to-square consequence and scope

Every actual unit square Z contains its closed center disk of radius 1/2.
If |p−c_Z|≥1/2, its nearest point in that smaller disk yields

    dist(p,Z) ≤ |p−c_Z|−1/2
                < 15/16 + 91/60 − 1/2 = 469/240.

If |p−c_Z|<1/2, then p belongs to Z and the distance is zero. Thus (3)
holds in all cases, including when Z is one of the displayed squares.

The theorem is local to an actual original pair and its FULL two stars.
An algebraically dominant sum of several different pair forces does not
by itself supply (1). In particular a caller must first prove that one
direct exit-bearing pair dominates, preserve its two original applications
as one common p, and establish any claimed point-to-terminal lower bound
from a genuine full unloaded cut. Arbitrary multi-exit hubs are not
silently assigned only one exit.

This manuscript contains a complete hand derivation. It has not itself
changed a canonical case flag or claimed a formal verification.
