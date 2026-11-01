# A dominant unloaded pair has contact radius less than 23/32

Date: November 1, 2026 UTC. Constructor: root. Complete hand proof,
frozen for independent review.

## 1. Whole original scope

Keep actual interior-disjoint unit squares in one disk of center O and
squared radius at most Q=1105/256. Keep their complete original physical
force and torque certificate, all positive magnitudes, support normals,
actual applications or shared-side means, and all circle coefficients.

Let A,B be unloaded actual units with an original direct positive pair
of magnitude d, normal n from A to B, and common original application p.
At each of A,B distinguish ONE other original positive pair force.
The actual neighbors on those forces have arbitrary degrees and loads;
no equation at them is assumed. Let r_A,r_B be the sums of ALL other
positive magnitudes at the respective endpoints, excluding the direct
pair and the one distinguished force there. Define

    t_A=r_A/d,  t_B=r_B/d,  T=t_A+t_B < 3/40.

**Theorem.** The same actual contact application satisfies

    |p-O| <= sqrt(Q-(2-3T^2/2)^2)+(19/12)T < 23/32.     (1)

All original endpoint degrees, weak positive forces, support owners,
normal-cone boundaries and closed shared-side means are retained. No
radius lower bound, original cut-size assumption, planar drawing or
terminal distinctness is needed for this local theorem.

This improves the complete 11/12 bound in
`SHARP_UNIT_SUPPORT_TORQUE_AND_COMPLETE_ONE_TRANSMITTER_UNICYCLIC_THREE_PORT_EXCLUSION_2026_11_01.md`.
That entire source and its clean review remain unchanged. The improvement
uses the same actual disk points but retains their much smaller errors
in the direction of the original pair normal. No sharper endpoint
estimate is assumed without proof.

## 2. The complete one-endpoint data

At A write z,u,q for its distinguished original pair force magnitude,
outward unit normal and actual application. Set t=t_A and

    delta=|u+n|.

Complete translation, the exact two-vector identity, and the sharp
unit-square support-torque lemma give

    z>=d-r_A>0,
    delta<=t/sqrt(1-t)<=(26/25)t,
    |det(q-p,u)|<=r_A/z<=(40/37)t.                  (2)

The sharp moment bound is valid because for any actual unit square,
any max-v support application a and any point x of that square,
`|det(x-a,v)|<=1`. At a vertex it is a difference of two normal
components times numbers in [0,1]; at an own-axis support side it
is a difference of tangential coordinates in an interval of length
one. Thus the complete sum of remaining moments has absolute value
at most r_A, with every application unchanged. The full current proof
is also printed in Section 2 of the cited source.

Write

    q-p=s u+v Ju,   lambda=1-u dot n,
    k=lambda/(s+1).

The actual support fact p-n in A and maximality of q in direction u
give s>=-u dot n. Since delta<1, lambda>0; hence 0<k<=1. The actual
immediate distinguished neighbor contains q+u. Therefore

    y_A=p+k(q+u-p)=p+lambda u+k v Ju               (3)

belongs to the ORIGINAL containing disk, by its convexity. This point
does not replace a contact, mean or square. Its error from the ideal
pair endpoint is

    epsilon_A=y_A-(p-2n)=lambda u+2n+k v Ju.

The exact identity

    |lambda u+2n|^2=delta^2(4-3delta^2/4)

and (2) imply

    |epsilon_A|<=2delta+|v|
       <=(52/25+40/37)t=(2924/925)t<=(19/6)t.       (4)

The rational comparison is 17544<17575; equality of the zero errors
is allowed at t=0. These are the entire unchanged disk-point data of
the accepted sharper-torque source, restated to expose their exact use.

## 3. The error in the pair direction is quadratic

Put c=u dot n. Since |u|=|n|=1, c=-1+delta^2/2. The original expression
for epsilon_A gives

    epsilon_A dot n
      =(1-c)c+2+k v(Ju dot n)
      =3delta^2/2-delta^4/4+k v(Ju dot n).          (5)

The first displayed scalar is nonnegative and at most 3delta^2/2,
since delta<1. Moreover

    |Ju dot n|=|Ju dot(u+n)|<=delta.

Together with 0<k<=1 and (2), this proves

    |epsilon_A dot n|<=3delta^2/2+delta |v|
      <=[(3/2)(26/25)^2+(26/25)(40/37)]t^2
      <3t^2                                                    (6)

when t>0; both sides are zero when t=0, so the weak bound by 3t^2
always holds. The coefficient comparison is purely rational:

    (3/2)(26/25)^2+(26/25)(40/37)
       =317590/115625 <346875/115625=3.

No transverse sign, angle direction or ownership restriction is needed.
This is the new estimate: the original pair direction loses only a
quadratic amount even though the full vector error is bounded linearly.

Apply exactly the same complete argument at B, with local original
normal -n. Its disk point and error obey

    y_B=p+2n+epsilon_B,
    |epsilon_B|<=(19/6)t_B,
    |epsilon_B dot n|<=3t_B^2.                    (7)

The change from -n to n in the last absolute value is harmless. Both
disk points use the SAME original p and the original distinguished
neighbor at their own endpoint.

## 4. Use the two disk points together

Set

    m=(y_A+y_B)/2,    w=(y_B-y_A)/2.

From (6)--(7), t_A^2+t_B^2<=T^2, and the unchanged normal n,

    w dot n>=2-(3/2)(t_A^2+t_B^2)>=2-3T^2/2>0.

Thus |w|>=2-3T^2/2. The exact parallelogram identity, applied to
the two actual disk points, gives

    |m-O|^2+|w|^2
       =(|y_A-O|^2+|y_B-O|^2)/2<=R^2<=Q.

Consequently

    |m-O|<=sqrt(Q-(2-3T^2/2)^2).                    (8)

The radicand is nonnegative: the preceding identity and inequalities
already exhibit an actual nonnegative quantity bounded by it. Also

    |p-m|=|(epsilon_A+epsilon_B)/2|
       <=(|epsilon_A|+|epsilon_B|)/2<=(19/12)T.    (9)

Combining (8)--(9) proves the nonconstant bound in (1). This uses the
actual pair of disk points simultaneously; it does not square two
independent radial error bounds and lose their directional information.

## 5. Exact uniform constant and zero-residual endpoint

For 0<=T<3/40 the expression 2-3T^2/2 is positive and is greater
than or equal to 6373/3200, with strict inequality at the allowed
upper-bound endpoint. The radicand in (8) is therefore less than

    Q-(6373/3200)^2
      =(44200000-40615129)/10240000
      =3584871/10240000
      <3686400/10240000=9/25.

The integer square is (6400-27)^2=40615129. Thus |m-O|<3/5, and
(9) gives |p-m|<19/160. It follows that

    |p-O|<3/5+19/160=23/32.

At T=0 both errors vanish, so m=p and |p-O|^2<=Q-4=81/256;
the bound is |p-O|<=9/16<23/32. The closed zero-residual case is
therefore included without using a false strict inequality at zero.

This completes the whole hand proof. QED.

## 6. Accepted input and precise limits

The complete input and its separate noncontributor acceptance are

- `SHARP_UNIT_SUPPORT_TORQUE_AND_COMPLETE_ONE_TRANSMITTER_UNICYCLIC_THREE_PORT_EXCLUSION_2026_11_01.md`,
  frozen SHA256 `27f4fa4758eec77ea3ac9b892d0f3bc952cce9f964efff86c4d89a91ec2fbc84`;
- `reviews/2026-11-01/REVIEW_SHARP_UNIT_SUPPORT_TORQUE_AND_COMPLETE_ONE_TRANSMITTER_UNICYCLIC_THREE_PORT_EXCLUSION_2026_11_01.md`,
  frozen SHA256 `856c62de10ef35827f02cd87328a4697496aeb1f1a43197ef449ded4360cebba`.

The whole source was read. Only its local sharp support-torque lemma
and complete disk-point construction are used here; its four-cycle
graph, width-one transmitter, common-side exclusion, lower-radius
window and canonical context are not prerequisites of this local
result. Their complete force-and-torque inputs are reprinted above.

The theorem does not create a dominant pair where none has been proved,
does not discard the remaining positive coefficients, and does not
assert that any other square is automatically far from p. Any caller
must supply both the full original residual ratio and its own genuine
geometric lower bound. The direct unloaded triangle remains open.

A clean full review is required before adoption. All estimates are
hand identities and printed rational comparisons. No mathematical
program, sampled pose, interval certificate, external graph list,
Lean, build, CI or change to a frozen existing source was used.
