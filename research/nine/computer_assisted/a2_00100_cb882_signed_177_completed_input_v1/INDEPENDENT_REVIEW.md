# Independent mathematical review of the signed Cb882 domain-177 terminal

2026-11-05: **ACCEPTED in the stated conditional strict-radius scope**.
The independently reconstructed scalar certificate proves the required
inequality on all 32 continuous cases. The physical BI and signed-ID
reductions, cap/height transport, small-B bound and literal guard attachment
to the entire frozen pending domain 177 are valid. I found no defect.

I additionally checked the polynomial equality faces exactly. They imply
that every physically possible equality case has B, I and D aligned. Together
with the stated original strict-CD premises this also supplies a closed-Q
exclusion, as explained below. The author's frozen manuscript only claims
the strict-radius result; it is not silently rewritten here.

This review is independent of the discovery producer and author. I did not
import or read the producer code to reconstruct the polynomials. The existing
accepted physical pair caps are reused as theorems. This report grants no
whole-original or mask credit: pending domain 177 is one conditional region
of original `negative-b882d8ade0cf9ea0`, and its actual ancestry/cover consumer
must still replay the new terminal before attaching it to the larger proof.

## Exact reviewed inputs

Paths in this table are under `research/nine/.runs/c_continue/`.

| Input | SHA256 |
| --- | --- |
| `signed_177_scalar/MANIFEST.json` | `471b05df37d0fdc44a3c1e899d560d8cb2158c8c9ab8976f2fc95fd72b519ae1` |
| `signed_177_scalar/HAND_PROOF.md` | `5ac51864d59ce7ddca77909bfc0e2cf565bd8c3ec2c1ab108036b7a3681acf6e` |
| `signed_177_guard.py` | `f776ff343c880717b7c1a439ba6c8f4790dd545d1b6dc31d3dd77c386a92cee3` |
| `SIGNED_177_TERMINAL.json` | `67eb4ccdef2e100e41d2973b0d6bd3c7e8d855129059a9d2a0eeb79d9fc51666` |
| `SIGNED_177_ATTACHMENT.json` | `167f9e5d6e0860b5ad71f3d6cc68cc3e9109bb4bf8ffd5b895f0ca5f749b7a69` |
| Frozen `cb882_abid_138/MANIFEST.json` | `de9647b32a2a138d24177e19ce4a9b414cdb143c07617b2eeb2f0f688043f25e` |

The independent scalar JSON records the individual hashes of all 32 domain
files. The frozen frontier manifest is under
`extracted/frozen_c_finite_frontiers_v2/covers/`. The accepted inherited
`opposite_boundary/HAND_PROOF.md` used for pair inputs, caps and the original
CD join is SHA256
`db830ffbebdc807b0e05f78766e0a0509d11418be31b9a7ef0623b212328831a`.

## Physical support reductions and the complete case cover

The same nine original unit squares remain in the closed disk with pairwise
disjoint interiors and all original marked predicates. The used row is
A,B,I,D; H is retained without a new predicate. Actual AB gives the necessary
horizontal projection gap `dAB >= hA+hB`.

For BI, the inherited order and `|vBI|<=1/16` imply
`dBI>|vBI|` from the incircle inequality `dBI^2+vBI^2>=1`. A separating normal
with nonpositive horizontal component has projection at most `|vBI|<1`,
below its support sum, so cannot be the physical separator. For its actual
owner o, either forward axis has projection at most
`alpha_o*dBI+beta_o*|vBI|`, because `alpha_o>=beta_o` and `dBI>|vBI|`.
The support sum is invariant under the owner's quarter-turn. Therefore

`LBI = RBI/alpha_o - beta_o/(16*alpha_o)`

is a lower bound for that same owner's horizontal gap. Both owners and both
physical axes have been retained; there is no shallow-axis assumption.

For ID, `dID>=0` and `1/16<=vID<=1/4` likewise exclude every separator with
nonpositive horizontal component. Each owner's two forward normals are
`(alpha,s*beta)` and `(beta,-s*alpha)`. For a fixed normal, maximizing its
vertical contribution uses `v*=1/4` when its vertical component is nonnegative
and `v*=1/16` otherwise. Thus

`LID = (RID - n_y*v*)/n_x`

is a necessary lower bound. A steep owner with beta zero is vertical and
cannot separate: its projection is at most `1/4`, while `RID>=1`. This case
is excluded physically before dividing. All other denominators are positive.

The scalar cover includes both BI owners, both ID owners, both ID axes, and
both signs of B and I, with D nonpositive. These are exactly
`2*2*2*2*2=32` cases. Zero-angle faces are included in the sign alternatives;
the impossible steep-zero case is handled separately as above.

## Independent rational polynomial reconstruction

For j=B,I,D write `z_j=s_j*x_j=tan(theta_j/2)`. The physical domain lies in
the certified rational box

`0<=xB<=1/23`, `0<=xI,xD<=5/12`.

The guard `|tan(thetaB)|<=2/23` implies the B bound because
`x=t/(sqrt(1+t^2)+1)<=t/2`; even at the guard's nonzero upper endpoint the
half-angle bound is strict. For I,D, `sqrt(2)-1<5/12`, since
`(17/12)^2-2=1/144>0`. Every physical point is therefore strictly below all
three enlarged global upper faces. Enlarging the box supplies a stronger
arithmetic obligation and does not replace physical canonical assumptions.

I reconstructed the features directly from

```text
alpha_j = (1-x_j^2)/(1+x_j^2)
beta_j  = 2*x_j/(1+x_j^2)
h_j     = (1-x_j^2+2*x_j)/(2*(1+x_j^2))
Rij     = ((1+z_i*z_j)^2 + (1+z_i*z_j)*abs(z_i-z_j))
          / ((1+x_i^2)*(1+x_j^2)).
```

The scalar target is
`F = hB-hD+T_D-2+LBI+LID >= 0`.
Each leaf supplies epsilonBI, epsilonID in `[-1,1]` and tau in `[0,1]`.
I checked their dyadic integer encodings and ranges. Replacing each absolute
value by `epsilon*(z_i-z_j)` lowers the support term because
`1+z_i*z_j>0`. Interpolating the two tolls with tau lowers their maximum.

The D base term and increment are independently expanded as

```text
-hD+Tbase_D = (-23-38*xD+23*xD^2)/(46*(1+xD^2))
Tsharp_D-Tbase_D = (143*xD-943*xD^2)/(368*(1+xD^2)).
```

For shallow ID the transverse loss is
`-s_o*2*x_o*v*/(1-x_o^2)`, using `v*=1/4` for positive s and `1/16`
for negative s. For steep ID it is
`+s_o*(1-x_o^2)*v*/(2*x_o)`, using `v*=1/4` for negative s and
`1/16` for positive s. The BI loss is `-2*x_o/(16*(1-x_o^2))`.
These distinct signed expressions were reconstructed, not read from saved
polynomial coefficients.

Let `D0=product_j(1-x_j^4)`. Multiplication by `5888*D0`, or by
`5888*2*x_IDowner*D0` for steep ID, clears the rational features. Every factor
is positive on the appropriate physical case. The reconstructed polynomial
has degree at most six in each variable; its dyadic-scaled coefficients are
integers. Numerical margins and LP outcomes in the candidate JSON are ignored.

For each closed box I independently applied the exact tensor Bernstein
transformation of degree six. In one variable its matrix entry is

```text
T[k,e] = sum_{m=0..min(k,e)}
         binom(e,m)*l^(e-m)*(u-l)^m*binom(k,m)/binom(6,m).
```

All 343 coefficients on every leaf are nonnegative. There are 34 leaves and
36 total nodes. Thirty cases use their whole root box; two cases each split
the I half-angle once into both closed halves. I checked the complete binary
prefix cover, distinct domain identities, every node/leaf count, every
weight range and all shared faces. Thus all 32 continuous scalar cases pass.

## Exact equality-face analysis

This is stronger than merely observing nonnegative coefficients. At a point
in the relative interior of a box face, precisely the Bernstein basis terms
supported on that face are positive. A nonnegative Bernstein sum vanishes
there only if every supported coefficient is zero.

I enumerated all 27 relative face types for each of the 34 boxes. Enlarged
global upper faces are physically unreachable; steep cases with zero owner
half-angle are physically impossible. Among the remaining faces, every zero
face is exactly `xB=xI=xD=0`. Internal split faces remain in this enumeration.
For any physical equality `F=0`, its nonnegative polynomial lower bound must
also vanish, so this analysis forces B, I and D aligned.

## Cap/height transport and the original closed-Q blocker

The unchanged accepted pair caps on A/E to the left and D/G to the right give

```text
46*[xD-xA-hA-hD+T_A+T_D]
+(27/2)*[xG-xE-hE-hG] <= 2*(211/4).
```

Actual AB and the two physical gap bounds imply the first bracket is at
least `2+F+T_A >= 2`. Actual EF and FG imply the second is at least
`2*hF>=1`. The cap sum is strict for `q<1105/256`; since
`46*2+27/2=2*(211/4)`, this is a contradiction. This proves the author's
entire stated guarded strict-radius lemma, with every original retained.

At closed Q, equality in these bounds forces `F=0` and `T_A=0`. The exact
zero-face audit aligns B,I,D, and `T_A>=2*betaA/23` aligns A. Since BI and ID
are now aligned pairs with vertical gaps below one, their actual horizontal
gaps are at least one. Actual AB also has gap at least one. Equality in the
cap sum forces `xD-xA=3`.

The inherited original AB/BC projection links and CD cone-inset inequality
then yield

`3 >= hA+2*hB+hC+gC+gD = 1+2*hB+hC+1/(4*hC) >= 3`.

Here B is already aligned and `hC+1/(4*hC)-1=(2*hC-1)^2/(4*hC)`.
Thus C aligns, and the CD inset gap is at least one, contradicting the
original strictly weak CD projection gap, which is below `hC+hD=1`.
No new cone is assigned to I or H. E/G cap-equality classification is not
needed for this contradiction. This separately establishes the stronger
closed-Q consequence under the same original predicates.

## Literal domain-177 attachment and remaining replay boundary

I checked the candidate initial state equals the entire pending-177 state
in the frozen manifest, with no new restriction or bound round. Its original
ID and root path match the fixed original register. Independent coordinate
and signed pair-difference intersections give

```text
BI horizontal: [855653/1048576, 53/30]
BI vertical:   [-1/16, 1/16]
ID horizontal: [434432029724121/5000000000000000, 1233569/1048576]
ID vertical:   [1/16, 261293/1048576].
```

The B slope interval is the stated symmetric
`46798823265/549755813888` bound, strictly below `2/23`; D lies in `[-1,0]`.
In particular the reversed `(3,8)` pair is handled with the correct signs
when forming I-to-D differences. The original nine-angle, eighteen-coordinate
and 36-frame layouts remain intact. These checks validate the literal guard
and state attachment. They do not replace the larger proof consumer's fresh
ancestry and complete-cover replay, which remains required before accepting
this terminal into that proof.

## Artifacts

The standard-library-only independent command is
`python -B -S research/nine/.runs/review_continue/verify_signed177_scalar_independent.py`.
It completed in about 0.45 seconds. No Lean, Lake, compilation, CI, numerical
solver or producer module was used.

| Review artifact | SHA256 |
| --- | --- |
| `verify_signed177_scalar_independent.py` | `3004fff6257ada749cae024d4ab48696b544cef8af9e699203581135a37a274d` |
| `SIGNED177_SCALAR_INDEPENDENT_REVIEW.json` | `39378772e7bd04dbf0de3c5536e22f2014707a1c3475be21e91f42373584f37e` |
| `signed177_scalar_review.log` | `2fbbb82cc226990a9610fb5d9b6fc37b9c9648d5b3299e9f6d15545b6d4c5f5b` |
| `SIGNED177_LITERAL_ATTACHMENT_REVIEW.json` | `5c3770abe50eba28dbfd75bd6ba81609c2ef2eef0f5104bc07a56d14d61881ec` |
