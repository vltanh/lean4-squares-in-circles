# Independent physical and evaluator review: two upper central units with wide inner mains

November 2, 2026. Independent agent review and hand translation. No Lean
or CI. The exact replay is the separate producer-independent replay by
the parent; this review does not claim to have rerun its 43,331 leaves.

**Result: PASS.** The five-variable necessary lower bound and its exact
interval evaluator are valid for the original physical domain below.
Every chirality and physical separator owner is covered. The endpoint
elimination, both main-height orders, and zero-slope cases are justified
here. The completed exact replay supplies the scalar inequality.

Reviewed sources:

- `root_wide_pair_relaxation.py`, SHA-256
  `b995cd27c15a201997ca216b15ca5d0b73a8759570c7f568d5602d562e5a465d`.
- `root_wide_pair/verify_wide_central_pair.py`, SHA-256
  `0348ba026937bd2f213ebc7178e802c78e34ae1b8e9fe485cb272c9f5dbfdf0e`.
- The reused directed-integer kernel
  `pr11/research/nine/computer_assisted/verify_joint_five_dyadic.py`,
  SHA-256
  `e9a077c6ed871e402f5e43604137a011428ffe9f0d5dcf18d2e1651dd1290c1f`.

The kernel was already independently audited in the earlier joint-cap
work. Its integer interval operations were reread for this use; the new
review concerns the physical reduction, new formulas, monotonicity, and
complete-tree interface.

## 1. Exact physical scope and five parameters

Retain four original mains A,B,C,D in horizontal center-cone order in
the closed disk Q=1105/256. Their outer links A--B and C--D are actual.
The middle link may be actual or weak. Retain two distinct original
central units F,G, both above B and C, with

`|xF|,|xG|<=l=29/60`, `yG>=yF`, and `|xG-xF|<=1/2`.

All their original independent frames and original physical pairs remain.
The theorem needs no selected outsider triple or occupancy premise.
An application to 010/11 retains those additional predicates but does
not use them here.

The accepted outer-link endpoint theorem gives

`1/2<=hB,hC<13/20`, `V=etaB+etaC<1/30`,

where gM=1/(4hM) and etaM=hM+gM-1. The inner x intervals are

`b-=hB-61/60`, `b+=1/60-gB-etaC`,

`c-=gC+etaB-1/60`, `c+=61/60-hC`.

Their common length is 1/30-V. The true xB,xC lie strictly inside
these intervals; including their boundaries is a safe closed relaxation.

Fold F and G's angles as tF,tG in [0,1], with

`a=1/sqrt(1+t^2)`, `b=t*a`, `h=(a+b)/2`.

For each main use a=h+sqrt(1/2-h^2), b=h-sqrt(1/2-h^2).
Reflection in the vertical axis exchanges the roles of B,C and replaces
xF by -xF, without changing any height or folded angle. Thus it is enough
to use the closed five-dimensional rectangle

`(hB,hC,tF,tG,xF) in [1/2,13/20]^2 x [0,1]^2 x [0,l]`.

The strict physical subdomain V<1/30 is included in V<=1/30. The exact
cover is allowed to reject V>1/30 independently.

## 2. A valid absolute-owner physical clearance

For folded original frames s=(a,b) and t=(c,d), define

`sigma(s,t)=(1+a*c+b*d+|a*d-b*c|)/2`.

This is a lower bound for their actual support sum on every owned
separating axis. Indeed, writing the folded angles alpha,beta in
[0,pi/4], the actual relative-frame support is

`[1+cos(delta)+sin(delta)]/2`,

where delta is either |alpha-beta| or alpha+beta up to quarter-turn
symmetry. For alpha>=beta,

`cos(alpha+beta)+sin(alpha+beta)`

minus

`cos(alpha-beta)+sin(alpha-beta)`

equals `2*sin(beta)*(cos(alpha)-sin(alpha))>=0`.
The smaller choice is exactly the displayed sigma. In particular
sigma>=1. No independent favorable chirality is imposed on an original
unit: lowering the support uniformly over both possibilities is a
necessary relaxation.

Suppose the horizontal center gap is at most D and the vertical gap is
V0>=0. An actual separating axis belongs to one original square. Its
absolute horizontal/vertical components are one of

`(a,b), (b,a), (c,d), (d,c)`.

If these components are (p,q), actual separation implies

`p*D+q*V0 >= sigma(s,t)`.

For q>0 the necessary vertical clearance is

`max(0,(sigma-p*D)/q)`.

For q=0, a positive numerator makes that owner impossible; a nonpositive
numerator permits the lower bound zero. Define K(s,t,D) as the minimum
of these bounds over all possible owners. Then every original pair
satisfies

`|dy| >= K(s,t,D)`.

This is precisely the mathematical function relaxed by `clearance`.
It is nonnegative and nonincreasing in D. All four owners, both normal
signs, both chiralities, and aligned limits are retained.

## 3. Why eliminating each main x-coordinate by endpoints is valid

Every central/main horizontal gap in these intervals is at most one.
For example |xF-xB|<=l+(61/60-hB)<=1; reflection gives the other side.
Since sigma>=1 and every owner component p<=1, every finite numerator
sigma-pD is nonnegative throughout 0<=D<=1.

Consequently, away from zero-component owners, K is a minimum of affine
decreasing functions of D. On substituting D=|x-z|, each owner branch
has the form constant minus a nonnegative multiple of |x-z|. It is
concave in z; their minimum is concave as well. Adding the affine term
z or -z preserves concavity. Such a function's minimum over a closed
interval occurs at an endpoint.

The zero vertical-component case is not discarded. It requires
D>=sigma/p>=1. In the present domain this can happen only at D=1,
which is an endpoint of the allowed main-coordinate interval. Its
possibly smaller value zero is already included by the endpoint rule.
Equivalently, apply the concavity argument to the actual positive-
component owner; a zero-component actual owner can occur only at the
listed boundary. This avoids an unjustified global concavity claim for
the clearance function after truncation outside D<=1.

Define

`L=min[-z+K(B,F,|xF-z|): z in {b-,b+}]`,

`R=min[ z+K(C,F,|xF-z|): z in {c-,c+}]`.

Then the corresponding expressions at the actual main positions are at
least L and R. These are the code's `left` and `right`.

## 4. The endpoint resources extend to the weak-middle domain

For an outer endpoint E, put X=|xE|, Y=|yE|, e=hE-1/2, and
aE=hE+sqrt(1/2-hE^2). The outer-link span gives

`X>89/60+e`, `hE<8/15`.

These are exactly the hypotheses used in Section 1 of
`UPPER_CENTRAL_PAIR_HALF_WIDTH_REPLACEMENT_HAND_PROOF.md`, whose
corner argument gives

`X+Y-aE<49/80`, hence `X+Y<129/80`.

The stronger weak-middle span supplies these endpoint hypotheses
unchanged; no actual middle edge was used in that corner argument.

The original outer cone links therefore imply

`yB>-129/80-xB`, `yC>-129/80+xC`.

Using F above both mains and the clearances yields

`yF>=-129/80+L`, `yF>=-129/80+R`.

For the averaged resource, the accepted endpoint budget is

`|yA|+|yD|+(37/50)U+(32/9)V<=1/8`,

with U=hA+hD-1>=0. Since XA+XD<2rho, rho=91/60,

`(XA+XD-yA-yD)/2 < 379/240-(16/9)V`.

Averaging the two original outer-cone and F-clearance inequalities
therefore gives

`yF>=-379/240+(16/9)V+(L+R)/2`.

The independent wide-main central clearance also gives yF>-3/10:
the uniform main heights exceed -6/5 and the original central unit's
own-half clearance exceeds 9/10. The relevant deductions are Sections
1--2 of `WEAK_MIDDLE_BOTH_WEAK_COMMON_REDUCTIONS.md`; they use only
the main chain and the central unit, not either selected short bit.

## 5. Both possible orders of the inner main heights

Put

`DB=max(|xF-b-|,|xF-b+|)`,

`DC=max(|xF-c-|,|xF-c+|)`,

`KB=K(B,F,DB)`, `KC=K(C,F,DC)`,

`M=K(B,C,c+-b-)`.

These are lower clearance bounds at the actual original positions.
The argument uses monotonicity in D here; it does not use the endpoint
concavity rule outside D<=1 for the main/main pair.

If yC>=yB, original main/main separation and then C/F separation give

`yF>=yB+M+KC>-129/80-b++M+KC`.

If yB>=yC, the other order gives

`yF>=yC+M+KB>-129/80+c-+M+KB`.

The union of the two orders therefore supplies the necessary lower bound

`Ymiddle=M-129/80+min(-b++KC,c-+KB)`.

This is exactly `middle_y`. Equality of main heights is harmless: the
relaxed main/main clearance is then necessarily zero, and either bound
remains valid. No choice of ordering is silently fixed.

Combining all five bounds, define

`Y=max(-3/10, -129/80+L, -129/80+R,`

`      -379/240+(16/9)V+(L+R)/2, Ymiddle)`.

The actual lower central center obeys yF>=Y. Because yG>=yF and the
original F/G horizontal gap is at most 1/2, their physical separation
gives the full whole-floor bound

`yG-hG >= Y+K(F,G,1/2)-hG`.

This proves the five-variable reduction used by both programs.

## 6. Exact evaluator and coverage audit

The exact checker matches that reduction with outward lower bounds.

- Main a decreases with h; main b and eta increase, and g decreases.
  Their endpoint enclosures are therefore valid. The main root stays
  below 1/sqrt(2), so every square root is defined.
- For a free frame, a decreases with t, while b and h increase on
  [0,1]. The endpoint enclosures in `free_shape` use these directions.
- The support interval is computed from the full products and absolute
  difference. Intersecting it with sigma>=1 is valid.
- Each clearance numerator is rounded down. A positive numerator is
  divided by the upper vertical component and rounded down again.
  A nonpositive lower numerator permits zero. An identically zero
  vertical component with positive numerator is impossible and is
  skipped. These are exact cases, without the exploratory tolerances.
- Every distance passed to clearance is an outward nonnegative rational
  upper bound. The endpoint affine terms use the appropriate lower
  or upper coordinate endpoints. `left`, `right`, the averaged bound,
  and both branches of `middle_y` are consequently lower bounds.
- The final subtraction uses an upper bound for hG. A positive floor
  reserve therefore proves the actual whole floor strictly exceeds
  one tenth, including every equality face of the closed root.

The checker first verifies the entire preorder binary-tree skeleton.
Its only split axes are 0 through 4 and its only leaves are the two
advertised rules. Exact rational midpoint subdivision covers each
parent, including the shared boundary. The replay then verifies every
leaf, all reported counts, maximum depth, and the empty frontier.

Rule 1 rejects V>1/30. Rule 2 proves the derived floor exceeds 1/10.
Both acceptance tests are strictly positive exact rational inequalities.
The original feasible domain lies in the fixed root and satisfies
V<1/30, so every original physical point is covered by the second rule
whenever it is not already in an impossible orientation box.

## 7. Completed arithmetic record and precise conclusion

The parent's separate exact replay report records:

- 86,661 nodes and 43,331 strict leaves, maximum depth 26;
- 69 orientation-budget leaves and 43,262 floor leaves;
- least exact reserve `112318305826923/92233720368547758080>0`;
- certificate SHA-256
  `ed365f824ba9027ee4472e3d1b34412a3dce5711279a234e9ef61eabd880d6e0`;
- all four malformed or false control certificates rejected.

I read that report and audited the frozen checker above. Combined with
the physical reduction in Sections 1--5 and the established interval
kernel, it proves:

**In the closed Q-disk, an original cone main four-chain with actual
outer links, together with two original central units above both inner
mains and horizontal center gap at most one half, forces the higher
central original's whole floor strictly above one tenth.**

The main middle link is allowed to be actual or weak; no selected
short-chain status or side occupancy is a premise. The conclusion is a
reusable physical lemma, not by itself a whole-mask closure.
