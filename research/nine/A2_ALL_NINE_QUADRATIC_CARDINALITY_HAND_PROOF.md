# All-nine quadratic central-cardinality inequalities

The premise is the independently reviewed geometric theorem
`SMALLER_CENTRAL_DISKS_NINE_UNIT_CAPACITY.md`, Sections1–4,
and its accepted review identified in
`A2_ALL_NINE_CENTRAL_CAPACITY_ROWS.md`. The theorem concerns all nine
actual original squares in the closed disk of squared radius Q=1105/256, with
pairwise disjoint open interiors. It requires no mask, cone, contact, root, or
common-orientation assumption.

Put h=23/100 and r=27/100. Two consequences already proved from that theorem are:

1. At least two distinct original squares meet the open origin disk of radius h.
2. Every original center satisfies ||c_i||>r.

Call an original *near* when it meets that open disk. Let e_i be its actual
indicator, which is used only in this mathematical proof, not introduced as an
independently chosen LP variable. Then sum e_i>=2.

## Exact radial bounds

Write q_i=||c_i||². Consequence2 gives the necessary weak quadratic inequality
q_i>=r² for each of the nine original centers.

Every physical square has the four original corner containment inequalities.
Maximizing their signs gives

    q_i+1/2+|c_i·u_i|+|c_i·v_i| <= Q.

Since the original frame is orthonormal,
|c_i·u_i|+|c_i·v_i|>=||c_i||. Thus rho=||c_i|| satisfies
rho²+rho+1/2<=Q. The function is strictly increasing for rho>=0, and

    (91/60)²+91/60+1/2 = Q+31/57600 > Q.

Therefore q_i<(91/60)². If certified coordinate intervals also give the exact
box upper bound B_i=max(x_lo²,x_hi²)+max(y_lo²,y_hi²), define

    M_i=min(B_i,(91/60)²).

Then q_i<=M_i on the unchanged whole parent. The corresponding minimum squared
distance of that coordinate box supplies a certified radial lower bound m_i.

If original i is near, choose a square point p with ||p||<h. Its distance to the
center is at most1/sqrt2, so ||c_i||<h+1/sqrt2. Since sqrt2<99/70,

    q_i < U := 1/2+h²+(99/70)h = 61473/70000.

Thus m_i>=U proves i is far. Such labels have e_i=0 and may contribute0 to the
cardinality upper bound. Every other label must be retained.

## Indicator upper bounds without selecting near labels

If M_i<=U, use the unconditional upper bound e_i<=1. This classification does
not assert that the original is near.

If M_i>U, define the same-original quadratic expression

    f_i=(M_i-q_i)/(M_i-U).

It is nonnegative on every physical configuration because q_i<=M_i. If i is
near then q_i<U, so f_i>1. Consequently e_i<=f_i always; the weaker endpoint
f_i>=1 is sufficient for the certificate. Independently e_i<=1 always.

For each eligible label one may choose either of these two upper bounds.
Adding any such choice over all nine labels and using sum e_i>=2 gives an
unconditional inequality on the entire unchanged original parent. No chosen
near pair or descendant case is involved.

Let C be the number of retained labels represented by a constant1, and K the
remaining labels with radial upper bounds f_i. The nontrivial finite family is:

    sum_(i in K) f_i >= 2-C,

and, when C=0, for every omitted label j in K,

    sum_(i in K, i!=j) f_i >= 1.

The second family uses1 as the upper bound for e_j. It prevents one large f_j
from accounting for both required near originals. Choices containing at least
two constants are already implied by f_i>=0, so no additional rows are needed.
If fewer than two labels survive the exact far exclusions, one of these constant
inequalities is contradictory, as required by the complete all-nine theorem.

For a selected subset S and required right side k, expansion gives the exact
lifted quadratic row

    sum_(i in S) q_i/(M_i-U)
        <= sum_(i in S) M_i/(M_i-U)-k.

Each q_i uses that original's two shared center-square monomials. Every
denominator is explicitly checked positive. All box bounds, far classifications,
constant classifications, rational coefficients, and omitted labels are printed
in the audit metadata.

These are necessary whole-parent inequalities only. A full original closure
still requires an independently replayed positive exact contradiction. They
grant no mask credit by themselves, and no Lean, Lake, or CI execution is claimed.
