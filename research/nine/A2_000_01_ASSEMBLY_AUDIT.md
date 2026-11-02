# Independent analytic audit of the recovered full 000/01 argument

This independent agent audit was performed on November 2, 2026, against
the fixed-domain contract at PR head `add3c530e760ddf15cb936a72ee4761a1fcdbe73`.
It checks the recovered mathematical assembly before publication. No
Lean, Lake, or CI was used. The separate exact replays subsequently passed
as recorded in `A2_000_01_VERIFIED_CLOSURE_2026_11_02.md`.

## Scope and result

No analytic gap was found in the whole-domain assembly, the joint
five-square cap, its local sharp support bounds, the endpoint-owned
normal reduction, or the central transfer theorem. This assessment
assumes the exact finite tables named by those theorems replay their
stated inequalities and complete covers. The low-floor geometric
reduction receives a separate independent audit and replay.

The complete assembly needs the nine tables listed in
`A2_000_01_WHOLE_DOMAIN_HAND_TABLE_PROOF.md`. The older separate
high-floor fork theorem is redundant: the new joint five-square cap
handles both the original high-floor P and the high-floor extra U.
Thus the five older fork tables are not hidden dependencies.

## Coverage of the current fixed predicate

The designated four-chain is both actual and center-cone; the short
chain is actual on L--P, center-cone but strictly weak on P--R. Every
square used in the proof is one of the nine original physical units.
The one common vertical reflection preserves every corner constraint,
every physical pair, all actual links, and all cone comparisons.

The original endpoint bands, their halfwidth bounds and height budget,
the shoulder bands, and the inner-main height range are consequences
of the current mask. The proof never applies a bounded-inner-height
theorem as though its lower bounds were automatic.

The two branches `y_P-h_P>=1/10` and `y_P-h_P<=1/10` cover the whole
real line and overlap on their shared boundary. In the first branch
the original P lies inside the required central x-band. In the second,
the low-floor theorem supplies an original extra U strictly above P
and in the central band; the whole-floor theorem supplies its floor.
No replacement square, missing ninth-square condition, or unproved
actual L--U / U--R link is used.

## The joint cap retains every normal owner and slope

For an endpoint-to-shoulder pair, the horizontal displacement has
magnitude at most 3/4 and the vertical displacement is positive. A
directed normal with nonpositive vertical component cannot project the
displacement to its own Euclidean norm, which is the minimum support
sum of the two contained half-unit disks. Thus the vertical component
is positive. Normalization gives `n=(-w,1)` in the right frame.
The endpoint/shoulder bands imply `-2/3<w<6`.

For an endpoint-owned separator, `h_E<8/15` forces its reduced frame
slope to have magnitude below 7/100. The alternative near-horizontal
normal would have `|w|>100/7`, already outside the preceding range.
The complete endpoint-owned case therefore has `|w|<1/14`.

For each central-to-shoulder pair, the horizontal displacement points
outward and the vertical displacement has magnitude below one. Every
directed separator consequently has an outward horizontal component.
Normalization gives `m_L=(-1,z_L)` and `m_R=(1,z_R)`. The horizontal
gap is at most 47/30; the positive and negative vertical reaches are
at most 57/80 and 353/480. The unit-vector lower bound
`sqrt(1+t^2)>=(7+24t)/25` gives `|z_L|,|z_R|<6`. Both physical owners
of every endpoint separator and every sign of every central separator
are retained.

## Original-square support assembly

For one outer pair the retained expression is

    Phi=(a e_x-k n).c_E+(b m+k n).c_S
          -a h_E-k H_E(n)-b H_S(m)-k H_S(n).

The nonnegative k multiplies a genuine separating slack. Its choice
may depend on the parameter box without depending on a replacement
packing. The shoulder-owned bounds optimize the actual shoulder frame
fixed by n and all allowed endpoint frames. The endpoint-owned
comparison retains the actual shoulder center and orientation, removes
w, and uses the **unboxed** constant

    E_0(k)=r sqrt(a^2+k^2)-a-k,  K<=k<=20.

It would be invalid to improve that constant using an endpoint box
after the comparison; the recovered theorem explicitly avoids this.
The seven derivative rows in that comparison have been independently
recomputed using exact rational arithmetic. All printed squared and
derivative reserves agree and are positive.

Adding the four actual separating slacks produces

    aD+b <= b+Phi_L+Phi_R-b C,
    C=H_U(m_L)+H_U(m_R)+(z_L+z_R)y_U.

This identity uses the same original central square once. The outer
terms are at most `2T+(29/2)p-16n`; the central term is at least
`1+(29/27)p-(32/27)n`. With `b=27/2`, the cancellation is exact.

## Central transfer and its strictness

The support expression

    |z_L+z_R| h_U+H_U(m_L)+H_U(m_R)

is the sum of the two projection widths of the triangle with vertices
`(0,0),(1,z_R),(0,z_L+z_R)` in the square's frame. Its minimum occurs
at an edge alignment: between consecutive projection-change angles
the positive support sum has second derivative equal to its negative.
The three candidate formulas in the manuscript follow by direct
projection and retain every sign.

The global lower bound `M>=1+(9/10)|z_L+z_R|` follows from the
sloping-edge expression

    max(d^2+s,s(z+1))/d,

whose minimum residual over s occurs at zero or at the crossing.
The crossing reduces to `u+v-uv>9/10` for nonnegative unit (u,v).
For mixed signs, or absolute sum at most one, the stronger lower bound
`M>=1+|z_L+z_R|` applies.

The explicit reserves in the nonpositive-sum and hand regions have
been independently recomputed. They are positive at every nonzero
slope pair. The remaining positive quadrant uses the complete table
for `max(G1,G2)>0`; G1 proves strict transfer, while G2 contradicts
the physical shoulder-center bound. Thus the table does not need to
prove a transfer inequality at physically impossible parameter values.

At the zero slope pair only the weak transfer `C>=1` is asserted.
This is exactly the boundary needed for the equality argument.

## Local sharp bounds

The local endpoint and shoulder penalties were independently expanded
at each triangle-edge alignment. Their sign conventions and positive
denominators agree with the physical vectors in Phi. The diagonal
candidate lower bounds and the norm Taylor remainders have the stated
directions. The resulting scalar upper bound is

    Phi <= T-(K/2)|w|+(3K/2)z-K(z-w)_+
              +(20+23*1_{w<0})w^2+19z^2.

The local shoulder-owned rectangle and endpoint-owned slope interval
then have strictly positive linear reserves except at their common
zero. At zero, strictly subcritical radius makes the original nonzero
endpoint disk-support inequality strict. Hence a fixed positive
radius gap is not introduced anywhere in the argument.

## Closed-Q exclusion of the strict-weak mask

This part is especially useful because it needs no classification of
the extra squares. The actual four-chain gives `D>=2`; the joint cap
gives `aD+b<=2T=2a+b`. Equality therefore holds. Strict central
transfer forces both central slopes to vanish, making the original
L--U and U--R links actually horizontally separated. Consequently

    B=x_R-x_L-h_L-h_R >= 2h_U >= 1.

The two original physical endpoint caps give `aD+bB<=2a+b`, so D=2,
B=1, and both endpoint caps attain equality. Their existing equality
theorem makes R coordinate aligned: `h_R=g_R=1/2`.

The original actual L--P and original cone/inset P--R comparisons
then give `B>=h_P+g_P>=1`. Since B=1, the identity

    h_P+1/(4h_P)-1=(h_P-1/2)^2/h_P

forces `h_P=g_P=1/2`. Hence `x_R-x_P>=g_P+g_R=1=h_P+h_R`,
contradicting the defining strict-weak edge. Projection equality is
assigned to the actual bit exactly as required by the contract.

The contract's simultaneous coordinate and chain reversal then yields
the same exclusion for 000/10. No conclusion about another mask or the
unrestricted A.2 theorem follows merely from these two closures.
