# The joint five-square cap with an arbitrary high-floor central square

This is a complete proof of the stated joint cap. It consists of hand
support reductions and five complete finite rational certificates.
Every interval row and every covering subdivision has passed a separate
exact replay. No Lean, Lake, or CI is used. The completion record and
certificate hashes are at the end.

Write

    Q=1105/256, r=sqrt(Q), a=46, b=27/2,
    K=207/16, T=211/4, rho=sqrt(Q-1/4)-1/2.

For a physical unit square V, let H_V(v) be its centered support
halfwidth and let h_V=H_V(e_x)=H_V(e_y).

## 1. Statement and original geometric hypotheses

There are five original interior-disjoint physical unit squares
E_L,L,U,R,E_R in a common centered disk of radius R0<=r. Their centers
satisfy the following closed bands:

| Square | Center x interval | Center y interval |
|---|---|---|
| E_L | [-91/60,-89/60] | [-1/8,1/8] |
| E_R | [89/60,91/60] | [-1/8,1/8] |
| L | [-13/12,-23/30] | [25/32,21/16] |
| R | [23/30,13/12] | [25/32,21/16] |
| U | [-29/60,29/60] | [3/5,91/60] |

Assume further

    h_E_L,h_E_R<8/15, y_U-h_U>=1/10.              (1)

No actual vertical endpoint/shoulder relation or actual horizontal
central/shoulder relation is assumed. The central square U can be any
original physical square meeting these hypotheses.

The joint cap is

    a(x_E_R-x_E_L-h_E_L-h_E_R)+b<=2T.             (2)

It is strict if R0<r. It is also strict at radius r whenever at least
one of the two directed central separating slopes is nonzero.

## 2. The complete separator domains follow from these bands

Every physical unit square contains its centered disk of radius1/2.
Thus a genuine separating inequality in vector n requires the center
projection to be at least |n|. A separating-axis theorem for two convex
squares supplies a side normal owned by one of the two original squares.

Each shoulder is above its corresponding endpoint, while their absolute
horizontal center gap is at most3/4. A directed separator with
nonpositive vertical component would have center projection less than
its norm. Therefore normalize the endpoint-to-shoulder vectors to

    n_L=(w_L,1), n_R=(-w_R,1).

In the right-hand frame the inward horizontal center gap belongs to
[2/5,3/4], and the vertical gap is at most23/16. If w=-t<=-2/3, the
projection is at most23/16-(2/5)t, which is less than sqrt(1+t^2).
The squared reserve at t=2/3 is4239/57600, and the difference then
increases. If w>=6, the projection is at most(3/4)w+23/16, again less
than sqrt(1+w^2): at6 the squared reserve is447/256, and its derivative
thereafter is positive. Hence

    -2/3<w_L,w_R<6.                              (3)

Modulo a quarter turn, every endpoint frame has |tan(theta)|<7/100.
Indeed its halfwidth is (1+t)/(2sqrt(1+t^2)), increasing for0<=t<=1;
at t=7/100 it exceeds8/15 because1605^2-256*10049=3481>0. If an
endpoint owns its separator, the near-horizontal side normal would
have |w|>100/7, contradicting(3). Thus that normal is the near-vertical
one and

    |w|<7/100<1/14.                              (4)

Each central-to-shoulder horizontal displacement points strictly
outward. Its absolute vertical displacement is less than one, by the
displayed y bands. A directed separator with a non-outward horizontal
component would again have center projection less than its norm.
Normalize the two central vectors to

    m_L=(-1,z_L), m_R=(1,z_R).

Their horizontal displacement is at most47/30. Their positive vertical
reach is at most57/80, and their negative vertical reach at most353/480.
The unit-vector inequality

    sqrt(1+t^2)>=(7+24t)/25

excludes t>=6 in both cases. At6 the reserves are119/600 and73/1200,
and both differences increase thereafter. Therefore

    -6<z_L,z_R<6.                                (5)

These deductions cover every endpoint-owner choice and every sign of
the central normals. They use genuine physical nonoverlap only.

## 3. Keep one original outer expression on each side

In the right-hand frame define, for any nonnegative k,

    Phi(E,S;w,z,k)
      =(a e_x-kn) dot c_E+(b m+kn) dot c_S
        -a h_E-kH_E(n)-bH_S(m)-kH_S(n),          (6)

where n=(-w,1), m=(1,z). The left expression is its horizontal
reflection, with that endpoint and shoulder's original variables.
Introduce the piecewise linear function

    ell(z)=(29/2)z if z>=0; ell(z)=16z if z<=0.  (7)

The two uniform outer-envelope results establish the following precise
quantified assertion: for every admitted (w,z) and either actual owner
of n, there is a nonnegative k such that

    Phi(E,S;w,z,k)<=T+ell(z)                     (8)

for every original endpoint and shoulder satisfying their stated
circle, box, frame, and ownership conditions. The selected k may
depend on the parameter row. It multiplies a genuine separating slack
and does not move or reconstruct any physical square.

The complete sources are `LINEAR_OUTER_SCALAR_ENVELOPES.md` for the
shoulder-owned case and `E_OWNED_VARIABLE_K_LINEAR_ENVELOPES.md` for
the endpoint-owned case.

When the shoulder owns n, its actual frame is fixed by (1,w), and the
endpoint is allowed its full near-aligned frame interval. Two exact
two-variable tables cover w in[-2/3,6] and t=|z| in[0,6], with their
local hand rectangle treating the sharp origin.

When the endpoint owns n, the hand comparison in
`MAIN_OWNED_ENDPOINT_SLOPE_REDUCTION_HAND_PROOF.md`, Section5, removes
w for every constant row multiplier K<=k<=20 and q_E=0. It retains the
actual shoulder center and frame and gives the unboxed endpoint
constant

    E_0(k)=r sqrt(a^2+k^2)-a-k.

Thus the two one-variable tables prove(8) by bounding

    E_0(k)+(b(1,z)+k e_y) dot c_S
                    -bH_S((1,z))-k h_S.         (9)

The unboxed constant is essential when k differs from K. A smaller
boxed endpoint maximum is not substituted after the comparison.

Every finite row in these four tables is a strict rational upper bound.
Their local hand arguments cover the zero faces; at the common sharp
point the original disk-support inequality is strict whenever R0<r.

## 4. The same central square supplies the remaining inequality

Put

    p=(z_L)_+ +(z_R)_+, n=(-z_L)_+ +(-z_R)_+,
    S=p-n, C=H_U(m_L)+H_U(m_R)+S y_U.

`CENTRAL_LINEAR_TRANSFER_HAND_TABLE.md` proves, for the full slope
domain(5) and the original L,U,R,

    C>=1+(29/27)p-(32/27)n.                      (10)

Its nonpositive-sum and mixed-sign regions have complete hand proofs.
Only the positive quadrant needs its exact two-variable table. The
proof retains U's single orientation and center in both support terms.
Its whole-floor hypothesis is exactly(1), and it requires no central
normal ownership. Equation(10) is strict at every nonzero slope pair.

## 5. Sum the original separating slacks

Let D=x_E_R-x_E_L-h_E_L-h_E_R. Add the two endpoint separating slacks
with the nonnegative multipliers selected in(8), and add the two actual
central separating slacks with multiplier b. Expanding the resulting
linear center and support terms gives the exact upper bound

    aD+b<=b+Phi_L+Phi_R-bC.                      (11)

The central center coefficient is (0,-bS), which explains its one
height in C. Neither its two supports nor its two appearances are
optimized independently.

By(7)--(8),

    Phi_L+Phi_R<=2T+(29/2)p-16n.

Since b=27/2, substituting(10) into(11) cancels these three terms
exactly and proves(2). A nonzero central slope makes the central step
strict. If both central slopes vanish, the strict finite outer rows
or local hand comparison apply; at their common origin R0<r makes
the original nonzero disk-support step strict. This proves the stated
strict subcritical-radius version in every case.

## 6. The actual four-chain consequence

If E_L,E_R are the two endpoints of an actual horizontal four-chain
of physical unit squares, its two interior units have horizontal
projection widths at least one. Therefore D>=2. But

    aD+b>=2a+b=211/2=2T.

This contradicts the strict version of(2) for R0<r. Hence any such
configuration satisfying the original center bands and whole floor
has squared containing radius at least1105/256.

The present theorem keeps all of those original geometric hypotheses.
A nine-square mask is closed only after its caller supplies them for
the original squares. In particular a central extra U supplied by the
whole-floor lemma may be used directly in place of a selected middle
unit; no proxy square is inserted.

## 7. Completion record

The five complete certificates are in `computer_assisted/`:

| Component | Strict interval leaves | Certificate |
|---|---:|---|
| Shoulder-owned endpoint normal, z<=0 | 1,700 | `outer_R_linear_negative_cover.json` |
| Shoulder-owned endpoint normal, z>=0 | 490 | `outer_R_linear_positive_cover.json` |
| Main-owned endpoint normal, z<=0 | 25 | `E_variable_k_linear_negative_cover.json` |
| Main-owned endpoint normal, z>=0 | 28 | `E_variable_k_linear_positive_cover.json` |
| Central transfer | 1,684 | `central_linear_transfer_compact.json` |

The central cover additionally has34 analytic leaves, including its two
whole signed quadrants; the outer sharp regions are covered by their
stated hand lemmas. The five tables contain3,927 strict interval rows
in total. All complete root systems and both children of every split
were independently reconstructed. No pending cell, approximate point
optimizer, or incomplete owner partition is used in this proof.

The independent replays use standalone outward64-bit dyadic arithmetic
and algebraic expressions written separately from the96-bit producer.
The two E tables also passed full replays with a separate exact-Fraction
backend. The support formulas, all owner and slope reductions, the
variable-k comparison, the central transfer, and the present assembly
also underwent independent mathematical audits.

The certificate SHA-256 values are:

```text
R negative  10d5ed1ef26b97ecaf86d0149a4840040804d2e31dc5a147b05047629e0852ed
R positive  36d29da96f39618b2a74a8fe1c2f7a30e97acc2bfc713e1f41c72999ebc2db66
E negative  94ddb170a16bf4b222e1ede3e85c6a24537b6fa9c23cceb68f73c210f93c91fc
E positive  ec1bf64bc56f7fb84485be5c6f40477c3d7e3e65797f1c8f603f3473717c7751
central     771bf108f5441de0e46810bd924f9fad118d94072f121136f3ed2423f7c0616a
```

From the `research/nine` directory the complete replays are:

```sh
python computer_assisted/verify_outer_scalar_family.py computer_assisted/outer_R_linear_negative_cover.json
python computer_assisted/verify_outer_scalar_family.py computer_assisted/outer_R_linear_positive_cover.json
python computer_assisted/verify_E_variable_k_linear.py computer_assisted/E_variable_k_linear_negative_cover.json
python computer_assisted/verify_E_variable_k_linear.py computer_assisted/E_variable_k_linear_positive_cover.json
python computer_assisted/verify_central_linear_transfer.py computer_assisted/central_linear_transfer_compact.json
```

Successful replay reports are stored beside the corresponding
certificates. Together with the explicit hand regions and the algebraic
assembly above, these records close every parameter and owner branch
of the joint theorem stated in Section1.
