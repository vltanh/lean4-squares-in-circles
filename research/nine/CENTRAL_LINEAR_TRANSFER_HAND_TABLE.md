# A central-square transfer for the outer linear envelopes

This note proves the stated three-square support inequality by hand
reductions and a complete rational two-variable table. The entire table
and its coverage have passed an independent exact replay. The outer
endpoint/shoulder envelopes are separate proved components used by the
joint-cap assembly.

Put

    Q=1105/256, r=sqrt(Q), rho=sqrt(Q-1/4)-1/2,
    b=27/2, c_+=29/2, c_-=16.

The rational bounds used below are

    r<133/64, rho<91/60.

Their squared reserves are respectively9/4096 and31/57600.

## 1. The exact statement and its joint-cap use

Let L,U,R be original interior-disjoint physical unit squares in the
centered Q-disk. Assume U has whole floor y_U-h_U>=1/10. Suppose there
are genuine directed separating inequalities from U toward L and R
with vectors

    m_L=(-1,z_L), m_R=(1,z_R), -6<=z_L,z_R<=6.

The normals may have either physical owner. Put

    p=(z_L)_+ +(z_R)_+, n=(-z_L)_+ +(-z_R)_+,
    S=p-n=z_L+z_R, s=|S|, Y=y_U,
    C=H_U(m_L)+H_U(m_R)+S Y.

Then the claimed central transfer is

    C>=1+(29/27)p-(32/27)n.                       (1)

It is strict whenever at least one central slope is nonzero. All the
supports and the height in C belong to this one original U.

To explain its role, suppose the two outer expressions already satisfy

    Phi_i<=T+(29/2)(z_i)_+-16(-z_i)_+,

where T=211/4 and each expression comes from its actual endpoint and
shoulder, with a nonnegative multiplier on their genuine separator.
The joint support expansion, using multiplier b on the two central
separators, is

    aD+b<=b+Phi_L+Phi_R-bC,

with a=46 and D=x_E_R-x_E_L-h_E_L-h_E_R. Equation(1) cancels all the
central terms and gives aD+b<=2T. Thus the central transfer is independent
of the endpoint normal owners and of the outer multipliers. It does not
replace the required proof of the two outer envelopes.

## 2. The central triangle and its exact candidates

Let

    d_i=sqrt(1+z_i^2), A=|z_L z_R-1|.

For every frame of U, the support sum

    s h_U+H_U(m_L)+H_U(m_R)

is the sum of the widths of the triangle with vertices
(0,0),(1,z_R),(0,S), measured in U's two orthogonal side directions.
Between successive changes of an extreme projected vertex, this
positive sum has the form A0 cos(theta)+B0 sin(theta), with negative
second derivative. Its minimum therefore occurs at an edge alignment.
The exact minimum is

    M=min(1+max(p,n),
          (d_L^2+A+s(2+|z_L|))/(2d_L),
          (d_R^2+A+s(2+|z_R|))/(2d_R)).           (2)

Indeed a vertical alignment has value1+max(p,n). In an m_i alignment,
the supports of m_i,m_j are respectively d_i/2 and(A+s)/(2d_i), while
the vertical support is s(1+|z_i|)/(2d_i). This proves(2), including all
projection signs. Degenerate triangles follow directly or by continuity.

Three hand lower bounds for this same triangle will be used:

    M>=1+s                         if s<=1;       (3)
    M>=1+s                         if z_L z_R<=0; (4)
    M>=1+(9/10)s                   always.       (5)

The first is proved in Section7 of
`JOINT_OPPOSITE_NORMAL_LOCAL_HAND_PROOF.md`. Here is the extension(4).
Reflect vertically so S=s>=0. A nonnegative sloping-edge parameter z_i
is then at least S, because the other parameter is nonpositive. Its
candidate is d_i+S/d_i>=1+S, since d_i>=z_i>=S and d_i>=1. A negative
edge parameter gives d_i+S(1-z_i)/d_i>=1+S. The vertical candidate is
also at least1+S, proving(4) for all magnitudes.

For completeness, (5) has a short global hand proof. In a nonnegative
sloping-edge parameter z, write d=sqrt(1+z^2). Its candidate is

    L(s,z)=max(d^2+s,s(z+1))/d.

The minimum of L-1-(9/10)s as a function of s>=0 occurs at s=0 or at
the crossing s=d^2/z. At0 the value is d-1>=0. At the crossing its sign
is the sign of

    (d-1)z+d-(9/10)d^2.

Divide by d^2 and put u=z/d,v=1/d. Then u,v>=0,u^2+v^2=1, and the
result is u+v-uv-9/10. Since

    u+v-uv=1-((u+v)-1)^2/2>=sqrt(2)-1/2>9/10,

it is positive. Negative edge parameters and the vertical alignment
already give1+s. This proves(5) without a table. The degenerate s=0
case is simply two opposite supports, whose sum is at least one.

## 3. All nonpositive sums are closed by hand

If S<=0, the original square satisfies Y<=r-h_U. Hence

    C>=s h_U+H_U(m_L)+H_U(m_R)-rs
      >=1+(9/10-r)s.

Since n=p+s, subtracting the right side of(1), and using r<133/64,
gives the strict lower reserve

    C-[1+(29/27)p-(32/27)n]
       >=p/9+(61/8640)s.                         (6)

This is positive unless p=s=0, which means both slopes vanish. No
central whole-floor assumption is needed in this case.

## 4. All mixed signs and the strip |S|<=1 are closed by hand

Under either z_L z_R<=0 or |S|<=1, use(4) or(3). If S>=0, the actual
whole floor gives Y>=h_U+1/10 and therefore

    C>=M+S/10>=1+(11/10)S.

Its reserve over(1) is

    (7p+23n)/270>=0.                              (7)

If S<0, use Y<=r-h_U and M>=1+s. The reserve is at least

    (7p+185n)/1728>=0,                            (8)

using r<133/64. Both reserves are strict at every nonzero slope pair.
Consequently only the positive quadrant with S>1 requires a table.

## 5. A second necessary inequality in the positive quadrant

Every physical unit square contains the centered half-unit disk, and
its center has norm at most rho. The two actual central separators give

    m_i dot c_U+H_U(m_i)
       <=m_i dot c_i-H_i(m_i)
       <=(rho-1/2)d_i.

Adding them and using the same actual central floor proves, for S>=0,

    M+S/10<=C<(61/60)(d_L+d_R).                  (9)

Thus a positive-slope cell is closed whenever either of the following
two quantities is positive throughout that cell:

    G_1=M-1-(263/270)S,
    G_2=M+S/10-(61/60)(d_L+d_R).                 (10)

G_1>0 proves(1) strictly, while G_2>=0 contradicts the necessary
physical inequality(9). It is enough to prove max(G_1,G_2)>0 pointwise;
the successful alternative need not be the same at every point of a row.

## 6. The complete exact positive-quadrant table

The producer `certify_central_linear_transfer.py` uses only rational
arithmetic with outward96-bit dyadic rounding and integer square roots
to certify every leaf. Floating discovery is not a premise of a leaf.
The compact certificate is `central_linear_transfer_compact.json`.

Its three roots are

    [-6,0] x [-6,0], [-6,0] x [0,6], [0,6] x [0,6].

The other mixed quadrant is their reflection exchanging z_L,z_R. The
first two roots use the complete hand proofs(6) and(7)--(8). In the
positive root,32 leaves satisfy S<=1 and use(7);1,684 leaves have a
strict exact lower bound for max(G_1,G_2). Every remaining node is an
exact midpoint bisection retaining both closed children. There are
3,433 nodes and1,718 leaves in the compact cover; none is unresolved.

The lower bound for a row is the larger of its direct interval lower
bound and its centered mean-value lower bound. For a rational box I
with midpoint m and continuous piecewise differentiable function G,

    G(I) subset G(m)+sum_j partial_j G(I)(I_j-m_j).

At min, max, and absolute-value changes, the derivative enclosure is
the hull of all potentially active branches. The displayed formulas
have only positive square-root denominators. Integrating the derivative
enclosures along a segment proves the centered bound across all branch
changes; no branch selection is assumed from a floating sample.

The separate implementation `verify_central_linear_transfer.py`
reconstructs all three roots, all midpoint splits and analytic guards,
and recomputes every exact row. It uses standalone64-bit directed
dyadics and a separately written positive-quadrant expression; it
imports no producer code or producer arithmetic. Every numerical leaf
must have z_L,z_R>=0. The nonpositive and mixed roots are verified only
by their complete hand-lemma guards, so no signed-sum switching formula
is part of the numerical proof.

The complete independent replay passed all1,684 numerical leaves and
all34 analytic leaves, with no missing nodes. Its smallest exact lower
bound was

    5007949818049/1152921504606846976>0.

The certificate SHA-256 is

    771bf108f5441de0e46810bd924f9fad118d94072f121136f3ed2423f7c0616a.

The proof files are in `computer_assisted/`:

- `central_linear_transfer_compact.json`;
- `central_linear_transfer_compact_dyadic_replay.json`;
- `certify_central_linear_transfer.py`;
- `verify_central_linear_transfer.py`;
- the independent arithmetic module `verify_joint_five_dyadic.py`.

The paper reductions, reconstructed complete cover, and independently
replayed strict rational rows establish(1) throughout the entire stated
slope domain. No numerical sample or optimization termination is used
as a proof premise.
