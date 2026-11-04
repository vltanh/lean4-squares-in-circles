# Independent review of three-square center-energy row conversion

November 4, 2026. The independently checked three-square theorem now has
reusable affine and moment-row conversions. The root relocated replay
reruns both exact geometric evaluators and all **1,877 exact polynomial
identities**, with all **21 frozen inputs** unchanged. The packet includes
the geometric hand proof, independent mathematical review, complete finite
table, coefficient review, source-reviewed wrapper and exact reports.

This is a shared necessary inequality, so it closes **zero original cells
and zero masks**. The fixed register remains **212 CLOSED / 19 OPEN** and
the mask ledger remains **8 CLOSED / 24 OPEN**. Every future complete
original proof must retain actual physical-square nonoverlap and prove
every projection interval used by an affine row. No Lean, Lake or CI was
run, and no human or proof-kernel verification is claimed.

[Geometric theorem](THREE_SQUARE_CENTER_ENERGY_HAND_PROOF.md) · [Immutable packet](computer_assisted/a2_shared_three_square_energy_rows_manifest.json) · [Root relocated replay](computer_assisted/a2_shared_three_square_energy_rows_root_replay.json)

**Accepted exact conversion, with the original physical and interval
premises retained.** The separate producer
three_square_energy_rows.py has SHA-256
712f594cfd4ec93f57d5c75c4f768592d1a70063fa2573959bfce4b674495547.
It implements consequences of the independently reviewed theorem
\[
E_T=\sum_{i<j,\ i,j\in T}\|c_j-c_i\|^2\geq7/2
\quad (|T|=3)
\]
for three of the same retained physical unit squares with pairwise disjoint
interiors. No angle or separation alternative is added.

## Affine rows

For each pair in the triple, choose either its two Cartesian projections
\((d_x,d_y)\), of weight one, or the orthogonal diagonal projections
\((d_x+d_y,d_x-d_y)\), each of weight one-half.
For either choice the weighted squared projections sum to
\(d_x^2+d_y^2\).

Every selected projection \(p\) must have its own already certified
interval \(l\leq p\leq u\). Its secant residual is
\((p-l)(p-u)\leq0\).
Therefore
\[
\frac72-E_T+\sum_p w_p(p-l_p)(p-u_p)\leq0.
\]
All quadratic terms cancel, leaving exactly
\[
-\sum_p w_p(l_p+u_p)p
\leq-\frac72-\sum_p w_p l_pu_p. \tag{1}
\]

The row name contains the three increasing original indices and the
three-bit Cartesian/diagonal code in increasing pair order.
The independent helper reconstructs each pair's coefficients directly.
For diagonal intervals \([a,b]\) and \([c,d]\), the coefficients before the
overall negative sign are
\[
w_x=(a+b+c+d)/2,\qquad
w_y=(a+b-c-d)/2,
\]
and the constant contribution is \((ab+cd)/2\).
These agree with (1) and the declared orientation
\((d_x,d_y)=c_j-c_i\).

The independent row checker separately expands the entire polynomial
\(7/2-E_T+\sum w(p-l)(p-u)\) in the original center variables and requires
that every quadratic term vanish. Thus agreement is checked against the
geometric theorem plus the exact secant products, not merely against
another enumeration of the producer's coefficient loop.

## Moment rows

The exact quadratic inequality is \(-E_T\leq-7/2\).
The independent reconstruction uses the three-center centroid identity
\[
-E_T=\left\|\sum_{i\in T}c_i\right\|^2
       -3\sum_{i\in T}\|c_i\|^2.
\]
Hence every selected coordinate square has coefficient \(-2\), and every
within-axis cross product between two selected centers has coefficient
\(+2\). All other variables have zero coefficient.

The original-variable count is 54. The standard upper-triangular lift adds
1,485 degree-two monomials, for a total of 1,539 coordinates.
The helper's explicit index formula was checked against an independent
enumeration of those monomials and against the existing moment-lift
implementation. The polynomial adapter was checked separately using the
centroid expression.

## Exact audit and reusable interface

The standard-library-only audit checks:

| Case | Rows |
|---|---:|
| All Cartesian triples | 84 |
| Every Cartesian/diagonal combination | 672 |
| Diagonal data supplied with mixing disabled | 84 |
| Partial diagonal availability | 197 |
| Asymmetric rational and degenerate intervals | 672 |
| Independent moment centroid expansion | 84 |
| Existing moment-lift implementation | 84 |
| Total | 1,877 |

The report is THREE_SQUARE_ENERGY_ROW_REPLAY.json.
The reusable independent module is independent_three_square_energy_rows.py,
SHA-256 d7f0e356bf268e6c9396287c1d1cadbebc32505b6dd71771e999f918baba5edc.
It exposes:

    linear_row(name, differences, diagonal=None)
    moment_row(name)
    moment_polynomial(name, independent_polynomial_module)

The first function reconstructs an affine row on the caller's certified
interval dictionaries. The second uses the fixed 54-variable monomial
ordering directly. The third is an adapter for the existing independent
polynomial checker API. None imports a producer or numerical solver.

The coefficient audit intentionally imports the producer being compared,
as untrusted code under review. That audit is separate from the reusable
physical row reconstruction used by complete proof checkers.

## Caller obligations

The original caller must supply the same three physical unit squares and
their actual pairwise interior disjointness. Disjoint point incircles
alone do not imply this \(7/2\) theorem. Every Cartesian or diagonal
interval used in an affine row must already be proved on that exact
caller, with all original frames and labels retained.

The fixture is an algebra input and does not prove its original ancestry.
The row check introduces no geometric subdivision and earns zero original
cell or mask closures. A whole-original certificate still requires its
complete caller, all used rows and final contradiction to be independently
replayed.


## Reconstruct the committed packet

From `research/nine/computer_assisted`, run:

```sh
cat a2_shared_three_square_energy_rows_checkpoint.tar.gz | sha256sum
# Expected SHA-256: b8cd0f25f76f2815fe1f0079d5cbe07181d30752476cf334c19b4f592ddae41d
tar -xzf a2_shared_three_square_energy_rows_checkpoint.tar.gz
cd three_square_energy_rows_package
python -B -S verify_all.py
```
