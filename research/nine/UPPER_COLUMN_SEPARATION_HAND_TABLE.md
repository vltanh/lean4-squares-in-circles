# Upper-column separation and the complete central-normal signs

Let Q=1105/256. All squares below are actual independently oriented unit
squares, with disjoint open interiors and all corners in the centered
closed Q-disk. No contact or separator owner is prescribed.

## 1. A five-row column theorem

**Theorem.** Two such squares whose center heights are both at least 3/5
have horizontal center distance strictly greater than 29/60.

Suppose the opposite, and select the square A with the higher center.
Write h for its horizontal (and vertical) projection halfwidth. Its
centered aligned square of halfwidth g=1/(4h) is contained in A. The
other square B contains the open radius-1/2 disk about its center.
Consequently the squared distance from B's center to A's aligned inset
must be at least 1/4. This remains necessary when actual squares touch.

Every contained unit-square center has norm less than rho=91/60:
the farthest squared corner norm is at least |c|^2+|c|+1/2, and
rho^2+rho+1/2-Q=31/57600>0. Also the uppermost vertex gives y_A+h<=sqrt(Q).
The rational comparison sqrt(Q)<133/64 follows from 17680<17689.
Thus

    y_A < min(91/60,133/64-h),  1/2<=h<=1/sqrt(2)<17/24.

For a row [a,b] of the following table, put

    g0=1/(4b),  H0=min(91/60,133/64-a).

Both the horizontal gap and the vertical gap from B's center to the
aligned inset are then bounded above, respectively, by

    (29/60-g0)_+,  (H0-3/5-g0)_+.

Indeed g>=g0, |x_B-x_A|<=29/60, and 0<=y_A-y_B<H0-3/5.
All entries are exact rational numbers.

| Closed h interval | g0 | H0 | 1/4 minus the sum of the two squared gap bounds |
|---|---|---|---|
| [1/2,23/40] | 10/23 | 91/60 | 14693/952200 |
| [23/40,3/5] | 5/12 | 481/320 | 1643/184320 |
| [3/5,5/8] | 2/5 | 473/320 | 13319/921600 |
| [5/8,13/20] | 5/13 | 93/64 | 3232367/155750400 |
| [13/20,17/24] | 6/17 | 457/320 | 1917191/266342400 |

The intervals cover every physical h, including all shared boundaries.
Every reserve is strictly positive. B's center therefore has distance
less than 1/2 from A's inset, contradicting physical interior nonoverlap.
This proves the theorem, including horizontal distance exactly 29/60.

## 2. Central order in the wider five-square cap

Let L,U,R be three distinct original squares satisfying

    x_L<=0<=x_R,  |x_U|<=29/60,
    y_L,y_R>=3/5,  y_U-h_U>=1/10.

Since h_U>=1/2, all three center heights are at least 3/5. If x_R<=x_U,
both x_R and x_U belong to [0,29/60], contrary to Section 1. Thus
x_R>x_U. The reflected argument gives x_L<x_U. Neither an outsider's
orientation nor an arbitrary ordering of the two central squares has
been assumed.

Every center height is less than 91/60, so each relevant vertical
center difference has magnitude less than

    91/60-3/5=11/12<1.

For the directed displacement d=c_R-c_U, let n be a genuine unit
separating normal from U to R supplied by the rectangle separating-axis
theorem. If n_x<=0, then d_x>0 implies

    n.d <= |n_y| |d_y| < 1.

Each physical square contains a centered radius-1/2 disk, so its support
halfwidth in n is at least 1/2. Their sum is at least one, contradicting
separation. Therefore n_x>0. Division by its positive horizontal
component gives the complete directed representation

    m_R=(1,z_R),  z_R in R.

Similarly every genuine directed normal from U to L has negative
horizontal component, giving

    m_L=(-1,z_L),  z_L in R.

This accounts for every physical owner and all touching boundaries.
Vertical and oppositely directed horizontal components have been
excluded by an inequality, rather than omitted from a finite cover.

## 3. Scope and reproduction

This theorem removes the central-normal sign restriction in a possible
wider five-square cap. It is not a new whole-mask closure. An application
still has to establish all displayed position and height conditions for
three distinct original squares, and the relevant endpoint envelopes.

The independent arithmetic reconstruction in
`verify_upper_column_table.py` recomputes the five rows from their
endpoints and checks the complete cover and radical comparisons. The
five-row argument above is the proof. No Lean, Lake or CI is used.
