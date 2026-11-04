# Three arbitrary unit squares have center energy at least 7/2

November 4, 2026. The complete physical proof, a separate mathematical
review, and two independent exact arithmetic evaluators have passed.
The root repeated both evaluators from a relocated frozen packet. Each
checked the same 128 closed angular triangles and 384 exact vertex
inequalities in rational arithmetic with sqrt(2). All ten frozen input
hashes remained unchanged. The verified archive contains fourteen members.

This is a shared theorem for three arbitrary original unit squares.
It adds **zero original-cell and zero mask closures**: the current register
remains **210 CLOSED / 21 OPEN**, and the mask ledger **8 CLOSED / 24 OPEN**.
`001/00`, its reversal, A.2, the unrestricted bound and global equality
remain OPEN. No Lean, Lake or CI; no human or proof-kernel verification is
claimed. Affine or lifted use requires a separately checked row conversion.

[Source-bound packet and root replay](computer_assisted/a2_shared_three_square_energy_manifest.json) ·
[Current handoff](HANDOFF_A2_FIXED_CLOSURE.md)

## Statement and proof scope

If three closed unit squares have pairwise disjoint interiors and centers
\(A,B,C\), with arbitrary rotations, then
\[
E=|A-B|^2+|B-C|^2+|C-A|^2\geq7/2.
\]
Three aligned squares centered at \((0,0),(1,0),(1/2,1)\) attain equality.
Touching is allowed. No enclosing circle or positive clearance is assumed.
This theorem earns zero original-cell and mask closures.

Numerical optimization suggested the dual vectors below. The proof uses
an exact finite table and the following geometric reductions; no numerical
optimum or floating-point grid is a premise. The accompanying checker
checks arithmetic and coverage, and must be read together with this proof.

## Pair separators and their ownership

Put \(f(t)=|\cos t|+|\sin t|\) and \(h(t)=(1+f(t))/2\).
For each disjoint pair, choose a separating axis normal to an edge of one
of its squares, and call that square the owner. Such an axis exists because
the difference body of two centered squares is a convex polygon whose edge
normals belong to their two original frames. A center difference outside its
interior violates at least one open supporting half-plane.

If \(n\) is the owner's signed unit normal directed towards the other center,
and the two frame angles differ by \(t\), their exact support condition is
\[
n\cdot(R-P)\geq h(t).
\]
The owner's half-width is \(1/2\); the other's is \(f(t)/2\).
Choosing another signed axis of either frame changes its angle by a multiple
of \(\pi/2\), leaving \(f\) unchanged. Always \(h(t)\geq1\).
Every pair of centers is also at distance at least one, since the open
radius-\(1/2\) disks in the square interiors are disjoint.

Choose one owner for each of the three pairs. Either a vertex owns two
edges, or the ownership orientation is a directed three-cycle. We handle
both exhaustive alternatives.

## Support triangle inequality

For every \(u,v\),
\[
f(u)+f(v)\geq1+f(u-v). \tag{1}
\]
Let \(d(t)\in[0,\pi/4]\) be the distance from \(t\) to
\((\pi/2)\mathbb Z\). Then \(d(u-v)\leq d(u)+d(v)\), and
\(f(t)=1+g(d(t))\), where \(g(x)=\cos x+\sin x-1\).
On this interval, \(g\) is nonnegative, nondecreasing and concave, and
\(g(0)=0\). If \(x+y\leq\pi/4\), concavity with endpoints \(0,x+y\)
gives \(g(x)+g(y)\geq g(x+y)\). If \(x+y\geq\pi/4\), reduce \(y\)
to \(\pi/4-x\) and use monotonicity to get
\(g(x)+g(y)\geq g(\pi/4)\). Consequently
\(g(d(u-v))\leq g(d(u))+g(d(v))\), proving (1).

## A vertex owns two edges

Translate its center to \(A=0\), and write the others as \(b,c\).
Its two signed normals are parallel or perpendicular.

If they agree, then \(n\cdot b,n\cdot c\geq1\).
For \(m=(b+c)/2,\ d=b-c\), we have \(|m|,|d|\geq1\), and
\[
E=2|m|^2+\tfrac32|d|^2\geq7/2.
\]
If they are opposite, \(|d|\geq2\), and already \(E\geq6\).

For perpendicular normals, rotate and possibly reflect so they are
\(e_x\) towards \(B\) and \(e_y\) towards \(C\).
Interchanging \(B,C\) and the two axes if necessary, assume the remaining
separator is owned by \(B\). Write its signed normal from \(B\) towards \(C\)
as \(n=(p,q)\), and set \(a=|p|,\ b_0=|q|\).
Then \(a,b_0\geq0,\ a^2+b_0^2=1\), and the three conditions are
\[
b_x\geq h,\quad c_y\geq s,\quad n\cdot(c-b)\geq t,
\]
where, by (1),
\[
h=(1+a+b_0)/2,\qquad s,t\geq1,\qquad s+t\geq1+h. \tag{2}
\]

For \(X=(b,c)\), let
\[
Q=\begin{pmatrix}2I&-I\\-I&2I\end{pmatrix},\qquad
Q^{-1}=\tfrac13\begin{pmatrix}2I&I\\I&2I\end{pmatrix}.
\]
Then \(E=X^TQX\). If \(LX=(b_x,c_y,n\cdot(c-b))\), the Gram matrix
\(G=LQ^{-1}L^T\) has diagonal \(2/3\), and
\[
G_{12}=0,\quad G_{13}=-p/3\leq a/3,\quad
G_{23}=q/3\leq b_0/3.
\]
Completing the square, for any componentwise nonnegative \(\lambda\),
\[
E\geq2\lambda\cdot(h,s,t)-\lambda^TG\lambda. \tag{3}
\]
With \(\lambda=(3/2,1,1)\), using \(s,t\geq1\),
\[
E\geq3h+4-\tfrac{17}{6}-a-\tfrac23b_0
 =\tfrac83+\tfrac12a+\tfrac56b_0. \tag{4}
\]
If \(a\leq15/17\), then \(3a+5b_0\geq5\), since
\[
b_0^2-(1-3a/5)^2=2a(15-17a)/25\geq0
\]
and \(1-3a/5\geq0\). Thus (4) gives \(E\geq7/2\).

With \(\lambda=(1,3/2,1)\), equation (2) gives
\(2h+3s+2t\geq4h+3\), whence
\[
E\geq4h+3-\tfrac{17}{6}-\tfrac23a-b_0
 =\tfrac{13}{6}+\tfrac43a+b_0. \tag{5}
\]
If \(b_0\leq24/25\), then \(4a+3b_0\geq4\), because
\[
a^2-(1-3b_0/4)^2=b_0(24-25b_0)/16\geq0.
\]
Equation (5) again gives \(E\geq7/2\).
The two sectors cover the whole nonnegative unit quarter-circle:
if \(a>15/17\), then \(b_0<8/17<24/25\).

## Directed cyclic ownership

Label the cycle \(A\to B\to C\to A\), with signed owner normals
\(n_0,n_1,n_2\). Let
\(d_0=B-A,d_1=C-B,d_2=A-C\); thus \(\sum d_i=0\) and
\(E=\sum|d_i|^2\).
Rotate so the normal angles are \(0,\theta,\phi\), with
\(\theta,\phi\in[0,2\pi]\). Since each normal is an axis of its original
square, the exact separation thresholds are
\[
s_0=h(\theta),\quad s_1=h(\phi-\theta),\quad s_2=h(\phi),
\qquad n_i\cdot d_i\geq s_i. \tag{6}
\]
For any \(\lambda_i\geq0\), put \(w_i=\lambda_i n_i\) and
\(\bar w=(w_0+w_1+w_2)/3\).
Expanding \(\sum|d_i-(w_i-\bar w)|^2\geq0\) and using (6) gives
\[
\begin{split}
E\geq\Phi_\lambda(\theta,\phi)
={}&2\sum_i\lambda_i s_i-\tfrac23\sum_i\lambda_i^2\\
&+\tfrac23\bigl(\lambda_0\lambda_1\cos\theta+
\lambda_1\lambda_2\cos(\phi-\theta)+
\lambda_2\lambda_0\cos\phi\bigr). \tag{7}
\end{split}
\]
We use only
\[
(1,1,1),\quad(3/2,1,1),\quad(1,3/2,1),\quad(1,1,3/2). \tag{8}
\]

### Concavity on a fixed sign triangle

Apart from a constant, each \(\Phi_\lambda\) is a sum of terms
\[
\lambda_i(|\cos u|+|\sin u|)
+\tfrac23\lambda_i\lambda_{i+1}\cos u, \tag{9}
\]
where \(u\) is one of \(\theta,\phi-\theta,\phi\), cyclically.
All vectors (8) satisfy \(0<\lambda_i\leq3/2\).
The coefficient of \(|\cos u|\), on either cosine-sign region, is
\(\lambda_i\pm(2/3)\lambda_i\lambda_{i+1}\geq0\);
the coefficient of \(|\sin u|\) is \(\lambda_i>0\).
On a fixed quadrant, (9) is therefore nonnegative and has second derivative
equal to its negative. It is concave there.
Composing with the three affine angle functions shows that
\(\Phi_\lambda\) is concave on every convex region retaining their signs.

### Complete finite cover and exact vertex checks

In units of \(\pi/4\), partition the entire angle square into
\[
\begin{array}{ll}
T_{k,j,0}:&(k,j),(k+1,j),(k+1,j+1),\\
T_{k,j,1}:&(k,j),(k,j+1),(k+1,j+1),
\end{array}
\qquad 0\leq k,j<8. \tag{10}
\]
These 128 closed triangles cover \([0,2\pi]^2\), including all shared
faces. Within each triangle the ranges of \(\theta,\phi,\phi-\theta\)
have integer endpoints and length at most one in these units.
Quadrant boundaries are even integers, so none lies strictly inside any
range. Thus the concavity argument applies on each triangle.

The literal file THREE_SQUARE_CYCLE_ENERGY_TABLE.json assigns one of
(8) to every triangle and lists its three values of
\(\Phi_\lambda-7/2\).
All vertex sine and cosine values lie in
\(\{0,\pm1,\pm\sqrt2/2\}\); every gap is exactly \(r+s\sqrt2\)
with rational \(r,s\).
The file check_three_square_center_energy.py independently reconstructs
all 384 gaps from (6)–(8), checks they are nonnegative, verifies that every
triangle address occurs once, and checks all sign-region and coefficient
conditions. Signs are checked by rational squaring; for example when
\(r<0<s\), nonnegativity is equivalent to \(2s^2\geq r^2\).
No numerical approximation to trigonometric values or \(\sqrt2\) is used.

By concavity, the value on a triangle is at least the barycentric average
of its three vertex values. Its selected \(\Phi_\lambda\) is therefore
at least \(7/2\) everywhere. Equations (7) and (10) prove the cyclic case.
Together with the star cases, this proves the theorem.

## Exact evidence and permitted consequence

The initial replay checks 128 triangles and 384 exact vertex inequalities.
The four vectors in (8) are used on 74, 24, 18 and 12 triangles respectively.
There are 54 vertex occurrences with zero gap.

| File | SHA-256 |
|---|---|
| THREE_SQUARE_CYCLE_ENERGY_TABLE.json | f656277b5a003aa7dc81e4403dc7c72e0f305bcf74512865cf515cca4c66d911 |
| check_three_square_center_energy.py | 9aaeff8302d18f88992aaa5fcd29b95cf5ec5ab4eaa63b107757146fa5b5fb2e |

Any three original physical squares inherit the theorem's pairwise interior
disjointness, so the center-energy inequality is unconditional on their
actual frames. An affine secant conversion still needs independent expansion
on the actual certified intervals. No whole original caller is closed here.

The independent mathematical review and both exact evaluators now pass.
The packet retains the original reviewed hand source unchanged, together
with its hash-bound review and the complete numerical discovery record.


## Reconstruct the committed packet

From `research/nine/computer_assisted`:

```sh
sha256sum a2_shared_three_square_energy_checkpoint.tar.gz
# Expected: 3d2a966fbaab1a00f6767e74a33a269c6dc38dc7f167455d7c0aa1a92051b5cf
tar -xzf a2_shared_three_square_energy_checkpoint.tar.gz
cd three_square_energy_package
python -B -S verify_all.py
```

The two evaluators share no imported candidate-checker code. Their complete
reports are compared with the separately retained accepted reports before
the wrapper records success. Source bytes are checked before and after.
