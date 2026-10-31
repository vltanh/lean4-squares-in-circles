# A radial side arm cannot return through a boundary detour

Date: October 25, 2026.

**Status: accepted complete hand proof after independent saved-source review.**
See `REVIEW_SIDE_ARM_BOUNDARY_DETOUR_2026_10_25.md` for the full
arm, radius, equality, inherited-theorem and original-gate review.
This manuscript extends the central-channel theorem to a genuine
two-edge radial side arm. The original arm is retained as two physical
bodies, and the theorem allows arbitrary additional positive forces at
its other endpoint. It adds no computational certificate.

Work with the original nine physical unit squares, the compatible
selected physical certificate, and

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad \delta=d-1.
\tag{1}
\]

## 1. The whole local theorem

Let \(L-U-A\) be an actual positive arm with these exact premises:

* \(L\) is a genuine degree-one radial S leaf, with radial direction
  \(e\), so its actual occupied square is
  \([d,d+1]e+[-1/2,1/2]Je\), and its actual inner application is
  \(de\).
* \(U\) has true positive degree two, zero circle load, and side-normal
  reserve one. Its only positive neighbors are \(L,A\).
* The original torque equation at \(U\) therefore gives the unchanged
  application on \(A\) as
  \[
                     p=\delta e\in A.
  \tag{2}
  \]
  The physical square \(U\), its transverse position and its actual
  side means are not removed or replaced by a leaf.

Suppose there is another actual positive normal channel from \(A\)
to a distinct physical square \(C\), with total reserve \(w\ge1\).
Every internal channel body has its true unloaded degree-two equation;
none has had another positive force deleted. Write \(n\) for the
channel direction from \(A\) to \(C\), and \(\alpha\) for its
actual support value. Thus

\[
 A\subset\{x:n\cdot x\le\alpha\},\qquad
 C\subset\{x:n\cdot x\ge\alpha+w\}.
\tag{3}
\]

The channel is distinct from the displayed arm, and \(C\ne L\).
Allow arbitrary actual degrees, forces and physical circle masks at
\(A,C\).

**Theorem.** No physical circle-touching square \(B\), distinct from
the channel bodies, can touch both \(A\) and \(C\). Moreover, when
\(d<1\), the second channel itself is impossible, without any
boundary-detour premise.

The boundary contacts \(AB,BC\) need only be physical contacts; their
stress weights may vanish. All original remaining squares remain
arbitrary and fixed.

## 2. The sharp center estimate retains the equality case

For every contained unit square \(T\), let \(c_T\) be its center and
\(u,v\) its orthonormal side axes. The actual maximum squared corner
radius is

\[
 |c_T|^2+\frac12+|c_T\cdot u|+|c_T\cdot v|.
\]

Since \(|a|+|b|\ge\sqrt{a^2+b^2}\), containment gives

\[
 |c_T|^2+|c_T|+\frac12\le R^2,
 \qquad |c_T|\le d+\frac12.
\tag{4}
\]

Every directional halfwidth of a unit square is at least \(1/2\).
Applying (4) to the actual far endpoint in (3),

\[
 \alpha+w+\frac12
 \le n\cdot c_C\le |c_C|\le d+\frac12.
\tag{5}
\]

Therefore

\[
                         \alpha\le d-w\le d-1=\delta.
\tag{6}
\]

These statements require neither a circle force nor a circle contact
on \(C\). No application point in (2) or (3) has been fixed by
convenience; both come from their actual channel equations.

## 3. Below \(d=1\), the far endpoint would repeat the genuine leaf

Suppose \(d<1\), so \(\delta<0\). The point (2) and support (3)
give

\[
       \alpha\ge n\cdot p=\delta(n\cdot e)\ge\delta,
\tag{7}
\]

because \(n\cdot e\le1\) and \(\delta<0\). Combining (6) and
(7) forces

\[
              \alpha=\delta,\qquad w=1,\qquad n=e.
\tag{8}
\]

The last conclusion follows from equality in (7), since \(\delta\)
is strictly negative. Every inequality in (5) is now equality. In
particular

\[
                  c_C=(d+1/2)e,\qquad H_C(e)=1/2.
\tag{9}
\]

For a unit square,
\(2H_C(e)=|e\cdot u|+|e\cdot v|\). Equality to one, together
with \((e\cdot u)^2+(e\cdot v)^2=1\), says that one component is
zero and the other has absolute value one. Consequently \(e\) is
one of its side axes. Equations (9) determine the entire occupied
square exactly:

\[
                  C=[d,d+1]e+[-1/2,1/2]Je=L.
\tag{10}
\]

This contradicts distinctness of the original physical units. Thus
there is no second channel at all when \(d<1\). This equality
argument keeps all transverse means and does not assert that the
channel end was loaded before it became forced to be radial.

## 4. At and above \(d=1\), use the complete central-detour theorem

Suppose \(d\ge1\). Equation (2) supplies an actual point of \(A\)
with norm \(\delta\), so

\[
                      \operatorname{dist}(0,A)\le\delta
                        =\max(d-1,0).
\tag{11}
\]

Theorem 4.1 of
`FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md` applies directly to (3) and
(11). Its exact hypotheses are an arbitrary contained unit \(A\)
meeting that central disk, an actual normal channel of reserve at
least one, and a physical circle-touching common neighbor of its
endpoints. It uses no force equation at either channel endpoint or
at the boundary detour body. It does not require that \(A\) itself
have a genuine leaf.

For completeness, its argument is the following uniform geometry.
The radius window gives \(0\le\delta<1/60\). Equations (6) and
(11) put the original channel support in
\(-\delta\le\alpha\le\delta\). Hence every point of \(C\)
has \(n\)-projection greater than \(59/60\), and its entire
angular shadow lies within
\(\beta=\arctan(13/20)\) of \(n\). An actual contact
\(q\in A\cap B\) has norm greater than \(3/5\), while
\(n\cdot q\le\delta\), so its angle from \(n\) is greater
than \(\arccos(1/36)\). Every physical circle-touching square
has angular shadow shorter than
\(\omega=\arctan(23/16)\) in this radius interval. Its other
contact \(p\in C\cap B\) would therefore require

\[
 \arccos(1/36)<\angle(n,q)
   \le\angle(n,p)+\angle(p,q)<\beta+\omega.
\]

But the exact comparison in that source is

\[
 \cos(\beta+\omega)=\frac{21}{\sqrt{446665}}>\frac1{36},
 \qquad \beta+\omega<\frac\pi2,
\]

which reverses the required angle inequality. This includes the
whole endpoint \(d=1\). Thus the actual boundary detour is
impossible at and above it, completing the theorem over (1).

## 5. One original complete six-body family closes

Use the exact C4 cyclic order \(A-B-C-D-A\), with the actual
length-two arm \(A-U-L\), and the full block-load representative
\(BC\) from `FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md`.

* In the S/side arm alternative, \(L,U,A\) satisfy Section 1.
* \(D\) is a true unloaded degree-two body. Its original channel is
  \(A-D-C\), with reserve at least one. Its actual side means remain.
* \(B\) is a positively loaded, hence physically circle-touching,
  common neighbor of \(A,C\). Both physical detour contacts are
  original positive edges.
* The distinct square \(C\) is not the actual leaf \(L\).

All premises hold over the entire original load/leaf/width family,
including every physical mask, circle-weight endpoint, contact owner,
shared mean and all three arbitrary completion squares. Therefore the
single pre-existing gate

    M6.B4L2.C4.CHAIN.LBC.S_SIDE

has a complete core contradiction. The reflection fixing \(A\)
exchanges \(B,D\), so this representative already includes the
reflected adjacent-load placement; it is not a newly added gate.

No other whole original gate is claimed closed by this manuscript.
The S/diagonal and D/side arm types do not have point (2); the
opposite-load and three-block-load C4 arms lack this exact channel
and boundary-detour combination. They retain their full obligations.
The root-degree-independent theorem can be used in larger graphs
whenever its actual arm/channel/detour premises have been established.

The complete C1.4.b2 cell, unrestricted sharp bound, all original
equality packings and earlier prerequisite-chain audit remain open.
No Lean compilation, CI, numerical pose subdivision or coefficient
certificate is used.
