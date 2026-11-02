# A complete union of three physical endpoint classes for the shoulder terminal

November 2, 2026 UTC. Hand proof, joining the exact support theorems
with their physical caller hypotheses. No mathematical program, Lean,
Lake, or CI is used.

Put Q=1105/256, r=sqrt(Q), a=46, b=27/2, and T=211/4.
For a physical unit S let h_S be its common horizontal and vertical
projection halfwidth, and let H_S(v) be its centered support function.

## 1. The physical seven-square theorem

Let four physical units form an actual horizontal projection chain
\[
                     M_0<_xM_1<_xM_2<_xM_3.
\]
Let L,C,R be three other units. All seven are interior-disjoint in
one centered disk. Suppose
\[
 x_L\le-29/60,\quad |x_C|<29/60,\quad x_R\ge29/60,
 \qquad y_C-h_C\ge7/60.                                 \tag{1}
\]
There are genuine physical separating normals from C toward L and R,
respectively proportional to
\[
                  (-1,\epsilon_L u),\qquad(1,\epsilon_R v),
 \quad u,v\ge0,\quad\epsilon_L,\epsilon_R\in\{-1,1\}.  \tag{2}
\]
The central normal owners are unrestricted, and no slope is bounded.

For each matched endpoint pair (M0,L) and (M3,R), assume one of
the following three alternatives. The choice is independent on the
two sides.

| Alternative | Exact physical premise |
|---|---|
| Vertical comparison | y_A-y_M>=h_A+h_M |
| Main-owned separator | An upward unit separator n=(c,s), s>=|c|, parallel to a side axis of M |
| Outward shoulder-owned separator | An upward unit separator n=(c,s), s>=|c|, parallel to a side axis of A, with c<=0 on the left and c>=0 on the right |

Here M is the matched outer main and A the shoulder. An upward
physical separator means
\[
                  n\mathbin{\cdot}(c_A-c_M)\ge H_M(n)+H_A(n).
\]
The vertical comparison is separately allowed even when the vertical
axis is not owned by either square.

**Theorem.** Under these premises the disk has squared radius at
least Q. At radius r, all slopes in (2) vanish. Any selected
nonvertical endpoint separator from the second or third alternative
is impossible at equality. The resulting actual upper three-chain
L<_xC<_xR routes to the physical4+3 sharp terminal.

This is a physical theorem about the stated class. It does not
assert that an arbitrary packing supplies the endpoint alternatives.

## 2. The common transfer inequalities

It suffices to consider a containing radius at most r. The actual
four-chain gives adjusted endpoint span
\[
                     D=x_3-x_0-h_0-h_3\ge2.             \tag{3}
\]
For a left transfer from L to C, put Y=y_C, h=h_C and
\[
                  A_L=a(-x_0-h_0)+b(1-x_C-h).
\]
Define A_R by horizontal reflection. The downward transfer has
a physical normal from the shoulder to C proportional to (1,-z)
in its reflected left-end frame. Each endpoint alternative supplies
\[
 A_i\le T-bE_i(z)-bz(Y-h-1/10),                         \tag{4}
\]
where E_i(z)=H_C(w_i(z))+(1+z)h-(1+z)>=0.
It also supplies the stronger center-cost inequality
\[
             a(-x_0-h_0)+b(1/2-x_C)\le T                \tag{5}
\]
and its right reflection, using the floor7/60 in (1).

For an upward transfer, each alternative supplies
\[
 A_i\le T-bE_i(z)-b\Psi_i(z)-bz(r-h-Y),                 \tag{6}
\]
after dropping any additional nonnegative endpoint reserve. Its
shoulder reserve satisfies
\[
                 \Psi_i(z)>(1/10)\min(z,1)\quad(z>0).
                                                                    \tag{7}
\]
For either oblique owner alternative it also satisfies
\[
                       \Psi_i(z)>(21/10-r)z\quad(z>0). \tag{8}
\]
For the original vertical alternative, (8) is needed only through
z<=11/2. That bound follows from (1), the outsider strip, the
endpoint whole shoulder floor3/8, and physical separation, exactly
as in Section8 of the shared-central source. Thus every upward
transfer used here has the required reserve.

Equations (4)--(8) are the conclusions, with matching premises, of
the following complete source pairs:

- Vertical: `DOWNWARD_TRANSFER_WITH_CENTRAL_CENTER_COST_HAND_PROOF.md`,
  `DOWNWARD_THREE_SQUARE_CAP_FLOOR_ONE_TENTH_HAND_PROOF.md`, and
  `SHARED_CENTRAL_ORIENTATION_AND_ALL_MIXED_SHOULDER_SIGNS_HAND_PROOF.md`.
- Main-owned: `ENDPOINT_OWNED_OBLIQUE_DOWNWARD_CENTER_TRANSFER_HAND_PROOF.md`
  and `ENDPOINT_OWNED_OBLIQUE_UPWARD_TRANSFER_HAND_PROOF.md`.
- Outward shoulder-owned: `SHOULDER_OWNED_OUTWARD_DOWNWARD_TRANSFER_HAND_PROOF.md`
  and `SHOULDER_OWNED_OUTWARD_UPWARD_TRANSFER_HAND_PROOF.md`.

Each uses actual physical supports. They retain one orientation and
one height for C; none assigns it two independent poses.

## 3. All four central sign combinations and equality

If both transfers are downward, add (5) and its right reflection.
The central x-coordinates cancel and yield
\[
                        aD+b\le2T=2a+b.
\]
Strict subcritical containment contradicts (3).

If both transfers are upward, the proved universal common-orientation
inequality bounds the sum of the two E terms below by
\[
 (2h-1)-(1/10)\{\min(u,1)+\min(v,1)\}.
\]
The two reserves (7) pay this complete loss. The top-height slacks
are nonnegative, so adding (6) again gives aD+b<=2T.

For either mixed pair, write m=min(u,v). The retained central E
terms and the two central height slacks together are at least
\[
                         (2h-1)-m(21/10-r).
\]
This is the exact shared-height inequality in Section7 of the
shared-central source, using Y-h>=1/10 and alpha_C<=1. The upward
reserve (8) pays the deficit since its slope is at least m. Adding
(4) and (6) gives the same aD+b<=2T conclusion.

The transfer inequalities are strict at a subcritical radius, and
their common-orientation or scalar reserves exclude a positive
central slope at Q. A nonvertical selected endpoint normal gives
a further strict reserve in either owner class. Hence equality
leaves the actual three-chain stated in Section1; the physical4+3
terminal applies to those same seven units. This proves the theorem.

## 4. The bounded-inner caller leaves only strictly inward endpoint axes

The bounded-inner-height extraction supplies all premises (1),(2),
with the stronger central floor109/930, whenever
|y_M1|,|y_M2|<7/20. It also proves, for the left matched pair,
\[
                 2/5<d_x=x_L-x_0<1,
 \qquad 0<d_y=y_L-y_0<197/120.                           \tag{9}
\]
The upper bound follows from y_L<91/60 and y_0>=-1/8.
Horizontal reflection gives the corresponding positive inward gap
on the right.

Every directed separating normal for this pair is upward: if its
vertical component were nonpositive, its center projection would
be less than d_x<1, whereas the sum of the two physical support
halfwidths is at least one.

Now consider an outward separating axis on the left, n=(-t,s),
t>=0, s>0, t^2+s^2=1. It cannot be nearly horizontal. If t>=s,
(9) would give
\[
 n\mathbin{\cdot}(c_L-c_0)
 <-\frac25t+\frac{197}{120}s
 \le\frac{149}{120}s
 \le\frac{149}{120\sqrt2}<1,                            \tag{10}
\]
where the final squared comparison is149^2=22201<28800.
This contradicts physical separation. Thus s>t.

Choose the axis from the physical side-axis alternatives of the
separating-axis theorem. If the main owns it, the
second alternative applies; if the shoulder owns it, the third
applies. A vertical comparison is already the first alternative.
Therefore an outward endpoint separating axis is entirely covered,
with no separate outward nearly horizontal branch.

In particular, any remaining strict counterexample in this bounded
inner-height class must have at least one matched pair with no
vertical comparison, no main-owned nearvertical separator, and
**only strictly inward separating axes**. These remaining axes are
shoulder-owned inward axes or nearly horizontal inward main-owned
axes. This is a necessary condition for the remaining counterexample,
not an exclusion of that domain.

The same direction argument applies to any other routed triple
whose matched endpoint gaps satisfy (9). No global caller or
unrestricted equality classification is asserted by this note.
