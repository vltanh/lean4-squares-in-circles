# Physical normal signs for a genuinely weak center-cone pair

November 2, 2026. Complete hand proof. Independently checked by the
weak-outer hand agent. No numerical calculation, Lean, Lake, or CI is
needed. The strict weak bit is essential and is retained explicitly.

Let two original physical unit squares O,T have disjoint open interiors.
In the chosen coordinates their center difference is `(d,v)`, where

\[
                 d\ge v\ge0,\qquad d<h_O+h_T.
\]

Here `h_S=H_S(e)=H_S(f)` is the true coordinate halfwidth of the original
square S. Let n be any signed unit separating normal owned by an axis of
one of the two original squares, so

\[
                 n\cdot(d,v)\ge H_O(n)+H_T(n).
\]

**Theorem.** Every such usable normal satisfies `n_x>0`. If `n_y<0`,
then also `|n_y|<n_x`.

## 1. Exclude every nonpositive horizontal component

If both components of n are nonpositive its projection on `(d,v)` is
nonpositive, while the support sum is at least one. Otherwise, when
`n_x<=0`, write `n=(-beta,alpha)` with `alpha>0`, `beta>=0`, and
`alpha^2+beta^2=1`.

If `alpha<beta`, then

\[
 n\cdot(d,v)=-\beta d+\alpha v
             \le(\alpha-\beta)d\le0,
\]

again impossible. Suppose `alpha>=beta` and choose O to be a genuine
owner of n. Its exact horizontal width and normal support are

\[
 h_O=(\alpha+\beta)/2,
 \qquad H_O(n)=1/2=(\alpha-\beta)h_O+\beta^2.
\]

The other original square retains its arbitrary original orientation.
Every square support function is invariant under a quarter turn of its
argument, since the square itself has quarter-turn symmetry about its
center. Therefore

\[
 H_T(n)=H_T((\alpha,\beta)).
\]

Subadditivity, positive homogeneity, and the equality `H_T(e)=H_T(f)=h_T`
give the reverse-triangle lower bound

\[
 \begin{split}
 H_T((\alpha,\beta))
 &\ge H_T(\alpha e)-H_T(\beta f)\\
 &=(\alpha-\beta)h_T.
 \end{split}
\]

Thus the physical support sum is at least

\[
              (\alpha-\beta)(h_O+h_T)+\beta^2.
\]

The center projection is at most `(alpha-beta)d`. If `alpha>beta`, the
strict weak inequality makes this strictly smaller than the displayed
support sum. If `alpha=beta`, its projection is nonpositive while the
term `beta^2=1/2` is positive. Both possibilities are impossible.

This argument includes `beta=0`, when the normal is vertical: the strict
weak comparison and `v<=d` exclude vertical separation. Hence `n_x>0`.

## 2. Exclude downward steep normals

Suppose `n_y<0` and `|n_y|>=n_x>0`. Then `n_x<=1/sqrt(2)`, while
`h_O+h_T<=sqrt(2)`. Consequently

\[
 n\cdot(d,v)\le n_xd
       <n_x(h_O+h_T)\le1.
\]

Each original square has support at least one half on a unit normal, so
the required physical support sum is at least one. This is a
contradiction, proving the second assertion.

## 3. Complete signed-owner table

Represent either original owner's frame by
`u=(alpha,beta)`, `w=(-beta,alpha)`, where `alpha>=|beta|` and `alpha>0`.
For each owner the eight-normal union over the two squares reduces as
follows; owners are still kept separately.

| Signed owned normal | Status in the exact weak-cone domain |
|---|---|
| `+u=(alpha,beta)` | Retained for either beta sign |
| `-u=(-alpha,-beta)` | Impossible: nonpositive horizontal component |
| `+w=(-beta,alpha)` | Retained only when `beta<0` |
| `-w=(beta,-alpha)` | Impossible: nonpositive horizontal component or downward steep |

For `+w`, `beta=0` is also impossible. A numerical or rational LP may
retain the weaker closed condition `beta<=0` as a necessary condition
inside the retained branch. It must not claim that the table excludes a
configuration whose original marked bit was changed to an actual link.

In particular, a physical configuration on `d=h_O+h_T` is outside this
lemma's hypothesis. Its equality faces may be preserved elsewhere in the
global proof and are not removed from the positional-root ledger by this
normal reduction.
