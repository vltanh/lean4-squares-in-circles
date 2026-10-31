# Two intact petals forbid every unloaded degree-two neighbor, including cyclic neighbors

Date: October 26, 2026.

**Status: complete hand implication; full root and separate independent reviews accepted.**
All hypotheses and the common selected-packing scope are those of
GLOBAL_CLOSURE_TWO_INTACT_PETALS_CENTRAL_DISK.md. Keep H's two
distinct intact loaded end triangles and every additional original
force. Put epsilon=max(sqrt(R^2-1/4)-2,0)<1/60.

## 1. The stronger uniform central disk

The conclusion of that source strengthens to

    D_(1/40) is contained in int H.                     (1)

Indeed O is already in int H. If (1) failed, an actual H side would
have height sigma<=1/40. Neither it nor its opposite side could be
an intact petal's actual common side: their heights are respectively
at most 1/40<1/5 and at least 39/40, whereas every common petal side
has height strictly between 1/5 and 39/40.

The two distinct petals must therefore use the two perpendicular
sides, using the accepted one-petal-per-side theorem. On each such
side of height P, its original strictly straddling ports supply a
boundary-tip point with positive transverse coordinate at most
sigma<=1/40. Hence

    P^2 > (67/120)^2-(1/40)^2
        = 4480/14400 = 14/45 > 1/4.

Both opposite perpendicular side heights would exceed 1/2, which
contradicts their sum one. This proves (1) with its entire closed
disk strictly inside H. All physical masks, original means, parallel
petal cases and port endpoints are inherited unchanged.

## 2. Every true unloaded degree-two neighbor is impossible

Let U be an actual positive neighbor of H, with true positive degree
two, zero total circle load, and other actual neighbor V. H and V
can have arbitrary additional forces. The complete actual
transmission law says its two opposite applications transmit one
normal n, with reserve w>=1:

    H subset {x:n.x<=h},  V subset {x:n.x>=h+w},
    h=h_H(n).

Equation (1) gives h>1/40. The sharp contained-neighbor support
theorem gives h+w<=d, where d=sqrt(R^2-1/4)-1<61/60.
But

    h+w > 1+1/40 =41/40 >61/60 >d.

This is impossible. No cyclic edge was declared a bridge. No
mean was replaced by a midpoint, and no additional U force was
deleted: its true degree two is an explicit hypothesis.

**Theorem.** A root of two intact triangle petals cannot have
any truly unloaded degree-two positive neighbor in the original
selected component, whether that neighbor belongs to a bridge
forest or to another cyclic block.

The stronger disk statement needs no minimum-support choice
beyond the common compatible intact-petal scope. Neither does
this channel consequence: its genuine two-force equation and
contained-neighbor bound suffice.

## 3. Original larger-block consequences and nonclosures

If a third simple cyclic block C_k meets H and has no other
articulation at either immediate H neighbor, those two neighbors
retain their true positive degree two. Both are therefore
positively loaded by Section 2.

For example, in the original nine-body common-root layout with
cyclic block sizes 3,3,5, the two pentagon neighbors of H must
both be positively loaded. Every force at the true degree-six H
and every force in the pentagon remains. The other two pentagon
vertices retain their original possible load assignments and
physical masks.

This is a complete original load-family exit, not a closure of
the entire C3.335.b0 cell or of an arbitrary rooted pentagon.
A chord or another articulation can change a neighbor's true
degree and must be retained before using this theorem.

No new checklist label, numerical certificate, pose sample,
Lean compilation or CI is introduced.

