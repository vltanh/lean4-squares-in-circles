# Center-distance chords for two original unit squares

The only physical premises are two distinct original unit squares with disjoint open interiors. Their open inscribed disks of radius 1/2 are disjoint, hence the squared distance between the original centers is at least 1. This statement uses the physical unit frames, not any relaxed frame length at a numerical point.

Let d be one signed Cartesian component of the center difference, with a certified interval proving d>=0. Let t be its other component, with a certified interval contained in [L,U], where -1<=L<U<=1. Choose rational a,b>=0 satisfying a²+L²<=1 and b²+U²<=1. Set w=(t-L)/(U-L), so 0<=w<=1, and ell=(1-w)a+w*b.

Both vectors (a,L),(b,U) lie in the closed unit disk. Direct expansion gives

    ell²+t² = (1-w)(a²+L²)+w(b²+U²)
                -w(1-w)((a-b)²+(L-U)²) <=1.

Since d²+t²>=1, we have d²>=ell². Both d and ell are nonnegative, so d>=ell. Thus, for m=(b-a)/(U-L), the necessary affine row is

    -d+m*t <= m*L-a.

All signs, both axes, closed interval endpoints, zero endpoint heights and tangency are included. The declared d-sign and t interval must be proved for the same original pair in the state consuming the row; they cannot be borrowed from another child or pair. Wider enclosing transverse intervals are allowed. The producer chooses lower dyadic approximations to the two square roots, but the independent checker only checks the two exact endpoint inequalities, the state guards and every literal coefficient.

No orientation sign, selected SAT axis, exact mask or circle radius is needed. The original nine-square callers retain all original squares and pair predicates. Adding this necessary row preserves their strict radius, strict weak link and all covering faces. A numerical point violating it is a relaxation diagnostic, not a physical configuration. No original or mask closure is obtained from this family alone.
