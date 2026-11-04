# Root physical review: frame and projection square rows

Reviewed November 4, 2026. Both identities and independent reconstruction
procedures are accepted as conditional necessary-row tools. No original-cell
or mask closure follows from these identities alone.

## 1. The same two physical frames

For distinct original squares i,j, let `u_i=(alpha_i,beta_i)` and
`v_i=(-beta_i,alpha_i)`, and similarly for j. These are their actual unit
frames in one realization. A retained SAT alternative already has the
physical products `z2=alpha_i alpha_j`, `z3=beta_i beta_j`,
`z4=alpha_i beta_j`, and `z5=beta_i alpha_j`. Thus, writing
`C=z2+z3` and `S=z4-z5`, the cross-frame dot products are
`u_i·u_j=v_i·v_j=C`, `u_i·v_j=-S`, and `v_i·u_j=S`.

For arbitrary rational x,y,a,b,c,d, the norm of
`(x,y)+a u_i+b v_i+c u_j+d v_j` has constant term
`x²+y²+a²+b²+c²+d²`. Its affine terms are exactly

```
2(xa+yb) alpha_i + 2(ya-xb) beta_i
+ 2(xc+yd) alpha_j + 2(yc-xd) beta_j
+ 2(ac+bd) C + 2(bc-ad) S.
```

Moving these terms to the left gives the producer's row. This derivation
checks the signs of both mixed quarter-turn products explicitly. The
independent checker constructs the Gram matrix of the six vectors
`e_x,e_y,u_i,v_i,u_j,v_j` and expands its off-diagonal entries. Its SAT-slot
calculation counts only retained SAT choices, so an intervening proxy
choice cannot silently shift the auxiliary meaning.

## 2. The same physical normal and center difference

Let `d=c_j-c_i` and let n be the actual signed unit normal of the retained
owner/axis/sign alternative. The first two existing products are
`z0=n_x d_x` and `z1=n_y d_y`. Proved bounds `l_k<=d_k<=u_k` give

`d_k² <= (l_k+u_k)d_k-l_k u_k`,

because the difference is `(d_k-l_k)(u_k-d_k)>=0`. Let D be the sum of
these two affine upper bounds. For every rational x,y,a,b,

```
0 <= ||(x,y)+a n+b d||²
  <= x²+y²+a²+b²D
     +2a(x n_x+y n_y)+2b(x d_x+y d_y)+2ab(z0+z1).
```

The replacement has the required direction because `b²>=0`. This is
valid also when b is negative, an interval has zero width, or d is at a
rectangle endpoint. The independent checker expands the Gram matrix of
`e_x,e_y,n,d` and replaces only its final diagonal entry. It derives n
from the same original owner, signed axis and SAT slot, and takes the
two difference intervals from the independently reconstructed caller.

## 3. What the computation establishes

Fresh root runs used only the Python standard library in a separate
directory. The frame suite reconstructed 376 rows, checked 18,424 exact
physical evaluations, and rejected eight damaged right sides. The
projection suite reconstructed 184 rows, checked 13,800 physical
evaluations, and rejected eight damaged right sides. Both suites include
all eight owner/axis/sign alternatives. The projection suite includes
all four interval endpoint combinations and checks the exact secant
slack identity. The complete algebra above establishes validity for all
rational parameters; the finite controls check the implementations.

The numerical eigenvector routines are discovery aids. Neither a
floating-point eigenvalue, a sampled point, nor an optimizer's status is
used in the physical implication. A proposed parameter vector may be
rounded arbitrarily without invalidating the norm identity.

## 4. Obligations of every original caller

An application must reconstruct the retained original path and its SAT
choices, bind all six existing auxiliary slots to their physical products,
and certify every interval before rebuilding a printed row. The caller's
exact multiplier replay must then verify each rational coefficient, right
side, multiplier, residual and residual correction. Projection rows from
a child may not be transported to a parent with different interval bounds
or a different separator choice.

All nine independent original frames, all 36 corners and pairs, the five
original center-cone comparisons, and exact marked bits remain in the
caller. A complete closed cover and its original ancestry are still
required for any ledger change. This package earns zero cells and masks;
the fixed counts and IDs remain unchanged.
