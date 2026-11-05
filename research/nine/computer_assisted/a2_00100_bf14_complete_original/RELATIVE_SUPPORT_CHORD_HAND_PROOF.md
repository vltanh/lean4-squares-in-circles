# Relative-support chord review

The proposed implication is valid for the original canonical unit-square frames and independently proved current intervals. It also applies to the folded frame family, using that family's own support radius. No separating-axis choice, new variable, or new branch is needed.

For either family let h=(1+C+|S|)/2. The accepted owner-free argument gives norm(center_j-center_i)>=h. Since C>=0 and C²+S²=1, 1<=C+|S|<=sqrt(2); hence 1<=h<(121/100), because (2*(121/100)-1)²=(71/50)²>2. The folded threshold is no larger than the actual signed-frame threshold, so the same distance inequality holds for it.

Let d be the signed longitudinal center difference, with a certified d>=0, and t the other coordinate. If t belongs to [L,U], division by 1<=h<=H gives t/h in [min(L,L/H),max(U,U/H)]. The literal's endpoints must enclose that entire ratio interval and lie in [-1,1]. The two nonnegative rational endpoint heights must satisfy a_l²+z_l²<=1 and a_u²+z_u²<=1. Concavity of sqrt(1-z²) on the closed interval then puts their affine chord ell(z)=m*z+b below that function throughout. Since d>=0 and d²+t²>=h², d>=h*sqrt(1-(t/h)²)>=m*t+b*h.

The guard b>=0 is essential: it permits substitution of h>=(1+C+epsilon*S)/2. Each of the four signed frame products is replaced by a lower McCormick plane over the independently proved same-state scalar rectangle. Multiplication by b/2 preserves all directions. Collecting terms gives precisely the producer's row -d+m*t+(b/2)*L <= -(b/2)*(1+K), where L+K<=C+epsilon*S.

Pitfalls explicitly guarded by the decoder: longitudinal sign, both ratio bounds including negative intervals, endpoint square checks, nonnegative intercept, canonical original-pair and scalar indices, and all four lower-plane selector bits. A degenerate ratio interval is accepted only at zero with both endpoint heights exactly one; it is the direct d>=h case. Closed endpoints and equality faces remain included. These checks do not establish the input intervals' ancestry; the enclosing independent tree checker must supply them from its reconstructed current state.

No C search adopts this family in this review. A saved-point violation is discovery evidence only. Actual weighted replay and complete original coverage remain necessary for any closure credit.
