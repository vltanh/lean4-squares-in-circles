# A same-original support-height bound for every physical pair

Let i,j be unit squares with disjoint open interiors and arbitrary physical orientations. In fixed Cartesian coordinates write

    h_k=(alpha_k+|beta_k|)/2,

where alpha_k≥|beta_k| and alpha_k²+beta_k²=1 are the canonical side components of the same original square. Then the original center distance satisfies

    ||c_j−c_i|| ≥ 1+|h_i−h_j|.                       (1)

This is a necessary consequence of physical nonoverlap; it selects no separating-axis owner or new cone comparison.

## Proof

Choose canonical original angles theta_i,theta_j∈[−π/4,π/4]. Put a=|theta_i|, b=|theta_j|, d=|a−b|, delta=|theta_i−theta_j|, and eta=min(delta,π/2−delta). Thus d,eta∈[0,π/4]. If the angles have the same sign, delta=d and eta=d. If they have opposite signs, delta=a+b and both a+b and π/2−a−b are at least |a−b|: the second claim follows from max(a,b)≤π/4. Therefore eta≥d in all sign cases, including zeros and endpoints.

Let F(t)=cos t+sin t. This is nondecreasing on [0,π/4]. For b,d≥0 with b+d≤π/4,

    F(b+d)−F(b)
      =cos b (cos d+sin d−1)+sin b (cos d−sin d−1)
      ≤ cos d+sin d−1
      =F(d)−1.

Indeed cos d+sin d−1≥0, cos b≤1, cos d−sin d−1≤0, and sin b≥0. Relabel a,b if needed. It follows that

    F(eta) ≥ F(d) ≥ 1+|F(a)−F(b)|
                         =1+2|h_i−h_j|.

The physical owner-free relative-support theorem supplies

    ||c_j−c_i|| ≥ (1+c+|s|)/2,

where c=cos(theta_j−theta_i)≥0 and s=sin(theta_j−theta_i). Since c+|s|=F(eta), (1) follows. The accepted proof of that relative-support theorem covers every physical separating-axis alternative. Original orientations, signed endpoints and contact are retained throughout.

## Exact affine consequences

Put u=h_i−h_j and d_vec=c_j−c_i. Squaring (1) and using |u|≥sigma*u for either sigma∈{−1,+1} gives

    ||d_vec||² ≥ 1+2 sigma*u+u².

For any rational t, the square (u−t)²≥0 yields

    ||d_vec||² ≥ 1+2(sigma+t)u−t².                  (2)

If the same whole parent already proves d_x∈[a,b] and d_y∈[c,e], the two square secants imply

    −(a+b)d_x−(c+e)d_y+2(sigma+t)u
        ≤ t²−1−ab−ce.                              (3)

Because 2u=alpha_i+|beta_i|−alpha_j−|beta_j|, (3) is a rational linear row in the existing original coordinates and frame variables. It introduces no auxiliary product, angle partition or case split. Every rational t gives a valid row. The implementation selects zero and endpoints/midpoint of a previously proved interval for u, purely to strengthen the available affine family.

The proof is independent of disk containment. It may therefore be applied to each of the 36 physical original pairs in any fixed mask, retaining all other original constraints. This lemma alone closes no original cell or mask; a complete exact caller deduction is still required.
