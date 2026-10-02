# A seven-cycle potential route to the global bound

Status: the abstract reduction below is proved. Its required full-domain pair inequalities are NOT yet proved. Numerical finite-state experiments are recorded separately and are not lower-bound certificates.

This route keeps the fact that the ring has length SEVEN. It is not another attempt to force one universal pair gap of 2*pi/7, which UNIFORM_HEPTAGON_MARKER_OBSTRUCTION.md already rules out.

## 1. A general cycle-potential lemma

Let x_0,...,x_6 be the seven exterior states in cyclic order, and let g_i be their actual consecutive OLD-marker gaps. Thus sum g_i=2*pi. A state includes the signed transverse coordinate; the old label is the one in SHARP_MARKER_RING.md.

Choose a finite type map kappa(x), a real-valued state potential psi(x), and numbers b_{kl}. Suppose every relevant disjoint pair satisfies

    g + psi(target) - psi(source) >= b_{kappa(source),kappa(target)}.       (1)

Then

    2*pi >= sum_{i=0}^6 b_{kappa(x_i),kappa(x_(i+1))}.                    (2)

Proof: sum (1); the potential differences telescope. No claim that the shifted quantities are independently defined circular distances is required. The cyclic order is always that of the already proved old markers.

Consequently a rational table whose EVERY seven-step closed type word has weight greater than 44/7 excludes the packing, since 2*pi<44/7. For a sharp candidate-radius proof with equality, one instead needs a table bounded below by 2*pi and an equality analysis of the pair inequalities. A numerical table approximately reaching 2*pi does not supply that argument.

## 2. The actual continuous domain to certify

At q<=98/25, the existing central-core and sharp-marker certificates imply, for all seven exterior states,

    0<=u<=a,
    (a+1/2)^2+(u+1/2)^2<=q,
    (a-1/2)^2+max(u-1/2,0)^2>1/144,
    7/8<g<29/28.

For a proposed nonsharp lower bound q<=qbar one can relax the strict inequalities to closed endpoints. The domain includes interior states, not only far-corner circle states; RADIALIZATION_OBSTRUCTION.md explains why those cannot be dropped.

A convenient parameterization is

    psi(a,sigma*u)=sigma*(L_k(a,u)-ell_old(a,u)),

where L_k is an explicit function on type k. Then the left side of (1) is the directed relative frame angle minus sigma*L_source plus tau*L_target. Each pair assertion is a five-variable continuous statement in a,u,A,v,g, with four sign choices. It is accessible to the existing interval support engine, rather than requiring a 23-variable global packing search.

A certificate can accept a box either because (1) holds throughout it or because all separating-axis support margins are positive throughout it, making every such pair overlap. Otherwise it must subdivide. This covers a disjunction of necessary conditions; an unresolved box or exhausted budget is failure.

## 3. Four trial state types

One discovery partition uses the magnitude u:

    type 0: u<2/5,
    type 1: 2/5<=u<11/20,
    type 2: 11/20<=u<3/4,
    type 3: 3/4<=u.

These cuts are discovery choices, not proved geometric singularities. A certificate must cover their boundaries explicitly. It is harmless to prove both neighboring branch versions at a boundary; it is not harmless to leave that boundary out.

For four types there are 4^7 closed words of length seven before cyclic identifications. For a symmetric weight table these give 812 distinct edge-count vectors. They can be enumerated with exact integer counts; this is a small discrete combinatorial check after, not instead of, the continuous pair proofs.

In the candidate, the cyclic order E,H,G,A,B,T,D has type word

    0,3,0,1,2,0,3.

Its table weight is

    4*b03+b01+b12+b02.

This exposes how an odd cycle can use a cheap alternating pair mechanism four times but must also pay for a three-step type transition. A single uniform marker gap loses this information.

## 4. Discovery results — NOT certificates

The exploratory pair costs were computed from the exact separating-axis trigonometric formulas using floating-point root formulas. Finite grids of admissible states and their sign choices were then used to solve linear programs for potentials and type weights. The following are only diagnostics:

- At q=q*, a finite grid augmented with the actual candidate states admits a four-type potential budget whose minimum seven-word weight numerically equals 2*pi. The type word above is among the tight words.
- A simpler two-type constant budget, separating small and large u, fell short on the tested grid. For a cut near 0.45 its best trial bound was about 6.2757 at q*, below 2*pi. This is a failure of that trial relaxation, not a nonexistence theorem for all two-type constructions.
- Restricting the four-type potential to polynomials of degrees two and three loses noticeable sharpness. A degree-six trial on the discovery grid reaches the candidate value, but no continuum conclusion follows.
- At the easier ceiling q=39/10, lower-degree trial potentials have visible positive numerical reserve above 2*pi. This is a candidate intermediate certification target, not an established improvement of GLOBAL_LOWER_BOUND.md.

The finite grids do not cover the continuum. In particular values and first derivatives at equality states must be correct before a sharp pair inequality can be certified. Sampling an exact contact does not prove a neighborhood nonnegative.

## 5. Why this is a promising but unfinished reduction

The potential lemma turns a possible global obstruction into a finite set of pair-support assertions plus seven-step combinatorics. It preserves the central-core condition and does not assume the five-corner scaffold, common square angles, circle contact of every square, or a rigid heptagon.

It could either yield a sharper unconditional lower bound first or lead to a sharp certificate with a local equality argument. At present neither outcome has been certified. The rigorously established unrestricted bound remains the one in GLOBAL_LOWER_BOUND.md.

No Lean code is being written. Exploratory optimizations and unsuccessful fits are not mathematical proof premises.
