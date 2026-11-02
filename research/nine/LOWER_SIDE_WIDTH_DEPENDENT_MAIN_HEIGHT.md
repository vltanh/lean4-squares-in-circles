# A lower side square forces a width-dependent main height

This is a complete physical two-square inequality followed by a complete
3,387-leaf rational table. It supplies one input to the original weak-middle
low-floor proof. It does not by itself close a fixed nine-square mask.

## 1. The original physical theorem

Put Q=1105/256 and l=29/60. Let M and S be two actual independently
oriented unit squares with disjoint open interiors in the centered closed
Q-disk. Write h for M's common coordinate projection halfwidth and
g=1/(4h) for its centered aligned inset halfwidth. Suppose

    1/2<=h<=13/20,
    g-1/60<=x_M<=61/60-h,
    29/60<=x_S<=13/12,
    y_S<y_M.

Define the continuous piecewise linear function

    f(h)=-2h/3+max(0,min((h-1/2)/6,(27/50-h)/3))+1/400.

Then

    y_M>f(h).                                             (T)

Horizontal reflection gives the corresponding left-side result.
The center bands above are necessary for an original inner main with
actual outer main links and a weak middle cone link; dropping the other
inner main's nonnegative eta contribution only enlarges these bands.
The statement does not assume that M is nearly aligned, that S has a
particular separator owner, or that the original main links are contacts.

## 2. The full three-parameter domain

Write X=x_S and represent S's folded unsigned angle by t in [0,1]:

    a=1/sqrt(1+t^2), b=t*a,
    p=(a+b)/2, kS=(a-b)/2.

For the original M use

    k=sqrt(1/2-h^2), aM=h+k, bM=h-k.

Both physical chiralities remain allowed. The complete closed parameter
root is

    h in [1/2,13/20], t in [0,1], X in [29/60,13/12].   (R)

Some h values at the top of this root give an empty original main-center
interval. Retaining them is harmless; the table proves its inequality on
this larger entire root.

The original horizontal center difference is at most

    d=max(X-g+1/60,61/60-h-X).

It is nonnegative, and the uniform estimates are

    d<=93/130<9/10,
    d-g<=43/130<1/2.                                  (1)

Indeed X-g+1/60<=11/10-g, and g>=5/13, while the other
term is at most 1/30.

## 3. All genuine physical owner axes

For two folded angles alpha,beta in [0,pi/4], the smaller side-axis
support sum among their two possible relative chiralities is

    sigma=(1+cos(alpha-beta)+|sin(alpha-beta)|)/2.

To check this, assume alpha>=beta. The difference between the cosine-plus-
sine sums at alpha+beta and alpha-beta is
2 sin(beta)(cos(alpha)-sin(alpha))>=0. The sum of absolute cosine and
sine is invariant under a quarter turn, so this covers both relative
physical frames.

In the parameters of (R), the same quantity is

    sigma=1/2+max(k*a+h*b,h*a-k*b).                    (2)

Expanding aM=h+k and bM=h-k on the two determinant signs proves this
identity directly. Also

    sigma>=1+|h-p|>=1.                                (3)

For completeness, the folded halfwidth function H(theta)=(cos(theta)+
sin(theta))/2 is increasing and concave on [0,pi/4]. For a fixed angular
difference Delta, its greatest halfwidth difference is H(Delta)-H(0),
which equals sigma-1. This proves (3).

Write V=y_M-y_S>0. Physical nonoverlap supplies an axis owned by M or S
with support sum at least sigma. A directed normal with nonpositive
vertical component has projection at most d<1<=sigma, so cannot separate.
The possible absolute component pairs for a genuine unit normal are

    (aM,bM), (bM,aM), (a,b), (b,a).

For each positive second component ny, its necessary inequality gives
V>=(sigma-nx*d)/ny. A zero second component is impossible by (1) and
is omitted. Every numerator is positive. Thus

    V>=C_axis:=min((sigma-aM*d)/bM,(sigma-bM*d)/aM,
                   (sigma-a*d)/b,(sigma-b*d)/a).      (4)

The original center distance is at least sigma as well, giving

    V>=C_disk:=sqrt(sigma^2-d^2).                    (5)

Equations (4)-(5) are necessary for the original physical pair; the
smaller chirality support only weakens them.

## 4. The original aligned inset gives another clearance

M contains the aligned square of halfwidth g. Separate that inset from
the original S. The coordinate horizontal axis fails because
d-g<1/2<=p. A side normal with the wrong vertical sign fails because
d-g<1/2 and its own S support is 1/2. The coordinate vertical and
the two upward S-owned alternatives consequently give

    V>=C_inset:=g+min(p,(1/2+(g-d)*b)/a,
                         (1/2+(g-d)*a)/b).           (6)

The term with denominator b is omitted at b=0. Both numerators are
at least 1/2-43/130=11/65>0 by (1), so all divisions and omitted-axis
conventions are sound on the full root.

Let C=max(C_axis,C_disk,C_inset). All three clearances concern the
same original M and S, so V>=C.

## 5. All original S corners bound its depth

Put

    Uplus=min(sqrt(Q-(X+kS)^2)-p,
              kS+sqrt(Q-(X+p)^2)),
    Uminus=min(sqrt(Q-(X+p)^2)-kS,
               sqrt(Q-(X-kS)^2)-p),
    U=max(Uplus,Uminus).

These are upper bounds on -y_S for the two actual chiralities, by the
original corner constraints after vertical reflection. For example the
first orientation has offsets (kS,p),(p,-kS),(-kS,-p),(-p,kS).
The two displayed necessary corner bounds are the potentially active
upper bounds; the independent checker uses all four in each chirality.
Every radicand is positive on (R), since X+p<13/12+17/24<sqrt(Q).
The universal center estimate also permits replacing U by min(U,91/60).

Therefore the original main center satisfies

    y_M=y_S+V>=C-U.                                 (7)

The exact table proves C-U-f(h)>0 throughout (R), finishing (T).

## 6. Complete finite table and independent reconstruction

The table is `side_height_envelope_bump_plus_1_400_candidate.json`.
It encodes an entire binary tree in preorder: tags 0,1,2 bisect h,t,X
respectively at their exact rational midpoints; tag 3 is a strict
positive leaf. Both closed children retain their splitting boundary.

The exact producer found 6,773 nodes and 3,387 leaves, with maximum
depth 29 and no remaining parameter box. Its target is explicitly
`bump_plus_1_400`; intermediate weaker targets are not proof dependencies.

The separate verifier `verify_side_height_envelope.py` imports neither
the producer nor its dyadic arithmetic. It reconstructs the complete
root, every midpoint and all physical formulas using Fraction arithmetic
and independently bounded 90-bit radicals. It evaluates all eight signed
corner formulas, the direct relative-frame support formula, (2)-(3),
and every physical-axis/inset alternative. It recomputes each strict
reserve without trusting the producer's recorded bound.

The piecewise correction is bounded over each leaf by its two affine
upper bounds and the exact global maximum 1/225, attained at h=79/150.
This is a bound on one continuous piecewise linear function, not an
unrecorded parameter split or a sampled inequality.

All 3,387 leaves passed independent replay. The accepted tree SHA-256 is

    82bacbcb6b7597328fe9b6f2da20c3aa565c5b0688702148fa0843f9e311ee90.

The exact least rational reserve and checker identity are recorded in
`side_height_envelope_bump_plus_1_400_candidate_exact_replay.json`.
Complete preorder coverage rejects missing or trailing nodes; every
accepted leaf proves a strict positive rational lower bound.
Four damaged controls were also rejected: missing subtrees, an invalid
node tag, a false whole-root leaf, and a noninteger tag. See
`check_side_height_envelope_controls.py` and
`side_height_envelope_negative_controls.json`.

An independent agent also reviewed the physical center band, both
chirality support forms, all four owner alternatives, the reflected
corner cap and the continuous correction's interval bound and found no
gap. No independent human or kernel verification is claimed. No Lean,
Lake or CI was used.

The separate complete P/R transfer in
`WEAK_MIDDLE_BELOW_SIDE_EXTRA_EXCLUSION.md` now contradicts
`y_M>=f(h_M)` in the original weak-middle low-floor caller. The present
pair theorem alone is only that transfer's derived main-height input;
whole-mask assembly is in `A2_010_01_WHOLE_DOMAIN_ASSEMBLY.md`.
