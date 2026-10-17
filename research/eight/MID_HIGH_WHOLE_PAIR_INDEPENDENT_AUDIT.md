# Independent review of the complete middle/high hand inequality

**Result: PASS.** The strengthened strict bound `.8926` holds on the stated
physical seven-ring domain for both ordered types, all signs, and every
retained source or target separating axis.

Reviewed SHA-256 hashes:

- Manuscript: `3db4337619e38923d25dfcb578e1da3a2b4e40a6ae2fdcd16f640dfe972f5121`.
- JavaScript checker: `8450ee514b7827dedd992fe09b9f6c56067db691bf94150e3ceda335424d0bca`.
- Independent polynomial reconstruction: `736c31d8df4e57d59f3772a96fd41c05d325b800bd7464bf50722d49ee80adcd`.

## Continuous proof

The diagonal coordinate change, sign reversal and label transformation
preserve the exact vertex potential. The middle label coefficients become
`k=1.534906` and `q=.045313` by direct substitution into the original affine
label. The physical radius identity is `Q-a-1/2`, with the stated arc bounds.

The negative-frame reduction uses the previously established centre gap
greater than `.76`; all other sign pairs have insufficient local-angle
difference. The central negative-frame margin and both extra source-axis
exclusions were checked in both ordered cases. After the quarter turn only
the negative/positive signs survive the direct cost tails. Their extra axis
is also excluded. The final Lipschitz tail applies to every later frame
angle. Reflected reversal covers all retained target axes.

All eight initial barrier formulas were rederived by maximizing the source
and target arc expressions. Their endpoint choices follow from derivatives
`-r+sigma` and `-D*r-tau*C`. Each coefficient used to establish increasing
barriers has the required sign.

The support coefficients in formula (12) were independently rederived.
Every endpoint choice in the cover follows from its stated derivative or
concavity argument; unconditional full-circle supports require no hidden
physical minimizer condition. The varying-multiplier middle-target derivative
bounds, including the decreasing product on `[.4,.6]`, have the correct
directions. The angle intervals and direct tails form a closed cover in both
orders and all signs.

The scalar endpoint arguments and the identity

`N''+N/4=(u^2+v^2-2*lambda^2)^2/(4*N^3)`

were checked independently. The norm never vanishes in the relevant rows;
its stated monotonicity makes the endpoint norm bounds valid throughout.
The post-quarter derivative bound has the correct width-sign change.

## Exact quarter contact

For middle source and high target, implicit differentiation gives

`B'=[C*A+D*(B+1)]/(C+D*r)=A+1-2*cos(x)/(C+D*r)`

before the quarter turn and

`B'=[C*(A-1)+D*B]/(C+D*r)`

afterwards. For high source and middle target, the same numerators are
divided by `1+r`. These identities verify the opposite signs of the contact
cost derivative on the two sides. The enlarged high arc has a unique
contact root, and monotonicity of the high label gives the required lower
cost bound for every feasible physical high state.

Solving the folded circle equation at the quarter turn gives the two
radicals in (23). Their coefficients, including the constant
`pi/4-2.2122495`, linear term `.5946665*d` and radical coefficients
`.7447965` and `-.284736`, were independently rederived. The second derivative
comparison is strictly negative on the entire middle interval. Its endpoint
minimum is therefore sufficient, including when the auxiliary high contact
lies beyond the physical high arc.

## Fixed arithmetic and transcription

The supplied checker replay passed all 225 strict comparisons. Its 28
endpoint numerators match the complete printed endpoint table.

The independent `audit_mid_high_polynomial_rows.py` reconstructs the five
polynomials directly from the manuscript formulas using Python Fractions.
It does not import or execute the supplied JavaScript arithmetic. For row 2,
it converts the degree-14 polynomial directly into Bernstein degree 20,
instead of repeating the checker's iterative elevation algorithm. Every one
of the 87 printed positive coefficient lower bounds passes.

For rows 1 and 2, the signs of the cosine and sine coefficients justify the
chosen Taylor replacements. Their lower polynomial is positive before
squaring. For rows 3 through 5, the target norm is bounded above and the
scalar term below; the positive lower scalar bound again prevents a squared
sign ambiguity. The elementary Taylor-sign facts used in those lower bounds
hold on all the stated intervals.

No unproved numerical contact, incomplete branch cover, polynomial
transcription error, or sign gap was found. The result is strict, so these
inequalities add no equality configurations to the later uniqueness analysis.
