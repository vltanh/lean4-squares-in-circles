# Anti-radial boundary access forces a diagonally oriented central square

Date: October 31, 2026.

**Status: complete hand theorem; independent mathematical review passed in REVIEW_ANNULAR_GLOBAL_ANTIRADIAL_ACCESS_ENDBLOCK_2026_10_31.md. No original coarse or fine gate is declared closed.** This is a whole-orientation physical theorem. It retains all nine actual squares and uses no selected force, contact-degree, normal or mean premise. Its resultant corollary applies to whole actual collections with the explicitly stated boundary-access property.

Let Q=1105/256. Suppose nine actual closed unit squares have pairwise disjoint open interiors and are contained in D_R, with

    2<R<=sqrt(Q).

Let H be any one of those units containing O. Choose signs and order of its actual own axes so its center is

    c=(x,y),       0<=y<=x<=1/2.

Write

    r=|c|, q=r²=x²+y², u=x+y, v=x-y,
    k=R-sqrt(2),
    t=401/100-(9/5)R,
    theta=atan(y/x) in [0,pi/4].

The proof below establishes x>t>0, so theta and every quotient displayed here are defined.

## 1. The theorem and its full block consequence

Suppose an actual unit B physically touches H and an actual circle corner z of B satisfies

    c dot z<=0.

Then both conclusions hold:

    q>v/2,                                                   (1)
    sin(2 theta)>=4*(R-sqrt(2))²-1.                           (2)

Thus an anti-radial physical boundary access requires a genuinely diagonal central-square frame. Equivalently,

    theta >= (1/2)*asin(4*(R-sqrt(2))²-1).                    (3)

The argument of asin lies strictly between zero and one in the full declared radius window. The theorem includes every physical circle corner, regardless of its original force coefficient.

**Whole-collection corollary.** Let U be any collection of original units such that every unit with a positive circle coefficient in U physically touches H. Keep all its original nonnegative corner coefficients and form its actual circle-load resultant F_U. If its total circle mass is positive and either

    q<=v/2,

or

    sin(2 theta)<4*(R-sqrt(2))²-1,

then c dot F_U>0. Indeed every circle corner of every positively loaded U-unit has positive c-projection by the theorem. This applies to arbitrary internal graphs, block orders and degrees; it does not prove that an arbitrary loaded endblock has the required physical adjacency to H.

For a genuine articulation side whose exact force-cut identity identifies its resultant with F_U, the same positive projection holds for that unchanged cut resultant. Actual applications, side means, individual zero corner weights and all other units remain untouched.

## 2. The nine-square central-disk input is stronger in the own coordinates

The accepted theorem NINE_SQUARE_CENTRAL_DISK_AND_SIX_BOUNDARY_NEIGHBORS_EXCLUSION.md gives, throughout 2<=R<=sqrt(Q), that no one of the nine units can contain the entire closed central disk of radius

    h=(9/5)R-351/100,       t=1/2-h.

If x<=t, then y<=x and all four sides of the actual origin-containing H are at distance at least h from O. It would contain that whole closed disk. Therefore

    x>t.                                                     (4)

The elementary enclosing bound sqrt(Q)<25/12 gives

    t>401/100-(9/5)*(25/12)=13/50>0.                         (5)

Only the no-central-disk conclusion is inherited here. Its center-norm corollary is not being substituted for the stronger own-coordinate implication (4).

## 3. Exact support on the anti-radial half-circle

For any unit vector e the actual support of H is

    h_H(e)=c dot e+(|e_x|+|e_y|)/2.

Set

    A=sqrt((1/2-x)²+(1/2+y)²),
    S=(x+y)/(2r).

The exact maximum on the closed anti-radial half-circle is

    max_(|e|=1, c dot e<=0) h_H(e)
       = A,   when q<=v/2;
       = S,   when q>=v/2.                                 (6)

At q=v/2 the two quantities agree. Here is a complete own-quadrant proof.

### 3.1. Northwest directions

Put e=(-a,b), a,b>=0, a²+b²=1. The anti-radial condition is y*b<=x*a, and

    h_H(e)=(1/2-x)a+(1/2+y)b.

The unrestricted maximizing direction is proportional to
`(1/2-x,1/2+y)`. It lies in the allowed cone exactly when

    y*(1/2+y)<=x*(1/2-x),

which is q<=v/2. Its value is then A. If q>v/2, the maximizing direction is instead the cone endpoint e=(-y,x)/r, where the value is S. This follows directly by the monotonicity of the scalar product with a fixed nonnegative vector as the unit direction approaches that vector; alternatively differentiate the one-angle expression. The zero-coordinate and x=1/2 boundary cases are included by the same formula or continuity.

### 3.2. Southeast directions

Put e=(a,-b), a,b>=0. The constraint is x*a<=y*b. The unrestricted positive support vector `(1/2+x,1/2-y)` has coordinate ratio at least one, whereas the allowed ratio a/b is at most y/x<=1. Its maximum on this cone is therefore at e=(y,-x)/r and equals S.

### 3.3. Southwest directions

There is no further anti-radial restriction in this quadrant. Its maximum is

    B=sqrt((1/2-x)²+(1/2-y)²).

Always B<=A. Thus in the first regime it introduces no larger value; the northwest boundary value S also satisfies S<=A by Cauchy-Schwarz.

In the second regime q>=v/2, use x,y<=1/2 to get q<=u/2. Direct expansion gives

    q*(B²-S²)=q²-u*q+v²/4.

The quadratic on the right decreases for q<=u/2. Hence

    q*(B²-S²) <= (v/2)²-u*(v/2)+v²/4
                =v*(v-u)/2=-v*y<=0.

Thus B<=S in this regime. The northeast quadrant contributes no additional anti-radial directions, except axis endpoints already included. These three exhaustive calculations prove (6).

## 4. Every physical boundary access has support at least R-sqrt(2)

Choose any actual contact point p in H intersection B. For every actual circle corner z of B,

    |z-p|<=sqrt(2),

because both points belong to the same actual unit square B. Write e=z/R. Projection gives

    R=z dot e<=p dot e+sqrt(2)<=h_H(e)+sqrt(2).

Consequently

    h_H(e)>=k.                                               (7)

This does not change p into a contact mean. It is a physical statement for each z separately and includes all boundary corners with zero multiplier.

## 5. One convex quartic excludes the entire shallow alternative

We prove uniformly that

    q<=v/2  implies  A<k.                                    (8)

Define the radius functions

    w=1-2k²,
    f(R)=t²+(t-w)²-w/2.

The needed scalar fact is

    f(R)>0,       t>w>0.                                     (9)

The proof of (9) is completely continuous and is supplied below; no table of square poses or numerical certificate is used.

Assume q<=v/2 but A>=k. Since

    A²=q-v+1/2<=1/2-v/2,

we obtain v<=1-2k²=w. By (4),(9),

    x>t>w,       y=x-v>=x-w>t-w>0.

Therefore

    q=x²+y²>t²+(t-w)²>w/2>=v/2,

contradicting q<=v/2. This proves (8), including its equality boundary.

### 5.1. Signs of w and t-w

We have

    k>2-sqrt(2)>41/70>29/50,
    k<1/sqrt(2).

The first uses sqrt(2)<99/70; the last follows from R<=sqrt(Q)<3/sqrt(2), since Q<9/2. Thus w>0.

Also

    (t-w)'=-9/5+4k>13/25>0.

At R=2, t=41/100 and w=8sqrt(2)-11<1/3, where sqrt(2)<17/12 follows by squaring. Hence

    (t-w)(2)>23/300>0,

and t>w throughout the full interval.

### 5.2. A strict lower curvature bound

Differentiating the displayed quartic, using t'=-9/5 and w'=-4k, gives

    f''(R)=174/25+8t-(144/5)k+48k².                         (10)

The last quadratic in k increases for k>3/10. Applying k>29/50 and t>13/50 from (5),

    f''(R)>174/25+8*(13/50)
                   +48*(29/50)²-(144/5)*(29/50)
           =5302/625>8.                                    (11)

### 5.3. Exact initial value and initial derivative

At R=2 direct expansion gives

    f(2)=1319281/5000-(4664/25)*sqrt(2),
    f'(2)=34001/125-(4812/25)*sqrt(2).

The upper radical enclosure sqrt(2)<577/408 follows from
577²-2*408²=1. Substitution into these two decreasing affine expressions gives

    f(2)>1/50,
    f'(2)>-1/4.                                             (12)

The exact rational reserves after that substitution are respectively

    31/255000,
    423/8500.

### 5.4. The whole radius interval

For d=R-2>=0, integrate (11) twice and use (12):

    f(R)>1/50-d/4+4d²
         =4*(d-1/32)²+103/6400>0.                          (13)

Together with 5.1 this proves all of (9). The proof of (8) is complete on the entire actual radius interval.

## 6. Finish the anti-radial access theorem

If c dot z<=0, then e=z/R belongs to the half-circle in (6). The shallow case is impossible, because (7),(8) would give k<=h_H(e)<=A<k. Thus q>v/2, proving (1), and (6),(7) give

    S>=k.

Since x=r*cos(theta), y=r*sin(theta),

    4S²=(x+y)²/r²=1+sin(2theta).

Both sides being nonnegative, S>=k is exactly (2). Also k>29/50>1/2 and k<1/sqrt(2), so 0<4k²-1<1. The increasing sine on [0,pi/2] proves (3).

For an original nonnegative circle-load collection satisfying the stated adjacency premise, failure of the necessary conditions (1),(2) forces every positively weighted corner to have positive c-projection. Summing those unchanged terms gives the whole-collection corollary.

## 7. Positive and negative controls and exact limitations

The five-square cross does not satisfy the retained nine-unit premise. Its central square has c=O and contains every central disk used above; therefore the crucial implication x>t does not apply. There is no false positive-cone assertion for that negative control.

The exact nine-unit constructions TWO_STACK_SHARP_EQUALITY_WITNESS.md and NONRIGID_WITNESS.md are retained. The former has an origin-containing central unit with c=(31/64,0), so theta=0; its actual boundary-neighbor corners have positive c-projection, as required. The latter has an origin-containing anchor with c=(1/2,1/16), so the conclusion again only restricts its physical boundary-neighbor corners, not distant loads elsewhere in the packing. Neither construction is excluded.

The theorem has a real geometric exception: sufficiently diagonal central frames have S as large as 1/sqrt(2), exceeding R-sqrt(2) in this radius window. No global contradiction is claimed in that region. A new two-resource capacity argument would still be needed to exclude or classify its whole nine-unit completions.

Likewise a large endblock can contain loaded units that are not physical neighbors of H. A positive radial pressure theorem for that endblock requires a further access or propagation argument. No missing adjacency is inferred from graph connectedness, a force cut, or a claimed block size.

## 8. Source and verification boundary

The sole inherited geometric theorem is the radius-dependent closed central-disk obstruction in NINE_SQUARE_CENTRAL_DISK_AND_SIX_BOUNDARY_NEIGHBORS_EXCLUSION.md. Its complete analytic single-unit arc argument is unchanged. The exact quadrant optimization, contact-support identity and the continuous quartic proof above are new self-contained arguments.

The separate endblock review reconstructs the exact quadrant support maximum, full continuous quartic comparison and retained physical adjacency premise. No formal verification is claimed.

No unit is deleted or deformed. No original force, torque, normal choice, side mean, physical mask or zero coefficient is altered. No mathematical exclusion script, numerical pose cover, Lean/Lake build or CI was used. The result does not close a canonical parent until a complete original-domain caller has established its hypotheses and treated the diagonal/deep-load alternatives.

