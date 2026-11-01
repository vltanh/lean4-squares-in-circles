# Complete common-junction unloaded triangle exclusion, including every original side mean

November 1, 2026. PR #11 continuation from `ad00eaa16a27e5e1000d1a9dc7be0c4421c54b91`.

**Evidence at construction:** H, with the root independently reconstructing the new shared-side calculation during development. A separate noncontributor review is requested. This closes the entire common-physical-junction feature of the direct unloaded triangle. It does not by itself close the distinct-contact feature or an entire original coarse parent.

## 1. Exact original domain and conclusion

Keep the same actual nine closed unit squares, pairwise disjoint in their interiors, in a disk with center O and radius R. Keep one unchanged original selected physical contact-force-and-torque certificate, including the strict common-normal convention at point-only internal contacts.

Let A, B, C be entirely selected-circle-unloaded actual squares. Their original positive internal edges are AB, BC, CA, and each has full original positive degree three: two internal edges and exactly one positive edge to an actual outside square. The three outside terminals may coincide; their frames, degrees, loads, zero coefficients and all other contacts are unrestricted. Every original application point and positive-length shared-side mean is retained.

Assume only that there is an actual common point P in A intersect B intersect C. **The three selected internal applications need not equal P.** Then this feature is impossible at

    R^2 <= Q = 1105/256.

More precisely, for nonparallel core frames the argument below proves

    R^2 >= |P-O|^2 + 5 > Q.

For parallel core frames, the complete previously established theorem gives R^2 > 9/2 > Q. Its entire contact chart, arbitrary original means and corner endpoints are covered in [EVERY_PARALLEL_FRAME_UNLOADED_THREE_FORCE_TRIANGLE_REQUIRES_RADIUS_SQUARED_GREATER_THAN_NINE_HALVES_2026_11_01.md](EVERY_PARALLEL_FRAME_UNLOADED_THREE_FORCE_TRIANGLE_REQUIRES_RADIUS_SQUARED_GREATER_THAN_NINE_HALVES_2026_11_01.md).

The new argument is independent of the force-ratio screen c/W < 1/12 and includes every positive force ratio.

## 2. Exhaustive nonparallel contact classification at P

The tangent sectors of the actual square interiors at P have disjoint interiors. A square contributes angle pi/2 at a vertex and angle pi at a side-interior point. If any of the three contributes pi, the other two must be quadrants that tile its complementary halfplane. All three frames are then parallel modulo quarter turns. Thus in the nonparallel case P is a genuine vertex of each square.

Two convex interior-disjoint squares with a common vertex P can intersect either only at P or along a positive segment issuing from P. In the second case their frames are parallel: their boundary segments lie on the same line, and the perpendicular own axes are parallel as well. If two of the three pairs shared positive segments, all three frames would consequently be parallel. Therefore the nonparallel case has precisely two possibilities:

1. Every pair intersects only at P, so all three original applications are forced to P.
2. Exactly one pair shares a positive segment from P. The other two intersections are exactly P. The original application on the shared segment is unrestricted.

This classification does not assume the selected application lies at the common physical endpoint. The second case below explicitly preserves its full interval.

## 3. Actual outside points and disk averaging

We use two elementary facts, without altering any original stress.

**Actual unit step.** If q minimizes a unit direction e on an actual unit square T, then q+e belongs to T. In T's own unit side coordinates, a nonzero component of e moves inward from the minimizing endpoint by at most one; a zero component leaves the original coordinate unchanged. This includes all support-face means and endpoints.

Consequently, if the original outside exit of a core square has unit normal e and original application q, the same actual outside neighbor contains

    w = q+e.

**Convex averaging.** If actual disk points w_i have positive auxiliary weights alpha_i with sum one and sum alpha_i(w_i-P)=0, then

    R^2 >= sum alpha_i |w_i-O|^2
        = |P-O|^2 + sum alpha_i |w_i-P|^2.

These weights are only a convex combination of already-established disk points. They need not be original force magnitudes; no original force, moment or application is reselected or replaced.

## 4. No shared segment: the full all-point junction

Write each actual core square as

    S_i = P + [0,1]u_i + [0,1]v_i,

where u_i, v_i are its orthonormal inward vertex axes. Both original internal contacts are at P. Their original strict common normals have negative components in both inward axes. The complete unloaded translation at i therefore gives an outside normal e_i with both inward components strictly positive. Its unchanged application is forced to the opposite corner

    q_i = P+u_i+v_i.

Both internal moments about P vanish. The complete original moment equation implies det(q_i-P,e_i)=0. The positive components then force

    e_i = (u_i+v_i)/sqrt(2),
    w_i = P+(1+sqrt(2))e_i.

Adding the three complete original translations cancels the internal forces, so the three positive original exit magnitudes z_i satisfy sum z_i e_i=0. Normalize them to use the convex-averaging fact. It gives

    R^2 >= |P-O|^2 + (1+sqrt(2))^2
        > |P-O|^2 + 5.

This is a complete reconstruction of the earlier equal-application argument on the all-point branch.

## 5. One shared segment: retain its arbitrary original mean

Apply one rigid motion and, if necessary, a reflection and relabeling of the actual configuration. Write P=(0,0) and

    A = [0,1] x [0,1],
    B = [0,1] x [-1,0].

Their intersection is the entire actual segment [0,1] x {0}. Their original AB application is

    p_AB=(s,0),     0 <= s <= 1,

and the original A-to-B force is t(0,-1), with t>0. Both endpoints and all means are included.

The third square's inward quadrant lies in the left halfplane. Nonparallelity makes both inward side directions have strictly negative horizontal components: for some theta strictly between pi/2 and pi,

    u=(cos theta,sin theta),
    v=(-sin theta,cos theta),
    C=[0,1]u+[0,1]v.

Thus AC and BC intersect only at P. The diagonal direction

    e_C = (u+v)/sqrt(2)

lies strictly in the left cone: e_C,x < 0 and |e_C,y| < -e_C,x.

### 5.1 Translation fixes the actual outside support corners

The strict original A-to-C normal has both components negative in A's positive inward axes. Together with t(0,-1), the full unloaded A translation forces its outside unit normal e_A=(a,b) to have a,b>0. Its original application is therefore exactly q_A=(1,1).

At B the strict B-to-C normal has negative horizontal and positive vertical components. Together with the original B-to-A force t(0,1), the full unloaded B translation forces e_B=(c,-d) with c,d>0, and its original application is q_B=(1,-1).

At C, both internal originals apply at P and strictly expose that vertex. Its outside normal has positive components in both inward axes, so q_C=u+v. Its full torque about P forces the outside normal to be exactly the e_C displayed above. This conclusion retains both original internal forces and does not require any relation between their magnitudes.

### 5.2 Full torque forces the two required cone inequalities

Let z_A,z_B>0 be the original outside magnitudes. Torque about P at A gives, exactly,

    -st + z_A det((1,1),(a,b)) = 0,
    z_A(b-a) = st >= 0.

Hence b>=a. At B the corresponding original equation is

    st + z_B det((1,-1),(c,-d)) = 0,
    z_B(d-c) = st >= 0.

Hence d>=c. No mean has been moved: these equations use its unchanged s throughout [0,1]. In particular s=0 and s=1 are both present.

### 5.3 Three actual outside points surround P

The actual unit-step fact supplies the three original disk points

    w_A=(1+a,1+b),
    w_B=(1+c,-1-d),
    w_C=(1+sqrt(2))e_C.

Put w_A=(x_A,y_A), w_B=(x_B,-y_B), w_C=(-x_C,y_C). The established cone information is

    y_A >= x_A > 0,
    y_B >= x_B > 0,
    x_C > |y_C|.

In particular P=0 lies in their convex hull. For an explicit positive witness, set

    D = x_A y_B + x_B y_A > 0,
    lambda_A = (x_C y_B - x_B y_C)/D,
    lambda_B = (x_C y_A + x_A y_C)/D,
    lambda_C = 1.

Each lambda is strictly positive because x_C>|y_C|, y_A>=x_A>0 and y_B>=x_B>0. Direct substitution gives

    lambda_A w_A + lambda_B w_B + lambda_C w_C = 0.

Normalize the lambdas by their positive sum. This proves the precise convex cancellation needed for disk averaging, including all force ratios and all allowed side means.

### 5.4 All three points are more than sqrt(5) from P

Since a,b>0 and a^2+b^2=1, a+b>1. Therefore

    |w_A|^2 = (1+a)^2+(1+b)^2
            = 3+2(a+b) > 5.

The same calculation gives |w_B|^2=3+2(c+d)>5. Finally

    |w_C|^2=(1+sqrt(2))^2=3+2sqrt(2)>5.

Convex averaging with the explicit positive weights gives the stronger strict estimate

    R^2 > |P-O|^2+5 > 1105/256.

This contradicts the required disk radius and completes the entire original shared-side-mean branch.

## 6. Complete feature cover and unchanged remaining obligation

| Common-junction feature | Original applications retained | Proven obstruction |
| --- | --- | --- |
| Parallel core frames | Entire T chart, all shared-side means and both corner endpoints | Existing complete theorem: R^2>9/2 |
| Nonparallel, no shared segment | Every original pair application necessarily equals P | R^2 >= |P-O|^2+3+2sqrt(2) |
| Nonparallel, exactly one shared segment | Arbitrary unchanged p_AB=(s,0), 0<=s<=1; other two originals at P | R^2 > |P-O|^2+5 |

The tangent-sector argument and at-most-one-shared-segment argument prove that these rows exhaust every common physical junction. All original outside edges stay positive, their actual neighbors may repeat, and the six other physical squares remain in the original disk and packing. No properties of their unused equations or circle masks are silently added.

Hence a surviving direct unloaded triangle at R^2<=Q must have **no point common to its three actual core squares**. The remaining physical contact systems therefore have three distinct pair-contact applications. Proving their complete exclusion remains open. This result is a whole geometric feature closure, not a whole original coarse-parent closure; the canonical 41/58 coarse, 2,373/2,513 fine and 18/38 nested exterior counts are unchanged by this manuscript alone.
