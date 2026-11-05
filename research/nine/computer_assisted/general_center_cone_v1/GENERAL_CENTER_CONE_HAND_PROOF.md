# General center cone support from four original corners

This extends the accepted one-parameter cone family. It retains every original square and uses no pair/SAT or extra frame assumptions. The caller's original frame is orthonormal with u=(alpha,beta),v=(-beta,alpha),alpha>0 and certified slope t=beta/alpha in a closed interval[L,U]subset[-1,1]. The four original corners lie in the closed disk of squared radius1105/256.

For center p, let A=p dot u,B=p dot v,S=|A|,T=|B|. The maximum squared corner norm gives

S^2+T^2+S+T <= 1105/256-1/2 =977/256.

Choose any rational r>=s>=0. The exact identity

S^2+T^2+S+T-((2r+1)S+(2s+1)T-r^2-s^2)=(S-r)^2+(T-s)^2>=0

therefore proves S+kT<=c, where k=(2s+1)/(2r+1) and c=(977/256+r^2+s^2)/(2r+1). Swapping S,T proves T+kS<=c as well.

For any fixed rational world direction n=(nx,ny), select one major frame axis u or v and a sign sigma. Let m=sigma*(n dot major)>0 and let w=n dot minor. If |w|<=k*m throughout the certified angle interval, then

n dot p <=m*|p dot major|+|w|*|p dot minor|<=m*c.

For major u, m=alpha*sigma*(nx+ny*t) and w=alpha*(ny-nx*t). For major v, m=alpha*sigma*(ny-nx*t) and w=alpha*(nx+ny*t). Divide by alpha>0. The guard consists of positivity of one affine function and nonnegativity of two affine functions over[L,U]. Checking both closed endpoints proves the guard on the full interval; equality of |w|=k*m is retained. The resulting inequality is affine in original x,y,alpha,beta and has zero right side.

The decoder independently reconstructs k,c, the two affine endpoint guards, and all literal coefficients from the row label and the independently propagated caller angles. No approximate optimization result is a premise.

## Parameters screened

The discovery family uses(r,s)=(31/32,31/32),(5/4,1/2),(9/8,3/4),(11/8,3/8). The first gives k=1,c=2915/1504 and valid global rows +/-x<=c*alpha and +/-y<=c*alpha for the full canonical slope interval[-1,1]. The interpolating families can give stronger support on narrower angle intervals.

Saved-point screening found no violations at the inspected C887 root point. Interpolating rows cut saved Cb882 and Cd402 points; the separate screen is only a discovery diagnostic. Independent actual weighted use must be checked before integration. No original or mask closure is claimed here.
