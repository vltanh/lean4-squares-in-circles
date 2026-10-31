function auditFramework(){
 const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b!==0n){const r=a%b;a=b;b=r;}return a;};
 const q=(a=0n,b=0n,d=1n)=>{a=BigInt(a);b=BigInt(b);d=BigInt(d);if(d===0n)throw Error("zero rational denominator");if(d<0n){a=-a;b=-b;d=-d;}const g=gcd(gcd(a,b),d);return[a/g,b/g,d/g];};
 const add=(a,b)=>q(a[0]*b[2]+b[0]*a[2],a[1]*b[2]+b[1]*a[2],a[2]*b[2]);
 const neg=a=>[-a[0],-a[1],a[2]];
 const sub=(a,b)=>add(a,neg(b));
 const mul=(a,b)=>q(a[0]*b[0]+2n*a[1]*b[1],a[0]*b[1]+a[1]*b[0],a[2]*b[2]);
 const div=(a,b)=>{if(b[0]===0n&&b[1]===0n)throw Error("division by zero");return q(a[2]===0n?0n:b[2]*(a[0]*b[0]-2n*a[1]*b[1]),b[2]*(a[1]*b[0]-a[0]*b[1]),a[2]*(b[0]*b[0]-2n*b[1]*b[1]));};
 const zero=a=>a[0]===0n&&a[1]===0n;
 const sgn=a=>{let[A,B]=a;if(A===0n)return B===0n?0:B>0n?1:-1;if(B===0n)return A>0n?1:-1;if(A>0n&&B>0n)return 1;if(A<0n&&B<0n)return -1;const d=A*A-2n*B*B;if(d===0n)throw Error("irrationality violation");return A>0n?(d>0n?1:-1):(d>0n?-1:1);};
 const stride=1000;
 const constp=a=>zero(a)?new Map():new Map([[0,a]]);
 const mono=(i,j,a=q(1))=>new Map([[i*stride+j,a]]);
 const from=a=>new Map(a.map(([i,j,A,B,D])=>[i*stride+j,q(A,B,D)]));
 const addp=(a,b)=>{const p=new Map(a);for(const[k,v]of b){const c=add(p.get(k)||q(),v);if(zero(c))p.delete(k);else p.set(k,c);}return p;};
 const scalep=(a,c)=>{const p=new Map();for(const[k,v]of a){const z=mul(v,c);if(!zero(z))p.set(k,z);}return p;};
 const subp=(a,b)=>addp(a,scalep(b,q(-1)));
 const mulp=(a,b)=>{const p=new Map();for(const[k,v]of a)for(const[l,w]of b){if(k%stride+l%stride>=stride)throw Error("exponent overflow");const key=k+l,z=add(p.get(key)||q(),mul(v,w));if(zero(z))p.delete(key);else p.set(key,z);}return p;};
 const powp=(a,n)=>{let p=constp(q(1));while(n--)p=mulp(p,a);return p;};
 const deg=p=>[Math.max(0,...[...p.keys()].map(k=>Math.floor(k/stride))),Math.max(0,...[...p.keys()].map(k=>k%stride))];
 const equal=(a,b)=>subp(a,b).size===0;
 const dividep=(p,f)=>{p=new Map(p);const z=new Map(),lf=Math.max(...f.keys()),cf=f.get(lf),fi=Math.floor(lf/stride),fj=lf%stride;while(p.size){const lp=Math.max(...p.keys()),pi=Math.floor(lp/stride),pj=lp%stride;if(pi<fi||pj<fj)return null;const key=(pi-fi)*stride+pj-fj,coeff=div(p.get(lp),cf);z.set(key,add(z.get(key)||q(),coeff));p=subp(p,mulp(new Map([[key,coeff]]),f));}return z;};
 const bin=(n,k)=>{let r=1n;for(let j=0;j<k;j++)r=r*BigInt(n-j)/BigInt(j+1);return r;};
 const fmt=a=>a.map(String);
 const serial=p=>[...p].sort((a,b)=>a[0]-b[0]).map(([k,v])=>[Math.floor(k/stride),k%stride,...fmt(v)]);
 return{q,add,sub,neg,mul,div,zero,sgn,constp,mono,from,addp,subp,mulp,powp,scalep,deg,equal,dividep,bin,fmt,serial,stride};
}
function radialTAxisCertificates(){
 const f=auditFramework();
 const {q,addp,subp,mulp,powp,scalep,constp,mono,deg,bin,sgn,sub,mul,serial,fmt,equal}=f;
 const one=constp(q(1)),sig=q(0,1,2),rt=q(0,1),X=mono(1,0),Y=mono(0,1),t=scalep(X,q(1,0,5)),t2=powp(t,2);
 const Z=addp(one,t2),U=scalep(t,q(2)),V=subp(one,t2);
 const J=mulp(subp(V,scalep(Z,sig)),Y),W=subp(Z,J);
 const N=addp(addp(powp(W,2),mulp(V,W)),addp(scalep(powp(Z,2),q(3)),scalep(mulp(U,Z),q(2))));
 const H=scalep(subp(mulp(addp(Z,scalep(V,q(2))),Z),mulp(U,W)),q(2));
 const C=addp(mulp(addp(scalep(W,q(2)),V),H),scalep(mulp(N,U),q(2)));
 const E=subp(mulp(addp(scalep(Z,q(4)),U),H),scalep(mulp(N,V),q(2)));
 const Q=addp(scalep(mulp(N,U),q(2)),mulp(V,H));
 if(!equal(subp(C,Q),scalep(mulp(W,H),q(2))))throw Error("mean identity");
 const radiusIdentity=subp(addp(powp(C,2),powp(E,2)),addp(scalep(mulp(powp(Z,2),powp(addp(N,H),2)),q(4)),mulp(powp(H,2),powp(Z,2))));
 if(radiusIdentity.size)throw Error("C circle identity");
 const common=mulp(mulp(V,W),E);
 const P0=addp(common,mulp(C,addp(subp(mulp(U,W),scalep(mulp(U,Z),rt)),scalep(mulp(V,Z),sub(sig,q(1))))));
 const P1=addp(common,mulp(C,addp(addp(powp(Z,2),scalep(mulp(V,Z),sub(sig,q(2)))),subp(mulp(U,W),scalep(mulp(U,Z),f.add(sig,q(1)))))));
 const depth=addp(mulp(V,subp(scalep(mulp(Z,C),q(2)),mulp(W,E))),mulp(mulp(U,addp(scalep(Z,sig),J)),C));
 const direct0=subp(mulp(mulp(Z,C),addp(scalep(U,sub(q(1),sig)),scalep(V,f.add(q(1),sig)))),depth);
 const direct1=subp(mulp(mulp(Z,C),addp(Z,scalep(V,sig))),depth);
 if(!equal(P0,direct0)||!equal(P1,direct1))throw Error("target numerator identities");
 const floors=[q(9,0,10),q(1,0,4)];
 const minima=[q(-71016608,57020496,9765625),q(-76862240,56169152,9765625)];
 const lowerTables=[
 [[8727,8290,7623,6778],[8142,7704,7041,6206],[7566,7126,6470,5648],[6992,6551,5904,5097],[6418,5975,5337,4549],[5837,5392,4764,3997],[5244,4797,4181,3436],[4633,4184,3580,2859],[3998,3547,2958,2262],[3332,2881,2307,1639],[2628,2179,1624,985]],
 [[8727,8290,7623,6778],[7931,7506,6858,6036],[7172,6757,6126,5329],[6442,6035,5421,4649],[5738,5335,4737,3989],[5055,4653,4069,3346],[4387,3985,3414,2714],[3732,3327,2767,2091],[3086,2676,2128,1475],[2447,2032,1496,865],[1812,1394,870,263]]
 ];
 const reports=[P0,P1].map((p,index)=>{
  const [n,m]=deg(p); if(n!==10||m!==3)throw Error("degree");
  let minimum=null,reconstruction=new Map();const coefficients=[];
  for(let i=0;i<=n;i++)for(let j=0;j<=m;j++){
   let b=q();
   for(const [key,value]of p){const k=Math.floor(key/f.stride),l=key%f.stride;if(k<=i&&l<=j)b=f.add(b,mul(value,q(bin(i,k)*bin(j,l),0,bin(n,k)*bin(m,l))));}
   if(sgn(sub(b,floors[index]))!==1)throw Error("strict coefficient floor");
   if(sgn(sub(b,q(lowerTables[index][i][j],0,1000)))<0)throw Error("coefficient table");
   if(minimum===null||sgn(sub(b,minimum))<0)minimum=b;
   coefficients.push([i,j,...fmt(b)]);
   for(let k=i;k<=n;k++)for(let l=j;l<=m;l++){
    let integer=bin(n,i)*bin(m,j)*bin(n-i,k-i)*bin(m-j,l-j);
    if((k-i+l-j)%2)integer=-integer;
    reconstruction=addp(reconstruction,mono(k,l,mul(b,q(integer))));
   }
  }
  if(!equal(reconstruction,p))throw Error("inverse Bernstein identity");
  if(sgn(sub(minimum,minima[index]))!==0)throw Error("exact minimum");
  return{degree:[n,m],coefficientCount:coefficients.length,strictFloor:fmt(floors[index]),exactMinimum:fmt(minimum),numerator:serial(p),coefficients,lowerThousandTable:lowerTables[index],allChecks:true};
 });
 return{map:{t:"x/5",zeta:"(v−1/sqrt(2))*y"},factors:{Z:serial(Z),U:serial(U),V:serial(V),W:serial(W),N:serial(N),H:serial(H),C:serial(C),E:serial(E)},meanIdentity:true,circleIdentity:true,targetIdentities:true,results:reports};
}
