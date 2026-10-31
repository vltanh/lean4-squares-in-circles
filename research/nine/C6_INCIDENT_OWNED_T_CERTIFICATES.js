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

function incidentSharedCertificates(){
 const f=auditFramework(),{q,constp,mono,addp,subp,mulp,scalep,powp,dividep,deg,serial,fmt,sgn,sub,add,mul,bin,equal}=f;
 const make=mode=>{
  const one=constp(q(1)),rt=q(0,1),X=mono(1,0),Y=mono(0,1);
  let t,w,Da,Db,Ca,Sa,U,V;
  if(mode==="shared_C"){
   t=scalep(X,q(2,0,15));w=mulp(t,Y);
   Da=addp(one,powp(t,2));Db=addp(one,powp(w,2));
   Ca=subp(one,powp(t,2));Sa=scalep(t,q(2));U=scalep(w,q(2));V=subp(one,powp(w,2));
  }else{
   w=addp(constp(q(1,0,10)),scalep(X,sub(q(-1,1),q(1,0,10))));t=mulp(w,Y);
   Da=addp(one,powp(t,2));Db=addp(one,powp(w,2));
   Ca=scalep(t,q(2));Sa=subp(one,powp(t,2));U=subp(one,powp(w,2));V=scalep(w,q(2));
  }
  const DD=mulp(Da,Db),Sn=addp(mulp(Ca,V),mulp(Sa,U)),Cn=subp(mulp(Ca,U),mulp(Sa,V)),En=subp(subp(scalep(DD,rt),mulp(Ca,Db)),mulp(U,Da));
  const L=mulp(DD,V);
  const P=mulp(addp(addp(DD,mulp(addp(U,V),Da)),Sn),V);
  const Q=mulp(subp(addp(DD,mulp(subp(V,U),Da)),Cn),V);
  const R=subp(mulp(addp(DD,mulp(subp(U,V),Da)),V),mulp(En,Db));
  const S=mulp(addp(scalep(DD,q(2)),mulp(addp(U,V),Da)),V);
  const Dn=subp(mulp(P,S),mulp(Q,R));
  const pq=addp(powp(P,2),powp(Q,2)),rs=addp(powp(R,2),powp(S,2));
  const An=subp(mulp(S,pq),mulp(Q,rs)),Bn=subp(mulp(P,rs),mulp(R,pq));
  if(!equal(addp(mulp(P,An),mulp(Q,Bn)),mulp(Dn,pq)))throw Error("first circle equality");
  if(!equal(addp(mulp(R,An),mulp(S,Bn)),mulp(Dn,rs)))throw Error("second circle equality");
  const Fn=addp(addp(mulp(mulp(mulp(Sn,Da),V),subp(An,Bn)),mulp(mulp(Sn,En),Bn)),mulp(mulp(En,Cn),An));
  const Gn=subp(addp(scalep(addp(mulp(U,An),mulp(V,Bn)),q(-1)),scalep(mulp(Dn,addp(mulp(U,P),mulp(V,Q))),q(2))),mulp(mulp(Dn,L),Db));
  const raw=mode==="shared_C"?addp(Fn,scalep(mulp(mulp(powp(Da,2),V),Gn),q(3,0,10))):Fn;
  let poly=raw;const cancellations={};
  for(const[name,factor]of Object.entries({Da,Db,V})){let n=0;for(;;){const quotient=dividep(poly,factor);if(quotient===null)break;poly=quotient;n++;}cancellations[name]=n;}
  if(JSON.stringify(cancellations)!==JSON.stringify({Da:1,Db:2,V:1}))throw Error("cancellation");
  if(!equal(raw,mulp(mulp(mulp(Da,powp(Db,2)),V),poly)))throw Error("positive factor identity");
  const [n,m]=deg(poly);
  if(n!==18||m!==(mode==="shared_C"?10:8))throw Error("degree");
  let minimum=null,minPositive=null,reconstruction=new Map();const coefficients=[],zeros=[];
  const floor=mode==="shared_C"?q(1,0,100):q(1,0,4);
  for(let i=0;i<=n;i++)for(let j=0;j<=m;j++){
   let value=q();
   for(const[key,c]of poly){const k=Math.floor(key/f.stride),l=key%f.stride;if(k<=i&&l<=j)value=add(value,mul(c,q(bin(i,k)*bin(j,l),0,bin(n,k)*bin(m,l))));}
   const sign=sgn(value);if(sign<0)throw Error("negative coefficient");
   if(sign===0)zeros.push([i,j]);else if(sgn(sub(value,floor))!==1)throw Error("positive coefficient floor");
   if(minimum===null||sgn(sub(value,minimum))<0)minimum=value;
   if(sign>0&&(minPositive===null||sgn(sub(value,minPositive))<0))minPositive=value;
   coefficients.push([i,j,...fmt(value)]);
   for(let k=i;k<=n;k++)for(let l=j;l<=m;l++){
    let integer=bin(n,i)*bin(m,j)*bin(n-i,k-i)*bin(m-j,l-j);
    if((k-i+l-j)%2)integer=-integer;
    reconstruction=addp(reconstruction,mono(k,l,mul(value,q(integer))));
   }
  }
  if(!equal(poly,reconstruction))throw Error("inverse Bernstein identity");
  if(mode==="shared_C"&&zeros.length!==0)throw Error("strict shared-C certificate");
  if(mode==="shared_B"&&JSON.stringify(zeros)!==JSON.stringify([[18,0],[18,8]]))throw Error("shared-B zero loci");
  return{mode,degree:[n,m],coefficientCount:coefficients.length,zeroIndices:zeros,minimum:fmt(minimum),minimumPositive:fmt(minPositive),strictPositiveFloor:fmt(floor),positiveFactorCancellations:cancellations,allCircleAndBernsteinIdentities:true,numerator:serial(poly),coefficients};
 };
 return{results:[make("shared_C"),make("shared_B")]};
}
