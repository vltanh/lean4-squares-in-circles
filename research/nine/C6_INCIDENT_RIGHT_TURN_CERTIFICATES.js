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


function incidentRightTurnCertificates(){
 const f=auditFramework(),{q,constp,mono,addp,subp,mulp,scalep,powp,deg,equal,serial,fmt,sgn,sub,add,mul,bin}=f;
 const one=constp(q(1)),X=mono(1,0),Y=mono(0,1),L=q(2,1);
 const t=scalep(X,q(21,0,100)),D=addp(one,powp(t,2)),Ca=subp(one,powp(t,2)),Sa=scalep(t,q(2));
 const e=addp(constp(q(5,0,4)),scalep(Y,q(1,0,4)));
 const d=subp(scalep(addp(powp(e,2),constp(sub(mul(L,L),q(1,0,4)))),q(2,-1,4)),one);
 const c=subp(constp(L),addp(d,one)),cm=subp(c,one),em=subp(e,one);
 const An=addp(subp(scalep(D,q(2)),mulp(d,Ca)),scalep(Sa,q(1,0,2)));
 const Bn=subp(subp(scalep(D,q(2)),mulp(cm,Sa)),mulp(em,Ca));
 const HC=subp(mulp(cm,Ca),mulp(em,Sa)),HB=addp(mulp(d,Sa),scalep(Ca,q(1,0,2)));
 const R2=addp(powp(addp(d,one),2),constp(q(1,0,4)));
 if(!equal(addp(powp(Ca,2),powp(Sa,2)),powp(D,2)))throw Error("unit trigonometry");
 if(!equal(addp(powp(c,2),powp(e,2)),R2))throw Error("physical endpoint circles");
 const Px=addp(scalep(mulp(d,D),q(-1)),Ca),Py=subp(scalep(D,q(-1,0,2)),Sa);
 const Qx=subp(mulp(cm,D),Sa),Qy=subp(mulp(em,D),Ca);
 if(!equal(subp(mulp(Px,Ca),mulp(Py,Sa)),mulp(D,subp(An,D))))throw Error("B normal projection");
 if(!equal(scalep(addp(mulp(Px,Sa),mulp(Py,Ca)),q(-1)),mulp(D,HB)))throw Error("B original mean");
 if(!equal(subp(mulp(Qx,Ca),mulp(Qy,Sa)),mulp(D,HC)))throw Error("C original mean");
 if(!equal(scalep(addp(mulp(Qx,Sa),mulp(Qy,Ca)),q(-1)),mulp(D,subp(Bn,D))))throw Error("C normal projection");
 const F=subp(mulp(An,HB),mulp(Bn,HC));
 const G=subp(addp(powp(An,2),powp(Bn,2)),mulp(R2,powp(D,2)));
 const H=subp(mulp(HC,D),scalep(powp(D,2),q(21,0,50)));

 const lambda=addp(constp(q(23,0,100)),scalep(X,q(1,0,100)));
 const mu=addp(addp(constp(q(3,0,100)),scalep(X,q(1,0,100))),scalep(Y,q(3,0,200)));
 const Height=subp(addp(H,mulp(lambda,F)),mulp(mu,G));
 const Acent=subp(An,scalep(D,q(1,0,2))),Bcent=subp(Bn,scalep(D,q(1,0,2)));
 const tx=subp(mulp(Acent,Ca),mulp(Bcent,Sa)),ty=scalep(addp(mulp(Acent,Sa),mulp(Bcent,Ca)),q(-1));
 const cx=subp(c,constp(q(1,0,2))),cy=subp(e,constp(q(1,0,2)));
 const Gap=addp(mulp(addp(scalep(cx,q(4)),scalep(cy,q(3))),tx),mulp(subp(scalep(cy,q(4)),scalep(cx,q(3))),ty));
 if(!equal(addp(powp(tx,2),powp(ty,2)),mulp(powp(D,2),addp(powp(Acent,2),powp(Bcent,2)))))throw Error("center-frame identity");
 const audit=(name,poly,expectedDegree,floor)=>{
  const[n,m]=deg(poly);if(n!==expectedDegree[0]||m!==expectedDegree[1])throw Error("degree "+name);
  let minimum=null,reconstruction=new Map();const coefficients=[];
  for(let i=0;i<=n;i++)for(let j=0;j<=m;j++){
   let value=q();
   for(const[key,c]of poly){const k=Math.floor(key/f.stride),l=key%f.stride;if(k<=i&&l<=j)value=add(value,mul(c,q(bin(i,k)*bin(j,l),0,bin(n,k)*bin(m,l))));}
   if(sgn(sub(value,floor))!==1)throw Error("coefficient floor "+name);
   if(minimum===null||sgn(sub(value,minimum))<0)minimum=value;
   coefficients.push([i,j,...fmt(value)]);
   for(let k=i;k<=n;k++)for(let l=j;l<=m;l++){let v=bin(n,i)*bin(m,j)*bin(n-i,k-i)*bin(m-j,l-j);if((k+l-i-j)%2)v=-v;reconstruction=addp(reconstruction,mono(k,l,mul(value,q(v))));}
  }
  if(!equal(poly,reconstruction))throw Error("inverse Bernstein "+name);
  return{name,degree:[n,m],coefficientCount:coefficients.length,minimum:fmt(minimum),strictFloor:fmt(floor),allIdentities:true,numerator:serial(poly),coefficients};
 };
 return{domain:{t:"21 X/100",e:"5/4+Y/4",rectangle:"[0,1]^2"},geometry:Object.fromEntries(Object.entries({D,Ca,Sa,d,c,e,An,Bn,HC,HB,F,G,H,lambda,mu,tx,ty,cx,cy}).map(([k,p])=>[k,serial(p)])),results:[audit("height",Height,[5,4],q(1,0,1000)),audit("gap",Gap,[4,4],q(1))]};
}
