// Exact full-domain C6 certificates. BigInt arithmetic only; no samples or angle subdivision.
// This standalone checker is not a Lean proof or a CI workflow.

function buildC6Framework(){
 const stride=512;
 const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){let t=a%b;a=b;b=t;}return a;};
 function Q(a,b=0n,d=1n){a=BigInt(a);b=BigInt(b);d=BigInt(d);if(!d)throw Error('zero denominator');if(d<0n){a=-a;b=-b;d=-d;}let g=gcd(gcd(a,b),d);return{a:a/g,b:b/g,d:d/g};}
 const zero=Q(0),one=Q(1),two=Q(2),sqrt2=Q(0,1);
 const qzero=x=>x.a===0n&&x.b===0n;
 const qa=(x,y)=>Q(x.a*y.d+y.a*x.d,x.b*y.d+y.b*x.d,x.d*y.d);
 const qn=x=>Q(-x.a,-x.b,x.d);
 const qs=(x,y)=>qa(x,qn(y));
 const qm=(x,y)=>Q(x.a*y.a+2n*x.b*y.b,x.a*y.b+x.b*y.a,x.d*y.d);
 const qi=x=>Q(x.d*x.a,-x.d*x.b,x.a*x.a-2n*x.b*x.b);
 const qd=(x,y)=>qm(x,qi(y));
 function sign(x){const a=x.a,b=x.b;if(b===0n)return a>0n?1:a<0n?-1:0;if(a===0n)return b>0n?1:-1;if(a>0n&&b>0n)return 1;if(a<0n&&b<0n)return-1;const t=a*a-2n*b*b;return a>0n?(t>0n?1:-1):(t>0n?-1:1);}
 function P(entries=[]){const p=new Map();for(const[i,j,c]of entries)if(!qzero(c))p.set(i*stride+j,c);return p;}
 const pc=x=>P([[0,0,x]]);
 const p1=pc(one),px=P([[1,0,one]]),py=P([[0,1,one]]);
 function pa(a,b){const p=new Map(a);for(const[k,v]of b){const z=qa(p.get(k)||zero,v);if(qzero(z))p.delete(k);else p.set(k,z);}return p;}
 const pn=a=>new Map([...a].map(([k,v])=>[k,qn(v)]));
 const ps=(a,b)=>pa(a,pn(b));
 function scale(a,c){return new Map([...a].map(([k,v])=>[k,qm(v,c)]).filter(([k,v])=>!qzero(v)));}
 function pm(a,b){const p=new Map();for(const[k,v]of a)for(const[l,w]of b){let z=qa(p.get(k+l)||zero,qm(v,w));if(qzero(z))p.delete(k+l);else p.set(k+l,z);}return p;}
 function pow(a,n){let p=p1;for(let j=0;j<n;j++)p=pm(p,a);return p;}
 function degree(a){let i=0,j=0;for(const k of a.keys()){i=Math.max(i,Math.floor(k/stride));j=Math.max(j,k%stride);}return[i,j];}
 function lead(a){let m=-1;for(const k of a.keys())if(k>m)m=k;return[m,a.get(m)];}
 function exactDivide(a,b){if(!b.size)throw Error('divide zero polynomial');let p=new Map(a),out=new Map();const[lb,cb]=lead(b),ib=Math.floor(lb/stride),jb=lb%stride;let iter=0;
  while(p.size){if(++iter>100000)throw Error('division loop');let[lp,cp]=lead(p),ip=Math.floor(lp/stride),jp=lp%stride;if(ip<ib||jp<jb)return null;let k=(ip-ib)*stride+jp-jb,v=qd(cp,cb);out.set(k,qa(out.get(k)||zero,v));for(const[l,w]of b){const kl=k+l,z=qs(p.get(kl)||zero,qm(v,w));if(qzero(z))p.delete(kl);else p.set(kl,z);}}
  return out;
 }
 function key(a){return[...a].sort((x,y)=>x[0]-y[0]).map(([k,v])=>k+':'+v.a+','+v.b+','+v.d).join(';');}
 const factors=[],factorKeys=new Map();
 function factor(a,name=''){const k=key(a);if(factorKeys.has(k))return factorKeys.get(k);const id=factors.length;factors.push({p:a,name:name||'factor'+id});factorKeys.set(k,id);return id;}
 const denDegree=d=>{let x=0,y=0;for(const[id,n]of d){const[a,b]=degree(factors[id].p);x+=a*n;y+=b*n;}return[x,y];};
 function simplify(n,d){d=new Map(d);if(!n.size)return{n,d:new Map()};for(const[id,powr]of [...d]){let count=powr;while(count>0){const quot=exactDivide(n,factors[id].p);if(quot===null)break;n=quot;count--;}if(count)d.set(id,count);else d.delete(id);}return{n,d};}
 const rc=q=>({n:pc(q),d:new Map()});
 const rp=p=>({n:p,d:new Map()});
 function rf(n,den,name=''){if(degree(den).every(x=>x===0))return rp(scale(n,qi(den.get(0)||zero)));const id=factor(den,name);return simplify(n,new Map([[id,1]]));}
 const rn=a=>({n:pn(a.n),d:new Map(a.d)});
 function ra(a,b){const d=new Map(a.d);for(const[k,e]of b.d)d.set(k,Math.max(d.get(k)||0,e));let an=a.n,bn=b.n;for(const[k,e]of d){for(let i=a.d.get(k)||0;i<e;i++)an=pm(an,factors[k].p);for(let i=b.d.get(k)||0;i<e;i++)bn=pm(bn,factors[k].p);}return simplify(pa(an,bn),d);}
 const rs=(a,b)=>ra(a,rn(b));
 function rm(a,b){const d=new Map(a.d);for(const[k,e]of b.d)d.set(k,(d.get(k)||0)+e);return simplify(pm(a.n,b.n),d);}
 function rd(a,b,name=''){let n=a.n,d=new Map(a.d);for(const[k,e]of b.d)for(let i=0;i<e;i++)n=pm(n,factors[k].p);if(degree(b.n).every(x=>x===0))n=scale(n,qi(b.n.get(0)||zero));else{const id=factor(b.n,name);d.set(id,(d.get(id)||0)+1);}return simplify(n,d);}
 const rk=(a,c)=>({n:scale(a.n,c),d:new Map(a.d)});
 const rpow=(a,n)=>{let b=rc(one);for(let i=0;i<n;i++)b=rm(b,a);return b;};
 const bin=(n,k)=>{if(k<0||k>n)return 0n;let v=1n;for(let i=1;i<=k;i++)v=v*BigInt(n-i+1)/BigInt(i);return v;};
 function bernstein(p){const[m,n]=degree(p),out=[];let min=null;for(let i=0;i<=m;i++)for(let j=0;j<=n;j++){let b=zero;for(const[k,c]of p){const a=Math.floor(k/stride),d=k%stride;if(a<=i&&d<=j)b=qa(b,qm(c,Q(bin(i,a)*bin(j,d),0n,bin(m,a)*bin(n,d))));}if(min===null||sign(qs(b,min))<0)min=b;out.push({i,j,c:b,sign:sign(b)});}return{degree:[m,n],count:out.length,min,positive:out.every(x=>x.sign>0),out};}
 function serialize(p){return[...p].sort((a,b)=>a[0]-b[0]).map(([k,v])=>[Math.floor(k/stride),k%stride,String(v.a),String(v.b),String(v.d)]);}
 function deserialize(a){return P(a.map(([i,j,x,y,d])=>[i,j,Q(x,y,d)]));}
 const fmt=q=>({a:String(q.a),b:String(q.b),d:String(q.d)});
 return{Q,zero,one,two,sqrt2,qa,qs,qm,qd,qn,sign,P,pc,p1,px,py,pa,ps,pm,pow,scale,degree,exactDivide,factors,factor,rc,rp,rf,ra,rs,rm,rd,rk,rpow,denDegree,bernstein,serialize,deserialize,fmt};
}

function c6BuildTargets(f){
 const {Q,one,sqrt2,qm,p1,px,py,pa,ps,pm,scale,rf,rc,ra,rs,rm,rd,rk,rpow}=f;
 const k=Q(-1,1),k2=qm(k,k),sigma=Q(0,1,2),H=pa(p1,scale(px,k2)),t=scale(px,k),j=scale(pm(ps(p1,px),py),k);
 const Da=pa(p1,pm(t,t)),Dw=pa(pm(H,H),pm(j,j));
 const ca=rf(scale(ps(ps(p1,pm(t,t)),scale(t,Q(2))),sigma),Da,"Da");
 const sa=rf(scale(pa(ps(p1,pm(t,t)),scale(t,Q(2))),sigma),Da,"Da");
 const u=rf(scale(ps(ps(pm(H,H),pm(j,j)),scale(pm(j,H),Q(2))),sigma),Dw,"Dw");
 const v=rf(scale(pa(ps(pm(H,H),pm(j,j)),scale(pm(j,H),Q(2))),sigma),Dw,"Dw");
 const C=rs(rm(ca,u),rm(sa,v)),S=ra(rm(sa,u),rm(ca,v));
 const ell=rd(rs(rs(rc(sqrt2),ca),u),v,"V");
 const p=ra(ra(ra(rc(one),u),v),S),q=rs(rs(ra(rc(one),v),u),C);
 const r=rs(rs(ra(rc(one),u),v),ell),s=ra(ra(rc(Q(2)),u),v);
 const D=rs(rm(p,s),rm(q,r)),p2q2=ra(rpow(p,2),rpow(q,2)),r2s2=ra(rpow(r,2),rpow(s,2));
 const A=rd(rs(rm(s,p2q2),rm(q,r2s2)),rk(D,Q(2)),"2D");
 const B=rd(rs(rm(p,r2s2),rm(r,p2q2)),rk(D,Q(2)),"2D");
 const torque=ra(rm(S,rs(A,rm(rs(rc(one),ell),B))),rm(rm(ell,C),A));
 const hB=ra(rm(C,rs(A,rc(one))),rm(S,rs(B,rc(one)))),hC=ra(rs(A,rc(one)),ell);
 const cT=[rs(A,rc(Q(1,0,2))),rs(B,rc(Q(1,0,2)))];
 const cB=[ra(rs(A,p),rk(ra(u,v),Q(1,0,2))),ra(rs(B,q),rk(rs(v,u),Q(1,0,2)))];
 const cC=[rs(rs(A,r),rk(rs(v,u),Q(1,0,2))),ra(rs(B,s),rk(ra(u,v),Q(1,0,2)))];
 const dot=(a,b)=>ra(rm(a[0],b[0]),rm(a[1],b[1])),det=(a,b)=>rs(rm(a[0],b[1]),rm(a[1],b[0]));
 const targets=[ra(rs(hB,rc(Q(21,0,50))),rk(torque,Q(1,0,4))),rs(hC,rc(Q(21,0,50))),ra(rk(dot(cT,cB),Q(4)),rk(det(cT,cB),Q(3))),ra(rk(dot(cC,cT),Q(4)),rk(det(cC,cT),Q(3)))];
 return{targets,torque,hB,hC,A,B,D,Da,Dw,C,S,ell,p,q,r,s,cT,cB,cC};
}

function exactCertificateReport() {
  const f = buildC6Framework();
  const data = c6BuildTargets(f);
  const names = [
    "hB - 21/50 + (S*(A-(1-ell)*B)+ell*C*A)/4",
    "hC - 21/50",
    "4*dot(cT,cB)+3*det(cT,cB)",
    "4*dot(cC,cT)+3*det(cC,cT)"
  ];
  const floors = [f.Q(1,0,10), f.Q(1,0,7), f.Q(50), f.Q(186)];
  const results = data.targets.map((r,i) => {
    const bern = f.bernstein(r.n);
    const allAboveFloor = bern.out.every(x => f.sign(f.qs(x.c,floors[i])) > 0);
    if (!bern.positive || !allAboveFloor) throw new Error("Coefficient certificate failed: "+names[i]);
    return {
      name:names[i],
      numeratorDegree:f.degree(r.n),
      denominatorDegree:f.denDegree(r.d),
      numerator:f.serialize(r.n),
      denominator:[...r.d].map(([id,power])=>({
        name:f.factors[id].name,power,polynomial:f.serialize(f.factors[id].p)
      })),
      bernsteinDegree:bern.degree,
      coefficientCount:bern.count,
      exactMinimum:f.fmt(bern.min),
      strictRationalFloor:f.fmt(floors[i]),
      allCoefficientsStrictlyAboveFloor:allAboveFloor,
      coefficients:bern.out.map(x=>[x.i,x.j,String(x.c.a),String(x.c.b),String(x.c.d)])
    };
  });
  return {
    field:"Q(sqrt(2)); coefficient tuple [i,j,a,b,d] means (a+b*sqrt(2))/d",
    rectangle:"0 <= x,y <= 1",
    torque:"S*(A-(1-ell)*B)+ell*C*A = 0",
    totalCoefficients:results.reduce((n,r)=>n+r.coefficientCount,0),
    allPassed:true,
    results
  };
}
if (typeof module !== "undefined" && module.exports) {
  module.exports={buildC6Framework,c6BuildTargets,exactCertificateReport};
}
if (typeof require !== "undefined" && typeof module !== "undefined" && require.main===module) {
  console.log(JSON.stringify(exactCertificateReport(),null,2));
}
