// Exact 44-bit interval and physical-capacity verifier.
import {readFileSync} from "node:fs";

const S=1n<<44n;
const fl=(a,b)=>{if(b<0n){a=-a;b=-b;}return a>=0n?a/b:-((-a+b-1n)/b)};
const ce=(a,b)=>-fl(-a,b);
const I=(n,d=1)=>{n=BigInt(n);d=BigInt(d);return[fl(n*S,d),ce(n*S,d)]};
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const neg=a=>[-a[1],-a[0]],sub=(a,b)=>add(a,neg(b));
const mul=(a,b)=>{const t=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]];return[fl(t.reduce((x,y)=>x<y?x:y),S),ce(t.reduce((x,y)=>x>y?x:y),S)]};
const div=(a,b)=>{if(b[0]<=0n&&b[1]>=0n)throw Error("zero divisor");const t=[fl(a[0]*S,b[0]),fl(a[0]*S,b[1]),fl(a[1]*S,b[0]),fl(a[1]*S,b[1])],v=[ce(a[0]*S,b[0]),ce(a[0]*S,b[1]),ce(a[1]*S,b[0]),ce(a[1]*S,b[1])];return[t.reduce((x,y)=>x<y?x:y),v.reduce((x,y)=>x>y?x:y)]};
const sq=a=>a[0]>=0n?mul(a,a):a[1]<=0n?mul(neg(a),neg(a)):[0n,ce((a[0]*a[0]>a[1]*a[1]?a[0]*a[0]:a[1]*a[1]),S)];
const hull=(a,b)=>[a[0]<b[0]?a[0]:b[0],a[1]>b[1]?a[1]:b[1]];
const out=a=>a.map(x=>Number(x)/Number(S));
const Z=I(0),O=I(1),TWO=I(2),HALF=I(1,2);
const root2=[24879108095803n,24879108095804n],K=add(TWO,root2);
const dconst=a=>[a,Z,Z],dx=a=>[a,O,Z],dy=a=>[a,Z,O];
const da=(a,b)=>a.map((x,i)=>add(x,b[i]));
const dn=a=>a.map(neg),ds=(a,b)=>da(a,dn(b));
const dm=(a,b)=>[mul(a[0],b[0]),add(mul(a[1],b[0]),mul(a[0],b[1])),add(mul(a[2],b[0]),mul(a[0],b[2]))];
const dd=(a,b)=>[div(a[0],b[0]),div(sub(mul(a[1],b[0]),mul(a[0],b[1])),sq(b[0])),div(sub(mul(a[2],b[0]),mul(a[0],b[2])),sq(b[0]))];

function isqrt(n){if(n<0n)throw Error("negative sqrt");if(n<2n)return n;let v=1n<<BigInt((n.toString(2).length+1)>>1);for(;;){const w=(v+n/v)>>1n;if(w>=v)return v;v=w;}}
function sqrtInterval(a){if(a[0]<0n)throw Error("sqrt domain");const lo=isqrt(a[0]*S),hi=isqrt(a[1]*S);return[lo,hi*hi===a[1]*S?hi:hi+1n];}
const dsqrt=a=>{const v=sqrtInterval(a[0]),v2=mul(TWO,v);return[v,div(a[1],v2),div(a[2],v2)];};
function radialAll(xi,ti,derivative=false){
 const x=derivative?dx(xi):dconst(xi),t=derivative?dy(ti):dconst(ti);
 const o=dconst(O),two=dconst(TWO),half=dconst(HALF),rt=dconst(root2);
 const p=dd(dm(two,x),da(o,dm(x,x))),q=dd(ds(o,dm(x,x)),da(o,dm(x,x)));
 const a=dd(ds(o,dm(t,t)),da(o,dm(t,t))),b=dd(dm(two,t),da(o,dm(t,t)));
 const r=ds(ds(rt,a),p),s=dsqrt(ds(o,dm(r,r)));
 const AX=da(da(o,dm(a,half)),p),AY=da(da(o,dm(b,half)),q);
 const BX=da(da(o,dm(a,half)),r),BY=ds(da(dn(o),dm(b,half)),s);
 const LA=dd(ds(da(dm(AX,AX),dm(AY,AY)),dconst(I(5,4))),dm(two,da(ds(o,dm(b,AX)),dm(a,AY))));
 const LB=dd(ds(da(dm(BX,BX),dm(BY,BY)),dconst(I(5,4))),dm(two,ds(da(o,dm(b,BX)),dm(a,BY))));
 const L=LA,u=da(AX,dm(L,b)),v=ds(BX,dm(L,b)),HA=ds(AY,dm(L,a)),HB=ds(dn(BY),dm(L,a));
 const DA=ds(dm(u,q),dm(HA,p)),DB=ds(dm(v,s),dm(HB,r));
 const NA=dm(HA,ds(dm(ds(u,o),q),dm(ds(HA,o),p))),NB=dm(HB,ds(dm(ds(v,o),s),dm(ds(HB,o),r)));
 const E=ds(dm(NA,DB),dm(NB,DA)),G=ds(LA,LB);
 const h=dn(dd(NA,DA)),R2=da(dm(da(L,o),da(L,o)),dconst(I(1,4)));
 const centers=[[ds(half,u),ds(half,HA)],[ds(v,half),ds(half,HB)],[dm(ds(v,u),half),h],[dn(dm(da(L,half),b)),dm(da(L,half),a)]];
 return {E,G,L,LA,LB,R2,HA,HB,DA,DB,r,s,p,q,a,b,supportA:da(dm(p,a),dm(q,b)),supportB:da(dn(dm(r,a)),dm(s,b)),centers};
}
function ea(x,t){const z=radialAll(x,t),v={};for(const k of ["E","G","L","LA","LB","R2","HA","HB","DA","DB","r","s","supportA","supportB"])v[k]=z[k][0];v.centers=z.centers.map(c=>c.map(v=>v[0]));return v;}
function ead(x,t){const z=radialAll(x,t,true);return{E:z.E,G:z.G};}

const cut=(a,b)=>a[0]>b[1]||a[1]<b[0],inside=(a,b)=>a[0]>=b[0]&&a[1]<=b[1];const absmax=a=>-a[0]>a[1]?-a[0]:a[1];

function assert(ok,msg){if(!ok)throw Error(msg);}
function partition(leaves){
 const set=new Set(leaves.map(r=>r[0]));
 assert(set.size===leaves.length,"duplicate path");
 let total=0n;const depth=Math.max(...leaves.map(r=>r[0].length));
 for(const [p]of leaves){assert(/^[01]*$/.test(p),"invalid path");for(let k=0;k<p.length;k++)assert(!set.has(p.slice(0,k)),"ancestor leaf");total+=1n<<BigInt(depth-p.length);}
 assert(total===(1n<<BigInt(depth)),"incomplete prefix cover");
}
function boxAt(path,bounds){
 const b=bounds.map(a=>a.slice());
 for(const bit of path){const dim=b[0][1]-b[0][0]>=b[1][1]-b[1][0]?0:1,m=(b[dim][0]+b[dim][1])/2n;if(bit==="0")b[dim][1]=m;else b[dim][0]=m;}
 return b;
}
function newtonReject(x,y,nums){
 const j=ead(x,y),J=[[j.E[1],j.E[2]],[j.G[1],j.G[2]]],C=nums.map(row=>row.map(n=>I(BigInt(n),1024)));
 const mid=[(x[0]+x[1])/2n,(y[0]+y[1])/2n],a=ea([mid[0],mid[0]],[mid[1],mid[1]]),F=[a.E,a.G],b=[x,y];
 const Q=C.map((row,i)=>[0,1].map(k=>sub(i===k?O:Z,add(mul(row[0],J[0][k]),mul(row[1],J[1][k])))));
 const N=C.map((row,i)=>add(sub([mid[i],mid[i]],add(mul(row[0],F[0]),mul(row[1],F[1]))),add(mul(Q[i][0],sub(b[0],[mid[0],mid[0]])),mul(Q[i][1],sub(b[1],[mid[1],mid[1]])))));
 return cut(N[0],x)||cut(N[1],y);
}
function maxDistance(b,k){let z=0n;for(let i=0;i<2;i++){const d=[b[i][0]-k[i][1],b[i][1]-k[i][0]];z+=d[0]*d[0]>d[1]*d[1]?d[0]*d[0]:d[1]*d[1];}return z;}

function expandedSquareDistance(b,k){let z=0n;for(let i=0;i<2;i++){const low=b[i][0]-k[i][1],high=b[i][1]-k[i][0];let a=-low>high?-low:high;a=a>S/2n?a-S/2n:0n;z+=a*a;}return z;}
function run(cert){
 assert(cert.scale_bits===44,"certificate scale");assert(root2[0]*root2[0]<2n*S*S&&root2[1]*root2[1]>2n*S*S,"sqrt2");
 assert(root2[1]-S<I(27,64)[0],"initial domain");
 partition(cert.enclosure.leaves);partition(cert.capacity.leaves);
 assert(cert.capacity.core_boxes_scaled.length===4&&cert.capacity.slots.length===5,"core and slot counts");
 assert(cert.capacity.slot_center_denominator===1000&&String(cert.capacity.slot_radius)==="9,20"&&String(cert.capacity.center_domain_radius)==="23,16","constants");
 const target=cert.target_scaled.map(a=>a.map(BigInt)),b0=I(27,64)[0],counts={};
 for(const [path,rule,arg]of cert.enclosure.leaves){
  const [x,t]=boxAt(path,[[0n,b0],[-b0,b0]]);let ok=false;
  if(rule==="outside")ok=x[0]>=root2[1]-S||t[0]>=root2[1]-S||t[1]<=S-root2[1];
  else if(rule==="target")ok=inside(x,target[0])&&inside(t,target[1]);
  else if(rule==="r"){const p=div(mul(TWO,x),add(O,sq(x))),a=div(sub(O,sq(t)),add(O,sq(t))),r=sub(sub(root2,a),p);ok=r[1]<=0n||2n*r[0]>=root2[1];}
  else if(rule==="Newton")ok=newtonReject(x,t,arg);
  else{
   const z=ea(x,t);
   if(rule==="E"||rule==="G")ok=z[rule][0]>0n||z[rule][1]<0n;
   if(rule==="L")ok=z.L[1]<=I(9,10)[0]||z.L[0]>=I(17,16)[1];
   if(rule==="support")ok=z.supportA[1]<=0n||z.supportB[0]>=0n;
   if(rule==="height")ok=z.HA[1]<=I(1,2)[0]||z.HB[1]<=I(1,2)[0];
   if(rule==="force")ok=z.DA[1]<=0n||z.DB[1]<=0n;
  }
  assert(ok,"parameter leaf "+path+" "+rule);counts[rule]=(counts[rule]||0)+1;
 }
 const z=ea(...target);assert(z.R2[1]<I(4)[0],"squared radius below four");
 assert(I(1025,256)[0]>I(4)[1],"center radius threshold");
 const cores=cert.capacity.core_boxes_scaled.map(k=>k.map(a=>a.map(BigInt)));
 for(let i=0;i<4;i++)for(let d=0;d<2;d++)assert(inside(z.centers[i][d],cores[i][d]),"core box");
 const cap=cert.capacity,rad=I(23,16)[0],S2=S*S,slots=cap.slots.map(p=>p.map(n=>I(n,1000))),cc={};
 for(const [path,rule,k]of cap.leaves){
 const b=boxAt(path,[[-rad,rad],[-rad,rad]]);let ok=false;
 if(rule==="outside"){let n=0n;for(const a of b){const d=a[0]>0n?a[0]:a[1]<0n?-a[1]:0n;n+=d*d;}ok=256n*n>529n*S2;}
 if(rule==="core")ok=maxDistance(b,cores[k])<S2;
 if(rule==="square")ok=(k===0||k===1)&&4n*expandedSquareDistance(b,cores[k])<S2;
 if(rule==="slot")ok=400n*maxDistance(b,slots[k])<81n*S2;
 assert(ok,"capacity leaf "+path+" "+rule);const key=rule+(k===undefined?"":":"+k);cc[key]=(cc[key]||0)+1;
 }
 return{parameterLeaves:cert.enclosure.leaves.length,parameterCounts:counts,capacityLeaves:cap.leaves.length,capacityCounts:cc,R2:out(z.R2)};
}

const certificate=JSON.parse(readFileSync(new URL("./strict_vertex_source_closure_certificate.json",import.meta.url),"utf8"));
console.log(JSON.stringify(run(certificate),null,2));
