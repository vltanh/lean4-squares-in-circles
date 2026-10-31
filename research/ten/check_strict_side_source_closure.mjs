// Exact 44-bit outward-rounded interval verifier. No floating-point predicate.
// Run: node research/ten/check_strict_side_source_closure.mjs
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
function ea(x,y) {
 const p=div(mul(TWO,x),add(O,sq(x))),q=div(sub(O,sq(x)),add(O,sq(x)));
 const r=div(mul(TWO,y),add(O,sq(y))),s=div(sub(O,sq(y)),add(O,sq(y)));
 const d=div(add(sub(sub(O,mul(root2,p)),mul(q,s)),mul(p,r)),q);
 const X=add(sub(sub(neg(O),r),q),p),Y=add(add(add(O,s),p),q);
 const D=sub(Y,div(mul(d,X),K));
 const t=div(add(add(add(mul(K,X),mul(d,Y)),sq(X)),sq(Y)),D);
 const u=sub(mul(K,HALF),div(mul(d,t),mul(TWO,K))),v=sub(K,u);
 const ha=mul(add(t,d),HALF),hb=mul(sub(t,d),HALF);
 const da=sub(mul(u,q),mul(ha,p)),db=sub(mul(v,s),mul(hb,r));
 const na=mul(ha,sub(mul(sub(u,O),q),mul(sub(ha,O),p)));
 const nb=mul(hb,sub(mul(sub(v,O),s),mul(sub(hb,O),r)));
 const E=sub(mul(na,db),mul(nb,da));
 const wx=add(v,X),wy=add(neg(hb),Y);
 const gx=sub(mul(mul(ha,db),p),mul(mul(hb,da),r));
 const gy=add(mul(mul(ha,db),q),mul(mul(hb,da),s));
 const G=sub(mul(wx,gy),mul(wy,gx));
 return {E,G,R2:add(sq(u),sq(ha)),ha,hb,da,db,u,v,p,q,r,s,D,ell:div(sub(sub(root2,p),r),q),centers:[[sub(HALF,u),sub(HALF,ha)],[sub(v,HALF),sub(HALF,hb)],[mul(sub(v,u),HALF),neg(div(na,da))],[add(sub(sub(sub(v,O),r),mul(q,HALF)),mul(p,HALF)),add(add(add(sub(O,hb),s),mul(p,HALF)),mul(q,HALF))]]};
}
const dconst=a=>[a,Z,Z],dx=a=>[a,O,Z],dy=a=>[a,Z,O];
const da=(a,b)=>a.map((x,i)=>add(x,b[i]));
const dn=a=>a.map(neg),ds=(a,b)=>da(a,dn(b));
const dm=(a,b)=>[mul(a[0],b[0]),add(mul(a[1],b[0]),mul(a[0],b[1])),add(mul(a[2],b[0]),mul(a[0],b[2]))];
const dd=(a,b)=>[div(a[0],b[0]),div(sub(mul(a[1],b[0]),mul(a[0],b[1])),sq(b[0])),div(sub(mul(a[2],b[0]),mul(a[0],b[2])),sq(b[0]))];
function ead(xi,yi){
 const x=dx(xi),y=dy(yi),o=dconst(O),two=dconst(TWO),half=dconst(HALF),rt=dconst(root2),k=dconst(K);
 const p=dd(dm(two,x),da(o,dm(x,x))),q=dd(ds(o,dm(x,x)),da(o,dm(x,x)));
 const r=dd(dm(two,y),da(o,dm(y,y))),s=dd(ds(o,dm(y,y)),da(o,dm(y,y)));
 const d=dd(da(ds(ds(o,dm(rt,p)),dm(q,s)),dm(p,r)),q);
 const X=da(ds(ds(dn(o),r),q),p),Y=da(da(da(o,s),p),q);
 const D=ds(Y,dd(dm(d,X),k));
 const t=dd(da(da(da(dm(k,X),dm(d,Y)),dm(X,X)),dm(Y,Y)),D);
 const u=ds(dm(k,half),dd(dm(d,t),dm(two,k))),v=ds(k,u);
 const ha=dm(da(t,d),half),hb=dm(ds(t,d),half);
 const dA=ds(dm(u,q),dm(ha,p)),dB=ds(dm(v,s),dm(hb,r));
 const na=dm(ha,ds(dm(ds(u,o),q),dm(ds(ha,o),p)));
 const nb=dm(hb,ds(dm(ds(v,o),s),dm(ds(hb,o),r)));
 const E=ds(dm(na,dB),dm(nb,dA));
 const wx=da(v,X),wy=da(dn(hb),Y);
 const gx=ds(dm(dm(ha,dB),p),dm(dm(hb,dA),r));
 const gy=da(dm(dm(ha,dB),q),dm(dm(hb,dA),s));
 const G=ds(dm(wx,gy),dm(wy,gx));
 return {E,G};
}

const cut=(a,b)=>a[0]>b[1]||a[1]<b[0];
const inside=(a,b)=>a[0]>=b[0]&&a[1]<=b[1];
const absmax=a=>{const x=a[0]<0n?-a[0]:a[0],y=a[1]<0n?-a[1]:a[1];return x>y?x:y;};



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
function run(cert){
 assert(cert.scale_bits===44,"scale");
 assert(cert.capacity.core_boxes_scaled.length===4&&cert.capacity.slots.length===5,"four core/five slots");
 assert(cert.capacity.slot_center_denominator===1000&&String(cert.capacity.slot_radius)==="9,20"&&String(cert.capacity.center_domain_radius)==="3,2","capacity constants");
 assert(root2[1]-S<I(27,64)[0],"root domain");
 assert(root2[0]*root2[0]<2n*S*S&&root2[1]*root2[1]>2n*S*S,"sqrt2 bracket");
 partition(cert.enclosure.leaves);partition(cert.capacity.leaves);
 const tb=cert.target_scaled.map(a=>a.map(BigInt));
 assert(tb.every((a,i)=>a[0]<a[1]),"target widths");
 const counts={},initial=[[0n,I(27,64)[1]],[0n,I(27,64)[1]]];
 for(const [path,rule,arg] of cert.enclosure.leaves){
 const [x,y]=boxAt(path,initial);let ok=false;
 if(rule==="outside")ok=x[0]>=root2[1]-S||y[0]>=root2[1]-S;
 else if(rule==="target")ok=inside(x,tb[0])&&inside(y,tb[1]);
 else if(rule==="boundary"||rule==="boundary2"){
 const bb=cert.boundary_boxes[rule==="boundary"?0:1],bx=[I(bb.x[0],bb.x[1])[0],I(bb.x[2],bb.x[3])[1]],by=[I(bb.y[0],bb.y[1])[0],I(bb.y[2],bb.y[3])[1]];
 ok=inside(x,bx)&&inside(y,by);
 }else if(rule==="Newton")ok=newtonReject(x,y,arg);
 else{
 const v=ea(x,y);
 if(rule==="E"||rule==="G")ok=v[rule][0]>0n||v[rule][1]<0n;
 else if(rule==="length")ok=v.ell[1]<=0n||v.ell[0]>S;
 else if(rule==="radius")ok=v.R2[0]>I(9,2)[1];
 else if(rule==="height")ok=v.ha[1]<=0n||v.hb[1]<=0n;
 else if(rule==="force")ok=v.da[1]<=0n||v.db[1]<=0n;
 }
 assert(ok,"failed enclosure "+path+" "+rule);counts[rule]=(counts[rule]||0)+1;
 }
 const boundaryNorms=[];
 for(const b of cert.boundary_boxes){
 const x=[I(b.x[0],b.x[1])[0],I(b.x[2],b.x[3])[1]],y=[I(b.y[0],b.y[1])[0],I(b.y[2],b.y[3])[1]];
 const j=ead(x,y),J=[[j.E[1],j.E[2]],[j.G[1],j.G[2]]],C=b.preconditioner.map(row=>row.map(n=>I(n,b.denominator)));
 const Q=C.map((row,i)=>[0,1].map(k=>sub(i===k?O:Z,add(mul(row[0],J[0][k]),mul(row[1],J[1][k])))));
 const norms=Q.map(row=>row.reduce((z,v)=>z+absmax(v),0n));assert(norms.every(n=>n<S),"boundary injectivity");boundaryNorms.push(norms.map(n=>String(n)+"/"+String(S)));
 assert(root2[0]-S>=x[0]&&root2[1]-S<=x[1],"known boundary root x");
 const yy=b.known_root.endsWith(",0")?Z:sub(root2,O);
 assert(inside(yy,y),"known boundary root y");
 }
 const v=ea(...tb),cores=cert.capacity.core_boxes_scaled.map(k=>k.map(a=>a.map(BigInt)));
 assert(v.R2[1]<I(17,4)[0],"radius below 17/4");
 for(let i=0;i<4;i++)for(let d=0;d<2;d++)assert(inside(v.centers[i][d],cores[i][d]),"uniform core box");
 const cap=cert.capacity,rad=I(3,2)[0],initialC=[[-rad,rad],[-rad,rad]],slots=cap.slots.map(p=>p.map(n=>I(n,cap.slot_center_denominator)));
 const cc={},S2=S*S;
 for(const [path,rule,k]of cap.leaves){
 const b=boxAt(path,initialC);let ok=false;
 if(rule==="outside"){let norm=0n;for(const a of b){const d=a[0]>0n?a[0]:a[1]<0n?-a[1]:0n;norm+=d*d;}ok=4n*norm>9n*S2;}
 if(rule==="core")ok=maxDistance(b,cores[k])<S2;
 if(rule==="slot")ok=400n*maxDistance(b,slots[k])<81n*S2;
 assert(ok,"failed center cover "+path+" "+rule);const key=rule+(k===undefined?"":":"+k);cc[key]=(cc[key]||0)+1;
 }
 return{enclosureLeaves:cert.enclosure.leaves.length,enclosureCounts:counts,boundaryNorms,centerCoverLeaves:cap.leaves.length,centerCoverCounts:cc,R2:out(v.R2)};
}

function verifyExactBoundaryRoots(){

const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){const t=a%b;a=b;b=t;}return a;};
const Q=(a,b=0n,d=1n)=>{a=BigInt(a);b=BigInt(b);d=BigInt(d);if(!d)throw Error("zero denominator");if(d<0n){a=-a;b=-b;d=-d;}const g=gcd(gcd(a,b),d);return[a/g,b/g,d/g];};
const I=(n,d=1)=>Q(n,0,d);
const add=(x,y)=>Q(x[0]*y[2]+y[0]*x[2],x[1]*y[2]+y[1]*x[2],x[2]*y[2]);
const neg=x=>[-x[0],-x[1],x[2]],sub=(x,y)=>add(x,neg(y));
const mul=(x,y)=>Q(x[0]*y[0]+2n*x[1]*y[1],x[0]*y[1]+x[1]*y[0],x[2]*y[2]);
const div=(x,y)=>mul(x,Q(y[2]*y[0],-y[2]*y[1],y[0]*y[0]-2n*y[1]*y[1]));
const sq=x=>mul(x,x);
const Z=I(0),O=I(1),TWO=I(2),HALF=I(1,2),root2=Q(0,1),K=add(TWO,root2);

function ea(x,y) {
 const p=div(mul(TWO,x),add(O,sq(x))),q=div(sub(O,sq(x)),add(O,sq(x)));
 const r=div(mul(TWO,y),add(O,sq(y))),s=div(sub(O,sq(y)),add(O,sq(y)));
 const d=div(add(sub(sub(O,mul(root2,p)),mul(q,s)),mul(p,r)),q);
 const X=add(sub(sub(neg(O),r),q),p),Y=add(add(add(O,s),p),q);
 const D=sub(Y,div(mul(d,X),K));
 const t=div(add(add(add(mul(K,X),mul(d,Y)),sq(X)),sq(Y)),D);
 const u=sub(mul(K,HALF),div(mul(d,t),mul(TWO,K))),v=sub(K,u);
 const ha=mul(add(t,d),HALF),hb=mul(sub(t,d),HALF);
 const da=sub(mul(u,q),mul(ha,p)),db=sub(mul(v,s),mul(hb,r));
 const na=mul(ha,sub(mul(sub(u,O),q),mul(sub(ha,O),p)));
 const nb=mul(hb,sub(mul(sub(v,O),s),mul(sub(hb,O),r)));
 const E=sub(mul(na,db),mul(nb,da));
 const wx=add(v,X),wy=add(neg(hb),Y);
 const gx=sub(mul(mul(ha,db),p),mul(mul(hb,da),r));
 const gy=add(mul(mul(ha,db),q),mul(mul(hb,da),s));
 const G=sub(mul(wx,gy),mul(wy,gx));
 return {E,G,R2:add(sq(u),sq(ha)),ha,hb,da,db,u,v,p,q,r,s,D,ell:div(sub(sub(root2,p),r),q),centers:[[sub(HALF,u),sub(HALF,ha)],[sub(v,HALF),sub(HALF,hb)],[mul(sub(v,u),HALF),neg(div(na,da))],[add(sub(sub(sub(v,O),r),mul(q,HALF)),mul(p,HALF)),add(add(add(sub(O,hb),s),mul(p,HALF)),mul(q,HALF))]]};
}

const b=sub(root2,O);for(const v of [ea(b,b),ea(b,Z)]){assert(v.E[0]===0n&&v.E[1]===0n&&v.G[0]===0n&&v.G[1]===0n,"boundary root identity");}
return true;
}

const certificate=JSON.parse(readFileSync(new URL("./strict_side_source_closure_certificate.json",import.meta.url),"utf8"));
verifyExactBoundaryRoots();
console.log(JSON.stringify(run(certificate),null,2));
