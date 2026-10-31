// A second arithmetic backend: 60-bit intervals, reciprocal-based Jet AD.
// The logical certificate checks are shared with the 44-bit checker;
// this is not a claim of independent mathematical or agent review.
// Coverage uses a full binary trie rather than the other checker's Kraft sum.
import {readFileSync} from "node:fs";

const S=1n<<60n;
function down(n,d){if(d<0n){n=-n;d=-d;}const q=n/d,r=n%d;return r<0n?q-1n:q;}
function up(n,d){return-down(-n,d);}
function integerSqrt(n){if(n<0n)throw Error("sqrt");if(n<2n)return n;let x=1n<<BigInt((n.toString(2).length+1)>>1);for(;;){let y=(x+n/x)>>1n;if(y>=x)return x;x=y;}}
const lowSqrt=integerSqrt(2n*S*S);
const root2=[lowSqrt,lowSqrt+1n];
const I=(n,d=1)=>[down(BigInt(n)*S,BigInt(d)),up(BigInt(n)*S,BigInt(d))];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const neg=a=>[-a[1],-a[0]],sub=(a,b)=>add(a,neg(b));
function mul(a,b){let l=null,h=null;for(const x of a)for(const y of b){const v=x*y;if(l===null||v<l)l=v;if(h===null||v>h)h=v;}return[down(l,S),up(h,S)];}
function reciprocal(a){if(a[0]<=0n&&a[1]>=0n)throw Error("zero divisor");return[down(S*S,a[1]),up(S*S,a[0])];}
const div=(a,b)=>mul(a,reciprocal(b));
const sq=a=>a[0]<=0n&&a[1]>=0n?[0n,up(((-a[0]>a[1]?-a[0]:a[1])**2n),S)]:mul(a,a);
const O=I(1),Z=I(0),TWO=I(2),HALF=I(1,2),K=add(TWO,root2);
const out=a=>a.map(n=>Number(n)/Number(S));
const cut=(a,b)=>a[0]>b[1]||a[1]<b[0],inside=(a,b)=>a[0]>=b[0]&&a[1]<=b[1];
const absmax=a=>-a[0]>a[1]?-a[0]:a[1];
class Jet{
 constructor(v,x=Z,y=Z){this.v=v;this.x=x;this.y=y;}
 plus(b){return new Jet(add(this.v,b.v),add(this.x,b.x),add(this.y,b.y));}
 negative(){return new Jet(neg(this.v),neg(this.x),neg(this.y));}
 minus(b){return this.plus(b.negative());}
 times(b){return new Jet(mul(this.v,b.v),add(mul(this.x,b.v),mul(this.v,b.x)),add(mul(this.y,b.v),mul(this.v,b.y)));}
 inverse(){const v=reciprocal(this.v),f=neg(sq(v));return new Jet(v,mul(f,this.x),mul(f,this.y));}
 over(b){return this.times(b.inverse());}
}
function allEA(xi,yi,derivative=false){
 const x=new Jet(xi,derivative?O:Z,Z),y=new Jet(yi,Z,derivative?O:Z);
 const one=new Jet(O),two=new Jet(TWO),half=new Jet(HALF),rt=new Jet(root2),k=new Jet(K);
 const dx=one.plus(x.times(x)),dy=one.plus(y.times(y));
 const p=two.times(x).over(dx),q=one.minus(x.times(x)).over(dx),r=two.times(y).over(dy),s=one.minus(y.times(y)).over(dy);
 const d=one.minus(rt.times(p)).minus(q.times(s)).plus(p.times(r)).over(q);
 const X=one.negative().minus(r).minus(q).plus(p),Y=one.plus(s).plus(p).plus(q);
 const D=Y.minus(d.times(X).over(k));
 const t=k.times(X).plus(d.times(Y)).plus(X.times(X)).plus(Y.times(Y)).over(D);
 const u=k.times(half).minus(d.times(t).over(two.times(k))),v=k.minus(u);
 const ha=t.plus(d).times(half),hb=t.minus(d).times(half);
 const da=u.times(q).minus(ha.times(p)),db=v.times(s).minus(hb.times(r));
 const na=ha.times(u.minus(one).times(q).minus(ha.minus(one).times(p))),nb=hb.times(v.minus(one).times(s).minus(hb.minus(one).times(r)));const E=na.times(db).minus(nb.times(da));
 const wx=v.plus(X),wy=hb.negative().plus(Y),forceA=ha.times(db),forceB=hb.times(da);
 const gx=forceA.times(p).minus(forceB.times(r)),gy=forceA.times(q).plus(forceB.times(s));
 const G=wx.times(gy).minus(wy.times(gx));
 const z=ha.minus(ha.times(q.minus(p)).over(da));
 const centers=[[half.minus(u),half.minus(ha)],[v.minus(half),half.minus(hb)],[v.minus(u).times(half),z.negative()],[v.minus(one).minus(r).minus(q.times(half)).plus(p.times(half)),one.minus(hb).plus(s).plus(p.times(half)).plus(q.times(half))]];
 const rad=k.times(k).plus(d.times(d)).times(k.times(k).plus(t.times(t))).over(new Jet(I(4)).times(k.times(k)));
 const ell=rt.minus(p).minus(r).over(q);
 return{E,G,R2:rad,ell,da,db,ha,hb,centers};
}
function ea(x,y){const r=allEA(x,y);const v={};for(const k of["E","G","R2","ell","da","db","ha","hb"])v[k]=r[k].v;v.centers=r.centers.map(c=>c.map(a=>a.v));return v;}
function ead(x,y){const r=allEA(x,y,true);return{E:[r.E.v,r.E.x,r.E.y],G:[r.G.v,r.G.x,r.G.y]};}



function assert(ok,msg){if(!ok)throw Error(msg);}
function partition(leaves){
 const root={};
 for(const [path]of leaves){let n=root;for(const bit of path){assert(bit==="0"||bit==="1","path character");assert(!n.leaf,"ancestor leaf");n[bit]??={};n=n[bit];}assert(!n.leaf&&!n[0]&&!n[1],"duplicate or descendant");n.leaf=true;}
 function visit(n){if(n.leaf){assert(!n[0]&&!n[1],"leaf child");return;}assert(n[0]&&n[1],"missing binary child");visit(n[0]);visit(n[1]);}visit(root);
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
// Certificate coordinates use units 2^-44; this backend uses 2^-60.
certificate.target_scaled=certificate.target_scaled.map(a=>a.map(v=>String(BigInt(v)<<16n)));
certificate.capacity.core_boxes_scaled=certificate.capacity.core_boxes_scaled.map(k=>k.map(a=>a.map(v=>String(BigInt(v)<<16n))));
verifyExactBoundaryRoots();
console.log(JSON.stringify(run(certificate),null,2));
