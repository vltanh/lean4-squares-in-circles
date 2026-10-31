// Separate 60-bit interval backend; shared logical certificate predicates.
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

function squareRoot(a){if(a[0]<0n)throw Error("sqrt domain");const lo=integerSqrt(a[0]*S),hi=integerSqrt(a[1]*S);return[lo,hi*hi===a[1]*S?hi:hi+1n];}
function jetSqrt(a){const v=squareRoot(a.v),f=reciprocal(mul(TWO,v));return new Jet(v,mul(f,a.x),mul(f,a.y));}
function allRadial(xi,ti,differentiate=false){
 const x=new Jet(xi,differentiate?O:Z,Z),t=new Jet(ti,Z,differentiate?O:Z),one=new Jet(O),two=new Jet(TWO),half=new Jet(HALF),rt=new Jet(root2);
 const p=two.times(x).over(one.plus(x.times(x))),q=one.minus(x.times(x)).over(one.plus(x.times(x)));
 const a=one.minus(t.times(t)).over(one.plus(t.times(t))),b=two.times(t).over(one.plus(t.times(t))),r=rt.minus(a).minus(p),s=jetSqrt(one.minus(r.times(r)));
 const ax=one.plus(a.times(half)).plus(p),ay=one.plus(b.times(half)).plus(q),bx=one.plus(a.times(half)).plus(r),by=one.negative().plus(b.times(half)).minus(s);
 const LA=ax.times(ax).plus(ay.times(ay)).minus(new Jet(I(5,4))).over(two.times(one.minus(b.times(ax)).plus(a.times(ay))));
 const LB=bx.times(bx).plus(by.times(by)).minus(new Jet(I(5,4))).over(two.times(one.plus(b.times(bx)).minus(a.times(by))));
 const L=LA,u=ax.plus(L.times(b)),v=bx.minus(L.times(b)),ha=ay.minus(L.times(a)),hb=by.negative().minus(L.times(a));
 const da=u.times(q).minus(ha.times(p)),db=v.times(s).minus(hb.times(r)),na=ha.times(u.minus(one).times(q).minus(ha.minus(one).times(p))),nb=hb.times(v.minus(one).times(s).minus(hb.minus(one).times(r)));
 const E=na.times(db).minus(nb.times(da)),G=LA.minus(LB),h=na.over(da).negative(),R2=L.plus(one).times(L.plus(one)).plus(new Jet(I(1,4)));
 return{E,G,L,LA,LB,R2,HA:ha,HB:hb,DA:da,DB:db,r,s,supportA:p.times(a).plus(q.times(b)),supportB:r.times(a).negative().plus(s.times(b)),centers:[[half.minus(u),half.minus(ha)],[v.minus(half),half.minus(hb)],[v.minus(u).times(half),h],[L.plus(half).times(b).negative(),L.plus(half).times(a)]]};
}
function ea(x,t){const z=allRadial(x,t),v={};for(const k of ["E","G","L","LA","LB","R2","HA","HB","DA","DB","r","s","supportA","supportB"])v[k]=z[k].v;v.centers=z.centers.map(c=>c.map(v=>v.v));return v;}
function ead(x,t){const z=allRadial(x,t,true);return{E:[z.E.v,z.E.x,z.E.y],G:[z.G.v,z.G.x,z.G.y]};}


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
certificate.target_scaled=certificate.target_scaled.map(a=>a.map(v=>String(BigInt(v)<<16n)));
certificate.capacity.core_boxes_scaled=certificate.capacity.core_boxes_scaled.map(k=>k.map(a=>a.map(v=>String(BigInt(v)<<16n))));
console.log(JSON.stringify(run(certificate),null,2));
