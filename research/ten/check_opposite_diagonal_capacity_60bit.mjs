// Separate 60-bit arithmetic backend; shared logical capacity predicates.
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

function sqrtInterval(a){if(a[0]<0n)throw Error("sqrt domain");const lo=integerSqrt(a[0]*S),hi=integerSqrt(a[1]*S);return[lo,hi*hi===a[1]*S?hi:hi+1n];}
function oppositeBoxes(b){

 const [d,xi,tau]=b,rem=sub(O,d);
 const hv=[],tv=[],av=[],bv=[];
 for(const de of d)for(const xe of xi){
 const di=[de,de],xx=[xe,xe],rr=sub(O,di),tt=add(add(O,di),mul(xx,rr)),bb=add(HALF,mul(HALF,mul(xx,rr)));
 tv.push(tt);bv.push(bb);av.push(add(bb,di));
 for(const te of tau)hv.push(add(I(-1,2),mul(rr,add(mul(HALF,xx),mul([te,te],sub(O,xx))))));
 }
 const join=v=>[v.reduce((m,a)=>a[0]<m?a[0]:m,v[0][0]),v.reduce((m,a)=>a[1]>m?a[1]:m,v[0][1])];
 const T=join(tv),HB=join(bv),HA=join(av),h=join(hv),cx=div(mul(d,T),mul(TWO,K));
 const cores=[[add(sub(HALF,mul(K,HALF)),cx),sub(HALF,HA)],[add(sub(mul(K,HALF),HALF),cx),sub(HB,HALF)],[cx,h]];
 const k2=sq(K),q=div(mul(add(k2,sq(d)),add(k2,sq(T))),mul(I(4),k2));
 const Q=[q[0],q[1]>I(17,4)[1]?I(17,4)[1]:q[1]];
 const rr=sqrtInterval(sub(Q,I(1,4))),rad=rr[1]-S/2n;
 return{cores,Q,rad:rad>3n*S/2n?3n*S/2n:rad};
}


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

function parameterBox(path,scaleBits){
 const U=1n<<44n,b=[[0n,U],[0n,U],[0n,U]];
 for(const bit of path){
 const [d,x,t]=b,v=[(d[1]-d[0])*U*U,((x[1]-x[0])*(U-d[0])*U)/2n,(t[1]-t[0])*(U-d[0])*(U-x[0])];
 let k=0;for(let i=1;i<3;i++)if(v[i]>v[k])k=i;
 const m=(b[k][0]+b[k][1])/2n;if(bit==="0")b[k][1]=m;else b[k][0]=m;
 }
 return b.map(a=>a.map(v=>v<<BigInt(scaleBits-44)));
}
function coreDistance(cell,k,rotated){
 let a=cell.map((v,i)=>[v[0]-k[i][1],v[1]-k[i][0]]);
 if(rotated){const f=mul(root2,HALF);a=[mul(add(a[0],a[1]),f),mul(sub(a[1],a[0]),f)];}
 let z=0n;for(const v of a){let d=-v[0]>v[1]?-v[0]:v[1];d=d>S/2n?d-S/2n:0n;z+=d*d;}return z;
}
function diskDistance(cell,p){let n=0n;for(let i=0;i<2;i++){const l=cell[i][0]-p[i][1],h=cell[i][1]-p[i][0];n+=(-l>h?-l:h)**2n;}return n;}
function run(data,scaleBits=44){
 assert(data.scale_bits===44,"data scale");
 assert(root2[0]*root2[0]<2n*S*S&&root2[1]*root2[1]>2n*S*S,"sqrt2");
 partition([...data.rows,...data.excluded].map(r=>[r.path]));
 const shift=BigInt(scaleBits-44);let cells=0,maxDepth=0;
 for(const row of data.excluded){
 const b=parameterBox(row.path,scaleBits),r=oppositeBoxes(b);
 assert(r.Q[1]<I(6241,1600)[0],"below-radius row "+row.path);
 }
 for(const row of data.rows){
 const b=parameterBox(row.path,scaleBits),raw=oppositeBoxes(b);
 for(let i=0;i<3;i++)for(let j=0;j<2;j++)assert(b[i][j]===(BigInt(row.b[i][j])<<shift),"parameter box");
 const cores=row.cores.map(k=>k.map(a=>a.map(v=>BigInt(v)<<shift))),rad=BigInt(row.rad)<<shift;
 for(let i=0;i<3;i++)for(let d=0;d<2;d++)assert(raw.cores[i][d][0]>=cores[i][d][0]&&raw.cores[i][d][1]<=cores[i][d][1],"core bounds "+row.path);
 assert(raw.rad<=rad,"center radius "+row.path);assert(row.slots.length===6,"six slots");
 const slots=row.slots.map(p=>p.map(n=>I(n,1000))),S2=S*S;
 partition(row.leaves);
 for(const [path,rule,k]of row.leaves){
 const r=BigInt(row.rad),cell=boxAt(path,[[-r,r],[-r,r]]).map(a=>a.map(v=>v<<shift));let ok=false;
 if(rule==="outside"){let norm=0n;for(const a of cell){const d=a[0]>0n?a[0]:a[1]<0n?-a[1]:0n;norm+=d*d;}ok=norm>rad*rad;}
 if(rule==="square")ok=k>=0&&k<3&&4n*coreDistance(cell,cores[k],k===2)<S2;
 if(rule==="slot")ok=k>=0&&k<6&&1000000n*diskDistance(cell,slots[k])<249001n*S2;
 assert(ok,"center leaf "+row.path+"/"+path+" "+rule);cells++;maxDepth=Math.max(maxDepth,path.length);
 }
 }
 return{parameterCapacityRows:data.rows.length,excludedParameterRows:data.excluded.length,centerLeaves:cells,maxCenterDepth:maxDepth,maxParameterDepth:Math.max(...[...data.rows,...data.excluded].map(r=>r.path.length))};
}

function verifyKIdentity(){

const gcd=(a,b)=>{a=a<0n?-a:a;b=b<0n?-b:b;while(b){const t=a%b;a=b;b=t;}return a;};
const Q=(a,b=0n,d=1n)=>{a=BigInt(a);b=BigInt(b);d=BigInt(d);if(!d)throw Error("zero denominator");if(d<0n){a=-a;b=-b;d=-d;}const g=gcd(gcd(a,b),d);return[a/g,b/g,d/g];};
const I=(n,d=1)=>Q(n,0,d);
const add=(x,y)=>Q(x[0]*y[2]+y[0]*x[2],x[1]*y[2]+y[1]*x[2],x[2]*y[2]);
const neg=x=>[-x[0],-x[1],x[2]],sub=(x,y)=>add(x,neg(y));
const mul=(x,y)=>Q(x[0]*y[0]+2n*x[1]*y[1],x[0]*y[1]+x[1]*y[0],x[2]*y[2]);
const div=(x,y)=>mul(x,Q(y[2]*y[0],-y[2]*y[1],y[0]*y[0]-2n*y[1]*y[1]));
const sq=x=>mul(x,x);
const Z=I(0),O=I(1),TWO=I(2),HALF=I(1,2),root2=Q(0,1),K=add(TWO,root2);

const k2=sq(K),v=add(sub(sq(k2),mul(I(12),k2)),I(4));assert(v[0]===0n&&v[1]===0n,"K quartic identity");
}

const certificate=JSON.parse(readFileSync(new URL("./opposite_diagonal_capacity_certificate.json",import.meta.url),"utf8"));
verifyKIdentity();
console.log(JSON.stringify(run(certificate,60),null,2));
