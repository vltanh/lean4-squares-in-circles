// Separate 60-bit arithmetic backend; shared logical certificate predicates.
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
function doubleBoxes(box){
 const [Q,t,tau]=box;
 if(t[0]>=root2[1]-S)return {excluded:"order"};
 const R=sqrtInterval(Q),den=add(O,sq(t)),c=div(sub(O,sq(t)),den);
 const sinAt=v=>div(mul(TWO,[v,v]),add(O,sq([v,v])));
 const s=[sinAt(t[0])[0],sinAt(t[1])[1]],X=mul(R,c),Y=mul(R,s);
 const circleAt=(v,z)=>sub([v,v],sq(sub(K,mul(sqrtInterval([v,v]),[z,z]))));
 // Q-(K-z*sqrt(Q))^2 increases in both Q and z on this domain.
 const ar=[circleAt(Q[0],c[0])[0],circleAt(Q[1],c[1])[1]],br=[circleAt(Q[0],s[0])[0],circleAt(Q[1],s[1])[1]],quarter=I(1,4);
 if(ar[1]<quarter[0]||br[1]<quarter[0])return {excluded:"circle"};
 const a=sqrtInterval([ar[0]<quarter[0]?quarter[0]:ar[0],ar[1]]),b=sqrtInterval([br[0]<quarter[0]?quarter[0]:br[0],br[1]]);
 const ratio=div(sub(O,sq(t)),mul(TWO,t)),L=sub(Y,div(s,c)),UB=div(b,ratio),U=[a[0]<UB[0]?a[0]:UB[0],a[1]<UB[1]?a[1]:UB[1]];
 if(U[1]<=L[0])return {excluded:"height"};
 const hs=tau.map(v=>add(mul(sub(O,[v,v]),L),mul([v,v],U))),h=[hs[0][0]<hs[1][0]?hs[0][0]:hs[1][0],hs[0][1]>hs[1][1]?hs[0][1]:hs[1][1]],h2=mul(ratio,h);
 const cores=[[sub(X,HALF),sub(Y,HALF)],[add(sub(X,K),HALF),sub(a,HALF)],[sub(b,HALF),add(sub(Y,K),HALF)],[sub(X,mul(K,HALF)),h],[h2,sub(Y,mul(K,HALF))]];
 const rad=sqrtInterval(sub(Q,quarter))[1]-S/2n;
 return {cores,rad};
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
 const b=[[68620520689500n,79164837199872n],[5864062014805n,7330077518507n],[0n,17592186044416n]];
 for(const bit of path){
 const score=[2n*(b[0][1]-b[0][0]),16n*(b[1][1]-b[1][0]),b[2][1]-b[2][0]];let k=0;for(let i=1;i<3;i++)if(score[i]>score[k])k=i;
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
 assert(data.scale_bits===44,"data scale");assert(root2[0]*root2[0]<2n*S*S&&root2[1]*root2[1]>2n*S*S,"sqrt2");
 partition([...data.rows,...data.excluded].map(r=>[r.path]));
 const initial=parameterBox("",scaleBits);
 assert(initial[0][0]<=I(6241,1600)[0]&&initial[0][1]>=I(9,2)[1],"Q initial interval");
 assert(initial[1][0]<=I(1,3)[0]&&initial[1][1]>=I(5,12)[1],"angle initial interval");
 const shift=BigInt(scaleBits-44);let cells=0,maxDepth=0;const excludedCounts={};
 for(const row of data.excluded){const r=doubleBoxes(parameterBox(row.path,scaleBits));assert(Boolean(r.excluded),"excluded parameter row "+row.path);excludedCounts[row.rule]=(excludedCounts[row.rule]||0)+1;}
 for(const row of data.rows){
 const b=parameterBox(row.path,scaleBits),raw=doubleBoxes(b);assert(!raw.excluded,"retained row unexpectedly excluded");
 for(let i=0;i<3;i++)for(let j=0;j<2;j++)assert(b[i][j]===(BigInt(row.b[i][j])<<shift),"parameter bounds");
 assert(row.cores.length===5&&row.slots.length===4,"five cores and four disks");
 const cores=row.cores.map(k=>k.map(a=>a.map(v=>BigInt(v)<<shift))),rad=BigInt(row.rad)<<shift;
 for(let i=0;i<5;i++)for(let d=0;d<2;d++)assert(raw.cores[i][d][0]>=cores[i][d][0]&&raw.cores[i][d][1]<=cores[i][d][1],"core box "+row.path);
 assert(raw.rad<=rad,"radius bound");partition(row.leaves);
 const slots=row.slots.map(p=>p.map(n=>I(n,1000))),S2=S*S;
 for(const [path,rule,k]of row.leaves){
 const r=BigInt(row.rad),cell=boxAt(path,[[-r,r],[-r,r]]).map(a=>a.map(v=>v<<shift));let ok=false;
 if(rule==="outside"){let norm=0n;for(const a of cell){const d=a[0]>0n?a[0]:a[1]<0n?-a[1]:0n;norm+=d*d;}ok=norm>rad*rad;}
 if(rule==="square")ok=k>=0&&k<5&&4n*coreDistance(cell,cores[k],k>=3)<S2;
 if(rule==="slot")ok=k>=0&&k<4&&1000000n*diskDistance(cell,slots[k])<249001n*S2;
 assert(ok,"center leaf "+row.path+"/"+path+" "+rule);cells++;maxDepth=Math.max(maxDepth,path.length);
 }
 }
 return{parameterCapacityRows:data.rows.length,excludedParameterRows:data.excluded.length,excludedCounts,centerLeaves:cells,maxCenterDepth:maxDepth,maxParameterDepth:Math.max(...[...data.rows,...data.excluded].map(r=>r.path.length))};
}

const certificate=JSON.parse(readFileSync(new URL("./loaded_double_diagonal_fork_certificate.json",import.meta.url),"utf8"));
console.log(JSON.stringify(run(certificate,60),null,2));
