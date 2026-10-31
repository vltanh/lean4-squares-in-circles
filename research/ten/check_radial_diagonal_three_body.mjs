// Exact uniform radial-D three-body capacity checker; 44-bit backend.
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
function isqrt(n){if(n<0n)throw Error("negative sqrt");if(n<2n)return n;let v=1n<<BigInt((n.toString(2).length+1)>>1);for(;;){const w=(v+n/v)>>1n;if(w>=v)return v;v=w;}}
function sqrtInterval(a){if(a[0]<0n)throw Error("sqrt domain");const lo=isqrt(a[0]*S),hi=isqrt(a[1]*S);return[lo,hi*hi===a[1]*S?hi:hi+1n];}

function coreBoxes(u,tau){
 const H=sqrtInterval(add(mul(mul(TWO,K),sub(u,I(2))),I(9,4)));
 const h=add(I(-1,2),mul(tau,sub(I(3,2),H)));
 return [[[sub(HALF,u)[0],sub(HALF,u)[1]],Z],
 [sub(sub(K,u),HALF),sub(HALF,H)],
 [sub(mul(K,HALF),u),h]];
}


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

function coreDistance(cell,k,rotated){
 let a=cell.map((v,i)=>[v[0]-k[i][1],v[1]-k[i][0]]);
 if(rotated){const f=mul(root2,HALF),p=mul(add(a[0],a[1]),f),q=mul(sub(a[1],a[0]),f);a=[p,q];}
 let n=0n;for(const v of a){let d=-v[0]>v[1]?-v[0]:v[1];d=d>S/2n?d-S/2n:0n;n+=d*d;}return n;
}
function diskDistance(cell,point){let n=0n;for(let i=0;i<2;i++){const a=cell[i][0]-point[i][1],b=cell[i][1]-point[i][0];n+=(-a>b?-a:b)**2n;}return n;}
function parameterBox(path,scaleBits){
 // Paths use the fixed 44-bit partition; lift exactly in the second backend.
 const original=1n<<44n,from=33425153484390n; // floor(19*2^44/10)
 let b=[[from,2n*original],[0n,original]];
 for(const bit of path){const d=10n*(b[0][1]-b[0][0])>=b[1][1]-b[1][0]?0:1,m=(b[d][0]+b[d][1])/2n;if(bit==="0")b[d][1]=m;else b[d][0]=m;}
 const shift=BigInt(scaleBits-44);return b.map(a=>a.map(v=>v<<shift));
}
function run(data,scaleBits=44){
 assert(data.scale_bits===44,"data scale");
 assert(root2[0]*root2[0]<2n*S*S&&root2[1]*root2[1]>2n*S*S,"sqrt2");
 const rows=[...data.rows.map(r=>[r.path]),...data.excluded.map(r=>[r.path])];partition(rows);
 // R>=79/40 gives u^2>=5841/1600>(191/100)^2.
 assert(5841n*10000n>191n*191n*1600n,"lower radius");
 for(const r of data.excluded){const b=parameterBox(r.path,scaleBits);assert(b[0][1]<=I(191,100)[0],"excluded parameter box");}
 let count=0,maxDepth=0;
 for(const row of data.rows){
 const b=parameterBox(row.path,scaleBits),shift=BigInt(scaleBits-44);
 for(let d=0;d<2;d++)for(let j=0;j<2;j++)assert(b[d][j]===(BigInt((d?row.tau:row.u)[j])<<shift),"parameter bounds");
 const computed=coreBoxes(...b),cores=row.cores.map(k=>k.map(a=>a.map(v=>BigInt(v)<<shift)));
 for(let i=0;i<3;i++)for(let d=0;d<2;d++)assert(computed[i][d][0]>=cores[i][d][0]&&computed[i][d][1]<=cores[i][d][1],"uniform core region");
 const rad=b[0][1]-S/2n;assert(rad===(BigInt(row.rad)<<shift),"center domain");
 assert(row.slots.length===6,"six disks");
 const slots=row.slots.map(p=>p.map(n=>I(n,1000))),S2=S*S;
 partition(row.leaves);
 for(const [path,rule,k]of row.leaves){
 const rawRad=BigInt(row.rad),cell=boxAt(path,[[-rawRad,rawRad],[-rawRad,rawRad]]).map(a=>a.map(v=>v<<shift));let ok=false;
 if(rule==="outside"){let norm=0n;for(const a of cell){const d=a[0]>0n?a[0]:a[1]<0n?-a[1]:0n;norm+=d*d;}ok=norm>rad*rad;}
 if(rule==="square")ok=k>=0&&k<3&&4n*coreDistance(cell,cores[k],k===2)<S2;
 if(rule==="slot")ok=k>=0&&k<6&&1000000n*diskDistance(cell,slots[k])<249001n*S2;
 assert(ok,"capacity leaf "+row.path+"/"+path+" "+rule);count++;maxDepth=Math.max(maxDepth,path.length);
 }
 }
 return{parameterCapacityRows:data.rows.length,excludedParameterRows:data.excluded.length,capacityLeaves:count,maxCenterDepth:maxDepth,maxParameterDepth:Math.max(...rows.map(a=>a[0].length))};
}

const certificate=JSON.parse(readFileSync(new URL("./radial_diagonal_three_body_certificate.json",import.meta.url),"utf8"));
console.log(JSON.stringify(run(certificate,44),null,2));
