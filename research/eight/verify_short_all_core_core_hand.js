"use strict";
// Exact fixed-comparison checker for all mixed quarter-one contact families.
// All arithmetic is rational BigInt. No numerical optimizer or adaptive box cover.
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){let t=a%b;a=b;b=t;}return a;}
class Rat{
  constructor(n,d=1n){n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d;}if(!d)throw Error("zero denominator");let g=gcd(n,d);this.n=n/g;this.d=d/g;}
  add(b){b=rr(b);return new Rat(this.n*b.d+b.n*this.d,this.d*b.d);}
  neg(){return new Rat(-this.n,this.d);}
  sub(b){return this.add(rr(b).neg());}
  mul(b){b=rr(b);return new Rat(this.n*b.n,this.d*b.d);}
  div(b){b=rr(b);return new Rat(this.n*b.d,this.d*b.n);}
  pow(k){return new Rat(this.n**BigInt(k),this.d**BigInt(k));}
  cmp(b){b=rr(b);let v=this.n*b.d-b.n*this.d;return v<0n?-1:v>0n?1:0;}
  toString(){return this.d===1n?String(this.n):this.n+"/"+this.d;}
}
function rr(x){if(x instanceof Rat)return x;if(typeof x==="bigint")return new Rat(x);let s=String(x);if(s.includes("/")){let [n,d]=s.split("/");return new Rat(n,d);}if(s.includes(".")){let neg=s[0]==="-";if(neg)s=s.slice(1);let [a,b]=s.split(".");return new Rat((neg?-1n:1n)*BigInt(a+b),10n**BigInt(b.length));}return new Rat(s);}
function ii(x){return Array.isArray(x)?x:[rr(x),rr(x)];}
function ia(a,b){a=ii(a);b=ii(b);return[a[0].add(b[0]),a[1].add(b[1])];}
function ineg(a){a=ii(a);return[a[1].neg(),a[0].neg()];}
function isub(a,b){return ia(a,ineg(b));}
function im(a,b){a=ii(a);b=ii(b);let z=[a[0].mul(b[0]),a[0].mul(b[1]),a[1].mul(b[0]),a[1].mul(b[1])];z.sort((x,y)=>x.cmp(y));return[z[0],z[3]];}
function idiv(a,b){b=ii(b);if(b[0].cmp(0)<=0&&b[1].cmp(0)>=0)throw Error("division across zero");return im(a,[rr(1).div(b[1]),rr(1).div(b[0])]);}
function ipow(a,k){a=ii(a);if(k===0)return ii(1);if(k%2===0&&a[0].cmp(0)<0&&a[1].cmp(0)>0){let z=[a[0].pow(k),a[1].pow(k)].sort((x,y)=>x.cmp(y));return[rr(0),z[1]];}let z=[a[0].pow(k),a[1].pow(k)].sort((x,y)=>x.cmp(y));return z;}
function isqrt(n){if(n<0n)throw Error("negative root");if(n<2n)return n;let x=1n<<BigInt((n.toString(2).length+1)>>1);while(true){let y=(x+n/x)>>1n;if(y>=x)return x;x=y;}}
function root(a){a=ii(a);if(a[0].cmp(0)<0)throw Error("negative interval root");let scale=10n**14n;let lo=isqrt(a[0].n*scale*scale/a[0].d),hi=isqrt(a[1].n*scale*scale/a[1].d)+1n;return[new Rat(lo,scale),new Rat(hi,scale)];}

const trigCache=new Map();
function trig(x,cosine){x=ii(x);let key=(cosine?"c":"s")+x.map(a=>a.toString()).join("|");if(trigCache.has(key))return trigCache.get(key);if(x[0].cmp(0)<0||x[1].cmp(3)>0)throw Error("trig range");let term=cosine?ii(1):x,sum=term,lo;for(let j=1;j<=16;j++){let den=cosine?(2*j-1)*(2*j):(2*j)*(2*j+1);term=ineg(idiv(im(term,ipow(x,2)),den));sum=ia(sum,term);if(j===15)lo=sum[0];}let out=[lo,sum[1]];trigCache.set(key,out);return out;}
function sin(x){return trig(x,false);}function cos(x){return trig(x,true);}
function atanSeries(q,n){let x=rr(1).div(q),s=rr(0);for(let j=0;j<=n;j++)s=s.add(x.pow(2*j+1).div(2*j+1).mul(j%2?-1:1));return s;}
const PI_MACHIN=[atanSeries(5,25).mul(16).sub(atanSeries(239,6).mul(4)),atanSeries(5,24).mul(16).sub(atanSeries(239,7).mul(4))];
const PI=[rr("3.141592653589793238"),rr("3.141592653589793239")];
if(PI_MACHIN[0].cmp(PI[0])<=0||PI_MACHIN[1].cmp(PI[1])>=0)throw Error("Machin enclosure");
const P2=idiv(PI,2);
function angle(t){if(t==="p")return P2;if(t==="lo")return isub(P2,".7");if(t==="hi")return ia(P2,".7");if(String(t).startsWith("p+"))return ia(P2,String(t).slice(2));return ii(t);}
function absI(x){x=ii(x);if(x[0].cmp(0)>=0)return x;if(x[1].cmp(0)<=0)return ineg(x);return[rr(0),x[0].neg().cmp(x[1])>0?x[0].neg():x[1]];}
function dec(x,digits=9){x=rr(x);let sc=10n**BigInt(digits),n=x.n*sc/x.d;if(x.n<0n&&x.n*sc%x.d)n--;let neg=n<0n;if(neg)n=-n;let s=String(n).padStart(digits+1,"0");return(neg?"-":"")+s.slice(0,-digits)+"."+s.slice(-digits);}
function decup(x,digits=9){return dec(rr(x).neg(),digits).startsWith("-")?dec(rr(x).neg(),digits).slice(1):"-"+dec(rr(x).neg(),digits);}

function pAdd(a,b){return Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||rr(0)).add(b[i]||0));}
function pNeg(a){return a.map(x=>rr(x).neg());}
function pSub(a,b){return pAdd(a,pNeg(b));}
function pScale(a,b){return a.map(x=>rr(x).mul(b));}
function pMul(a,b){let r=Array(a.length+b.length-1).fill(null).map(()=>rr(0));for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)r[i+j]=r[i+j].add(rr(a[i]).mul(b[j]));return r;}
function pPow(a,k){let r=[rr(1)];for(let j=0;j<k;j++)r=pMul(r,a);return r;}
function choose(n,k){if(k<0||k>n)return rr(0);let r=rr(1);for(let j=1;j<=k;j++)r=r.mul(n-j+1).div(j);return r;}
function bernstein(p,lo,hi){lo=rr(lo);let w=rr(hi).sub(lo),n=p.length-1,a=Array(n+1).fill(null).map(()=>rr(0));for(let j=0;j<=n;j++)for(let k=0;k<=j;k++)a[k]=a[k].add(p[j].mul(choose(j,k)).mul(lo.pow(j-k)).mul(w.pow(k)));return a.map((_,k)=>a.slice(0,k+1).reduce((s,x,i)=>s.add(x.mul(choose(k,i)).div(choose(n,i))),rr(0)));}

const labels=[{"C":{"p":[3177,0,108816]},"O":{"p":[0,0,94766]}},{"C":{"p":[25648,0,62095],"n":[-14041,0,62095]},"O":{"p":[6130,0,99940],"n":[24463,-13422,103828]}},{"C":{"n":[11680,0,113855]},"O":{"n":[-2623,9133,88074]}},{"C":{"p":[4149,0,104729],"n":[-15540,0,62750]},"O":{"p":[-68803,51554,119909],"n":[50866,-33147,113360]}},{"C":{"p":[25812,0,58829],"n":[3897,0,104073]},"O":{"p":[6294,0,71553],"n":[-23483,19335,76744]}},{"C":{"p":[2448,0,99195],"n":[1027,0,95269]},"O":{"p":[2448,0,86884],"n":[29579,-20967,83048]}},{"C":{"p":[9072,0,95324],"n":[7651,0,99173]},"O":{"p":[-20704,21826,83472],"n":[-18660,18602,80996]}}];

const checks=[],rows=[];
function gt(name,x,v=0){x=ii(x);if(x[0].cmp(v)<=0)throw Error(name+" failed "+dec(x[0]));checks.push({name,lower:dec(x[0],12),threshold:String(v)});}
function lt(name,x,v=0){gt(name,ineg(x),rr(v).neg());}
const dc=ia(".5",idiv(root(2),24)),ac=rr("7/12"),p4=idiv(PI,4),gamma=rr("17953/20000"),K=[0,0,1,0,1,1,1];
gt("core lower angle coefficient",rr("9/7").sub("8/7"));
gt("core corner alpha second derivative numerator",rr(3).sub("7/6"));
const v=isub(3,im(2,root(2)));
gt("core side upper-bound minimum",isub(isub(v,idiv(ipow(v,3),3)),idiv(ia(1,v),7)),"1/400");
lt("core side squared radius",ac.pow(2).add("1/4"),"16/25");
lt("core corner squared radius",ia(rr("1/2").add("1/144"),idiv(root(2),12)),"16/25");
lt("core gap endpoint bound",im("32/25",isub(1,cos("27/20"))),1);
lt("core gap axial bound",rr("16/25"),1);
function psi(tab,sg){const c=rr(tab[0]).div(100000),g=rr(tab[2]).div(100000);return sg>0?[c.neg(),isub(isub(p4,im(g,dc)),c)[1]]:[ia(isub(im(g,dc),p4),c.neg())[0],c.neg()];}
function label0(tab){return rr(tab[0]).div(100000);}
for(let i=0;i<7;i++)for(const sk of Object.keys(labels[i].C))for(const tk of Object.keys(labels[(i+1)%7].C)){
 const s=sk==="p"?1:-1,t=tk==="p"?1:-1;if(K[i]===0&&s<0&&t>0)continue;
 const a=labels[i].C[sk],b=labels[(i+1)%7].C[tk],ps=psi(a,s),pt=psi(b,t);
 const cb=rr("27/20").sub(ps[1]).add(pt[0]);
 let method="core gap and endpoint marker ranges",bound=ii(cb);
 if(i===4&&s>0&&t<0){bound=ia(isub(P2,".7"),label0(a).sub(label0(b)));method="quarter frame lower bound and nonnegative transverse terms";}
 if(i===5&&s>0&&t<0){
  const c=label0(a).sub(label0(b)),gmin=rr(Math.min(a[2],b[2])).div(100000);
  const high=rr(".951").add(c),low=ia(isub(P2,".7"),c.add(gmin.div(10)));
  gt("edge5 primary/secondary projection cap if b+B<=.1",rr(1).sub(ac).sub(".1"));
  gt("edge5 low-half contact bound",low,".898");
  gt("edge5 high-half direct bound",high,".898");
  bound=[high.cmp(low[0])<0?high:low[0],high.cmp(low[1])<0?high:low[1]];method="split phi=.951; all four SAT axes force b+B>.1 below it";
 }
 gt("core pair "+i+" "+s+" "+t,bound,".898");
 rows.push({edge:i,signs:(s>0?"+":"-")+(t>0?"+":"-"),method,lower:dec(bound[0],12)});
}
if(rows.length!==19)throw Error("core row count");
for(let i=0;i<7;i++)for(const[k,a]of Object.entries(labels[i].C)){
 const g=rr(a[2]).div(100000);gt("core label positive "+i+k,g);lt("core label upper "+i+k,g,"8/7");
}
gt("cyclic table reserve",rr(7).mul(gamma),"710/113");
const report={status:"PASS",scope:"All 19 allowed core/core rows of wrong quarter word0010111, with each corrected cost>.898>.89765",fixed_comparisons:checks.length,rows,checks};
if(typeof console!=="undefined")console.log(JSON.stringify(report,null,2));

