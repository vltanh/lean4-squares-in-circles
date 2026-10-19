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
const Q=rr("9789/2500"),R=root(Q),d=isub(root(Q.div(2)),".5"),a0=isub(root(Q.sub(".25")),".5");
function lab(i,s){return labels[i].O[s>0?"p":"n"].map(x=>rr(x).div(100000));}
function norm(edge,ss,st,rev){let[c,p,q]=lab(edge,ss),[C,P,t]=lab(edge+1,st);if(rev)[c,C,p,P,q,t]=[C.neg(),c.neg(),P.neg(),p.neg(),t,q];return{edge,ss,st,rev,c:c.sub(C),p,q,P,t};}
function constant(z){return ia(z.c, isub(im(z.p,z.p.cmp(0)>=0?d:a0),im(z.P,z.P.cmp(0)>=0?a0:d)));}
gt("pi/4<.786 gives phi>-.026",isub(".786",idiv(PI,4)),0);
gt("sin and cosine difference .7",isub(cos(".7"),sin(".7")),0);
lt("same-sign forbidden primary positive half",isub(a0,im(d,cos(".7"))),1);
lt("same-sign forbidden primary negative sliver",ia(isub(a0,im(d,cos(".026"))),im(d,sin(".026"))),1);
gt("zero-primary lower coefficient",rr("1.399").mul(".764").sub(".915"),0);
const f=rr(1).sub(rr(".764").pow(2)).add(rr(".767").mul(rr(".915").mul(".764").sub("1.399")));
lt("zero-primary monotonic numerator",f,0);lt("zero-primary numerator derivative",rr(".767").mul(".915").sub(rr(2).mul(".764")),0);
const z0=ia(".5",idiv(isub(im("1.399",cos(".7")),".915"),sin(".7")));
gt("opposite-primary common lower",ia(rr(".7").sub(".264"),im(".767",z0)),1);
for(const edge of[0,1,3]){
 const z=norm(edge,1,-1,false);gt("opposite edge "+edge+" constant",constant(z),"-.264");
 gt("opposite edge "+edge+" source transverse",z.q,".767");gt("opposite edge "+edge+" target transverse",z.t,".767");
 rows.push({edge,signs:"+-",axes:[2,4],proved_lower:"1"});
}
const same=[norm(0,1,1,false),norm(1,-1,-1,true),norm(3,1,1,false),norm(3,-1,-1,true)];
const amin=ia(".5",ia(im(ia(d,".5"),cos(".7")),im(isub(".5",d),sin(".7"))));
gt("favorable-primary target A lower",amin,"1.31");
const bmax=isub(root(isub(Q,ipow(ia(amin,".5"),2))),".5");
lt("favorable-primary target B upper",bmax,".3");
const ps=[];
for(const z of same){
 gt("same-sign primary q lower "+z.edge+z.rev,z.q,".767");
 const lower=ia(constant(z),isub(ia(".7",im(z.q,z0)),z.t.mul(".3")));
 gt("same-sign favorable primary "+z.edge+z.rev,lower,".89765");
 ps.push({edge:z.edge,signs:z.ss>0?"++":"--",axis:z.rev?4:2,lower:dec(lower[0],12)});
 rows.push(ps.at(-1));
 rows.push({edge:z.edge,signs:z.ss>0?"++":"--",axis:z.rev?2:4,conclusion:"impossible"});
}
lt("unfavorable secondary forward cap at .3",im(isub(d,".5"),ia(sin(".3"),cos(".3"))),".5");
const sec=[norm(0,1,1,true),norm(1,-1,-1,false),norm(3,1,1,true),norm(3,-1,-1,false)];
function fc(z,x){const t=ii(x),s=sin(t),c=cos(t),N=root(ia(z.P.pow(2).add(z.t.pow(2)).add(4),im(4,isub(im(z.P,s),im(z.t,c)))));return isub(ia(ia(t,z.c.add(rr(2).add(z.P).sub(z.t).div(2))),ia(im(z.p,a0),im(2,ia(s,c)))),im(R,N));}
gt("secondary norm concavity",rr(2).sub(rr(2).mul("3.31").div(4)),0);
for(const z of sec){
 if(z.p.cmp(0)>0)throw Error("source axial primary sign");gt("source axial transverse sign "+z.edge+z.rev,rr(2).sub(z.q),0);
 lt("secondary target vector length "+z.edge+z.rev,root(z.P.pow(2).add(z.t.pow(2))),"1.31");
 const exceptional=z.edge===3&&z.rev;
 if(exceptional){
  gt("diagonal target ordering at .5",isub(im(2,isub(cos(".5"),sin(".5"))),z.P.add(z.t)),0);
  gt("diagonal source X negative at .3",ia(z.P,im(2,sin(".3"))),0);
  gt("diagonal target Y negative at .5",isub(im(2,cos(".5")),z.t),0);
  const x=rr(".3"),sum=ia(sin(x),cos(x));
  const v=ia(ia(x,z.c),ia(im(z.p,a0),ia(ia(1,sum),im(d,isub(z.t.sub(z.P),im(2,sum))))));
  gt("exceptional diagonal lower",v,"1.09");gt("exceptional diagonal derivative",isub(1,im(2,isub(d,".5"))),0);
  for(const x of[".5",".7"])gt("exceptional circle endpoint "+x,fc(z,x),"1.19");
 }else for(const x of[".3",".7"])gt("secondary circle endpoint "+z.edge+z.rev+" "+x,fc(z,x),"1.03");
 rows.push({edge:z.edge,signs:z.ss>0?"++":"--",axis:z.rev?3:1,proved_lower:exceptional?"1.09":"1.03"});
}
const branches=rows.reduce((n,r)=>n+(r.axes?r.axes.length:1),0);
if(branches!==18)throw Error("branch count");
const report={status:"PASS",scope:"All14 outer/outer zero-quarter primary branches and all4 same-sign secondary branches facing the wrong transverse direction; no inference for remaining10 zero-quarter secondary branches",fixed_comparisons:checks.length,raw_branches:branches,primary_rows:ps,rows,checks};
if(typeof console!=="undefined")console.log(JSON.stringify(report,null,2));

