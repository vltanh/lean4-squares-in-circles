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

// Every row below is fixed. This checker performs only rational coefficient tests.
const fs=require('fs');
const labels=JSON.parse(fs.readFileSync(__dirname+'/short_hand_labels.json','utf8'));
const input=JSON.parse(fs.readFileSync(process.argv[2]||__dirname+'/short_quarter_scalar_hand_table.json','utf8'));
const Q=rr('9789/2500'),R=root(Q),d=isub(root(Q.div(2)),'.5'),a0=isub(root(Q.sub('.25')),'.5'),r0=idiv('.5',ia(a0,'.5'));
function norm(o){let[e,ss,st,ax]=o,[c,p,q]=labels[e].O[ss>0?'p':'n'].map(x=>rr(x).div(100000)),[C,P,t]=labels[(e+1)%7].O[st>0?'p':'n'].map(x=>rr(x).div(100000));if(ax===2||ax===3)[c,C,p,P,q,t,ss,st]=[C.neg(),c.neg(),P.neg(),p.neg(),t,q,-st,-ss];return{e,ss,st,axis:ax===1||ax===3?1:4,c:c.sub(C),p,q,P,t};}
function add(a,b){return Array.from({length:Math.max(a.length,b.length)},(_,j)=>ia(a[j]||0,b[j]||0));}
function scale(a,b){return a.map(x=>im(x,b));}
function mul(a,b){let o=Array(a.length+b.length-1).fill(null).map(()=>ii(0));for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)o[i+j]=ia(o[i+j],im(a[i],b[j]));return o;}
function power(a,k){let o=[ii(1)];for(let j=0;j<k;j++)o=mul(o,a);return o;}
function con(a){return[ii(a)];}
function neg(a){return scale(a,-1);}
function sub(a,b){return add(a,neg(b));}
function low(a){return a.map(x=>x[0]);}
function derivative(a){return a.slice(1).map((x,i)=>x.mul(i+1));}
function value(a,x){return a.reduceRight((s,t)=>s.mul(x).add(t),rr(0));}
function minimum(a){return a.reduce((s,x)=>s.cmp(x)<0?s:x);}
function maximum(a){return a.reduce((s,x)=>s.cmp(x)>0?s:x);}
function bounds(a,l,h){return bernstein(a,l,h);}
function prove(poly,lo,hi){
 const a=low(poly),b=bernstein(a,lo,hi),m=minimum(b);
 if(m.cmp(0)<0)throw Error('negative Bernstein coefficient on '+lo+' '+hi+': '+dec(m,14));
 return {degree:a.length-1,method:'positive Bernstein coefficients',reserve:dec(m,14),coefficient_lower:b.map(x=>dec(x,14))};
}

const sinP=Array(10).fill(null).map(()=>ii(0)),cosP=Array(11).fill(null).map(()=>ii(0));
function fact(n){let v=1n;for(let j=2;j<=n;j++)v*=BigInt(j);return v;}
for(let j=0;j<=4;j++){sinP[2*j+1]=ii(new Rat(j%2?-1n:1n,fact(2*j+1)));cosP[2*j]=ii(new Rat(j%2?-1n:1n,fact(2*j)));}
// S7 <= sin <= S9, C10 <= cos <= C8, throughout 0<=u<=.7.
sinP[9]=[rr(0),rr(1).div(fact(9))];cosP[10]=[rr(-1).div(fact(10)),rr(0)];
function csource(z,l){const X=z.axis===4?z.p.sub(l):z.p,Y=z.axis===1?z.q.sub(l).mul(z.ss):z.q.mul(z.ss);const ax=im(X,a0),di=im(X.add(Y),d);let mode,v;
 if(X.cmp(0)>=0){mode='concave endpoint minimum';v=[ax[0].cmp(di[0])<0?ax[0]:di[0],ax[1].cmp(di[1])<0?ax[1]:di[1]];}
 else if(isub(Y,im(X,r0))[0].cmp(0)>=0&&Y.sub(X).cmp(0)>=0){mode='axial monotone minimum';v=ax;}
 else if(isub(im(X,r0),Y)[0].cmp(0)>=0&&X.sub(Y).cmp(0)>=0){mode='diagonal monotone minimum';v=di;}
 else {mode='whole-circle lower bound';v=isub(im('-.5',X.add(Y)),im(R,root(X.pow(2).add(Y.pow(2)))));}
 return{mode,v,X,Y};
}
if(input.Q!=='9789/2500'||input.rows.length!==140)throw Error('wrong fixed table');
const results=[],failures=[];
for(let idx=0;idx<input.rows.length;idx++){
 const row=input.rows[idx],z=norm(row.original),l=rr(row.lam),sign=rr(row.r),lo=rr(row.lo),hi=rr(row.hi),src=csource(z,l);
 let X,Y,v;
 if(z.axis===1){X=sub(con(z.P.neg()),scale(cosP,l));Y=scale(sub(con(z.t.neg()),scale(sinP,l.mul(sign))),z.st);v=add(con(z.P.pow(2).add(z.t.pow(2)).add(l.pow(2))),add(scale(cosP,l.mul(z.P).mul(2)),scale(sinP,l.mul(z.t).mul(sign).mul(2))));}
 else {X=sub(con(z.P.neg()),scale(sinP,l.mul(sign)));Y=scale(sub(scale(cosP,l),con(z.t)),z.st);v=add(con(z.P.pow(2).add(z.t.pow(2)).add(l.pow(2))),add(scale(sinP,l.mul(z.P).mul(sign).mul(2)),scale(cosP,l.mul(z.t).mul(-2))));}
 let premise=[];if(row.mode==='axial')premise=[sub(Y,scale(X,r0)),sub(Y,X)];if(row.mode==='diagonal')premise=[sub(scale(X,r0),Y),sub(X,Y)];if(row.mode==='endpoints')premise=[X];
 const prem=premise.map(p=>prove(p,lo,hi));
 if(src.v[0].cmp(row.source_lower)<0)throw Error('invalid printed source bound');
 let base=add(con(ia(ia(P2,z.c),row.source_lower)),add([ii(0),ii(sign)],scale(add(con(1),add(cosP,sinP)),l.div(2))));
 const target=[];
 if(row.mode==='circle'){
  const t=rr(row.t);if(t.cmp(0)<=0)throw Error('norm t');let major=add(con(t.mul('5/16')),add(scale(v,rr(15).div(t.mul(16))),add(scale(power(v,2),rr(-5).div(t.pow(3).mul(16))),scale(power(v,3),rr(1).div(t.pow(5).mul(16))))));
  target.push(sub(scale(add(X,Y),'-.5'),scale(major,R)));
 }else if(row.mode==='axial')target.push(scale(X,a0));else if(row.mode==='diagonal')target.push(scale(add(X,Y),d));else target.push(scale(X,a0),scale(add(X,Y),d));
 let g=z.e===2?rr('.8975'):rr('17953/20000');const cost=target.map(p=>prove(sub(add(base,p),con(g)),lo,hi));
 if(cost.some(p=>rr(p.reserve).cmp(0)<=0))throw Error('non-strict cost polynomial');
 const out={index:idx,original:row.original,sign:row.r,interval:[String(row.lo),String(row.hi)],lambda:String(row.lam),target_mode:row.mode,norm_t:String(row.t),source_mode:src.mode,source_lower:dec(src.v[0],14),premises:prem,cost};results.push(out);
 if(prem.some(x=>x.method==='FAIL')||cost.some(x=>x.method==='FAIL'))failures.push(out);
}
console.log(JSON.stringify({status:failures.length?'INCOMPLETE':'PASS',scope:'Fixed one-variable affine SAT support envelopes; exact cubic radical majorants and Taylor/Bernstein polynomial identities; no state box cover',rows:results.length,failures:failures.map(x=>({index:x.index,original:x.original,sign:x.sign,interval:x.interval,premises:x.premises.filter(z=>z.method==='FAIL'),cost:x.cost.filter(z=>z.method==='FAIL')})),results},null,2));
