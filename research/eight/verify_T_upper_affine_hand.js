"use strict";
// Exact rational kernel, reused from the independently audited 0010111 scalar proof.
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
const integerBinomialCache=new Map();
function integerBinomial(n,k){const key=n+'|'+k;if(integerBinomialCache.has(key))return integerBinomialCache.get(key);let v=1n;for(let j=1;j<=k;j++)v=v*BigInt(n-j+1)/BigInt(j);integerBinomialCache.set(key,v);return v;}
function lcm(a,b){return a/gcd(a,b)*b;}
function bernstein(p,lo,hi){
 lo=rr(lo);hi=rr(hi);const n=p.length-1,D=p.reduce((d,x)=>lcm(d,x.d),1n),U=lcm(lo.d,hi.d);
 const L=lo.n*(U/lo.d),W=hi.n*(U/hi.d)-L;
 const lp=[1n],wp=[1n],up=[1n];for(let i=1;i<=n;i++){lp.push(lp[i-1]*L);wp.push(wp[i-1]*W);up.push(up[i-1]*U);}
 const a=Array(n+1).fill(0n);
 for(let i=0;i<=n;i++){const c=p[i].n*(D/p[i].d)*up[n-i];for(let j=0;j<=i;j++)a[j]+=c*integerBinomial(i,j)*lp[i-j]*wp[j];}
 let B=1n;for(let j=0;j<=n;j++)B=lcm(B,integerBinomial(n,j));
 const den=D*up[n]*B,out=[];
 for(let k=0;k<=n;k++){let num=0n;for(let j=0;j<=k;j++)num+=a[j]*integerBinomial(k,j)*(B/integerBinomial(n,j));out.push(new Rat(num,den));}
 return out;
}

// Fixed one-angle affine-support verifier. No domain subdivision is performed.
const fs=require('fs');
const input=JSON.parse(fs.readFileSync(process.argv[2],'utf8'));
const Q=rr(input.Q),R=root(Q),zero=rr(0);
const WORD=input.word||[0,1,0,1,0,1,1];
if(WORD.length!==7||WORD.some(k=>![0,1].includes(k))||WORD.reduce((a,b)=>a+b,0)!==4)throw Error('invalid declared quarter word');
function add(a,b){return Array.from({length:Math.max(a.length,b.length)},(_,j)=>ia(a[j]||0,b[j]||0));}
function scale(a,b){return a.map(x=>im(x,b));}
function mul(a,b){let o=Array(a.length+b.length-1).fill(null).map(()=>ii(0));for(let i=0;i<a.length;i++)for(let j=0;j<b.length;j++)o[i+j]=ia(o[i+j],im(a[i],b[j]));return o;}
function power(a,k){let o=[ii(1)];for(let j=0;j<k;j++)o=mul(o,a);return o;}
function con(a){return[ii(a)];}
function neg(a){return scale(a,-1);}
function sub(a,b){return add(a,neg(b));}
function low(a){return a.map(x=>x[0]);}
function minimum(a){return a.reduce((s,x)=>s.cmp(x)<0?s:x);}
function fact(n){let v=1n;for(let j=2;j<=n;j++)v*=BigInt(j);return v;}
const sinP=Array(10).fill(null).map(()=>ii(0)),cosP=Array(11).fill(null).map(()=>ii(0));
for(let j=0;j<=4;j++){sinP[2*j+1]=ii(new Rat(j%2?-1n:1n,fact(2*j+1)));cosP[2*j]=ii(new Rat(j%2?-1n:1n,fact(2*j)));}
sinP[9]=[zero,rr(1).div(fact(9))];cosP[10]=[rr(-1).div(fact(10)),zero];
function abAt(u,kind){
 u=rr(u);let a;
 if(kind==='C'&&u.cmp('6/7')<=0)a=ii('7/12');
 else{
  const v=u.add(1),den=u.pow(2).add(1).mul(2);
  const disc=kind==='O'?v.pow(2).add(u.pow(2).add(1).mul(Q.sub('.5')).mul(4)):v.pow(2).sub(u.pow(2).add(1).mul('71/36'));
  a=idiv(ia(root(disc),kind==='O'?v.neg():v),den);
 }
 return {a,b:im(a,u)};
}
function makeArc(s){
 if(!['C','O'].includes(s.kind)||![-1,1].includes(s.sign)||!Number.isInteger(s.role)||s.role<0||s.role>6)throw Error('invalid arc kind, sign or role');
 const lo=rr(s.lo),hi=rr(s.hi),A=abAt(lo,s.kind),B=abAt(hi,s.kind);
 if(lo.cmp(0)<0||hi.cmp(1)>0||lo.cmp(hi)>=0)throw Error('invalid arc endpoints');
 const side=s.kind==='C'&&hi.cmp('6/7')<=0;
 if(s.kind==='C'&&!side&&lo.cmp('6/7')<0)throw Error('unsplit core side/corner');
 const shift=rr(s.kind==='O'?'-.5':'.5'),radius=s.kind==='O'?R:ii('1/12');
 return {...s,lo,hi,...Object.fromEntries(['c','p','q'].map(k=>[k,rr(s[k])])),A,B,side,shift,radius,
   rlo:side?ii(0):idiv(isub(A.b,shift),isub(A.a,shift)),
   rhi:side?ii(0):idiv(isub(B.b,shift),isub(B.a,shift))};
}
const arcs=new Map(input.arcs.map(s=>[s.id,makeArc(s)]));
if(arcs.size!==input.arcs.length)throw Error('duplicate arc IDs');
function reverseArc(s){return {...s,sign:-s.sign,c:s.c.neg(),p:s.p.neg(),q:s.q.neg()};}
function sourceMinimum(s,X,Y){
 const vlo=ia(im(X,s.A.a),im(Y,s.A.b)),vhi=ia(im(X,s.B.a),im(Y,s.B.b));
 function bothmin(){return [vlo[0].cmp(vhi[0])<0?vlo[0]:vhi[0],vlo[1].cmp(vhi[1])<0?vlo[1]:vhi[1]];}
 if(s.side||X.cmp(0)>=0)return{mode:s.side?'side endpoint minimum':'concave endpoint minimum',v:bothmin()};
 const dl=isub(Y,im(X,s.rlo)),dh=isub(Y,im(X,s.rhi));
 if(dl[0].cmp(0)>=0&&dh[0].cmp(0)>=0)return{mode:'lower endpoint minimum',v:vlo};
 if(dl[1].cmp(0)<=0&&dh[1].cmp(0)<=0)return{mode:'upper endpoint minimum',v:vhi};
 return{mode:'whole-circle lower bound',v:isub(im(s.shift,X.add(Y)),im(s.radius,root(X.pow(2).add(Y.pow(2)))))};
}
function prove(poly,lo,hi,strict=false){
 const a=low(poly);while(a.length>1&&a[a.length-1].cmp(0)===0)a.pop();
 const b=bernstein(a,lo,hi),m=minimum(b);
 if(m.cmp(0)<0||(strict&&m.cmp(0)<=0))throw Error('negative/non-strict coefficient '+dec(m,14));
 return{degree:a.length-1,reserve:dec(m,14),coefficient_lower:b.map(x=>dec(x,14))};
}
function verifyRow(row){
 let s=arcs.get(row.source),t=arcs.get(row.target),axis=row.axis;
 if(!s||!t||![1,2,3,4].includes(axis)||s.role!==row.edge||t.role!==(row.edge+1)%7)throw Error('wrong row states');
 if(axis===2||axis===3){[s,t]=[reverseArc(t),reverseArc(s)];axis=axis===2?4:1;}
 const l=rr(row.lambda),r=rr(row.r),lo=rr(row.lo),hi=rr(row.hi),k=rr(row.k);
 if(l.cmp(0)<0||lo.cmp(0)<0||hi.cmp('.7')>0||lo.cmp(hi)>0||row.k!==WORD[row.edge]||![-1,1].includes(row.r))throw Error('invalid row domain');
 const Sin=row.k===0?scale(sinP,r):cosP,Cos=row.k===0?cosP:scale(sinP,r.neg());
 const Xs=axis===4?s.p.sub(l):s.p,Ys=axis===1?s.q.sub(l.mul(s.sign)):s.q;
 const src=sourceMinimum(s,Xs,Ys);
 let X,Y,V;
 if(axis===1){
  X=sub(con(t.p.neg()),scale(Sin,l));Y=add(con(t.q.neg()),scale(Cos,l.mul(t.sign)));
  V=add(con(t.p.pow(2).add(t.q.pow(2)).add(l.pow(2))),add(scale(Sin,l.mul(t.p).mul(2)),scale(Cos,l.mul(t.q).mul(t.sign).mul(-2))));
 }else{
  X=add(con(t.p.neg()),scale(Cos,l));Y=add(con(t.q.neg()),scale(Sin,l.mul(t.sign)));
  V=add(con(t.p.pow(2).add(t.q.pow(2)).add(l.pow(2))),add(scale(Cos,l.mul(t.p).mul(-2)),scale(Sin,l.mul(t.q).mul(t.sign).mul(-2))));
 }
 const premises=[];
 if(row.mode==='lower')premises.push(sub(Y,scale(X,t.rlo)),sub(Y,scale(X,t.rhi)));
 else if(row.mode==='upper')premises.push(sub(scale(X,t.rlo),Y),sub(scale(X,t.rhi),Y));
 else if(row.mode==='endpoints'&&!t.side)premises.push(X);
 else if(row.mode==='circle'&&t.side)throw Error('circle support used on a core side');
 else if(!['lower','upper','endpoints','circle'].includes(row.mode))throw Error('unknown target mode');
 const pr=premises.map(p=>prove(p,lo,hi));
 let base=add(con(ia(im(P2,k),s.c.sub(t.c))),add([ii(0),ii(r)],scale(add(con(1),add(cosP,sinP)),l.div(2))));
 base=add(base,con(src.v));
 const target=[];
 if(row.mode==='lower'||row.mode==='endpoints')target.push(add(scale(X,t.A.a),scale(Y,t.A.b)));
 if(row.mode==='upper'||row.mode==='endpoints')target.push(add(scale(X,t.B.a),scale(Y,t.B.b)));
 if(row.mode==='circle'){
  const h=rr(row.h);if(h.cmp(0)<=0)throw Error('nonpositive radical majorant parameter');
  const major=add(con(h.mul('5/16')),add(scale(V,rr(15).div(h.mul(16))),add(scale(power(V,2),rr(-5).div(h.pow(3).mul(16))),scale(power(V,3),rr(1).div(h.pow(5).mul(16))))));
  target.push(sub(scale(add(X,Y),t.shift),scale(major,t.radius)));
 }
 const beta=rr(input.beta?.[row.edge]||0);
 if(beta.cmp(0)<0)throw Error('negative frame charge');
 base=sub(base,scale(sub(add(sinP,cosP),con(1)),beta.div(2)));
 const gamma=rr(row.gamma??input.gamma[row.edge]);
 if(gamma.cmp(input.gamma[row.edge])<0)throw Error('row target weaker than the declared edge bound');
 const cost=target.map(p=>prove(sub(add(base,p),con(gamma)),lo,hi,true));
 return{source_mode:src.mode,source_lower:dec(src.v[0],14),premises:pr,cost};
}
const results=[],failures=[];
for(let i=0;i<input.rows.length;i++){
 try{results.push({index:i,...verifyRow(input.rows[i])});}
 catch(e){failures.push({index:i,row:input.rows[i],reason:String(e.message)});}
}
const atanCache=new Map();
function atanI(x){
 x=rr(x);const key=x.toString();if(atanCache.has(key))return atanCache.get(key);
 const y=idiv(x,ia(1,root(x.pow(2).add(1))));let sum=ii(0),upper;
 for(let j=0;j<=25;j++){
  sum=ia(sum,im(idiv(ipow(y,2*j+1),2*j+1),j%2?-1:1));
  if(j===24)upper=sum[1];
 }
 const out=[rr(dec(sum[0].mul(2),20)),rr(decup(upper.mul(2),20))];atanCache.set(key,out);return out;
}
function alphaEnds(a){return a.sign===1?[atanI(a.lo),atanI(a.hi)]:[ineg(atanI(a.hi)),ineg(atanI(a.lo))];}
const domainCache=new Map();
function requiredDomain(s,t,k,r){
 const key=[s.id,t.id,k,r].join('|');if(domainCache.has(key))return domainCache.get(key);
 const [sl,sh]=alphaEnds(s),[tl,th]=alphaEnds(t);
 const fl=ia(isub('19/25',sh),tl),fh=ia(isub(rr('710/113').sub('114/25'),sl),th),base=im(P2,k);
 const l=r===1?isub(fl,base):isub(base,fh),h=r===1?isub(fh,base):isub(base,fl);
 const out=[l[0].cmp(0)>0?l[0]:zero,h[1].cmp('.7')<0?h[1]:rr('.7')];domainCache.set(key,out);return out;
}
function covered(intervals,lo,hi){
 if(lo.cmp(hi)>0)return true;
 intervals=intervals.map(x=>x.map(rr)).sort((a,b)=>a[0].cmp(b[0]));let end=lo;
 for(const [a,b]of intervals){if(b.cmp(end)<0)continue;if(a.cmp(end)>0)return false;if(b.cmp(end)>0)end=b;if(end.cmp(hi)>=0)return true;}
 return false;
}
let cover=null;
if(input.cuts){
 const errors=[],chains=[];
 for(let role=0;role<7;role++)for(const kind of ['C','O'])for(const sign of [-1,1]){
  let [lo,hi]=(input.cuts[String(role)]||['-1','1']).map(rr);
  if(sign===-1)[lo,hi]=[hi.neg(),lo.neg()];lo=lo.cmp(0)>0?lo:zero;hi=hi.cmp(1)<0?hi:rr(1);
  if(lo.cmp(hi)<0&&!covered(input.arcs.filter(s=>s.role===role&&s.kind===kind&&s.sign===sign).map(s=>[s.lo,s.hi]),lo,hi))errors.push({type:'state arc gap',role,kind,sign,interval:[lo.toString(),hi.toString()]});
 }
 const rowgroups=new Map();
 for(let i=0;i<input.rows.length;i++){
  const row=input.rows[i],key=[row.edge,row.source,row.target,row.axis,row.r].join('|');
  if(!rowgroups.has(key))rowgroups.set(key,[]);rowgroups.get(key).push([row.lo,row.hi]);
 }
 for(let edge=0;edge<7;edge++)for(const s of arcs.values())if(s.role===edge)for(const t of arcs.values())if(t.role===(edge+1)%7)for(const axis of [1,2,3,4])for(const r of [-1,1]){
  const [lo,hi]=requiredDomain(s,t,WORD[edge],r);if(lo.cmp(hi)>0)continue;
  const key=[edge,s.id,t.id,axis,r].join('|'),chain=rowgroups.get(key)||[];
  if(!covered(chain,lo,hi))errors.push({type:'angle chain gap',edge,source:s.id,target:t.id,axis,r,required:[lo.toString(),hi.toString()],provided:chain});
  chains.push({edge,source:s.id,target:t.id,axis,r,required_lower:dec(lo,14),required_upper:decup(hi,14),rows:chain.length});
 }
 cover={status:errors.length?'INCOMPLETE':'PASS',angle_chains:chains.length,errors,chains};
}
console.log(JSON.stringify({status:failures.length||(cover&&cover.errors.length)?'INCOMPLETE':'PASS',scope:'Fixed one-angle affine SAT support inequalities; declared state and necessary-angle domain unions are checked when cuts are supplied',rows:input.rows.length,passed:results.length,failures,cover,results},null,2));

