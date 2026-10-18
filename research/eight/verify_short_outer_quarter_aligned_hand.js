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

const labels=JSON.parse(require('fs').readFileSync(__dirname+'/short_hand_labels.json','utf8'));
const checks=[];
function gt(n,x,v=0){x=ii(x);if(x[0].cmp(v)<=0)throw Error(n+': '+dec(x[0],14)+' <= '+v);checks.push({name:n,lower:dec(x[0],14),threshold:String(v)});}
function lt(n,x,v=0){gt(n,ineg(x),rr(v).neg());}
const Q=rr('9789/2500'),R=root(Q),d=isub(root(Q.div(2)),'.5'),a0=isub(root(Q.sub('.25')),'.5'),b0=isub(1,d),gamma=rr('17953/20000');
function a(b){return isub(root(isub(Q,ipow(ia(b,'.5'),2))),'.5');}
function rat(b){return idiv(ia(b,'.5'),ia(a(b),'.5'));}
function lab(i,s){return labels[i].O[s>0?'p':'n'].map(x=>rr(x).div(100000));}
function row(e,s,ax){let[c,p,q]=lab(e,s),[C,P,t]=lab((e+1)%7,s);if(ax===2||ax===3)[c,C,p,P,q,t]=[C.neg(),c.neg(),P.neg(),p.neg(),t,q];return {e,s,ax,c:c.sub(C),p,q,P,t};}
const F=[row(2,-1,3),row(4,-1,3),row(6,1,1)],E=[row(2,-1,4),row(4,-1,4),row(6,1,2)];
for(let j=0;j<3;j++){let f=F[j],e=E[j];if(f.p.cmp(e.P.neg())||f.P.cmp(e.p.neg())||f.q.cmp(e.t)||f.t.cmp(e.q)||f.c.cmp(e.c))throw Error('reflection binding');}
function aligned(z,B){let aa=isub(1,B),bb=a(aa);return ia(ia(P2,z.c),isub(ia(im(z.p,aa),im(z.t,B)),ia(im(z.q,bb),im(z.P,a(B)))));}
function alignedD(z,B){let aa=isub(1,B),bb=a(aa);return ia(z.t.sub(z.p),ia(im(z.P,rat(B)),ineg(im(z.q,idiv(ia(aa,'.5'),ia(bb,'.5'))))));}
function Ld(z,b){return isub(z.q,im(z.p,rat(b)));}
gt('d+.5>1.399',ia(d,'.5'),'1.399');lt('d+.5<1.4',ia(d,'.5'),'1.4');lt('a0+.5<1.915',ia(a0,'.5'),'1.915');
gt('b0>.1',b0,'.1');lt('b0<.101',b0,'.101');gt('a(b0)+.5>1.885',ia(a(b0),'.5'),'1.885');
for(let j=0;j<3;j++){
 let z=E[j];
 if(j===0){gt('aligned H second derivative >1',Q.mul(z.q).div(rr('1.4').pow(3)).add(Q.mul(z.P).div(rr('1.885').pow(3))),1);const H=aligned(z,'.0517'),v=alignedD(z,'.0517');gt('aligned edge2 quadratic completion',isub(H,idiv(ipow(absI(v),2),2)),'.8981');lt('aligned edge2 derivative at1/80',alignedD(z,'1/80'));}
 else {gt('aligned endpoint derivative negative '+j,z.p.add(z.q).sub(z.t));gt('aligned endpoint bound '+j,aligned(z,b0),'.8981');}
 gt('aligned low-B allowance '+j,isub(aligned(z,'1/80'),'.0012'),gamma);
}
// Source +f: negative half, interior critical points and b=0 boundary.
function fcontact(B,u){return ia('.5',ia(im(isub('.5',a(B)),cos(u)),im(ia(B,'.5'),sin(u))));}
lt('f contact .35,.3 is negative',fcontact('.35','.3'));
gt('critical product negative half',im(rr('.94766').mul('1.399'),isub(1,idiv(sin('.3'),ia(im('.85',cos('.3')),im('1.399',sin('.3')))))),1);
gt('f contact at B=d and u0 positive',fcontact(d,0));lt('f contact at B=d and u=.3 below d',fcontact(d,'.3'),d[0]);
for(let j=0;j<3;j++){
 const z=F[j];gt('f source derivative positive '+j,z.q.sub(z.p));if(z.p.cmp(0)<0||z.P.cmp(0)>0)throw Error('signs');
 gt('target linear diagonal minimum '+j,isub(ia(im(z.t,ia(a0,'.5')),im(z.P.neg(),'.5')),im(z.t.sub(z.P),ia(d,'.5'))));gt('target linear diagonal coefficient '+j,z.t.sub(z.P),'.94765');
 for(const [l,h] of [['0','.15'],['.15','.3']]){const speed=x=>ia(im(isub(d,'.5'),sin(x)),im(ia(d,'.5'),cos(x)));const b=fcontact(d,h),v1=im(Ld(z,b),speed(l)),v2=im(Ld(z,b),speed(h));gt('f diagonal derivative '+j+' '+l+' '+h+' left',v1,1);gt('f diagonal derivative '+j+' '+l+' '+h+' right',v2,1);}
 lt('f positive critical target weight '+j,z.t.mul('1.915').sub(z.P.mul('1.4')),'1.82');lt('f derivative q<1.2 '+j,z.q,'1.2');
}
gt('positive f D',isub(im('.5',cos('.1')),im('1.915',sin('.1'))));gt('positive f cos-sin>.895',isub(cos('.1'),sin('.1')),'.895');
gt('positive f interior derivative',rr(1).sub(rr('1.82').mul(rr(1).sub(rr('.895').div('1.4')))));gt('positive f diagonal derivative',rr(1).sub(rr('1.2').mul('.4')));
function fpcontact(B,x){return ia('.5',ia(im(isub('.5',a(B)),cos(x)),im(isub('.5',B),sin(x))));}
lt('positive f contact at B0 remains negative',fpcontact(0,'.1'));gt('positive f contact at diagonal remains positive',fpcontact(d,'.1'));lt('positive f diagonal contact less d',fpcontact(d,0),d[0]);
// Source -e: negative strip.
gt('negative e direct derivative',im('.94766',isub(im('1.399',cos('.03')),im('.5',sin('.03')))),1);
const W03=idiv(ia(1,ia(cos('.03'),sin('.03'))),2),Bupper=idiv(isub(ia(W03,im(a0,sin('.03'))),d),cos('.03'));
lt('negative e source diagonal target B<.16',Bupper,'.16');gt('a(.16)+.5>1.86',ia(a('.16'),'.5'),'1.86');
gt('negative e diagonal derivative',im(rr('.83048').mul('1.86').sub(rr('.33147').mul('.66')),isub(1,idiv(sin('.03'),im('1.86',cos('.03'))))),1);
// Source -e: positive strip, pointwise monotone C_x and B split.
gt('positive e v>1.29',root(Q.sub('2.25')),'1.29');gt('positive e contact h>.88',im(isub(a(b0),'.5'),cos('.06')),'.88');
lt('positive e L_a<1.3',rr('.19335').add(rr('.94766').mul('1.5').div('1.29')),'1.3');
lt('positive e derivative of L_a h negative',rr('1.3').mul('.5').sub(rr('.767').mul('3.9').mul(rr('.88').pow(2)).div(rr('1.4').pow(3))));
for(let j=0;j<3;j++){
 const z=E[j];gt('e p+q>.94765 '+j,z.p.add(z.q),'.94765');gt('e q>.767 '+j,z.q,'.767');lt('e p<=.19335 allowance '+j,z.p,'.19336');lt('e t>=.83048 bound '+j,z.t.neg(),rr('.83047').neg());
 const dx=B=>isub(1,im(ia(z.p,im(z.q,idiv(isub('1.5',B),ia(a(isub(1,B)),'.5')))),isub(a(B),'.5')));
 gt('positive e derivative at B0>-.02 '+j,dx(0),'-.02');gt('positive e derivative at B1/80 positive '+j,dx('1/80'));
}
console.log(JSON.stringify({status:'PASS',scope:'Six aligned same-sign OO quarter-one branches: source+f near x in[-.3,.1], source-e near x in[-.03,.06]',cost_lower:'17953/20000',checks:checks,normalized_f:F.map(z=>Object.fromEntries(Object.entries(z).map(([k,v])=>[k,v instanceof Rat?v.toString():v]))),normalized_e:E.map(z=>Object.fromEntries(Object.entries(z).map(([k,v])=>[k,v instanceof Rat?v.toString():v])))},null,2));
