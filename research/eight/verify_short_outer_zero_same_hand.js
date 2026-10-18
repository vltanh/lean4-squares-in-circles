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
function gt(n,x,v=0){x=ii(x);if(x[0].cmp(v)<=0)throw Error(n+": "+dec(x[0],12)+" <= "+v);checks.push({name:n,lower:dec(x[0],12),threshold:String(v)});}
function lt(n,x,v=0){gt(n,ineg(x),rr(v).neg());}
const Q=rr("9789/2500"),R=root(Q),d=isub(root(Q.div(2)),".5"),a0=isub(root(Q.sub(".25")),".5"),r0=idiv(".5",ia(a0,".5"));
function lab(i,s){return labels[i].O[s>0?"p":"n"].map(x=>rr(x).div(100000));}
function norm(edge,s){let[c,p,q]=lab(edge,s),[C,P,t]=lab(edge+1,s);if(s<0)[c,C,p,P,q,t]=[C.neg(),c.neg(),P.neg(),p.neg(),t,q];return{edge,sign:s,axis:s>0?1:3,c:c.sub(C),p,q,P,t,name:"edge"+edge+(s>0?"++ axis1":"-- axis3")};}
const Z=[norm(0,1),norm(1,-1),norm(3,1),norm(3,-1)];
function minI(a,b){a=ii(a);b=ii(b);return[a[0].cmp(b[0])<0?a[0]:b[0],a[1].cmp(b[1])<0?a[1]:b[1]];}
function maxI(a,b){a=ii(a);b=ii(b);return[a[0].cmp(b[0])>0?a[0]:b[0],a[1].cmp(b[1])>0?a[1]:b[1]];}
function src(z,l,m){l=rr(l);let y=z.q.sub(l);if(m==="circle")return isub(im("-.5",z.p.add(y)),im(R,root(z.p.pow(2).add(y.pow(2)))));if(m==="diagonal")return im(d,z.p.add(y));return minI(im(z.p,a0),im(d,z.p.add(y)));}
function F(z,l,m,x,kind){l=rr(l);let s=sin(x),c=cos(x),W=idiv(ia(1,ia(s,c)),2),X=ineg(ia(z.P,im(l,s))),Y=isub(im(l,c),z.t),T=kind==="axial"?im(X,a0):isub(im("-.5",ia(X,Y)),im(R,root(ia(ipow(X,2),ipow(Y,2)))));return ia(ia(x,z.c),ia(src(z,l,m),ia(im(l,W),T)));}
gt("R<2",isub(2,R));gt("d<1",isub(1,d));lt("a0-.5<.915",isub(a0,".5"),".915");lt("axial derivative factor<1.043",root(rr(".915").pow(2).add(".25")),"1.043");
gt("favorable same-sign phi>.107",isub(idiv(ia(1,ia(sin(".107"),cos(".107"))),2),ia(d,im(a0,sin(".107")))));
function diagonalSource(z,l){gt(z.name+" source q-l<=p lambda"+l,z.p.sub(z.q).add(l));if(z.p.cmp(0)>0)throw Error("bad diagonal source p");}
function normConcave(z,l,lo,hi){l=rr(l);gt(z.name+" target t>lambda "+l,z.t,l);const s0=sin(lo),c0=cos(lo),s1=sin(hi),c1=cos(hi);const u=ia(l,idiv(z.P,s0)),v=maxI(idiv(isub(z.t,im(l,c0)),s0),idiv(isub(z.t,im(l,c1)),s1));const M=root(ia(ipow(u,2),ipow(v,2)));gt(z.name+" norm concavity "+lo+" "+hi,l.mul(2),M[1]);}
function elementaryConcave(z,l,lo,hi){l=rr(l);const n2=z.P.pow(2).add(z.t.pow(2)),u=isub(im(z.t,cos(hi)),im(z.P,sin(hi))),Nmin=ia(z.P,im(l,sin(lo)));gt(z.name+" n>lambda "+l,n2,l.pow(2));if(u[0].cmp(l)>=0){gt(z.name+" N'' positive on"+lo+" "+hi,u,l);return;}const loss=idiv(im(2,im(isub(l,u),isub(n2,im(l,u)))),ipow(Nmin,3));gt(z.name+" full curvature on"+lo+" "+hi,isub(sin(lo),loss));}
function endpoints(z,l,m,lo,hi,kind="circle"){for(const x of[lo,hi]){let f=F(z,l,m,x,kind);gt(z.name+" "+kind+" endpoint"+x+" lambda"+l,f,".898");rows.push({edge:z.edge,signs:z.sign>0?"++":"--",axis:z.axis,lambda:l,source_support:m,target_support:kind,interval:[lo,hi],endpoint:x,lower:dec(f[0],12)});}}
function axial(z,l,lo,hi){for(const x of[lo,hi]){const X=ineg(ia(z.P,im(l,sin(x)))),Y=isub(im(l,cos(x)),z.t);lt(z.name+" target X negative "+x,X);gt(z.name+" axial derivative nonnegative "+x,isub(Y,im(X,r0)));}}
diagonalSource(Z[0],".98");normConcave(Z[0],".98",".107",".2");endpoints(Z[0],".98","diagonal",".107",".2");
if(Z[0].p.cmp(0)!==0||Z[0].q.cmp(".94766")!==0)throw Error("zero source cancel");normConcave(Z[0],".94766",".2",".7");endpoints(Z[0],".94766","endpoints",".2",".7");
diagonalSource(Z[1],"1");axial(Z[1],"1",".107",".3");gt("edge1 early axial envelope concavity",isub(im(".5",cos(".3")),im(isub(a0,".5"),sin(".3"))));endpoints(Z[1],"1","diagonal",".107",".3","axial");
normConcave(Z[1],".94",".3",".7");endpoints(Z[1],".94","circle",".3",".7");
gt("edge3++ source concave p",Z[2].p);axial(Z[2],".90362",".107",".7");gt("edge3++ axial envelope increasing",rr(1).sub(rr(".90362").mul("1.043")));endpoints(Z[2],".90362","endpoints",".107",".7","axial");
diagonalSource(Z[3],"1.025");elementaryConcave(Z[3],"1.025",".107",".16");endpoints(Z[3],"1.025","diagonal",".107",".16");
diagonalSource(Z[3],"1");elementaryConcave(Z[3],"1",".16",".3");endpoints(Z[3],"1","diagonal",".16",".3");
elementaryConcave(Z[3],".95",".3",".4");endpoints(Z[3],".95","circle",".3",".4");
elementaryConcave(Z[3],".906",".4",".5");endpoints(Z[3],".906","circle",".4",".5");
normConcave(Z[3],".906",".5",".7");endpoints(Z[3],".906","circle",".5",".7");
const report={status:"PASS",scope:"All four same-sign outer/outer zero-quarter favorable secondary branches, edges0++,1--,3++,3--; sourcef after reflection/reversal; whole |phi|<=.7",raw_branches:4,fixed_comparisons:checks.length,proved_cost_lower:".898",normalized_rows:Z.map(z=>({edge:z.edge,signs:z.sign>0?"++":"--",axis:z.axis,c:z.c.toString(),p:z.p.toString(),q:z.q.toString(),P:z.P.toString(),t:z.t.toString()})),rows,checks};console.log(JSON.stringify(report,null,2));

