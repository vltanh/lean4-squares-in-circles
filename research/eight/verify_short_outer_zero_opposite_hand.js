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
const checks=[],regimes=[];
function gt(name,x,v=0){x=ii(x);if(x[0].cmp(v)<=0)throw Error(name+" failed: "+dec(x[0],12)+" <= "+v);checks.push({name,lower:dec(x[0],12),threshold:String(v)});}
function lt(name,x,v=0){gt(name,ineg(x),rr(v).neg());}
const Q=rr("9789/2500"),R=root(Q),d=isub(root(Q.div(2)),".5"),a0=isub(root(Q.sub(".25")),".5");
const b0=isub(1,d),H0=root(isub(Q,ipow(ia(b0,".5"),2))),r0=idiv(".5",ia(a0,".5"));
function outer(b){return isub(root(isub(Q,ipow(ia(b,".5"),2))),".5");}
function lab(i,s){return labels[i].O[s>0?"p":"n"].map(n=>rr(n).div(100000));}
function norm(edge,rev){let[c,p,q]=lab(edge,1),[C,P,t]=lab(edge+1,-1);if(rev)[c,C,p,P,q,t]=[C.neg(),c.neg(),P.neg(),p.neg(),t,q];return{edge,rev,name:"edge"+edge+(rev?" axis3":" axis1"),c:c.sub(C),p,q,v:P.neg(),t};}
const Z=[norm(0,false),norm(0,true),norm(1,false),norm(1,true),norm(3,false),norm(3,true)];
function sgnTrig(x){x=rr(x);return{h:ii(x),s:x.cmp(0)>=0?sin(x):ineg(sin(x.neg())),c:cos(x.cmp(0)>=0?x:x.neg()),pos:x.cmp(0)>=0};}
function minI(a,b){a=ii(a);b=ii(b);return[a[0].cmp(b[0])<0?a[0]:b[0],a[1].cmp(b[1])<0?a[1]:b[1]];}
function src(z,l,method="endpoints"){l=rr(l);let y=z.q.sub(l);if(method==="circle")return isub(im("-.5",z.p.add(y)),im(R,root(z.p.pow(2).add(y.pow(2)))));if(method==="diagonal")return im(d,z.p.add(y));return minI(im(z.p,a0),im(d,z.p.add(y)));}
function E(z,l,method,x,which){l=rr(l);let S=src(z,l,method),{h,s,c,pos}=sgnTrig(x),W=idiv(ia(1,ia(absI(s),c)),2),X=isub(z.v,im(l,s)),Y=isub(z.t,im(l,c));let support;if(which==="axial")support=im(X,a0);else if(which==="diagonal")support=im(d,ia(X,Y));else support=isub(im("-.5",ia(X,Y)),im(R,root(ia(ipow(X,2),ipow(Y,2)))));return ia(ia(h,z.c),ia(im(l,W),ia(S,support)));}
function targetDiag(z,x){const{h,s,c,pos}=sgnTrig(x),b=ia(".5",pos?im(isub(".5",d),ia(s,c)):isub(im(isub(".5",d),c),im(ia(".5",d),s)));return ia(ia(h,z.c),ia(ia(im(z.p,outer(b)),im(z.q,b)),im(d,z.v.add(z.t))));}
function sourceDiag(z,x){const{h,s,c,pos}=sgnTrig(x),K=ia(isub(".5",d),pos?ia(s,c):c),H=root(isub(Q,ipow(K,2))),X=ia(im(c,H),im(s,K)),Y=isub(im(c,K),im(s,H));return ia(ia(h,z.c),ia(im(d,z.p.add(z.q)),ia(im(z.v,isub(X,".5")),im(z.t,isub(Y,".5")))));}
const eta=".898";
gt("R<2",isub(2,R));gt("d+.5>1.399",ia(d,".5"),"1.399");lt("d+.5<1.4",ia(d,".5"),"1.4");gt("a0+.5>1.914",ia(a0,".5"),"1.914");lt("a0+.5<1.915",ia(a0,".5"),"1.915");
gt("b0>.1",b0,".1");lt("b0<.101",b0,".101");gt("H0>1.885",H0,"1.885");lt("H0<1.886",H0,"1.886");lt("r(b0)<.319",idiv(ia(b0,".5"),H0),".319");
lt("whole arc curvature ratio",ipow(idiv(ia(a0,".5"),ia(d,".5")),3),"2.57");lt("restricted ratio",rr("1.886").div("1.399").pow(3),"2.46");
const sc1=ia(sin(".1"),cos(".1")),W1=idiv(ia(1,sc1),2);
gt("near contact cannot have b=0",isub(W1,im(d,sc1)));
gt("near contact cannot have B=0",isub(isub(W1,im(a0,sin(".1"))),d));
const bm=ia(".5",ia(im(isub(".5",d),cos(".1")),im(ia(".5",d),sin(".1"))));
lt("negative diagonal endpoint b<.245",bm,".245");lt("r(.245)<.41",idiv(".745",root(Q.sub(rr(".745").pow(2)))),".41");
gt("negative projected endpoint X>1.8",Q.sub(rr(".8").pow(2)),rr("1.8").pow(2));
lt("negative projected endpoint Y<.8",rr(".601").add(rr(".1").mul(2)),".802");
lt("sharper negative Y bound",ia(".601",im(".1",R)),".8");
gt("positive K<.7",isub(".7",ia(isub(".5",d),sc1)));
gt("positive H>1.85",Q.sub(rr(".7").pow(2)),rr("1.85").pow(2));
gt("positive f derivative",rr(1).div("1.886").sub(rr(".7").div(rr("1.85").pow(3))));
gt("negative diagonal endpoint derivative",im(rr(".76").mul("1.399"),cos(".1")),1);
gt("negative projected endpoint derivative",rr(".76").mul("1.8").mul(rr(1).sub(rr(".1").div("1.885"))),1);
gt("positive diagonal endpoint derivative",rr(1).sub(rr("1.2").mul(".4")));
for(const z of Z){gt(z.name+" source coordinate monotonic",z.q.sub(z.p.cmp(0)>0?z.p:0));gt(z.name+" target coordinate monotonic",z.t.sub(z.v.cmp(0)>0?z.v:0));}
const near=[{k:0,h:".08",rule:"concavity"},{k:1,h:".04",rule:"concavity"},{k:4,h:".06",rule:"one-valley"},{k:5,h:".1",rule:"one-peak"}];
for(const r of near){const z=Z[r.k];
 gt(z.name+" negative source endpoint slope",z.q.sub((z.p.cmp(0)>0?z.p:rr(0)).mul(".41")),".76");
 gt(z.name+" negative target endpoint slope",z.t.sub((z.v.cmp(0)>0?z.v:rr(0)).mul(rr(".8").div("1.8"))),".76");
 lt(z.name+" positive source endpoint slope upper",z.q.add(z.p.cmp(0)<0?z.p.neg():0),"1.2");
 for(const fun of[targetDiag,sourceDiag]){gt(z.name+" aligned "+fun.name,fun(z,0),eta);gt(z.name+" positive endpoint "+fun.name+" "+r.h,fun(z,r.h),eta);}
 if(z.v.cmp(0)<0){const h=r.h;gt(z.name+" positive projected endpoint increasing",isub(1,im(ia(z.t.mul("1.915"),z.v.neg().mul(".601")),isub(1,idiv(isub(cos(h),sin(h)),"1.886")))));}
 regimes.push({edge:z.edge,axis:z.rev?3:1,angle_interval:["-.1",r.h],contact_rule:r.rule,endpoint_cost_lower:eta});
}
gt("edge0 axis1 contact concavity",isub(Z[0].v,im(Z[0].q,sin(".08"))));
gt("edge0 axis3 contact concavity",rr(".13422").mul(".959").pow(1).mul(".959").sub(rr("1.03828").mul("2.57").mul(".04")));
gt("cos.04-sin.04>.959",isub(cos(".04"),sin(".04")),".959");
gt("edge3 axis1 negative contact concavity",isub(im(rr(".51554").mul(rr("1.399").div("1.915").pow(3)),ipow(cos(".1"),2)),".19335"));
gt("edge3 axis1 positive right derivative negative",im(rr("1.19909").sub(rr(".51554").mul(".319")),isub(cos(".06"),sin(".06"))),".96079");
gt("edge3 axis3 positive left derivative positive",rr("1.19909").sub(".96079").sub(rr(".51554").mul(".319")));
for(const u of["0",".1"]){const v=rr("-.51554").add(rr(".19335").mul("2.46").mul(rr(1).add(u).pow(2))).sub(rr(".76744").mul(".99").mul(u));lt("edge3 axis3 negative curvature "+u,v);}
gt("sin u>=.99u on[0,.1]",rr(1).sub(rr(".1").pow(2).div(6)),".99");
gt("zero aligned edge3 concavity",rr(".51554").sub(rr(".19335").mul("2.46")));
const lammin=rr(".90362");
gt("all negative axial envelopes decrease",im(lammin,isub(im(ia(a0,".5"),cos(".7")),im(".5",sin(".7")))),1);
gt("all negative diagonal envelopes decrease endpoint0",im(lammin,ia(d,".5")),1);
gt("all negative diagonal envelopes decrease endpoint.7",im(lammin,ia(im(ia(d,".5"),cos(".7")),im(isub(d,".5"),sin(".7")))),1);
lt("positive axial derivative factor",root(rr(".915").pow(2).add(".25")),"1.043");
gt("positive diagonal envelopes increase",rr(1).sub(".4"));
function endpoints(z,l,m,x,label=undefined,margin=eta){for(const kind of["axial","diagonal"]){const val=E(z,l,m,x,kind);gt((label||z.name)+" "+kind+" "+x+" lambda"+l,val,margin);regimes.push({edge:z.edge,axis:z.rev?3:1,kind,lambda:l,source:m,endpoint:x,lower:dec(val[0],12)});}}
function circles(z,l,m,xs){gt(z.name+" circle concavity lambda"+l,rr(l),root(z.v.pow(2).add(z.t.pow(2)))[1]);for(const x of xs){const val=E(z,l,m,x,"circle");gt(z.name+" circle endpoint "+x+" lambda"+l,val,eta);regimes.push({edge:z.edge,axis:z.rev?3:1,kind:"circle",lambda:l,source:m,endpoint:x,lower:dec(val[0],12)});}}
function axialAfter(z,l,m,h,slop=0,end=".7"){const s=sin(h),c=cos(h),X=isub(z.v,im(l,s)),Y=isub(z.t,im(l,c));lt(z.name+" axial support X at"+h,X);gt(z.name+" axial support derivative at0 at"+h,isub(Y,im(X,r0)));gt(z.name+" axial derivative bound lambda"+l,rr(1).sub(rr(l).mul("1.043")),rr(slop).neg());const lower=isub(E(z,l,m,h,"axial"),rr(slop).mul(rr(end).sub(h)));gt(z.name+" axial continuation from"+h,lower,eta);regimes.push({edge:z.edge,axis:z.rev?3:1,kind:"axial continuation",lambda:l,angle_interval:[h,end],derivative_lower:String(rr(slop).neg()),lower:dec(lower[0],12)});}
endpoints(Z[0],".94766","endpoints","-.1");endpoints(Z[0],".94766","endpoints",".08");
gt("edge0 positive axial increasing",rr(1).sub(rr(".94766").mul("1.043")));
endpoints(Z[1],".96135","endpoints","-.1");circles(Z[1],".96135","endpoints",[".04",".08"]);axialAfter(Z[1],".96135","endpoints",".08",".003");
gt("edge1 axis1 negative support Y<=X",rr(".9994"),rr(".88074").add(".09133"));
gt("edge1 axis1 near-positive diagonal ordering",isub(im(".9994",isub(cos(".02"),sin(".02"))),rr(".88074").add(".09133")));
endpoints(Z[2],".9994","endpoints","0");
gt("edge1 axis1 positive diagonal endpoint0",E(Z[2],".9994","endpoints","0","diagonal"),eta);
circles(Z[2],".9994","endpoints",[".02",".3"]);axialAfter(Z[2],".9994","endpoints",".3",".043");
gt("edge1 axis3 source diagonal criterion",rr(".9994").sub(".88074"),".09133");
endpoints(Z[3],".9994","diagonal","0");
gt("edge1 axis3 axial concavity to.2",isub(im(".5",cos(".2")),im(isub(a0,".5"),sin(".2"))));
gt("edge1 axis3 positive axial endpoint.2",E(Z[3],".9994","diagonal",".2","axial"),eta);
gt("edge1 axis3 lambda .93 target positive",rr(".9994").sub(".93"));gt("edge1 axis3 lambda.93 axial increasing",rr(1).sub(rr(".93").mul("1.043")));
gt("edge1 axis3 lambda.93 endpoint .2",E(Z[3],".93","circle",".2","axial"),eta);
gt("edge3 axis1 negative target endpoint criterion",im(".90362",ia(cos(".1"),sin(".1"))),".96079");
endpoints(Z[4],".90362","endpoints","-.1");circles(Z[4],".90362","endpoints",[".06",".3"]);axialAfter(Z[4],".90362","endpoints",".3",0);
endpoints(Z[5],".90362","circle","-.1");
gt("edge3 axis3 target Y positive forlambda.9635",rr("1.19909").sub(".9635"));
gt("edge3 axis3 lambda.9635 axial derivative>-.005",rr(1).sub(rr(".9635").mul("1.043")),"-.005");
for(const kind of["axial","diagonal"]){const low=isub(E(Z[5],".9635","circle",".1",kind),".0005");gt("edge3 axis3 nearpositive "+kind+" continuation",low,eta);regimes.push({edge:3,axis:3,kind:"nearpositive "+kind,lambda:".9635",angle_interval:[".1",".2"],lower:dec(low[0],12)});}
endpoints(Z[5],".90362","circle",".2");gt("edge3 axis3 lambda.90362 axial increase",rr(1).sub(rr(".90362").mul("1.043")));
const report={status:"PASS",scope:"All six opposite-sign outer/outer zero-quarter secondary branches on edges0,1,3, axes1 and3, signs(+,-), full |phi|<=.7; hand contact curvature and scalar support proof",proved_cost_lower:eta,target:"17953/20000",raw_branches:6,fixed_comparisons:checks.length,normalized_rows:Z.map(z=>({edge:z.edge,axis:z.rev?3:1,c:z.c.toString(),p:z.p.toString(),q:z.q.toString(),v:z.v.toString(),t:z.t.toString()})),regimes,checks};
console.log(JSON.stringify(report,null,2));

