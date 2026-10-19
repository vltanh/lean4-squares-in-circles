"use strict";
// Independent reconstruction of the negative OO quarter contact bounds.
const arithmetic=(function(){

class F {
 constructor(n,d=1n){ n=BigInt(n); d=BigInt(d); if(d===0n)throw Error("zero denominator");if(d<0n){n=-n;d=-d}let a=n<0n?-n:n,b=d;while(b){let t=a%b;a=b;b=t;}this.n=n/a;this.d=d/a; }
 static of(x){if(x instanceof F)return x;if(typeof x==="string"&&x.includes("/")){let z=x.split("/");return new F(z[0],z[1])}if(typeof x==="string"&&x.includes(".")){let sign=x.startsWith("-")?-1n:1n;let z=x.replace("-","").split(".");return new F(sign*BigInt(z[0]+z[1]),10n**BigInt(z[1].length));}return new F(x)}
 add(y){y=F.of(y);return new F(this.n*y.d+y.n*this.d,this.d*y.d)}
 sub(y){y=F.of(y);return new F(this.n*y.d-y.n*this.d,this.d*y.d)}
 mul(y){y=F.of(y);return new F(this.n*y.n,this.d*y.d)}
 div(y){y=F.of(y);return new F(this.n*y.d,this.d*y.n)}
 neg(){return new F(-this.n,this.d)}
 pow(k){return k<0?new F(this.d**BigInt(-k),this.n**BigInt(-k)):new F(this.n**BigInt(k),this.d**BigInt(k))}
 cmp(y){y=F.of(y);let z=this.n*y.d-y.n*this.d;return z>0n?1:z<0n?-1:0}
 lt(y){return this.cmp(y)<0}gt(y){return this.cmp(y)>0}
 num(){return Number(this.n)/Number(this.d)}
 str(){return this.d===1n?String(this.n):this.n+"/"+this.d}
}
const f=x=>F.of(x);
const sum=a=>a.reduce((s,x)=>s.add(x),f(0));
const fac=n=>{let r=1n;for(let j=2;j<=n;j++)r*=BigInt(j);return r}
const choose=(n,k)=>fac(n)/(fac(k)*fac(n-k));
const trig=(x,kind,degree)=>{x=f(x);let s=f(0);for(let j=kind==="sin"?1:0;j<=degree;j+=2){let sg=((j-(kind==="sin"?1:0))/2)%2?-1n:1n;s=s.add(x.pow(j).mul(new F(sg,fac(j))))}return s};
const add=(a,b)=>Array.from({length:Math.max(a.length,b.length)},(_,i)=>(a[i]||f(0)).add(b[i]||f(0)));
const scale=(a,s)=>a.map(x=>x.mul(s));
const mul=(a,b)=>{let c=Array.from({length:a.length+b.length-1},()=>f(0));a.forEach((x,i)=>b.forEach((y,j)=>c[i+j]=c[i+j].add(x.mul(y))));return c};
const monomial=(n,c=1)=>{let a=Array.from({length:n+1},()=>f(0));a[n]=f(c);return a};
const trigpoly=(kind,degree)=>{let p=Array.from({length:degree+1},()=>f(0));for(let j=kind==="sin"?1:0;j<=degree;j+=2){let sg=((j-(kind==="sin"?1:0))/2)%2?-1n:1n;p[j]=new F(sg,fac(j))}return p};
const bern=(p,l,r)=>{l=f(l);r=f(r);const n=p.length-1,h=r.sub(l);let power=Array.from({length:n+1},()=>f(0));for(let i=0;i<=n;i++)for(let j=0;j<=i;j++)power[j]=power[j].add(p[i].mul(choose(i,j)).mul(l.pow(i-j)).mul(h.pow(j)));return power.map((_,k)=>sum(power.slice(0,k+1).map((v,j)=>v.mul(choose(k,j)).div(choose(n,j)))))};
return {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern};
})();
const {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern}=arithmetic;
const intervals=(function(){

const I=(l,h=l)=>[f(l),f(h)];
const ia=(x,y)=>{x=Array.isArray(x)?x:I(x);y=Array.isArray(y)?y:I(y);return[x[0].add(y[0]),x[1].add(y[1])];};
const ineg=x=>{x=Array.isArray(x)?x:I(x);return[x[1].neg(),x[0].neg()];};
const is=(x,y)=>ia(x,ineg(y));
const im=(x,y)=>{x=Array.isArray(x)?x:I(x);y=Array.isArray(y)?y:I(y);let z=[x[0].mul(y[0]),x[0].mul(y[1]),x[1].mul(y[0]),x[1].mul(y[1])].sort((a,b)=>a.cmp(b));return[z[0],z[3]];};
const id=(x,y)=>{y=Array.isArray(y)?y:I(y);if(!y[0].gt(0))throw Error("nonpositive interval denominator");return im(x,[f(1).div(y[1]),f(1).div(y[0])]);};
const ip=(x,k)=>{x=Array.isArray(x)?x:I(x);if(k%2===0&&x[0].lt(0)&&x[1].gt(0))return[f(0),x[0].neg().gt(x[1])?x[0].pow(k):x[1].pow(k)];let z=[x[0].pow(k),x[1].pow(k)].sort((a,b)=>a.cmp(b));return z;};
function isqrt(n){if(n<0n)throw Error("negative square root");if(n<2n)return n;let z=1n<<BigInt((n.toString(2).length+1)>>1);for(;;){let y=(z+n/z)>>1n;if(y>=z)return z;z=y;}}
function rootI(x){x=Array.isArray(x)?x:I(x);if(x[0].lt(0))throw Error("negative radical");const S=10n**14n;return[new F(isqrt(x[0].n*S*S/x[0].d),S),new F(isqrt(x[1].n*S*S/x[1].d)+1n,S)];}
function trigI(x,kind){x=Array.isArray(x)?x:I(x);if(x[0].lt(0)||x[1].gt(3))throw Error("trig domain");let term=kind==="sin"?x:I(1),s=term,lo;for(let j=1;j<=16;j++){let d=kind==="sin"?(2*j)*(2*j+1):(2*j-1)*(2*j);term=ineg(id(im(term,ip(x,2)),d));s=ia(s,term);if(j===15)lo=s[0];}return[lo,s[1]];}
const sinI=x=>trigI(x,"sin"),cosI=x=>trigI(x,"cos");
const atanS=(q,n)=>{let x=f(1).div(q),z=f(0);for(let j=0;j<=n;j++)z=z.add(x.pow(2*j+1).mul(new F(j%2?-1n:1n,BigInt(2*j+1))));return z;};
const PI=I("3.141592653589793238","3.141592653589793239");
if(!atanS(5,25).mul(16).sub(atanS(239,6).mul(4)).gt(PI[0])||!atanS(5,24).mul(16).sub(atanS(239,7).mul(4)).lt(PI[1]))throw Error("Machin enclosure");
return {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI};
})();
const {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI}=intervals;
const result=(function(){

const checks=[];
function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),threshold:f(y).str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),d=is(rootI(Q.div(2)),".5"),hp=id(PI,2);
const p={c:f(".02478"),q:f(".93015"),v:f(".02363"),k:f(".11055")},t={c:f(".01670"),q:f("2.42322"),v:f("-.91744"),k:f(".95769")};
function state(b){b=Array.isArray(b)?b:I(b);const V=ia(b,".5"),U=rootI(is(Q,ip(V,2))),a=is(U,".5"),r=id(V,U),rp=id(Q,ip(U,3)),rpp=id(im(Q.mul(3),V),ip(U,5));return{b,V,U,a,r,rp,rpp};}
function label(z,b){const s=state(b);return ia(z.c,ia(im(z.q,s.b),ia(im(z.v,ip(s.b,2)),im(z.k.neg(),im(s.a,s.b)))));}
function D(z,b){const s=state(b);return{one:ia(z.q,ia(im(z.v.mul(2),s.b),im(z.k.neg(),is(s.a,im(s.b,s.r))))),two:ia(z.v.mul(2),im(z.k,ia(im(2,s.r),im(s.b,s.rp)))),three:im(z.k,ia(im(3,s.rp),im(s.b,s.rpp)))};}
for(const [lo,hi,bound]of[["0",".2","-.018"],[".2",".4","-.096"],[".4",".6","-.126"],[".6",".8","-.045"],[".8",".9","-.081"]]){
 const s=state(I(lo,hi)),q=is(Q.add(1),im(2,s.U));
 const NN=u=>is(is(im(Q.mul(4),u),im(2,ip(u,2))),Q.mul(Q.add(1)));
 const L=NN(s.U[0]),H=NN(s.U[1]),nn=[L[0],H[1]],fp=id(nn,im(ip(s.U,2),ip(q,2)));
 const c0=is(is(id(Q,ip(s.U,3)),id(im(2,ip(s.r,2)),q)),id(ip(s.r,2),is(q,".25")));
 const c1=is(id(Q,ip(s.U,3)),id(im(3,ip(s.r,2)),q));
 const abs=x=>x.lt(0)?x.neg():x;const mm=[...c0,...c1].map(abs).sort((a,b)=>a.cmp(b)).at(-1);
 const middle=id(mm.div(2),im(q,rootI(is(q,".25"))));
 const upper=is(ia(ineg(im(s.r,fp)),middle),D(p,lo).two);
 lt("independent fixed-target curvature "+lo+":"+hi,upper,bound);
}
function lower3(b,x){
 const z=state(b),s=sinI(x),c=cosI(x);
 const B=ia(".5",is(im(z.V,s),im(is(z.a,".5"),c)));
 const vel=ia(im(is(z.a,".5"),s),im(z.V,c)),k=ia(im(z.r,c),s),k1=im(z.rp,c),k2=im(z.rpp,c);
 return{B,vel,k,k1,k2};
}
function end3(b){
 const z=lower3(b,".7"),pD=D(p,b),tD=D(t,z.B),H=is(ia(is(hp,".7"),label(t,z.B)),label(p,b));
 return{...z,pD,tD,H,first:ia(ineg(pD.one),im(tD.one,z.k)),second:ia(ineg(pD.two),ia(im(tD.two,ip(z.k,2)),im(tD.one,z.k1)))};
}
for(const[lo,hi,bound]of[["0",".1","-.389"],[".1",".2","-.362"]]){
 const L=end3(lo),H=end3(hi),upper=ia(ineg(L.pD.two),ia(im(H.tD.two,ip(L.k,2)),im(L.tD.one,H.k1)));
 lt("independent endpoint early curvature "+lo+":"+hi,upper,bound);
}
for(const[lo,hi,bound]of[[".2",".3",".410"],[".3",".5",".916"],[".5",".76","3.85"]]){
 const L=end3(lo),H=end3(hi),lower=ia(ineg(H.pD.three),ia(im(L.tD.three,ip(L.k,3)),ia(im(3,im(L.tD.two,im(H.k,H.k1))),im(".609",L.k2))));
 gt("independent endpoint third derivative "+lo+":"+hi,lower,bound);
}
const Z=end3(".72365");gt("independent final reference cost",Z.H,".89778507");lt("independent final reference derivative upper",Z.first,".000001");gt("independent final reference derivative lower",Z.first,"-.000001");lt("independent final reference physical",Z.B,d[0]);
gt("independent final curvature anchor",end3(".6").second,".65");lt("independent endpoint derivative .6",end3(".6").first,0);
gt("independent aligned endpoint",ia(is(hp,label(p,d)),label(t,is(1,d))),".8977827");
function diag3(x){const z=lower3(d,x),dd=D(t,z.B),zz=is(z.B,".5");return{...z,H:ia(is(ia(hp,f(x).neg()),label(p,d)),label(t,z.B)),first:is(im(dd.one,z.vel),1),second:is(im(dd.two,ip(z.vel,2)),im(dd.one,zz))};}
gt("independent diagonal curvature anchor",diag3(".4").second,".3");lt("independent diagonal derivative .4",diag3(".4").first,0);
gt("independent diagonal reference cost",diag3(".5").H,".90204");lt("independent diagonal reference derivative upper",diag3(".5").first,".022");gt("independent diagonal reference derivative lower",diag3(".5").first,"-.022");
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",checks,comparison_count:checks.length};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;

