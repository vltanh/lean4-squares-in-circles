#!/usr/bin/env node
"use strict";
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
const checks=[],tables=[];
function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),h=f("1.03981"),k=f(".95769"),ac=f("7/12"),gamma=f(".89765"),dc=ia(".5",id(rootI(2),24)),d=is(rootI(Q.div(2)),".5"),a0=is(rootI(Q.sub(".25")),".5"),lo=is(id(PI,2),".7");
function a(B){return is(rootI(is(Q,ip(ia(B,".5"),2))),".5");}
function T(B){return is(ia(".01670",is(im("2.42322",B),im(".91744",ip(B,2)))),im(k,im(a(B),B)));}
function D(B){const A=a(B),r=id(ia(B,".5"),ia(A,".5"));return ia(is(is("2.42322",im("1.83488",B)),im(k,A)),im(k,im(B,r)));}
function Dp(B){const A=a(B),r=id(ia(B,".5"),ia(A,".5")),rp=id(Q,ip(ia(A,".5"),3));return ia("-1.83488",im(k,ia(im(2,r),im(B,rp))));}
gt("outer label derivative second curvature>1.38",f(3).mul(".95").mul("3.9").div(8),"1.38");
gt("D(.6)>.6101",D(".6"),".6101");gt("Dprime(.6)>-.049",Dp(".6"),"-.049");lt("Dprime(.6)<0",Dp(".6"),0);
gt("global D>.609 from strong convexity",f(".6101").sub(f(".049").pow(2).div("2.76")),".609");
lt("D at axis<1.069",D(0),"1.069");lt("D at diagonal<1.069",D(d),"1.069");
gt("outer diagonal>.899",d,".899");lt("outer diagonal<.9",d,".9");
gt("core diagonal>.5589",dc,".5589");lt("core diagonal<.559",dc,".559");
lt("outer axial a<1.415",a0,"1.415");
gt("radial ratio>.261",id(".5",ia(a0,".5")),".261");
gt("lower-angle sine>.764",sinI(lo),".764");lt("lower-angle cosine<.645",cosI(lo),".645");
gt("whole late direct cost>.904",is("1.48545",im(h,dc)),".904");
gt("axis1 outer-coordinate derivative positive",f(".609").sub(h.mul(f(".645").sub(f(".261").mul(".764")))),0);
function F1(phi){return is(ia(ia(phi,f(".01545").add(h.div(2))),im(h.div(2),cosI(phi))),im(h,im(is(a0,".5"),sinI(phi))));}
function F1p(phi){return is(is(1,im(h.div(2),sinI(phi))),im(h,im(is(a0,".5"),cosI(phi))));}
gt("F1 curvature lower>.39",im(h,is(im(is(a0,".5"),sinI(lo)),id(cosI(lo),2))),".39");
gt("F1(.9)>1.0136",F1(".9"),"1.0136");
gt("F1prime(.9)>-.0017",F1p(".9"),"-.0017");lt("F1prime(.9)<.0017",F1p(".9"),".0017");
gt("F1 whole-interval lower>1.013",f("1.0136").sub(f(".0017").pow(2).div(".78")),"1.013");
gt("axis2 scalar dominates axis1 by norm",is(ip(ia(dc,".5"),2),ia(".25",ip(is(a0,".5"),2))),0);
gt("B0(.95)>.7226",ia(".5",is(id(cosI(".95"),2),id(sinI(".95"),12))),".7226");
gt("cos.95>.581",cosI(".95"),".581");
lt("axis3 early source core b<.306",f(".9").sub(".7226").div(".581"),".306");
gt("T(.7226)>.5579",T(".7226"),".5579");
gt("axis3 early bound>1.109",ia(is(is(lo,".00125"),im(h,".306")),".5579"),"1.109");
gt("axis3 late scalar derivative positive",f(1).sub(f("1.069").mul("7/12")),0);
const B95=ia(".5",is(id(cosI(".95"),2),id(sinI(".95"),12)));
gt("axis3 late scalar at.95>.9258",ia(is(is(".95",".00125"),im(h,dc)),T(B95)),".9258");
lt("axis4 geometrically requires phi>1.2",is(ia(ac.sub(".5"),im(is(d,".5"),sinI("1.2"))),im(ia(d,".5"),cosI("1.2"))),0);
gt("T(5/12)>.3668",T("5/12"),".3668");
gt("axis4 direct bound>.984",ia(is(is("1.2",".00125"),im(h,dc)),T("5/12")),".984");
for(const x of[".904","1.013","1.109",".9258",".984"])gt("terminal "+x+" exceeds gamma",f(x),gamma);
return {status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge2 core-minus to outer-minus, both core pieces, all four axes, entire quarter-one angle interval",comparisons:checks.length,checks,tables};
})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;
