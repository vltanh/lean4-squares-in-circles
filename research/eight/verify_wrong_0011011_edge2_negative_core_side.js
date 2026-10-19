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
const Q=f("3.9156"),ac=f("7/12"),k=f(".11055"),V=f(".961795"),z=f(".02363"),gamma=f(".89765"),cm=f(".22042").sub(f(".34492").mul(ac));
const d=is(rootI(Q.div(2)),".5"),a0=is(rootI(Q.sub(".25")),".5"),lo=is(id(PI,2),".7");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}
function L(b){return is(ia(".02478",ia(im(".93015",b),im(".02363",ip(b,2)))),im(".11055",im(a(b),b)));}
function Lp(b){let aa=a(b),r=id(ia(b,".5"),ia(aa,".5"));return ia(is(ia(".93015",im(".04726",b)),im(".11055",aa)),im(".11055",im(b,r)));}
function M(u){let t=rootI(is(Q,ip(u,2)));return is(ia(".369499372",is(im(".02363",ip(u,2)),im(".055275",u))),im(is(V,im(k,u)),t));}
function M1(u){let t=rootI(is(Q,ip(u,2)));return ia(is(im(".04726",u),".055275"),ia(im(k,t),id(im(is(V,im(k,u)),u),t)));}
function M2(u){let t=rootI(is(Q,ip(u,2)));return ia(is(".04726",id(im(".22110",u),t)),id(im(Q,is(V,im(k,u))),ip(t,3)));}
gt("M''' numerator positive on u>=1",V.sub(k.mul(Q)),0);
gt("M'(1)>.67",M1(1),".67");gt("M''(1)>.58",M2(1),".58");
gt("M''(1.4)>.78",M2("1.4"),".78");
gt("quadratic tangent excess at u=1>.0014",is(is(M(1),M("1.4")),ia(im(M1("1.4"),"-.4"),f(".39").mul(".16"))),".0014");
gt("rounded M0 lower",M("1.4"),"-.790136934");
gt("rounded M1 error lower",M1("1.4"),f(".973417553").sub(".0000000004"));
lt("rounded M1 error upper",M1("1.4"),f(".973417553").add(".0000000004"));
gt("rounded quadratic remains strictly below true tangent minorant",f(".000000001").sub(f(".0000000004").mul(".6")),0);
lt("physical axial coordinate u<1.915",ia(a0,".5"),"1.915");
gt("outer diagonal>.899",d,".899");lt("outer diagonal<.9",d,".9");
lt("source maximum L(d)<.79091",L(d),".79091");
gt("core side label derivative>.93",f(".98439").sub(f(".10668").mul(".5")),".93");
gt("all-state direct bound after phi1.67",f("1.67").sub(".79091").add(cm),gamma);
gt("quarter+.1 exceeds1.67",ia(id(PI,2),".1"),"1.67");
const p=f(".973417553"),g=f(".98439"),kk=f(".39"),zz=f(".05334");
const s=trigpoly("cos",10),c=trigpoly("sin",9),xx=monomial(1);
const D=add([f("-.4")],add(scale(c,f("13/12")),scale(s,f(".5"))));
const vv=add([PI[0].div(2).sub(".790136935").add(cm).sub(gamma)],scale(xx,-1));
let PP=add(mul(mul(s,s),add(scale(vv,kk.mul(4)),[p.pow(2).neg()])),scale(s,g.mul(p).mul(2)));
PP=add(PP,scale(mul(D,s),g.mul(kk).mul(4)));
PP=add(PP,scale(add(vv,add(scale(D,p),scale(mul(D,D),kk))),zz.mul(-4)));
PP=add(PP,[g.pow(2).neg()]);
const tail=sum(PP.slice(10).map((v,j)=>v.lt(0)?v.neg().mul(f(".7").pow(j+10)):f(0)));
lt("negative polynomial tail below1e-7",tail,".0000001");
lt("sine degree9 error below5e-10",f(".7").pow(11).div(fac(11)),".0000000005");
lt("cosine degree10 error below3e-11",f(".7").pow(12).div(fac(12)),".00000000003");
const ds=f(2).mul("1.001").mul("2.6").add(2).add(f("1.6").mul("1.501")).add(f(".216").mul(".9"));
const dc=f("1.6").mul("1.1").mul("1.001").add(f(".216").mul("1.8").mul("1.1"));
lt("discriminant derivative in s below10",ds,10);lt("discriminant derivative in c below3",dc,3);
lt("total trigonometric replacement error below1e-7",f(10).mul(".00000000003").add(f(3).mul(".0000000005")),".0000001");
gt("side quadratic leading coefficient positive",f(".39").mul(".76").pow(1).mul(".76").sub(".05334"),0);
gt("sin phi>.76 throughout lower half",sinI(lo),".76");
const P9=PP.slice(0,10);P9[0]=P9[0].sub(".0000002");
const bs=bern(P9,0,".7"),printed=[".0001770",".0059290",".0067752",".0049065",".0024489",".0010489",".0014710",".0033222",".0050111",".0038894"];
for(let i=0;i<bs.length;i++)gt("side discriminant Bernstein "+i,bs[i],printed[i]);
tables.push({name:"side discriminant degree9",degree:9,interval:["0",".7"],power_coefficients:P9.map(t=>t.str()),bernstein_coefficients:bs.map(t=>t.str()),printed_lower:printed});
const lambda=f(".9545"),q=f(".853");
function NN(phi){return rootI(is(lambda.pow(2).add(q.pow(2)),im(lambda.mul(q).mul(2),cosI(phi))));}
function FF(phi){return is(ia(ia(phi,cm.sub(".02478").add(lambda.add(q).div(2))),im(lambda,sinI(phi))),im(rootI(Q),NN(phi)));}
gt("axis3 chord slope source",f(".853"),f(".93015").sub(f(".08692").mul(d[0])));
gt("axis3 chord slope core side",f(".98439").sub(f(".05334").mul(".5")),".9545");
gt("axis3 scalar concavity through1.5",is(im(lambda,sinI(lo)),id(im(rootI(Q),NN("1.5")),4)),0);
gt("axis3 early left endpoint>.96",FF(lo),".96");
gt("axis3 early right endpoint>.907",FF("1.5"),".907");
lt("L(.7)<.604399",L(".7"),".604399");
gt("axis3 near-quarter direct bound for b<=.7",f("1.5").sub(".604399").add(cm),gamma);
gt("L'(.7)>.903",Lp(".7"),".903");
lt("source ratio derivative negative",f(".04726").add(".22110").sub(f(".93015").sub(f(".11055").mul("1.415")).mul(".557")),0);
lt("source ratio Lprime/r at axis<3",im(Lp(0),id(ia(a0,".5"),".5")),3);
gt("source radial ratio at axis>.261",id(".5",ia(a0,".5")),".261");
gt("sin1.5>.997",sinI("1.5"),".997");lt("cos1.5<.071",cosI("1.5"),".071");
lt("axis3 lower contact B<.21",f("1.0345").sub(f(".899").mul(".926")),".21");
gt("axis3 contact decreases toward quarter",f(".98439").sub(f(".10668").mul(".21")).mul("1.2").mul(".997"),1);
gt("axis3 B0 contact decreases toward quarter",f(".903").mul("1.2").mul(".997").div("1.071"),1);
lt("upper half sinx<.1",sinI(".1"),".1");gt("upper half cosx>.995",cosI(".1"),".995");
lt("upper axis2 impossible",f("1.415").mul(".1").add(ac),1);
lt("upper axis3 positive contact B<.156",f("1.05").sub(f(".899").mul(".995")),".156");
lt("upper axis4 positive contact B<.152",f("1.05").sub(".899").div(".995"),".152");
gt("upper axis3 fixed-b contact cost increases",f(1).sub(f(".98439").mul(".4")),0);
lt("upper axis4 negative target derivative magnitude<.177",f(".915").mul(".1").add("1/12").div(f(".995").pow(2)),".177");
gt("upper axis4 fixed-b contact cost increases",f(1).sub(f(".98439").mul(".177")),0);
lt("upper B0 axis3 actual a<1.056",f("1.05").div(".995"),"1.056");
gt("a(.7)>1.056",a(".7"),"1.056");
gt("upper B0 axis3 r>.77",f("1.2").div("1.556"),".77");
gt("upper B0 axis3 denominator>.666",f(".77").mul(".995").sub(".1"),".666");
lt("L'(d)<1.073",Lp(d),"1.073");
gt("upper B0 axis3 derivative positive",f(1).sub(f("1.073").mul(".4").div(".666")),0);
gt("upper B0 axis4 derivative positive",f(1).sub(f(3).mul(f(".05").add("1/12"))),0);
lt("upper axis3 diagonal cannot block B0 continuation",f(".4").mul("1.1"),".5");
lt("upper axis4 diagonal cannot block B0 continuation",f(".9").add(ac.mul(".1")),1);
return {status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge2 O-minus to core-side-minus, all four axes and entire quarter-one interval; combined with the separate core-corner theorem this is the complete negative target family.",comparisons:checks.length,checks,tables};
})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;
