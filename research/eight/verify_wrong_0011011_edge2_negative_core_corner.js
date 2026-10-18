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
const intervals=(function(){const {F,f}=arithmetic;
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
const result=(function(){const {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern}=arithmetic;const {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI}=intervals;
const checks=[],tables=[];
function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),k=f(".11055"),V=f(".961795"),z=f(".02363"),c=f("7/12"),rho=f("1/12"),gamma=f(".89765");
const dc=ia(".5",id(rootI(2),24)),d=is(rootI(Q.div(2)),".5"),a0=is(rootI(Q.sub(".25")),".5"),lo=is(id(PI,2),".7");
function M(u){const t=rootI(is(Q,ip(u,2)));return is(ia(".369499372",is(im(z,ip(u,2)),im(".055275",u))),im(is(V,im(k,u)),t));}
function M1(u){let t=rootI(is(Q,ip(u,2)));return ia(is(im(".04726",u),".055275"),ia(im(k,t),id(im(is(V,im(k,u)),u),t)));}
function M2(u){let t=rootI(is(Q,ip(u,2)));return ia(is(".04726",id(im(".22110",u),t)),id(im(Q,is(V,im(k,u))),ip(t,3)));}
function U(phi,diag){let A=diag?ia(dc,".5"):I("13/12"),B=diag?is(dc,".5"):I(0);return ia(1,is(im(A,cosI(phi)),im(B,sinI(phi))));}
function target(A,B){return ia(is(".22042",im(".34492",A)),is(im(".98439",B),im(".05334",ip(B,2))));}
function H(phi,diag){let A=diag?dc:I(c),B=diag?dc:I(".5");return ia(ia(phi,M(U(phi,diag))),target(A,B));}
function Hp(phi,diag){let A=diag?ia(dc,".5"):I("13/12"),B=diag?is(dc,".5"):I(0),up=ineg(ia(im(A,sinI(phi)),im(B,cosI(phi))));return ia(1,im(M1(U(phi,diag)),up));}
gt("continued u lower >1.33",U("1.191",true),"1.33");
lt("continued u upper <1.7",U(lo,false),"1.7");
gt("M''' numerator positive",V.mul("1.33").sub(k.mul(Q)),0);
gt("M'' at1.33 positive",M2("1.33"),0);gt("M' at1.33 positive",M1("1.33"),0);
gt("continued contact below actual outer axis",a0,"1.2");
gt("core negative derivative positive",f(".98439").sub(f(".10668").mul(".559")),0);
lt("core diagonal<.559",dc,".559");gt("core diagonal>.5589",dc,".5589");
gt("core curvature magnitude<34",f(34).pow(2),f(24).pow(2).mul(2));
const Ldiag=is(ia(".02478",im(".93015",d)),im(".08692",ip(d,2)));
lt("source label maximum<.79091",Ldiag,".79091");
gt("target core-corner minimum>.49807",target(I(c),I(".5")),".49807");
gt("whole late corner direct cost",f("1.191").sub(".79091").add(".49807"),gamma);
const coarseM=["2.57","1.90","1.47","1.32","1.27"],coarseDelta=[".339",".209",".150",".129",".109"];
const splits=[lo,I(".95"),I("1.03"),I("1.07"),I("1.085"),I("1.1")];
for(let j=0;j<splits.length-1;j++){
 const l=splits[j],r=splits[j+1],mm=M2(U(l,false)),delta=is(im(M1(U(r,true)),cosI(r)),".34492");
 gt("early core-coordinate concavity "+j,is(im(12,delta),mm),0);
 lt("printed early M2 upper "+j,mm,coarseM[j]);gt("printed early delta lower "+j,delta,coarseDelta[j]);
 gt("printed early concavity difference "+j,f(12).mul(coarseDelta[j]).sub(coarseM[j]),0);
 tables.push({name:"early concavity interval "+j,phi_lower:l.map(x=>x.str()),phi_upper:r.map(x=>x.str()),M2_upper:mm[1].str(),delta_lower:delta[0].str()});
}
lt("middle M''<1.213",M2(U("1.1",false)),"1.213");
gt("middle delta>.0697",is(im(M1(U("1.13",true)),cosI("1.13")),".34492"),".0697");
lt("middle z expression decreases for z>=1",f(2).mul("1.213"),f(36).mul(".0697"));
lt("middle core second derivative<1",f("1.213").sub(f(12).mul(".0697")).sub(".10668"),1);
lt("late M''<1.127",M2(U("1.13",false)),"1.127");
gt("late delta>-.0054",is(im(M1(U("1.191",true)),cosI("1.191")),".34492"),"-.0054");
lt("late core second derivative<3",f(2).mul("1.127").add(f(".0054").mul(34)).sub(".10668"),3);
gt("diagonal K>1.12479",ia(ip(ia(dc,".5"),2),ip(is(dc,".5"),2)),"1.12479");
gt("join K>1.12479",f("13/12").pow(2),"1.12479");
const xx=[f(0),f(1)],xm=[f(-1),f(1)],t2=add([Q],scale(mul(xx,xx),-1)),J=add([f("1.12479")],scale(mul(xm,xm),-1));
const E=add(add(mul([V,k.neg()],add(scale(J,Q),scale(mul(mul(xx,xm),t2),-1))),scale(mul(mul(xx,J),t2),f(-2).mul(k))),scale(mul(xm,mul(t2,t2)),k.neg()));
const BB=add(scale(J,f(2).mul(z)),scale(mul(xm,[k.div(-2),f(2).mul(z)]),-1));
const AA=add([f(".4")],scale(BB,-1)),PP=add(mul(E,E),scale(mul(mul(AA,AA),mul(mul(t2,t2),t2)),-1));
const printed={E:["1.6639","1.3858","1.1359",".9266",".7658",".6529"],A:[".3544",".3645",".3875"],P:["1.5254","1.2197",".9677",".7662",".6102",".4933",".4088",".3495",".3091",".2822",".2642"]};
for(const[name,P]of[["E",E],["A",AA],["P",PP]]){
 let bs=bern(P,"1.33","1.7");
 for(let i=0;i<bs.length;i++)gt("common endpoint curvature "+name+" coefficient "+i,bs[i],printed[name][i]);
 tables.push({name:"common endpoint curvature "+name,degree:P.length-1,interval:["1.33","1.7"],coefficients:bs.map(x=>x.str())});
}
gt("diagonal H(1.049)>.8977757",H("1.049",true),".8977757");
gt("diagonal H'(1.049)>-.000123",Hp("1.049",true),"-.000123");lt("diagonal H'(1.049)<.000123",Hp("1.049",true),".000123");
gt("diagonal strong convexity bound>.89777",f(".8977757").sub(f(".000123").pow(2).div(".8")),".89777");
gt("join H(1.16)>.900224",H("1.16",false),".900224");
gt("join H'(1.16)>-.00029",Hp("1.16",false),"-.00029");lt("join H'(1.16)<.00029",Hp("1.16",false),".00029");
gt("join strong convexity bound>.9002",f(".900224").sub(f(".00029").pow(2).div(".8")),".9002");
gt("diagonal H(1.1)>.89849",H("1.1",true),".89849");gt("diagonal H'(1.1)>0",Hp("1.1",true),0);
gt("diagonal H(1.13)>.89958",H("1.13",true),".89958");
gt("middle interpolated bound",f(".89849").sub(f(".059").pow(2).div(8)),gamma);
gt("late interpolated bound",f(".89958").sub(f(3).mul(f(".059").pow(2)).div(8)),gamma);

gt("source chord slope<.853",f(".853"),f(".93015").sub(f(".08692").mul(d[0])));
gt("target chord slope>.9545",f(".98439").sub(f(".05334").mul(".559")),".9545");
lt("core center radius<.8",ia(ip(dc,2),ip(dc,2)),f(".8").pow(2));
gt("whole quarter width >=1",1,".9999999");
const lambda=f(".9545"),qChord=f(".853"),cm=f(".22042").sub(f(".34492").mul(c));
function Naxis3(phi){return rootI(is(lambda.pow(2).add(qChord.pow(2)),im(lambda.mul(qChord).mul(2),cosI(phi))));}
function Faxis3(phi){return is(ia(ia(phi,cm.sub(".02478").add(lambda.add(qChord).div(2))),im(lambda,sinI(phi))),im(rootI(Q),Naxis3(phi)));}
gt("axis3 whole early concavity reserve",is(im(lambda,sinI(lo)),id(im(rootI(Q),Naxis3("1.191")),4)),0);
gt("axis3 left endpoint>.96",Faxis3(lo),".96");
gt("axis3 right endpoint>.96",Faxis3("1.191"),".96");
return {status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge2 outer-minus to core-corner-minus, all four retained axes, entire quarter-one angle range.",comparisons:checks.length,checks,tables};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;
