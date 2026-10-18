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
return {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern};})();
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
return {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI};})();
const {I,ia,ineg,is,im,id,ip,rootI,sinI,cosI,PI}=intervals;
const result=(function(){
const checks=[],tables=[];
function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),g=f("1.0424"),gam=f(".89765"),R=rootI(Q),ac=f("7/12");
const d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),halfpi=id(PI,2),lo=is(halfpi,".7");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}
function L(b){return is(ia(".02478",ia(im(".93015",b),im(".02363",ip(b,2)))),im(".11055",im(a(b),b)));}
lt("outer axial a<1.415",a0,"1.415");gt("outer diagonal>.899",d,".899");lt("outer diagonal<.9",d,".9");
lt("core radius below.8",im(2,ip(dc,2)),f(".8").pow(2));
gt("L convex source derivative positive floor",f(".93015").sub(f(".11055").mul("1.415")),".773");
lt("L chord slope on [0,.5]<.8085",id(is(L(".5"),".02478"),".5"),".8085");
lt("L chord slope on [0,.7]<.8281",id(is(L(".7"),".02478"),".7"),".8281");
lt("L chord slope on [0,d]<.853",is(".93015",im(".08692",d)),".853");
function Ax2(x){return is(ia(ia(halfpi,x),f("-.01029").add(".4265")),ia(im(g,dc),ia(im(f(".853"),im(is(a0,".5"),id(sinI(x),cosI(x)))),id(".853",im(12,cosI(x))))));}
gt("axis2 concave scalar left>1.33",Ax2(0),"1.33");gt("axis2 concave scalar right>1.35",Ax2(".7"),"1.35");
function NNlow(phi,q){return rootI(is(g.pow(2).add(f(q).pow(2)),im(g.mul(q).mul(2),cosI(phi))));}
function F3low(phi,q){return is(ia(ia(phi,f("-.01029").add(g.add(q).div(2))),im(g,sinI(phi))),im(R,NNlow(phi,q)));}
gt("axis3 lower chord concavity",is(im(g,sinI(lo)),id(im(R,NNlow(halfpi,".8085")),4)),0);
gt("axis3 lower chord left>.982",F3low(lo,".8085"),".982");gt("axis3 lower chord quarter>.9179",F3low(halfpi,".8085"),".9179");
gt("axis3 large-source contact derivative at left>1",ia(id(cosI(lo),2),sinI(lo)),1);
gt("axis3 large-source contact cost decreases",g,1);
function Nup(x){return rootI(ia(g.pow(2).add(f(".853").pow(2)),im(g.mul(".853").mul(2),sinI(x))));}
function F3up(x){return is(ia(ia(ia(halfpi,x),f("-.01029").add(g.add(".853").div(2))),im(g,ia(sinI(x),cosI(x)))),im(R,Nup(x)));}
gt("axis3 upper whole concavity",is(g,id(im(R,g.add(".853")),4)),0);
gt("axis3 upper chord at .02>.8999",F3up(".02"),".8999");gt("axis3 upper chord at.7>1.272",F3up(".7"),"1.272");
gt("lower axis4 core corner barrier at left>1.5",ia(".5",ia(im(ia(dc,".5"),cosI(lo)),sinI(lo))),"1.5");
lt("lower axis4 core corner barrier excludes axial source",a0,"1.5");
gt("lower axis4 side contact upper comparison 13/12>1",f("13/12"),1);
lt("a(.7)<1.074",a(".7"),"1.074");
gt("lower axis4 contact derivative>1/g globally for b>=.7",f("13/12").sub(f(1).div(g)).sub(g.mul(f(".574").pow(2)).div(4)),0);

const s10=trigpoly("cos",10),c8=trigpoly("cos",8),s11=trigpoly("sin",11),s9=trigpoly("sin",9);
for(const [name,q,xsign,scoeff,degree,losslimit,left,floors] of [
 ["lower",f(".8281"),-1,g.mul("13/12"),11,f(".00031"),f(0),[".03216",".09189",".12506",".14048",".14758",".15443",".16617",".18482",".21039"]],
 ["upper",f(".853"),1,g.div(-12),9,f(".000011"),f(".02"),[".03108",".44049",".83611","1.19488","1.49153","1.70162","1.80557","1.79252","1.66077"]]
]){
 const K=PI[0].div(2).sub(".01029").add(g.add(q).div(2)).sub(gam);
 const A=add(add(mul(s10,[K,f(xsign)]),[g]),scale(degree===11?s11:s9,scoeff));
 const P=add(mul(A,A),scale(add([g.pow(2)],scale(mul(c8,c8),q.pow(2))),Q.neg()));
 let tail=f(0);for(let j=9;j<P.length;j++)if(P[j].lt(0))tail=tail.add(P[j].neg().mul(f(".7").pow(j)));
 lt(name+" polynomial negative tail below declared allowance",tail,losslimit);
 const P8=P.slice(0,9);P8[0]=P8[0].sub(losslimit);
 const bs=bern(P8,left,".7");
 for(let j=0;j<bs.length;j++)gt(name+" primary Bernstein "+j,bs[j],floors[j]);
 tables.push({name:name+" primary squared lower polynomial",degree:8,interval:[left.str(),".7"],negative_tail:tail.str(),tail_allowance:losslimit.str(),power_coefficients:P8.map(t=>t.str()),bernstein_coefficients:bs.map(t=>t.str()),printed_lower:floors});
 gt(name+" positive angle coefficient",K.sub(".7"),".89");
}
gt("cos Taylor lower remains positive",f(1).sub(f(".7").pow(2).div(2)),".75");
gt("sine Taylor lower remains nonnegative after dividing x",f(1).sub(f(".7").pow(2).div(6)),0);
gt("upper primary unsquared lower numerator positive",g.mul(f(1).sub(f(".7").div(12))),0);
for(const z of["1.33","1.35",".982",".9179",".8999","1.272",".89777"])gt("terminal "+z+" exceeds gamma",f(z),gam);
return {status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge2 outer-minus to core-plus, side and corner, all four axes, whole quarter-one interval; uses the previously proved closed .02 quarter strip and aligned theorem.",comparisons:checks.length,checks,tables};
})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;
