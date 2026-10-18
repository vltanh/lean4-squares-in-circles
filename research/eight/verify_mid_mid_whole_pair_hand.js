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
const {oneNormPolynomial}=(function({F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern}){
const P0=x=>[f(x)];
const P1=x=>[f(x),f(1)];
const sq=a=>mul(a,a);
const sm=(...a)=>a.reduce(add,[f(0)]);
function oneNormPolynomial({p,q,c,tau,axis,quadrant,lam,sourceFloor,gamma=".9005",sinSign=1,cosSign=-1}){
 p=f(p);q=f(q);c=f(c);gamma=f(gamma);let b=f(".18"),half=f(".5");
 lam=lam.map(f);sourceFloor=sourceFloor.map(f);
 let sn,cs;
 if(axis==="f"){
 sn=add(lam,P0("-.09"));
 cs=scale(add(scale(lam,quadrant-tau),P0(b.mul(-quadrant))),half);
 } else{
 sn=scale(add(scale(lam,1-tau),P0(b.neg())),half);
 cs=scale(add(scale(lam,quadrant-1),P0(b.mul(-quadrant))),half);
 }
 let T=sm(P1(b.div(2).sub(c.mul(tau)).add(p.add(q).mul(tau).div(2)).sub(gamma)),sourceFloor,scale(lam,half));
 T=add(T,mul(sn,trigpoly("sin",sinSign>0?7:9)));
 T=add(T,mul(cs,trigpoly("cos",cosSign>0?6:8)));
 let V=sm(P0(p.pow(2).add(q.pow(2))),sq(lam));
 if(axis==="f"){
 V=add(V,scale(mul(lam,trigpoly("sin",tau>0?9:7)),p.mul(2*tau)));
 V=add(V,scale(mul(lam,trigpoly("cos",10)),q.mul(-2)));
 } else{
 V=add(V,scale(mul(lam,trigpoly("cos",tau>0?10:8)),p.mul(-2*tau)));
 V=add(V,scale(mul(lam,trigpoly("sin",7)),q.mul(-2)));
 }
 return {P:add(sq(T),scale(V,"-3.9156")),T,V,sn,cs};
}
return {oneNormPolynomial};

})(arithmetic);
const configs=[
  {
    "id": "MMf++",
    "p": "1.489593",
    "q": "1.580219",
    "c": "-2.143075",
    "tau": 1,
    "axis": "f",
    "quadrant": 1,
    "lam": [
      ".87"
    ],
    "sourceFloor": [
      "208720273/25000000000"
    ],
    "gamma": ".8912",
    "lo": ".6",
    "hi": "1.09"
  },
  {
    "id": "MMprimary+",
    "p": "1.489593",
    "q": "1.580219",
    "c": "-2.143075",
    "tau": 1,
    "axis": "e",
    "quadrant": -1,
    "lam": [
      "1"
    ],
    "sourceFloor": [
      "-827383531/500000000"
    ],
    "gamma": ".8912",
    "sinSign": -1,
    "lo": "1.57",
    "hi": "1.85"
  }
];
const polynomialRows=[
  {
    "id": "MMf++",
    "degree": 16,
    "lo": ".6",
    "hi": "1.09",
    "bern_lower_numerators": [
      97837,
      100029,
      101671,
      102928,
      103966,
      104945,
      106025,
      107361,
      109106,
      111414,
      114433,
      118313,
      123199,
      129239,
      136578,
      145361,
      155733
    ],
    "denominator": 1000000,
    "T_degree": 8,
    "T_lower": 4
  },
  {
    "id": "MMprimary+",
    "degree": 18,
    "lo": "1.57",
    "hi": "1.85",
    "bern_lower_numerators": [
      248977,
      257702,
      265257,
      271671,
      276972,
      281190,
      284354,
      286491,
      287630,
      287799,
      287024,
      285333,
      282752,
      279306,
      275022,
      269924,
      264037,
      257385,
      249991
    ],
    "denominator": 1000000,
    "T_degree": 9,
    "T_lower": 3
  }
];
const result=(function(arithmetic,oneNormPolynomial,configs,polynomialRows){
const {F,f,trig,bern}=arithmetic;

const checks=[];
function gt(name,a,b=0){a=f(a);b=f(b);const gap=a.sub(b);checks.push({name,pass:gap.gt(0),gap:gap.str()})}
function lt(name,a,b=0){gt(name,b,a)}
const Q=f("3.9156"),p=f("1.489593"),q=f("1.580219"),cM=f("-2.143075"),beta=f(".18"),gamma=f(".8912");
const all=f("1.298747247"),alh=f("1.298747249"),ahl=f("1.199256060"),ahh=f("1.199256062");
const bll=all.div(4),blh=alh.div(4),bhl=ahl.mul(3).div(7),bhh=ahh.mul(3).div(7);
const Emll=cM.add(p.mul(all)).add(q.mul(bll)),Emlh=cM.add(p.mul(alh)).add(q.mul(blh));
const Emhl=cM.add(p.mul(ahl)).add(q.mul(bhl)),Emhh=cM.add(p.mul(ahh)).add(q.mul(bhh));
const Slo=x=>trig(x,"sin",7),Shi=x=>trig(x,"sin",9),Clo=x=>trig(x,"cos",10),Chi=x=>trig(x,"cos",8);
for(const [tag,a,b,side]of [["low lower",all,bll,0],["low upper",alh,blh,1],["high lower",ahl,bhl,0],["high upper",ahh,bhh,1]])(side?gt:lt)("root "+tag,a.add(".5").pow(2).add(b.add(".5").pow(2)),Q);
gt("M lower label>.3046",Emll,".3046");lt("M lower label<.30461",Emlh,".30461");
gt("M high label>.4555",Emhl,".4555");lt("M high label<.455511",Emhh,".455511");
gt("r>.458",bll.add(".5"),f(".458").mul(alh.add(".5")));
lt("r<.597",bhh.add(".5"),f(".597").mul(ahl.add(".5")));
lt("lower-cut r<.459",blh.add(".5"),f(".459").mul(all.add(".5")));
gt("M derivative>.69",q.sub(p.mul(".597")),".69");
lt("M derivative<.898",q.sub(p.mul(".458")),".898");
lt("r derivative<.8",Q,f(".8").mul(ahl.add(".5").pow(3)));
lt("high b<.513966884",bhh,".513966884");
gt("a+.5>1.699",ahl.add(".5"),"1.699");
lt("a-.5<.799",alh.sub(".5"),".799");
lt(".5-low b<.176",f(".5").sub(bll),".176");
gt("low b>.3246",bll,".3246");
lt("high b<.514",bhh,".514");
gt("one minus high b>.486",f(1).sub(bhh),".486");
gt("one minus high b>low b",f(1).sub(bhh),blh);
lt("one minus high b<high b",f(1).sub(bhl),bhl);
const atan=(x,d)=>{let s=f(0);x=f(x);for(let j=1;j<=d;j+=2)s=s.add(x.pow(j).mul(new F(((j-1)/2)%2?-1n:1n,BigInt(j))));return s};
lt("angle width<.16",atan(new F(3n,7n),9).sub(atan(".25",7)),".16");
lt("upper angle<.405",atan(new F(3n,7n),9),".405");
gt("lower angle>.24",atan(".25",3),".24");
gt("pi>3.14",atan(".2",7).mul(16).sub(new F(4n,239n)),"3.14");
lt("pi<3.16",atan(".2",9).mul(16).sub(atan(new F(1n,239n),3).mul(4)),"3.16");
gt("sqrt2<1.42",f("1.42").pow(2),2);
gt("same-sign direct tail",f("1.09").sub(".0378").sub(".455511").add(".3046"),gamma);
gt("positive-negative direct tail",f(".32").sub(".0378").add(f(".3046").mul(2)),gamma);
gt("negative-positive direct tail",f("1.85").sub(".0378").sub(f(".455511").mul(2)),gamma);
gt("parallel contact projection derivative>.75",f(1).sub(f(".32").pow(2).div(2)).sub(f(".597").mul(".32")),".75");
lt("lower-left contact impossible, positive phi",f("-.175").add(f(".799").mul(".32")).sub(f(".175").mul(f(1).sub(f(".32").pow(2).div(2)))),0);
lt("lower-left contact impossible, negative phi",blh.mul(2),1);
gt("contact concavity factor p>M' sin",p,".898");
const apr=f("1.215616124");
lt("parallel complementary radical lower",apr.add(".5").pow(2).add(f("1.5").sub(bhl).pow(2)),Q);
gt("parallel endpoint cost>.89124",cM.mul(2).add(q).add(p.mul(ahl.add(apr))),".89124");
const negativeN=f("1.699").mul(f(1).sub(f(".05").pow(2).div(2))).sub(f(".014").mul(".05"));
gt("negative contact derivative numerator positive",negativeN,0);
lt("negative phi fixed-target cost derivative",f("1.09").sub(f(".69").mul(negativeN)),0);
lt("negative phi fixed-source cost derivative",f("1.09").sub(f(".69").mul(negativeN).div(f(1).add(f(".597").mul(".05")))),0);
gt("positive contact normal numerator",f(".699").mul(f(1).sub(f(".32").pow(2).div(2))).sub(f(".014").mul(".32")),0);
gt("positive fixed-target cost derivative",f(".91").sub(f(".898").mul(f(".799").add(f(".176").mul(".32")))),0);
lt("tan(.32)<.332",Shi(".32"),f(".332").mul(Clo(".32")));
gt("positive normalized D>.801",f(1).sub(f(".597").mul(".332")),".801");
lt("positive normalized N<.858",f(".799").add(f(".176").mul(".332")),".858");
lt("J derivative negative",f(".8").mul(".332").mul(".858"),f(".458").mul(".801"));
lt("positive fixed-source cost factor<.91",f(".898").mul(f(".799").add(f(".176").mul(".332"))),f(".91").mul(f(1).sub(f(".459").mul(".332"))));
lt("negative source-f impossible",f(".799").pow(2).add(f(".014").pow(2)),f(".8246").pow(2));
gt("M+.87f selects high endpoint",f(".87").mul(bhl.sub(blh)),Emhh.sub(Emll));
lt("negative primary source selects high endpoint",p.add(1).mul(".597"),q);
lt("primary negative target, negative angle impossible",f(".799").sub(f("1.699").mul(f(1).sub(f(".05").pow(2).div(2)))),0);
lt("primary negative target impossible to1.05",f(".799").sub(f("1.699").mul(Clo("1.05"))).add(".014"),0);
lt("primary positive target impossible in quadrant I",f(".799"),".8246");
const roots=[{tag:"low",aL:all,bL:bll,bH:blh,eL:f(".3046")},{tag:"high",aL:ahl,bL:bhl,bH:bhh,eL:f(".4555")}];
for(const z of roots){
const coefficient=f(".41").sub(z.bH);
const sinTerm=coefficient.gt(0)?f(0):coefficient;
const v=f("1.05").add(".59").sub(".455511").sub(ahh).add(z.eL).add(sinTerm).add(f(".41").add(z.aL).mul(Clo("1.09")));
gt("short primary negative-target endpoint "+z.tag,v,"1.07");
}
const polyResults=[];
for(let i=0;i<configs.length;i++){
const z=oneNormPolynomial(configs[i]),decl=polynomialRows[i],bp=bern(z.P,decl.lo,decl.hi),bt=bern(z.T,decl.lo,decl.hi);
if(bp.length!==decl.bern_lower_numerators.length)throw Error("polynomial degree mismatch");
bp.forEach((v,j)=>gt(decl.id+" P Bernstein "+j,v,new F(BigInt(decl.bern_lower_numerators[j]),1000000n)));
bt.forEach((v,j)=>gt(decl.id+" T Bernstein "+j,v,decl.T_lower));
polyResults.push(decl);
}
return {status:checks.every(z=>z.pass)?"PASS":"FAIL",comparison_count:checks.length,polynomial_rows:polyResults,checks};

})(arithmetic,oneNormPolynomial,configs,polynomialRows);
console.log(JSON.stringify(result,null,2));
if(result.status!=="PASS")throw Error("Middle/middle hand arithmetic failed");
