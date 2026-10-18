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
const result=(function(){const {F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern}=arithmetic;
const checks=[];
function gt(name,a,b=0){a=f(a);b=f(b);let gap=a.sub(b);checks.push({name,pass:gap.gt(0),gap:gap.str()});}
function lt(name,a,b=0){gt(name,b,a);}
const Q=f("3.9156"),ac=f("7/12"),gamma=f(".89765"),pi=f("3.14159");
const atan=(x,d)=>{x=f(x);let z=f(0);for(let j=1;j<=d;j+=2)z=z.add(x.pow(j).mul(new F(((j-1)/2)%2?-1n:1n,BigInt(j))));return z;};
gt("Machin lower bound for pi",atan(".2",7).mul(16).sub(new F(4n,239n)),pi);
const I=(l,h=l)=>[f(l),f(h)];
const ia=(x,y)=>[x[0].add(y[0]),x[1].add(y[1])];
const ineg=x=>[x[1].neg(),x[0].neg()];
const is=(x,y)=>ia(x,ineg(y));
const im=(x,y)=>{let z=[x[0].mul(y[0]),x[0].mul(y[1]),x[1].mul(y[0]),x[1].mul(y[1])].sort((a,b)=>a.cmp(b));return[z[0],z[3]];};
const id=(x,y)=>{if(!y[0].gt(0))throw Error("nonpositive interval denominator");return im(x,[f(1).div(y[1]),f(1).div(y[0])]);};
const scaleI=(x,k)=>im(x,I(k)), pow2=x=>im(x,x);
function root(name,r,lo,hi){gt(name+" lower positive",lo,0);lt(name+" squared lower",f(lo).pow(2),r);gt(name+" squared upper",f(hi).pow(2),r);return I(lo,hi);}
function outer(name,b,lo,hi){
 b=f(b);const a=is(root(name+" radical",Q.sub(b.add(".5").pow(2)),f(lo).add(".5"),f(hi).add(".5")),I(".5"));
 const r=id(I(b.add(".5")),ia(a,I(".5")));
 const rp=id(I(Q),im(pow2(ia(a,I(".5"))),ia(a,I(".5"))));
 return {a,r,rp,b:I(b)};
}
const a0=outer("axis",0,"1.41457567100","1.41457567101").a;
const d=is(root("outer diagonal",Q.div(2),"1.39921406510","1.39921406512"),I(".5"));
const cc=ia(I(".5"),root("core diagonal",f(1).div(288),".05892556509",".05892556511"));
const b0=is(root("outer a=1",Q.sub("2.25"),"1.29058126439","1.29058126440"),I(".5"));
gt("a0<1.415",f("1.415"),a0[1]);gt("d>.899",d[0],".899");lt("d<.9",d[1],".9");
lt("core coordinate<.559",cc[1],".559");gt("b0>.790",b0[0],".790");lt("b0<.791",b0[1],".791");
lt("a0-1<.415",a0[1].sub(1),".415");
gt("outer r>.261",f(".5"),f(".261").mul(a0[1].add(".5")));
gt("outer r'>.557",Q,f(".557").mul(a0[1].add(".5").pow(3)));
gt("r'>1.16 when a<=1",Q,f("1.16").mul(f("1.5").pow(3)));
gt("r<.861 when b<=b0",f(".861").mul("1.5"),b0[1].add(".5"));
gt("r>.86 when b>=b0",b0[0].add(".5"),f(".86").mul("1.5"));
gt("L derivative positive",f(".93015").sub(f(".11055").mul("1.415")),".773");
lt("L'/r decreasing numerator",f(".04726").add(".22110").sub(f(".93015").sub(f(".11055").mul("1.415")).mul(".557")),0);
function L(o){return ia(ia(I(".02478"),scaleI(o.b,".93015")),is(scaleI(pow2(o.b),".02363"),scaleI(im(o.a,o.b),".11055")));}
function Lp(o){return is(ia(I(".93015"),scaleI(o.b,".04726")),scaleI(is(o.a,im(o.r,o.b)),".11055"));}
const oB0={a:I(1),b:b0,r:scaleI(ia(b0,I(".5")),"2/3")};
gt("L'/r at b0 >1.08",id(Lp(oB0),oB0.r)[0],"1.08");
gt("quarter E2 OC+ endpoint",is(is(I(pi.div(2).sub(".01029")),scaleI(b0,".81960")),scaleI(pow2(b0),".02363"))[0],".89777");
const cminus=f(".22042").sub(f(".34492").mul(ac));
gt("C3 minus side increasing",f(".98439").sub(f(".10668").mul(".5")),0);
gt("E2 OC- curvature>.6",
f("1.16").mul(f(".98439").sub(f(".10668").mul(".101")).sub(f(".11055").mul(".9")))
.sub(".22110").sub(".10668").sub(".04726"),".6");
function G(o){const B=is(I(1),o.a);return is(ia(is(I(pi.div(2).add(cminus)),L(o)),scaleI(B,".98439")),scaleI(pow2(B),".05334"));}
function Gp(o){return ia(ineg(Lp(o)),im(o.r,is(I(".98439"),scaleI(is(I(1),o.a),".10668"))));}
const gpt=outer("G test", ".898", " .90042707771".trim(),".90042707772");
gt("G(.898)>.89778",G(gpt)[0],".89778");gt("G'(.898)>-.0001",Gp(gpt)[0],"-.0001");lt("G'(.898)<.0001",Gp(gpt)[1],".0001");
gt("G strong convexity lower bound",f(".89778").sub(f(".0001").pow(2).div("1.2")),gamma);
gt("E2 CO+ curvature>.5",f(".557").mul("1.02956"),".5");
function H2(o){return is(is(is(I(pi.div(2).add("1.03856")),scaleI(o.a,"1.02956")),scaleI(o.b,".16031")),scaleI(im(o.a,o.b),".63457"));}
function H2p(o){return is(im(o.r,ia(I("1.02956"),scaleI(o.b,".63457"))),ia(I(".16031"),scaleI(o.a,".63457")));}
const h2pt=outer("H2 test",".5725","1.16293227462","1.16293227464");
gt("H2(.5725)>.89778",H2(h2pt)[0],".89778");gt("H2' >-.0001",H2p(h2pt)[0],"-.0001");lt("H2' <.0001",H2p(h2pt)[1],".0001");
gt("H2 strong convexity lower bound",f(".89778").sub(f(".0001").pow(2)),gamma);
gt("outer O3- nonconstant coefficient positive",f("2.42322").sub(f(".91744").mul(".9")).sub(f(".95769").mul("1.415")),0);
lt("core C0+ <.583",f(".00125").add(f("1.03981").mul(".559")),".583");
gt("E2 CO- direct",pi.div(2).sub(".583").add(".01670"),gamma);
lt("C3- upper<.58",f(".22042").sub(f(".34492").mul(".558")).add(f(".98439").mul(".559")),".58");
gt("C3+ lower",f("-.01449"),"-.0145");
gt("O3+ lower>-.01451",f("-.01025").mul("1.415"),"-.01451");
gt("O4- lower>-.03",f("-.02112").mul("1.415"),"-.03");
lt("C4+ upper<.58",f(".04970").add(f(".94831").mul(".559")),".58");
gt("E3 CO target-negative direct",pi.div(2).sub(".58").sub(".03"),gamma);
gt("E3 OC source-positive direct",pi.div(2).sub(".01451").sub(".58"),gamma);
const quadMinimum=(c,l,q)=>f(c).sub(f(l).pow(2).div(f(q).mul(4)));
for(const [name,qv,D,e,target] of [["O3-", "2.42322",".91744",".95769",".5"],["O4+","3.85510","1.49748","1.89442",".53"]]){
 const C=f(qv).sub(f(e).mul("1.415"));
 const lin=f(e).mul(".522").sub(f(D).mul(2));
 const quad=f("1.5").mul(e).mul(".557");
 gt(name+" derivative lower quadratic",quadMinimum(C,lin,quad),target);
}
const O3minus=o=>is(ia(I(".0167"),scaleI(o.b,"2.42322")),ia(scaleI(pow2(o.b),".91744"),scaleI(im(o.a,o.b),".95769")));
const od={a:d,b:d};
lt("O3- diagonal upper<.68",O3minus(od)[1],".68");
gt("E3 OC both-negative direct",pi.div(2).sub(".68").add(".16823"),gamma);
function V(o){return is(ia(I(".03965"),scaleI(o.b,"3.85510")),ia(scaleI(pow2(o.b),"1.49748"),scaleI(im(o.a,o.b),"1.89442")));}
function J(o){return is(ia(I(pi.div(2).sub(".01449")),scaleI(is(I(1),o.a),"1.0424")),V(o));}
lt("E3 CO++ contact concavity",f("2.99496").sub(f("3.78884").mul(".86")).add(f("1.16").mul(f("1.0424").sub(f("1.89442").mul(".790")))),0);
gt("J at b0",J(oB0)[0],".9025");gt("J at diagonal",J(od)[0],".89779");
function H3(o){const b=is(o.a,I(1));return is(ia(is(I(pi.div(2).sub(cminus)),scaleI(b,".98439")),scaleI(pow2(b),".05334")),V(o));}
function H3p(o){const T=is(is(I("1.09107"),scaleI(o.a,".10668")),scaleI(o.b,"1.89442"));return ia(ia(I("-3.85510"),scaleI(o.b,"2.99496")),ia(scaleI(o.a,"1.89442"),im(o.r,T)));}
function H3pp(o){const T=is(is(I("1.09107"),scaleI(o.a,".10668")),scaleI(o.b,"1.89442"));return ia(is(I("2.99496"),scaleI(o.r,"3.78884")),ia(scaleI(pow2(o.r),".10668"),im(o.rp,T)));}
lt("H3''' negative after division by r'",f("-5.68326").add(".32004").add(f("3").mul("1.09107").div("1.399")),0);
const split=outer("H3 split",".63","1.12440758432","1.12440758433");
gt("H3''(.63)>.2",H3pp(split)[0],".2");gt("H3'(.63)>0",H3p(split)[0],0);
const h3pt=outer("H3 test",".604","1.14218878330","1.14218878331");
gt("H3(.604)>.897788",H3(h3pt)[0],".897788");gt("H3'(.604)>-.000013",H3p(h3pt)[0],"-.000013");lt("H3'(.604)<.000013",H3p(h3pt)[1],".000013");
gt("H3 strong convexity lower bound",f(".897788").sub(f(".000013").pow(2).div(".4")),gamma);
gt("H3 at b0>.8978",H3(oB0)[0],".8978");
function Kfun(o){return is(is(I(pi.div(2).add(".89861")),scaleI(o.a,".94831")),O3minus(o));}
function Kp(o){return ia(ia(I("-2.42322"),scaleI(o.b,"1.83488")),ia(scaleI(o.a,".95769"),im(o.r,is(I(".94831"),scaleI(o.b,".95769")))));}
gt("K curvature>.29",f("1.83488").sub(f("1.91538").mul(".861")).add(f(".557").mul(f(".94831").sub(f(".95769").mul(".791")))),".29");
const kp=outer("K test",".575","1.16131724845","1.16131724846");
gt("K(.575)>.9008",Kfun(kp)[0],".9008");gt("K'(.575)>-.003",Kp(kp)[0],"-.003");lt("K'(.575)<.003",Kp(kp)[1],".003");
gt("K strong convexity lower bound",f(".9008").sub(f(".003").pow(2).div(".58")),gamma);

const width=f(".02"),cb=f(".9998"),gp=f("1.0424"),g0=f("1.03981");
gt("cos(.02)>=.9998",f(1).sub(width.pow(2).div(2)),".9997999");
gt("quarter signed denominator positive",cb.sub(width),".979");
lt("OC axis1 impossible",ac.add(f(".559").mul(width)),1);
lt("OC axis2 impossible",ac.add(f("1.415").mul(width)),1);
gt("core diagonal>.558",cc[0],".558");
lt("OC3 positive core end infeasible",f("1.415").add(f(".9").mul(width)).sub(".558"),1);
lt("OC4 positive core end infeasible",f("1.415").add(f(".559").mul(width)).sub(f(".558").mul(cb)),1);
lt("OC3 zero core at outer diagonal infeasible",f(".9").add(f(".9").mul(width)),1);
lt("OC4 zero core at outer diagonal infeasible",f(".9").add(ac.mul(width)),1);
lt("OC3 positive contact core coordinate<.5",f("1.415").add(f(".9").mul(width)).sub(1),".5");
lt("OC3 negative contact core coordinate<.13",f("1.01").sub(f(".899").mul(cb)).add(f(".9").mul(width)),".13");
lt("OC4 positive contact core coordinate<.5",f("1.415").add(ac.mul(width)).sub(1),cb.mul(".5"));
lt("OC4 negative contact core coordinate<.13",f("1.01").sub(".899").add(ac.mul(width)),cb.mul(".13"));
gt("core negative side derivative>.97",f(".98439").sub(f(".10668").mul(".13")),".97");
gt("OC3 positive-half derivative",f(1).sub(gp.mul(".4")),0);
gt("OC3 negative-half positive target b>=.49",gp.mul(".99").mul(cb),1);
lt("negative target OC3 forces a<1.029",f("1.01").add(f(".9").mul(width)),cb.mul("1.029"));
gt("a(outer b=.75)>1.03",Q,f("1.53").pow(2).add(f("1.25").pow(2)));
gt("OC3 negative-half negative target derivative sign",f(".97").mul("1.25").mul(cb),1);
const smallOC=outer("small OC split",".49","1.21333009078","1.21333009080");
const oc0=is(ia(is(I(pi.div(2)),L(smallOC)),I(".01449")),scaleI(is(smallOC.a,I(1)),"1.0424"));
gt("small OC aligned endpoint>.942",oc0[0],".942");
gt("small OC whole strip",f(".942").sub(width),gamma);
const numeratorPlus=f(".915").mul(width).add(f("1/12"));
const numeratorMinus=f("13/12").sub(f(".915").mul(width));
lt("OC4 positive F_e<.102",numeratorPlus,cb.pow(2).mul(".102"));
gt("OC4 negative F_e>1.065",numeratorMinus,"1.065");
gt("OC4 positive-half cost derivative",f(1).sub(gp.mul(".102")),0);
gt("OC4 negative-half cost derivative",f(".97").mul("1.065"),1);
gt("OC3 zero-core unique root, outer axis",a0[0].mul(cb),"1.01");
lt("OC3 zero-core root a<1.029",f("1.028"),cb.mul("1.029"));
gt("OC3 zero-core root a>.982",f(1).sub(f(".9").mul(width)),".9819999");
gt("a(.83)<.982",f("1.482").pow(2).add(f("1.33").pow(2)),Q);
gt("OC3 zero-core root r>.817",f("1.25"),f(".817").mul("1.529"));
lt("OC3 zero-core root r<.9",f("1.33"),f(".9").mul("1.482"));
lt("outer L' global upper<1.073",f(".93015").add(f(".04726").mul(".9")).add(f(".11055").mul(".9")),"1.073");
gt("OC3 zero-core negative-half derivative sign",f(".773").mul("1.25").mul(cb),".92");
gt("OC3 zero-core positive-half derivative sign",f(".817").mul(cb).sub(width),f("1.073").mul(".33"));
gt("L'/r global lower>.972",f(".93015").add(f(".04726").mul(".899")),".972");
lt("L'/r global upper<3",f(".93015").sub(f(".11055").mul(a0[0])),f(3).mul(".261"));
gt("OC4 zero-core a lower above diagonal",f(1).sub(ac.mul(width)),d[1]);
lt("OC4 zero-core a upper below axis",f("1.01").add(ac.mul(width)),a0[0]);
gt("OC4 zero-core negative-half derivative sign",f(".972").mul(f("13/12").mul(cb).sub(".01")),1);
gt("OC4 zero-core positive-half derivative sign",f(1).sub(f(3).mul(f("1/12").add(".01"))),0);
gt("CO target-negative whole strip",pi.div(2).sub(width).sub(".583").add(".01670"),gamma);
lt("CO+ axis3 impossible",ac.add(f(".559").mul(width)),1);
lt("CO+ axis4 impossible",ac.add(f("1.415").mul(width)),1);
lt("CO+ axis1 contact on core side",f("1.415").add(f(".9").mul(width)).sub(1),".5");
lt("CO+ axis2 every feasible core on side",f("1.415").add(ac.mul(width)).sub(1),cb.mul(".5"));
gt("CO+ axis1 positive-half derivative",f(1).sub(g0.mul(".4")),0);
gt("CO+ axis1 negative-half B>=.462 derivative sign",g0.mul(".962").mul(cb),1);
const smallCO=outer("small CO split",".462","1.22920675455","1.22920675456");
gt("small CO aligned endpoint>.9093",H2(smallCO)[0],".9093");lt("small CO aligned derivative negative",H2p(smallCO)[1],0);
lt("CO+ axis1 negative-half derivative upper<.481",f(1).sub(g0.mul(".5").mul(cb)),".481");
gt("small CO whole strip",f(".9093").sub(width.mul(".481")),gamma);
gt("CO+ axis2 positive-half derivative",f(1).sub(g0.mul(".102")),0);
gt("CO+ axis2 negative-half derivative sign",g0.mul("1.065"),1);
const opdiag=ia(scaleI(d,".15006"),scaleI(pow2(d),".63457"));
lt("O3+ maximum<.64805",opdiag[1],".64805");
gt("CO+ zero-core-coordinate exit cost",pi.div(2).sub(width).sub(".00125").sub(".64805"),gamma);
return {status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"All permitted mixed edge2 quarter-one transitions for |phi-pi/2|<=1/50; includes aligned prerequisites.",comparisons:checks.length,checks};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;
