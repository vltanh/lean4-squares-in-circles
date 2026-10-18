#!/usr/bin/env node
"use strict";
// Exact fixed-comparison checker for CORE_HIGH_WHOLE_PAIR_HAND_PROOF.md.
// No packages are required. Run: node verify_core_high_whole_pair_hand.js
const arithmetic = (function(){

class F {
 constructor(n,d=1n){ n=BigInt(n); d=BigInt(d); if(d===0n)throw Error("zero denominator");if(d<0n){n=-n;d=-d}let a=n<0n?-n:n,b=d;while(b){let t=a%b;a=b;b=t;}this.n=n/a;this.d=d/a; }
 static of(x){if(x instanceof F)return x;if(typeof x==="string"&&x.includes(".")){let sign=x.startsWith("-")?-1n:1n;let z=x.replace("-","").split(".");return new F(sign*BigInt(z[0]+z[1]),10n**BigInt(z[1].length));}return new F(x)}
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
const result = (function({F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern}){

const checks=[];
function gt(name,a,b=0){a=f(a);b=f(b);const gap=a.sub(b);checks.push({name,pass:gap.gt(0),gap:gap.str(),decimal_gap:gap.num()})}
function lt(name,a,b=0){gt(name,f(b),f(a))}
const Q=f("3.9156"), g=f("1.077372"),K=f("7.506931"),u=f(".569472"),v=f(".390886"),beta=f(".18");
const ac=new F(7n,12n),gamma=f(".8833"),Rhi=f("1.978788"),pilo=f("3.14159"),pihi=new F(355n,113n);
const dl=f(".899214"),dh=f(".899215"),al=f("1.199256"),ah=f("1.199257"),bl=al.mul(new F(3n,7n)),bh=ah.mul(new F(3n,7n));
const kl=pilo.div(4).add(u.sub(v).mul(dl)),kh=pihi.div(4).add(u.sub(v).mul(dh));
const Astar=g.add(beta).div(2), Cstar=g.sub(beta).div(2), nq2=g.sub(u).pow(2).add(v.pow(2));
const coremax=f(".786"), costloss=f(".0378");
gt("R upper",Rhi.pow(2),Q);
lt("diagonal lower",dl.add(".5").pow(2).mul(2),Q);gt("diagonal upper",dh.add(".5").pow(2).mul(2),Q);
lt("H lower endpoint a lower",al.add(".5").pow(2).add(bl.add(".5").pow(2)),Q);
gt("H lower endpoint a upper",ah.add(".5").pow(2).add(bh.add(".5").pow(2)),Q);
gt("H lower b>.5139",bl,".5139");lt("H upper a<1.2",ah,"1.2");
gt("H radial slope>.596",bl.add(".5"),ah.add(".5").mul(".596"));
gt("H lower label>.4639",kl.sub(u.mul(ah)).add(v.mul(bl)),".4639");
lt("H lower label<.464",kh.sub(u.mul(al)).add(v.mul(bh)),".464");
lt("H upper label<.786",pihi.div(4),".786");
lt("marker slope u+v<1",u.add(v),1);lt("marker slope u+v<g",u.add(v),g);
gt("all negative phi>-.812",f(".76").sub(pihi.div(2)),"-.812");
gt("direct upper phi tail",f("2.5").sub(coremax.mul(2)).sub(costloss),gamma);
const trigRows=[
[".812",".725",null,".688",null],["1.2",".932",".933",".362",".3625"],["1.25",null,null,".315",null],
["1.4",".985",".986",".169",".17"],["1.5",null,null,null,".071"],
["2.28",".758",null,"-.652",null],["2.4",".675",null,"-.738",null],
["2.45",".637",null,"-.771",null],["2.5",".598",".599","-.802","-.8"]];
for(const [x,sl,sh,cl,ch] of trigRows){
 if(sl!==null)gt("sin lower "+x,trig(x,"sin",15),sl);
 if(sh!==null)lt("sin upper "+x,trig(x,"sin",13),sh);
 if(cl!==null)gt("cos lower "+x,trig(x,"cos",14),cl);
 if(ch!==null)lt("cos upper "+x,trig(x,"cos",12),ch);
}
gt("cos(.812)>.67",trig(".812","cos",14),".67");
gt("cos(1.2)>.362",trig("1.2","cos",14),".362");
gt("whole marker root<.7",f(".7").pow(2),u.pow(2).add(v.pow(2)));
gt("rotating length dominates fixed length",g.pow(2),u.pow(2).add(v.pow(2)));
lt("R N/4<.9",Rhi.mul(g.add(".7")).div(4),".9");
gt("concavity trigonometric coefficient",g.sub(beta.div(2)),".9");
gt("quarter norm>.640901",nq2,f(".640901").pow(2));
lt("quarter norm<.640902",nq2,f(".640902").pow(2));
const parallel=pilo.div(4).add(g.mul(f(1).sub(dh)));
const quarter=pilo.div(4).add(g.mul("1.5")).sub(u.sub(v).mul(dh.add(".5"))).sub(Rhi.mul(".640902"));
gt("parallel common baseline>.8939",parallel,".8939");
gt("quarter common baseline>.88336",quarter,".88336");
gt("core primary small-angle impossibility",f("1.399").mul(".362").sub(".4"),new F(1n,12n));
gt("negative H direct tail",f("1.25").sub(coremax).add(".463").sub(costloss),gamma);
gt("negative H narrow branch B>.85",f(".5").add(f("1.399").mul(".315")).sub(new F(1n,12n)),".85");
gt("B>.85 forces A<1",f("1.5").pow(2).add(f("1.35").pow(2)),Q);
gt("negative H narrow branch label>.7",kl.sub(u).add(v.mul(".85")),".7");
gt("negative H narrow branch cost",f("1.2").sub(coremax).add(".7").sub(costloss),gamma);
gt("positive H primary impossible through2.45",f("1.0139").mul(".637"),new F(1n,12n).add(f(".7").mul(".771")));
lt("positive H primary B<.6",new F(1n,12n).add(f(".7").mul(".802")).div(".598").sub(".5"),".6");
lt("B<.6 forces A>1.14",f("1.64").pow(2).add(f("1.1").pow(2)),Q);
lt("positive H late label<.54",kh.sub(u.mul("1.14")).add(v.mul(".6")),".54");
gt("positive H late cost",f("2.45").sub(coremax).sub(".54").sub(costloss),gamma);
lt("secondary positive-angle derivative amplitude",Cstar.pow(2).add(g.mul(ac).sub(Cstar).pow(2)),1);
gt("negative-angle core side coefficient",K,g.mul(".812").div(".67"));
const dneg=g.mul(new F(13n,12n)).sub("1.09").sub(g.mul(".4").pow(2).div(f(4).mul("1.09")));
gt("negative-angle projected derivative quadratic",dneg);
lt("positive core target impossible through .45",f(".4").add(f(".45").div(12)).sub(f(1).sub(f(".45").pow(2).div(2)).div(2)),0);
lt("positive core endpoint derivative amplitude",f(".97").pow(2).add(f(".15").pow(2)),1);
const positiveCoreSecondary=f(".45").add(".59").add(pilo.div(4)).sub(dh).sub(coremax).add(f(".968").mul(f(1).sub(f(".45").pow(2).div(2)))).sub(f(".15").mul(".45"));
gt("positive core target secondary at .45",positiveCoreSecondary,".94");
lt("negative source core remains on side",f("1.415").sub(1),".5");
gt("negative-phi decreasing H target coefficient",g.mul(".67"),v);
gt("negative-phi endpoint derivative at zero",g.mul(dl).add(Cstar),1);
gt("negative-phi endpoint derivative at .812",f(".51").mul(".725").add(f("1.41").mul(".688")),1);
gt("negative-phi derivative coefficient one",g.mul(dl).sub(Cstar),".51");
gt("negative-phi derivative coefficient two",g.mul(dl).add(Cstar),"1.41");
const minusN0=u.pow(2).add(v.sub(g).pow(2));
lt("negative-H full-circle norm at zero",minusN0,f(".892").pow(2));
const cm=Astar.add(u.sub(v).div(2)).add(kl);
gt("negative-H full-circle endpoint zero",cm.add(g.sub(beta.div(2))).sub(Rhi.mul(".892")),".886");
const minusN12=g.pow(2).add(u.pow(2)).add(v.pow(2)).add(g.mul(2).mul(u.mul(".933").sub(v.mul(".362"))));
lt("negative-H full-circle norm at1.2",minusN12,f("1.575").pow(2));
gt("negative-H full-circle endpoint1.2",f("1.2").add(cm).add(g.sub(beta.div(2)).mul(f(".932").add(".362"))).sub(Rhi.mul("1.575")),"1.02");
lt("late target B coefficient changes",g.mul(".3625"),v);
gt("late target A coefficient negative",g.mul(".932"),0);
lt("late endpoint derivative subtractand",g.mul(ah).sub(Cstar),".85");
gt("positive-H endpoint derivative at zero",g.sub(f(".596").mul(u)).sub(v),0);
gt("positive-H endpoint derivative at1.4",g.mul(f(".596").mul(".985").add(".169")).sub(f(".596").mul(u)).sub(v),0);
for(const [name,aaLo,aaHi,bbLo,bbHi,emax] of [["lower",al,ah,bl,bh,f(".464")],["diagonal",dl,dh,dl,dh,pihi.div(4)]]){
 const Dlo=Cstar.add(g.mul(bbLo)), Bhi=g.mul(aaHi).sub(Cstar),Blo=g.mul(aaLo).sub(Cstar);
 gt(name+" endpoint D>1",Dlo,1);gt(name+" endpoint B>.51",Blo,".51");
 gt(name+" endpoint derivative negative at1.4",Dlo.mul(".985").add(Blo.mul(".169")),1);
 gt(name+" positive-H endpoint at0",Astar.sub(emax).add(Dlo),gamma);
 gt(name+" positive-H endpoint at1.4",f("1.4").add(Astar).sub(emax).add(Dlo.mul(".169")).sub(Bhi.mul(".986")),gamma);
 gt(name+" positive-H endpoint at-.812",f("-.812").add(Astar).sub(emax).add(Dlo.mul(".688")).add(Cstar.add(g.mul(aaLo)).mul(".725")),gamma);
}
gt("Nplus increasing from1.4",v.mul(".985"),u.mul(".17"));
gt("Nplus second derivative positive",g.pow(2).sub(u.pow(2)).sub(v.pow(2)),f(".641").pow(2));
const cp=Astar.sub(u.sub(v).div(2)).sub(kh);
const plusN14=g.pow(2).add(u.pow(2)).add(v.pow(2)).sub(g.mul(2).mul(u.mul(".985").add(v.mul(".169"))));
lt("positive-H norm at1.4",plusN14,f(".536").pow(2));
gt("positive-H full-circle endpoint1.4",f("1.4").add(cp).add(g.sub(beta.div(2)).mul(".985")).sub(beta.div(2).mul(".17")).sub(Rhi.mul(".536")),".89");
const plusN25=g.pow(2).add(u.pow(2)).add(v.pow(2)).sub(g.mul(2).mul(u.mul(".598").sub(v.mul(".802"))));
lt("positive-H norm at2.5",plusN25,f("1.26").pow(2));
gt("positive-H full-circle endpoint2.5",f("2.5").add(cp).add(g.sub(beta.div(2)).mul("1.398")).sub(Rhi.mul("1.26")),".98");
lt("H primary negative target excludes negative phi",f("1.2").sub(f(".558").mul(".67")).sub(1),0);
gt("H primary positive target phi>-.026",f(".76").sub(pihi.div(4)),"-.026");
lt("H primary excludes phi<=.75",f(".7").sub(f("1.058").mul(f(1).sub(f(".75").pow(2).div(2)))).add(f(".06").mul(".75")),0);
gt("H primary negative core coefficient",K,g.div(".598"));
gt("n decreases",g.mul(u),u.pow(2).add(v.pow(2)));
gt("n'(1)>-.214",u.pow(2).add(v.pow(2)).sub(g.mul(u)).add(f(".214").mul(".64")),0);
lt("n''<.7",g.pow(2).mul(v.pow(2)).div(f(".64").pow(3)),".7");
const B=beta.div(2).sub(kh).add(u.neg().add(v).add(g).div(2)).sub(gamma);
const B0=B.add(Rhi.mul(".914")),B2=beta.div(2).add(Rhi.mul(".35")),C0=g.sub(Rhi.mul("1.204902"));
gt("polynomial multiplier x+B0 positive at left",f(".75").add(B0),0);
const S7=trigpoly("sin",7),S9=trigpoly("sin",9),C8=trigpoly("cos",8),C6=trigpoly("cos",6);
let P=mul([B0,f(1)],S7);P=add(P,scale(mul(S9,S9),B2.neg()));P=add(P,scale(mul(S9,C8),beta.div(2).neg()));P=add(P,[C0]);P=add(P,scale(C6,g.mul(new F(13n,12n))));
const br=bern(P,".75","1.5"), declared=[34281,45678,53640,59000,62526,64903,66706,68387,70249,72436,74913,77453,79629,80800,80112,76492,68645,55061,34020];
if(br.length!==declared.length)throw Error("Bernstein degree mismatch");
for(let i=0;i<br.length;i++)gt("whole primary polynomial Bernstein "+i,br[i],new F(BigInt(declared[i]),10000000n));
lt("primary final-QI derivative",f("1.09").add(g.mul(f(".071").mul(".979").sub(new F(13n,12n)))),0);
gt("primary QII Z>1.56",Q.mul(g.sub(u).pow(2)),f("1.56").pow(2).mul(nq2));
lt("primary QII concavity",f(".09").mul("1.5").sub(f(".56").mul(g)),0);
lt("primary QII endpoint norm",g.div(".598").sub(u).pow(2).add(v.pow(2)),f("1.294").pow(2));
const primaryEnd=f("2.5").sub(costloss).sub(kh).add(u.neg().add(v).add(g).div(2)).add(g.div(".599")).sub(g.mul(".802").div(f(12).mul(".598"))).sub(Rhi.mul("1.294"));
gt("primary QII endpoint2.5",primaryEnd,"1.08");
gt("positive core corner phi>2.28",f(".5").add(".758").sub(f(".652").div(12)),"1.2");
const aFirst=f("1.1135"),aSecond=f(".5").add(".598").sub(f(".802").div(12));
gt("positive corner first b cap",aFirst.add(".5").pow(2).add(f(".646").add(".5").pow(2)),Q);
lt("positive corner first label cap",kh.sub(u.mul(aFirst)).add(v.mul(".646")),".565");
gt("positive corner first cost",f("2.28").sub(coremax).sub(".565").sub(costloss),gamma);
gt("positive corner second b cap",aSecond.add(".5").pow(2).add(f(".754").add(".5").pow(2)),Q);
lt("positive corner second label cap",kh.sub(u.mul(aSecond)).add(v.mul(".754")),".655");
gt("positive corner second cost",f("2.4").sub(coremax).sub(".655").sub(costloss),gamma);

gt("core corner diagonal lower",new F(1n,144n),f(".5589255").sub(".5").pow(2).mul(2));
gt("core corner diagonal upper",f(".5589256").sub(".5").pow(2).mul(2),new F(1n,144n));
lt("core marker global maximum",K.mul(ac.sub(".5589255")).add(g.mul(".5589256")),".786");
gt("negative-H late endpoint B coefficient",g.mul(bl),Cstar);
gt("negative-H late endpoint A coefficient",g.mul(al),Cstar);
gt("primary sine lower on full range",trig(".75","sin",7),".598");
lt("positive-H quarter strip concavity",g.sub(beta.div(2)).neg().mul(".985").add(beta.div(2).mul(".17")),0);
const result={status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"C/H whole boundary pair at Q=9789/2500 and gamma=8833/10000",comparison_count:checks.length,polynomial:{degree:P.length-1,interval:["3/4","3/2"],bernstein_lower_numerators:declared,denominator:10000000},checks};
return result;

})(arithmetic);
console.log(JSON.stringify(result,null,2));
if(result.status !== "PASS") throw new Error("Core/high hand arithmetic failed");
