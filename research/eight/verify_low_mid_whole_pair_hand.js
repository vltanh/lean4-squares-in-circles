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
const configs=[{"id":"L+M+f","p":"1.489593","q":"1.580219","c":"-2.143075","tau":1,"axis":"f","quadrant":1,"lam":[".945"],"sourceFloor":["-.00001"],"lo":".76","hi":"1.4"},{"id":"L-M+f_QI","p":"1.489593","q":"1.580219","c":"-2.143075","tau":1,"axis":"f","quadrant":1,"lam":[".98"],"sourceFloor":["-.00004"],"lo":"1","hi":"1.58"},{"id":"L-M+f_QII","p":"1.489593","q":"1.580219","c":"-2.143075","tau":1,"axis":"f","quadrant":-1,"lam":[".98"],"sourceFloor":["-.00004"],"lo":"1.57","hi":"1.71"},{"id":"MLtight","p":".403875","q":"1.089065","c":"-457049398977/800000000000","tau":1,"axis":"f","quadrant":1,"lam":["1.146","-.335"],"sourceFloor":["-16688256133/125000000000","8608945307/50000000000"],"lo":".4","hi":".79"},{"id":"LMprimaryplus_QI","p":"1.489593","q":"1.580219","c":"-2.143075","tau":1,"axis":"e","quadrant":1,"lam":[".9"],"sourceFloor":["-14757025241/10000000000"],"lo":"1.5","hi":"1.58","sinSign":-1},{"id":"LMprimaryplus_QII","p":"1.489593","q":"1.580219","c":"-2.143075","tau":1,"axis":"e","quadrant":-1,"lam":[".9"],"sourceFloor":["-14757025241/10000000000"],"lo":"1.57","hi":"1.71","sinSign":-1},{"id":"MLprimaryplus_QI","p":".403875","q":"1.089065","c":"-457049398977/800000000000","tau":1,"axis":"e","quadrant":1,"lam":[".94"],"sourceFloor":["-39570292457/25000000000"],"lo":"1.3","hi":"1.58","sinSign":-1},{"id":"MLprimaryplus_QII","p":".403875","q":"1.089065","c":"-457049398977/800000000000","tau":1,"axis":"e","quadrant":-1,"lam":[".94"],"sourceFloor":["-39570292457/25000000000"],"lo":"1.57","hi":"1.71","sinSign":-1}];
const polynomialRows=[{"id":"L+M+f","lo":".76","hi":"1.4","degree":16,"lower_numerators":["298611","278811","258892","239202","220081","201865","184883","169463","155931","144612","135834","129926","127221","128056","132775","141727","155267"],"denominator":1000000},{"id":"L-M+f_QI","lo":"1","hi":"1.58","degree":16,"lower_numerators":["286934","263872","241970","221471","202620","185660","170838","158401","148603","141698","137948","137617","140977","148304","159880","175992","196933"],"denominator":1000000},{"id":"L-M+f_QII","lo":"1.57","hi":"1.71","degree":16,"lower_numerators":["183687","269849","356678","444166","532306","621092","710515","800569","891246","982538","1074437","1166936","1260028","1353703","1447954","1542774","1638153"],"denominator":1000000},{"id":"MLtight","lo":".4","hi":".79","degree":18,"lower_numerators":["50244","46802","43299","39758","36203","32659","29150","25702","22343","19100","16001","13079","10363","7888","5689","3800","2262","1113","394"],"denominator":1000000},{"id":"LMprimaryplus_QI","lo":"1.5","hi":"1.58","degree":18,"lower_numerators":["747732","735914","723910","711721","699347","686789","674049","661128","648026","634744","621285","607648","593835","579847","565684","551349","536841","522163","507315"],"denominator":1000000},{"id":"LMprimaryplus_QII","lo":"1.57","hi":"1.71","degree":18,"lower_numerators":["536389","548221","559794","571110","582174","592988","603556","613881","623966","633814","643429","652813","661971","670904","679617","688111","696391","704459","712319"],"denominator":1000000},{"id":"MLprimaryplus_QI","lo":"1.3","hi":"1.58","degree":18,"lower_numerators":["117881","125949","132444","137371","140737","142549","142814","141541","138738","134417","128586","121256","112440","102148","90394","77191","62552","46492","29025"],"denominator":1000000},{"id":"MLprimaryplus_QII","lo":"1.57","hi":"1.71","degree":18,"lower_numerators":["38888","40901","42846","44725","46539","48289","49976","51602","53168","54675","56123","57515","58851","60132","61359","62533","63655","64726","65746"],"denominator":1000000}];
const result=(function({F,f,sum,fac,choose,trig,add,scale,mul,monomial,trigpoly,bern},oneNormPolynomial,configs,polynomialRows){
const checks=[];function gt(name,a,b=0){a=f(a);b=f(b);const gap=a.sub(b);checks.push({name,pass:gap.gt(0),gap:gap.str()})}function lt(name,a,b=0){gt(name,b,a)}
const Q=f("3.9156"),Rhi=f("1.978788"),mu=f(".403875"),q=f("1.089065"),pM=f("1.489593"),qM=f("1.580219"),cM=f("-2.143075"),beta=f(".18"),gamma=f(".9005");
const a0l=f("1.414575670"),a0h=f("1.414575672"),all=f("1.298747247"),alh=f("1.298747249"),ahl=f("1.199256060"),ahh=f("1.199256062");
const bll=all.div(4),blh=alh.div(4),bhl=ahl.mul(new F(3n,7n)),bhh=ahh.mul(new F(3n,7n));
const ellLl=mu.mul(all.sub(a0h)).add(q.mul(bll)),ellLh=mu.mul(alh.sub(a0l)).add(q.mul(blh));
const Emll=cM.add(pM.mul(all)).add(qM.mul(bll)),Emlh=cM.add(pM.mul(alh)).add(qM.mul(blh));
const Emhl=cM.add(pM.mul(ahl)).add(qM.mul(bhl)),Emhh=cM.add(pM.mul(ahh)).add(qM.mul(bhh));
const Slo=x=>trig(x,"sin",7),Shi=x=>trig(x,"sin",9),Clo=x=>trig(x,"cos",10),Chi=x=>trig(x,"cos",8);
gt("R upper",Rhi.pow(2),Q);
lt("a0 lower",a0l.add(".5").pow(2).add(".25"),Q);gt("a0 upper",a0h.add(".5").pow(2).add(".25"),Q);
for(const [tag,a,b,side] of [["L lower",all,bll,0],["L upper",alh,blh,1],["M upper-cut lower",ahl,bhl,0],["M upper-cut upper",ahh,bhh,1]])(side?gt:lt)(tag,a.add(".5").pow(2).add(b.add(".5").pow(2)),Q);
gt("L high label>.30682",ellLl,".30682");lt("L high label<.30683",ellLh,".30683");
gt("M lower label>.3046",Emll,".3046");lt("M lower label<.30461",Emlh,".30461");
gt("M high label>.4555",Emhl,".4555");lt("M high label<.455511",Emhh,".455511");
gt("L r>.261",f(".5"),f(".261").mul(a0h.add(".5")));
lt("L r<.459",blh.add(".5"),f(".459").mul(all.add(".5")));
gt("M r>.458",bll.add(".5"),f(".458").mul(alh.add(".5")));
lt("M r<.597",bhh.add(".5"),f(".597").mul(ahl.add(".5")));
gt("M label increasing",qM,pM.mul(".597"));gt("L label increasing",q,mu.mul(".459"));
const atan=(x,d)=>{let s=f(0);x=f(x);for(let j=1;j<=d;j+=2)s=s.add(x.pow(j).mul(new F(((j-1)/2)%2?-1n:1n,BigInt(j))));return s};
lt("atan(.25)<.245",atan(".25",5),".245");gt("atan(.25)>.24",atan(".25",3),".24");
lt("atan(3/7)<.405",atan(new F(3n,7n),9),".405");
gt("L slope<.984",f(".984"),q.sub(mu.mul(".261")));
gt("L concavity magnitude>.22",mu.mul(Q),f(".22").mul(a0h.add(".5").pow(3)));
lt("L minus .98b upper quadratic loss",f(".004").pow(2).div(".44"),".00004");
gt("positive L .945 floor",ellLl.sub(f(".945").mul(blh)),"-.00001");
gt("M endpoint secant below .8",f(".8").mul(bhl.sub(blh)),Emhh.sub(Emll));
gt("M endpoint secant above .797",Emhl.sub(Emlh),f(".797").mul(bhh.sub(bll)));
gt("critical lambda>.8",f("1.146").sub(f(".335").mul(".79")),".8");
gt("M negative f source selects lower",pM.mul(".458").add(1),qM);
lt("L negative primary source selects upper",mu.add(".9").mul(".459"),q);
lt("M negative primary source selects upper lambda1",pM.add(1).mul(".597"),qM);
lt("M+L+ f impossible through .4",f(".014").add(f(".915").mul(".4")).sub(f(".5").mul(f(1).sub(f(".4").pow(2).div(2)))),0);
gt("positive L target upper endpoint tangent bound",q,f(".797").mul(f(".459").mul(".711").add(".704")).add(mu.mul(".459")));
gt("target derivative decreases after .79",Slo(".79"),f(".459").mul(Chi(".79")));
const lm=f(".797"),cc=lm.sub(beta).div(2),bb=lm.mul(alh).sub(cc),dd=cc.add(lm.mul(blh));
lt("post-.79 scalar derivative amplitude",bb.pow(2).add(dd.pow(2)),1);
const f79=f(".79").add(lm.add(beta).div(2)).add(".3046").sub(".30683").sub(lm.mul(blh)).sub(bb.mul(Shi(".79"))).add(cc.add(lm.mul(bll)).mul(Clo(".79")));
gt("critical post-.79 endpoint",f79,".9006");
const direct=[
["L+M+",f("1.4").sub(".0378").sub(".455511")],
["mixed plus-minus",f(".64").sub(".0378").add(".3046")],
["negative-negative L source",f(".95").sub(".0378").sub(".30683").add(".3046")],
["positive-positive M source",f(".95").sub(".0378").add(".3046").sub(".30683")],
["both negative labels",f("1.71").sub(".0378").sub(".30683").sub(".455511")],
["M negative source negative target",f("1.4").sub(".0378").sub(".455511")]
];for(const [tag,v]of direct)gt("direct tail "+tag,v,gamma);
gt("sin/cos at1.5 primary exclusion",f("1.699").mul(Clo("1.5")).add(f(".8246").mul(Slo("1.5"))),".915");
gt("L/M primary negative target excluded to .95",f("1.699").mul(Clo(".95")).sub(".014"),".915");
gt("M/L primary negative target excluded to1.1",f("1.798").mul(Clo("1.1")),".799");
gt("M/L primary positive target excluded to1.3",f("1.798").mul(Clo("1.3")).add(f(".5").mul(Slo("1.3"))),".799");
const roots=[
{tag:"Mlo",aL:all,aH:alh,bL:bll,bH:blh,eL:f(".3046"),eH:f(".30461")},
{tag:"Mhi",aL:ahl,aH:ahh,bL:bhl,bH:bhh,eL:f(".4555"),eH:f(".455511")}
];
for(const lam0 of [".945","1"]){let l=f(lam0),A=l.add(beta).div(2),C=l.sub(beta).div(2),angle=lam0===".945"?".11":".35",loss=lam0===".945"?f(".00001"):f(0);
for(const z of roots){let B=l.mul(z.aH).sub(C),Dl=C.sub(l.mul(z.bH)),Dh=C.sub(l.mul(z.bL)),cprod=Dl.gt(0)?Dl.mul(Clo(angle)):Dl.mul(Chi(angle));
const val=f(angle).add(A).add(z.eL).sub(loss).sub(B.mul(Shi(angle))).add(cprod);
gt("endpoint monotone start "+lam0+" "+z.tag,val,lam0===".945"?".94":"1.01");
lt("endpoint derivative amplitude "+lam0+" "+z.tag,B.pow(2).add((Dh.pow(2).gt(Dl.pow(2))?Dh:Dl).pow(2)),1);
}}
const Lroots=[{tag:"axial",aL:a0l,aH:a0h,bL:f(0),bH:f(0),eL:f(0)},{tag:"cut",aL:all,aH:alh,bL:bll,bH:blh,eL:f(".30682")}];
const l945=f(".945"),c945=l945.sub(beta).div(2);
for(const z of Lroots){const B=l945.mul(z.aH).sub(c945),D=c945.sub(l945.mul(z.bH));
const val=f(".11").add(l945.add(beta).div(2)).add(".4555").sub(l945.mul(bhh)).add(z.eL).sub(B.mul(Shi(".11"))).add(D.mul(Clo(".11")));
gt("M+L- endpoint at .11 "+z.tag,val,".917");}
lt("M+L- derivative amplitude",(l945.mul(a0h).sub(c945)).pow(2).add(c945.pow(2)),f("1.029").pow(2));
gt("M+L- whole short interval",f(".917").sub(f(".029").mul(".53")),gamma);
gt("M-L- target axial derivative",q,Chi(".76"));
gt("M-L- target A coefficient negative",Slo(".76"),mu);
lt("M-L- derivative amplitude",a0h.sub(".41").pow(2).add(f(".41").pow(2)),f("1.09").pow(2));
const mlmm=f(".76").add(".59").sub(".30461").add(bll).sub(a0h.sub(".41").mul(Shi(".76"))).add(f(".41").mul(Clo(".76")));
gt("M-L- start>.97",mlmm,".97");
gt("M-L- full interval lower",f(".97").sub(f(".09").mul(".64")),gamma);
for(const z of Lroots)for(const ang of["1.1","1.4"]){
const val=f(ang).add(".59").sub(".455511").sub(ahh).add(z.eL).add(f(".41").sub(z.bH).mul(Slo(ang))).add(f(".41").add(z.aL).mul(Clo(ang)));
gt("M/L negative primary concave endpoint "+z.tag+" "+ang,val,"1.01");}
const l15=f("1.5"),r2=mu.pow(2).add(q.pow(2)),Nquarter=mu.add(l15).pow(2).add(q.pow(2));
lt("L fixed norm<1.162",r2,f("1.162").pow(2));lt("M-L+ quarter norm<2.194",Nquarter,f("2.194").pow(2));
lt("M-L+ norm at1<1.7",r2.add(l15.pow(2)).add(f(3).mul(mu.mul(Shi(1)).sub(q.mul(Clo(1))))),f("1.7").pow(2));
lt("M-L+ norm at1.71<2.3",r2.add(l15.pow(2)).add(f(3).mul(mu.mul(Shi("1.71")).sub(q.mul(Clo("1.71"))))),f("2.3").pow(2));
const C15=l15.add(beta).div(2).sub(".30461").add(l15.mul(bll)).add(mu.mul(a0l)).add(mu.add(q).div(2));
gt("M-L+ full-circle endpoint1",f(1).add(C15).add(f("1.41").mul(Slo(1))).sub(f(".09").mul(Chi(1))).sub(Rhi.mul("1.7")),1);
gt("M-L+ full-circle quarter",f("3.14159").div(2).add(C15).add("1.41").sub(Rhi.mul("2.194")),".97");
gt("M-L+ full-circle endpoint1.71",f("1.71").add(C15).add(f("1.41").mul(Slo("1.71").sub(Chi("1.71")))).sub(Rhi.mul("2.3")),1);
lt("M-L+ QI curvature",f("-1.41").mul(".84").add(f(".09").mul(".55")).add("1.1"),0);
lt("M-L+ QII curvature",Rhi.mul(l15.add("1.162")).div(4),"1.41");

lt("sin .79<.711",Shi(".79"),".711");
lt("cos .79<.704",Chi(".79"),".704");
gt("sin1>.84",Slo(1),".84");
lt("cos1<.55",Chi(1),".55");
lt("quarter norm curvature factor<1.1",Rhi.mul("2.2").div(4),"1.1");
const polyResults=[];
const Tfloors=["4","5","5","1","3","3",".5",".8"];
for(let i=0;i<configs.length;i++){let row=configs[i],z=oneNormPolynomial(row),b=bern(z.P,row.lo,row.hi),tb=bern(z.T,row.lo,row.hi),decl=polynomialRows[i];
if(b.length!==decl.lower_numerators.length)throw Error("degree mismatch");
b.forEach((v,j)=>gt(row.id+" P Bernstein "+j,v,new F(decl.lower_numerators[j],1000000n)));
tb.forEach((v,j)=>gt(row.id+" positive T Bernstein "+j,v,Tfloors[i]));
polyResults.push({...decl,T_bernstein_lower:Tfloors[i]});}
return{status:checks.every(z=>z.pass)?"PASS":"FAIL",comparison_count:checks.length,polynomial_rows:polyResults,checks};
})(arithmetic,oneNormPolynomial,configs,polynomialRows);
console.log(JSON.stringify(result,null,2));
if(result.status!=="PASS")throw Error("Low/middle hand arithmetic failed");
