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
    "id": "CMpositivef",
    "p": "1.489593",
    "q": "1.580219",
    "c": "-2.143075",
    "tau": 1,
    "axis": "f",
    "quadrant": 1,
    "lam": [
      "1.077372"
    ],
    "sourceFloor": [
      "0"
    ],
    "lo": ".7",
    "hi": "1.53",
    "gamma": ".9005"
  }
];
const polynomialRows=[
  {
    "id": "CMpositivef",
    "degree": 16,
    "lo": ".7",
    "hi": "1.53",
    "bern_lower_numerators": [
      930757,
      865698,
      798263,
      729205,
      659251,
      589108,
      519469,
      451021,
      384457,
      320478,
      259803,
      203178,
      151376,
      105205,
      65512,
      33176,
      9117
    ],
    "denominator": 1000000,
    "T_lower": 4,
    "T_degree": 8
  }
];
const curvatureTable=[
  {
    "x": ".6",
    "slo": 56464,
    "shi": 56465,
    "clo": 82533,
    "chi": 82534,
    "zhi": 179424,
    "nlo": 374711
  },
  {
    "x": ".7",
    "slo": 64421,
    "shi": 64422,
    "clo": 76484,
    "chi": 76485,
    "zhi": 177007,
    "nlo": 353482
  },
  {
    "x": ".8",
    "slo": 71735,
    "shi": 71736,
    "clo": 69670,
    "chi": 69671,
    "zhi": 174969,
    "nlo": 338316
  },
  {
    "x": ".9",
    "slo": 78332,
    "shi": 78333,
    "clo": 62160,
    "chi": 62161,
    "zhi": 173272,
    "nlo": 327185
  },
  {
    "x": "1",
    "slo": 84147,
    "shi": 84148,
    "clo": 54030,
    "chi": 54031,
    "zhi": 171878,
    "nlo": 318896
  },
  {
    "x": "1.04",
    "slo": 86240,
    "shi": 86241,
    "clo": 50622,
    "chi": 50623,
    "zhi": 171398,
    "nlo": 316201
  },
  {
    "x": "1.08",
    "slo": 88195,
    "shi": 88196,
    "clo": 47132,
    "chi": 47133,
    "zhi": 170961,
    "nlo": 313805
  },
  {
    "x": "1.12",
    "slo": 90010,
    "shi": 90011,
    "clo": 43568,
    "chi": 43569,
    "zhi": 170563,
    "nlo": 311680
  },
  {
    "x": "1.16",
    "slo": 91680,
    "shi": 91681,
    "clo": 39933,
    "chi": 39934,
    "zhi": 170204,
    "nlo": 309802
  },
  {
    "x": "1.2",
    "slo": 93203,
    "shi": 93204,
    "clo": 36235,
    "chi": 36236,
    "zhi": 169882,
    "nlo": 308152
  }
];
const curvatureIntervals=[
  {
    "i": 0,
    "Blower_numerator": 32188,
    "Dlower_numerator": 55193
  },
  {
    "i": 1,
    "Blower_numerator": 28895,
    "Dlower_numerator": 46704
  },
  {
    "i": 2,
    "Blower_numerator": 23320,
    "Dlower_numerator": 34899
  },
  {
    "i": 3,
    "Blower_numerator": 15480,
    "Dlower_numerator": 22276
  },
  {
    "i": 4,
    "Blower_numerator": 16819,
    "Dlower_numerator": 30005
  },
  {
    "i": 5,
    "Blower_numerator": 12424,
    "Dlower_numerator": 23091
  },
  {
    "i": 6,
    "Blower_numerator": 7672,
    "Dlower_numerator": 16401
  },
  {
    "i": 7,
    "Blower_numerator": 2563,
    "Dlower_numerator": 9851
  },
  {
    "i": 8,
    "Blower_numerator": -2891,
    "Dlower_numerator": 3183
  }
];
const result=(function(arithmetic,oneNormPolynomial,configs,polynomialRows,curvatureTable,curvatureIntervals){
const{F,f,trig,bern}=arithmetic;

const checks=[];
function gt(name,a,b=0){a=f(a);b=f(b);const gap=a.sub(b);checks.push({name,pass:gap.gt(0),gap:gap.str()})}
function lt(name,a,b=0){gt(name,b,a)}
const Q=f("3.9156"),p=f("1.489593"),q=f("1.580219"),cM=f("-2.143075"),g=f("1.077372"),K=f("7.506931"),ac=new F(7n,12n),beta=f(".18"),gamma=f(".9005");
const Rhi=f("1.978788"),pilo=f("3.14159"),pihi=new F(355n,113n);
const all=f("1.298747247"),alh=f("1.298747249"),ahl=f("1.199256060"),ahh=f("1.199256062");
const bll=all.div(4),blh=alh.div(4),bhl=ahl.mul(3).div(7),bhh=ahh.mul(3).div(7);
const ccl=f(".5589255"),cch=f(".5589256");
const Emll=cM.add(p.mul(all)).add(q.mul(bll)),Emlh=cM.add(p.mul(alh)).add(q.mul(blh));
const Emhl=cM.add(p.mul(ahl)).add(q.mul(bhl)),Emhh=cM.add(p.mul(ahh)).add(q.mul(bhh));
const Astar=g.add(beta).div(2),Cstar=g.sub(beta).div(2);
const Slo=x=>trig(x,"sin",11),Shi=x=>trig(x,"sin",13),Clo=x=>trig(x,"cos",10),Chi=x=>trig(x,"cos",12);
gt("R upper",Rhi.pow(2),Q);
for(const [tag,a,b,side]of [["M low lower",all,bll,0],["M low upper",alh,blh,1],["M high lower",ahl,bhl,0],["M high upper",ahh,bhh,1]])(side?gt:lt)(tag,a.add(".5").pow(2).add(b.add(".5").pow(2)),Q);
lt("core diagonal lower",ccl.sub(".5").pow(2).mul(2),new F(1n,144n));
gt("core diagonal upper",cch.sub(".5").pow(2).mul(2),new F(1n,144n));
lt("core label maximum<.786",K.mul(ac).sub(K.sub(g).mul(ccl)),".786");
lt("core center radius<.8",cch.pow(2).mul(2),f(".8").pow(2));
lt("M center radius<1.34",alh.pow(2).add(blh.pow(2)),f("1.34").pow(2));
gt("M lower label>.3046",Emll,".3046");lt("M lower label<.30461",Emlh,".30461");
gt("M high label>.4555",Emhl,".4555");lt("M high label<.455511",Emhh,".455511");
gt("M r>.458",bll.add(".5"),f(".458").mul(alh.add(".5")));
lt("M r<.597",bhh.add(".5"),f(".597").mul(ahl.add(".5")));
gt("M derivative positive",q.sub(p.mul(".597")),0);
lt("M derivative<.898",q.sub(p.mul(".458")),".898");
lt("M derivative<1 and g",f(".898"),1);gt("g>1",g,1);
lt("high b<.513966884",bhh,".513966884");
lt("high b-.5<.014",bhh.sub(".5"),".014");
gt("low b+.5>.8246",bll.add(".5"),".8246");
lt("M a-.5<.799",alh.sub(".5"),".799");
gt("M a+.5>1.699",ahl.add(".5"),"1.699");
lt("core b-.5<.059",cch.sub(".5"),".059");
gt("core a+.5>1.058",ccl.add(".5"),"1.058");
gt("sqrt2<1.42",f("1.42").pow(2),2);
const atan=(x,d)=>{let s=f(0);x=f(x);for(let j=1;j<=d;j+=2)s=s.add(x.pow(j).mul(new F(((j-1)/2)%2?-1n:1n,BigInt(j))));return s};
lt("M angle<.405",atan(new F(3n,7n),9),".405");
lt("core angle<.786",pihi.div(4),".786");
gt("all frame differences>-.432",f(".76").sub(".405").sub(pihi.div(4)),"-.432");
gt("unrestricted tail at2.18",f("2.18").sub(".455511").sub(".786").sub(".0378"),gamma);
lt("core source primary impossible through1.5",new F(1n,12n).sub(f("1.699").mul(Clo("1.5"))).add(".014"),0);
gt("core-primary negative target direct",f("1.5").sub(".786").sub(".0378").add(".3046"),gamma);
gt("sin2.18>.820",Slo("2.18"),".820");gt("cos2.18>-.573",Clo("2.18"),"-.573");
lt("core primary positive target through2.18",new F(1n,12n).add(f(".799").mul(".573")).sub(f(".8246").mul(".820")),0);
lt("core primary positive target in QI",new F(1n,12n),".8246");
lt("core negative f source is on side",f("1.34").sub(1),".5");
lt("positive M target f excluded to .7",f(".059").add(f(".799").mul(".7")).sub(f(".8246").mul(f(1).sub(f(".7").pow(2).div(2)))),0);
const roots=[{tag:"low",aL:all,aH:alh,bL:bll,bH:blh,eL:f(".3046")},{tag:"high",aL:ahl,aH:ahh,bL:bhl,bH:bhh,eL:f(".4555")}];
for(const z of roots){
gt("negative M target parallel "+z.tag,g.add(z.eL).sub(g.mul(z.bH)),".979");
lt("negative M target sine coefficient bound "+z.tag,g.mul(z.aH).sub(Cstar),".952");
gt("negative M target positive sine coefficient "+z.tag,g.mul(z.aL).sub(Cstar),0);
gt("negative M target D lower "+z.tag,Cstar.sub(g.mul(z.bH)),"-.106");
lt("negative M target D upper "+z.tag,Cstar.sub(g.mul(z.bL)),".106");
gt("negative-angle coefficient E>1.74 "+z.tag,Cstar.add(g.mul(z.aL)),"1.74");
}
lt("negative M target derivative amplitude",f(".952").pow(2).add(f(".106").pow(2)),1);
gt("negative-angle endpoint derivative",f(-1).sub(f(".106").mul(".432")).add(f("1.74").mul(f(1).sub(f(".432").pow(2).div(2)))),0);
lt("positive-M target upper support at1.53",p.add(g.mul(Shi("1.53"))).mul(".597").add(g.mul(Chi("1.53"))),q);
gt("positive-M support derivative stays negative",Slo("1.53"),f(".597").mul(Chi("1.53")));
gt("positive-M endpoint QI cost decreases",Cstar.add(g.mul(bhl)).mul(Slo("1.53")),1);
gt("shared quarter endpoint>.9006",pilo.div(2).sub(".455511").add(g.mul(f(1).sub(ahh))),".9006");
lt("positive-M endpoint QII derivative loss<.11",g.mul(bhh).sub(Cstar),".11");
gt("M-source negative-core parallel>.979",f(".4555").add(g.mul(f(1).sub(bhh))),".979");
lt("M-source negative-core positive-angle derivative amplitude",Cstar.pow(2).add(g.mul(ac).sub(Cstar).pow(2)),1);
gt("negative-angle core coefficient remains positive",K,g.mul(".432").div(f(1).sub(f(".432").pow(2).div(2))));
gt("negative-angle M/core derivative",g.mul(13).div(12).sub("1.09").sub(g.mul(".014").pow(2).div("4.36")),0);
lt("M-source positive-core f impossible to1.2",f(".014").add(f("1.2").div(12)).sub(f(".5").mul(f(1).sub(f("1.2").pow(2).div(2)))),0);
lt("M-source positive-core QI derivative amplitude",f(".41").add(cch).pow(2).add(cch.sub(".41").pow(2)),1);
lt("M-source positive-core QII derivative loss",cch.sub(".41"),1);
const f12=f("1.2").add(".59").add(".4555").sub(bhh).sub(".786").add(f(".41").add(ccl).mul(Clo("1.2"))).add(f(".41").sub(cch).mul(Shi("1.2")));
gt("M-source positive-core endpoint1.2",f12,"1.15");
lt("M-source primary impossible to .6",f(".799").sub(f("1.058").mul(f(1).sub(f(".6").pow(2).div(2)))).add(f(".059").mul(".6")),0);
gt("primary cancellation K>g/s",K,g.div(".564"));
gt("sin1.2>.932",Slo("1.2"),".932");gt("sin1.94>.932",Slo("1.94"),".932");
lt("M-source primary selects high from1.2",p.add(g.div(".932")).mul(".597"),q);
const G12=f("1.2").sub(f(".09").mul(Shi("1.2").add(Chi("1.2")).sub(1))).sub(".455511").add(g.div(2)).add(g.mul(new F(13n,12n).mul(Clo("1.2")).sub(ahh.sub(".5"))).div(Slo("1.2")));
gt("primary endpoint G(1.2)>.902",G12,".902");
const Gp12=f(1).add(f(".09").mul(Slo("1.2").sub(Chi("1.2")))).add(g.mul(ahl.sub(".5").mul(Clo("1.2")).sub(new F(13n,12n))).div(Slo("1.2").pow(2)));
gt("primary G'(1.2)>0",Gp12,0);
lt("cos1.2<.363",Chi("1.2"),".363");
lt("primary G''' negative numerator",f(".7").mul(".363").mul(f(5).add(f(".363").pow(2))),new F(13n,6n));
gt("cos1.94>-.362",Clo("1.94"),"-.362");
gt("primary QII G derivative",f(".91").sub(g.mul(f(".7").mul(".362").add(new F(1n,12n))).div(f(".932").pow(2))),0);
gt("primary side/negative-target direct tail1.94",f("1.94").sub(".455511").sub(g.div(2)).sub(".0378"),gamma);
gt("sin2.13>.847",Slo("2.13"),".847");gt("cos2.13>-.532",Clo("2.13"),"-.532");
gt("positive-core corner blocked to2.13",f(".5").add(".847").sub(f(".532").div(12)),alh);
const cornerA=f(".5").add(".820").sub(f(".573").div(12));
gt("corner barrier forces b<.381",cornerA.add(".5").pow(2).add(f(".881").pow(2)),Q);
lt("corner barrier forces M<.394",cM.add(p.mul(alh)).add(q.mul(".381")),".394");
gt("positive-core corner final cost",f("2.13").sub(".0378").sub(".786").sub(".394"),gamma);

const rat=n=>new F(BigInt(n),100000n);
for(const row of curvatureTable){
const sl=rat(row.slo),sh=rat(row.shi),cl=rat(row.clo),ch=rat(row.chi),Xu=p.add(g.div(sl)),Xd=p.add(g.div(sh));
gt("curvature sin lower "+row.x,trig(row.x,"sin",11),sl);
lt("curvature sin upper "+row.x,trig(row.x,"sin",13),sh);
gt("curvature cos lower "+row.x,trig(row.x,"cos",10),cl);
lt("curvature cos upper "+row.x,trig(row.x,"cos",12),ch);
gt("curvature Z upper "+row.x,rat(row.zhi).pow(2).mul(Xu.pow(2).add(q.pow(2))),Rhi.pow(2).mul(Xu.pow(2)));
gt("curvature N lower "+row.x,Xd.pow(2).add(q.pow(2)),rat(row.nlo).pow(2));
}
const curvatureResults=[];
for(let i=0;i<curvatureTable.length-1;i++){
const a=curvatureTable[i],b=curvatureTable[i+1],decl=curvatureIntervals[i];
const B=f(1).add(rat(a.chi).pow(2)).mul(f(1).sub(rat(a.zhi))).add(rat(b.clo).mul(13).div(6));
const den=(B.gt(0)?rat(b.shi):rat(a.slo)).pow(3);
const lowerSum=rat(Math.min(a.slo+a.clo,b.slo+b.clo));
const D=f(".09").mul(lowerSum).add(g.mul(B).div(den)).sub(Rhi.mul(q.pow(2)).mul(g.pow(2)).mul(rat(a.chi).pow(2)).div(rat(a.slo).pow(4).mul(rat(b.nlo).pow(3))));
gt("curvature B row "+i,B,rat(decl.Blower_numerator));
if(i===curvatureTable.length-2)lt("last curvature B is negative",B,0);
gt("curvature D row "+i,D,rat(decl.Dlower_numerator));
gt("curvature >.03 row "+i,rat(decl.Dlower_numerator),".03");
curvatureResults.push({...decl,B:B.str(),D:D.str()});
}
const x0=f("1.08"),s0l=f(".881957806"),s0h=f(".881957807"),c0l=f(".471328364"),c0h=f(".471328365"),r0l=f("1.978787507"),r0h=f("1.978787508"),n0l=f("3.138070988"),n0h=f("3.138070991");
gt("test-point sine lower",trig(x0,"sin",19),s0l);lt("test-point sine upper",trig(x0,"sin",21),s0h);
gt("test-point cosine lower",trig(x0,"cos",18),c0l);lt("test-point cosine upper",trig(x0,"cos",20),c0h);
lt("test-point radius lower",r0l.pow(2),Q);gt("test-point radius upper",r0h.pow(2),Q);
const Xl=p.add(g.div(s0h)),Xh=p.add(g.div(s0l));
gt("test-point norm lower",Xl.pow(2).add(q.pow(2)),n0l.pow(2));lt("test-point norm upper",Xh.pow(2).add(q.pow(2)),n0h.pow(2));
const Flo=x0.sub(f(".09").mul(s0h.add(c0h).sub(1))).sub(cM).add(p.add(q).add(g).div(2)).add(g.div(s0h)).add(g.mul(13).div(12).mul(c0l).div(s0h)).sub(r0h.mul(n0h));
gt("F(1.08)>.9006",Flo,".9006");
const Zl=r0l.mul(Xl).div(n0h),Zh=r0h.mul(Xh).div(n0l),Yl=c0l.mul(Zl.sub(1)).sub(new F(13n,12n)),Yh=c0h.mul(Zh.sub(1)).sub(new F(13n,12n));
gt("test-point derivative Z-1 positive",Zl,1);lt("test-point derivative bracket negative",Yh,0);
const Fpl=f(1).add(f(".09").mul(s0l.sub(c0h))).add(g.mul(Yl).div(s0l.pow(2))),Fph=f(1).add(f(".09").mul(s0h.sub(c0l))).add(g.mul(Yh).div(s0h.pow(2)));
gt("F'(1.08)>-.0003",Fpl,"-.0003");lt("F'(1.08)<.0003",Fph,".0003");
gt("strong-convexity reserve exceeds gamma",f(".9006").sub(f(".0003").pow(2).div(".06")),gamma);
const polynomialResults=[];
for(let i=0;i<configs.length;i++){
const z=oneNormPolynomial(configs[i]),decl=polynomialRows[i],bp=bern(z.P,decl.lo,decl.hi),bt=bern(z.T,decl.lo,decl.hi);
if(bp.length!==decl.bern_lower_numerators.length)throw Error("polynomial degree mismatch");
bp.forEach((v,j)=>gt(decl.id+" P Bernstein "+j,v,new F(BigInt(decl.bern_lower_numerators[j]),1000000n)));
bt.forEach((v,j)=>gt(decl.id+" T Bernstein "+j,v,decl.T_lower));
polynomialResults.push(decl);
}
return{status:checks.every(z=>z.pass)?"PASS":"FAIL",comparison_count:checks.length,polynomial_rows:polynomialResults,curvature_table:curvatureTable,curvature_intervals:curvatureResults,checks};

})(arithmetic,oneNormPolynomial,configs,polynomialRows,curvatureTable,curvatureIntervals);
console.log(JSON.stringify(result,null,2));
if(result.status!=="PASS")throw Error("Core/middle reconstructed hand arithmetic failed");
