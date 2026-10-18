"use strict";
// Exact fixed arithmetic for the whole positive-core/positive-outer edge-3 family.
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
const Q=f("3.9156"),g=f("1.04240"),gamma=f(".89765"),kk=f("1.89442"),ac=f("7/12");
const R=rootI(Q),d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}
function rr(b){return id(ia(b,".5"),ia(a(b),".5"));}
function rp(b){return id(Q,ip(ia(a(b),".5"),3));}
function rpp(b){return id(im(Q.mul(3),ia(b,".5")),ip(ia(a(b),".5"),5));}
function J(b){return ia(".03965",ia(im("3.85510",b),ia(im("-1.49748",ip(b,2)),im(kk.neg(),im(a(b),b)))));}
function JD(b){return is(is("3.85510",im("2.99496",b)),im(kk,is(a(b),im(b,rr(b)))));}
function JDD(b){return ia("-2.99496",im(kk,ia(im(2,rr(b)),im(b,rp(b)))));}
function JDDD(b){return im(kk,ia(im(3,rp(b)),im(b,rpp(b))));}
gt("diagonal>.899",d,".899");lt("diagonal<.9",d,".9");lt("axial<1.415",a0,"1.415");
lt("core norm<.8",im(2,ip(dc,2)),f(".8").pow(2));
gt("J'(.5)>.624",JD(".5"),".624");lt("J''(.5)<0",JDD(".5"),0);gt("J''(.5)>-.032",JDD(".5"),"-.032");
gt("J''(.55)>0",JDD(".55"),0);gt("middle derivative>.622",f(".624").sub(f(".032").mul(".05")),".622");
lt("J'(0)<1.176",JD(0),"1.176");lt("J'(d)<1.176",JD(d),"1.176");lt("J(d)<.763568",J(d),".763568");
gt("late direct bound",f("1.68").sub(".01449").sub(".763568"),".9019");
lt("1.68 precedes quarter+.11",f("1.68"),ia(hp,".11")[0]);
lt("axis4 early upper impossible",is(ia(ac.sub(".5"),im(is(a0,".5"),sinI(".11"))),id(cosI(".11"),2)),0);
lt("radial logarithmic derivative<2.15",id(im(3,ia(d,".5")),ip(ia(d,".5"),2)),"2.15");
gt("secondary derivative concavity",kk.mul(3).sub(g.mul("2.15")),0);
gt("primary derivative concavity",is(kk.mul(3),id(g.mul("2.15"),sinI(lo))),0);
for(const phi of[lo,"1.3"]){
 const tag=phi==="1.3"?"1.3":"lo";
 gt("early secondary derivative at B=.5 "+tag,is(im(g,ia(im(rr(".5"),sinI(phi)),cosI(phi))),JD(".5")),0);
 gt("early secondary derivative at B=d "+tag,is(im(g,ia(sinI(phi),cosI(phi))),JD(d)),0);
}
gt("secondary full-circle scalar concavity",is(im(g,sinI(lo)),id(im(R,rootI(g.pow(2).add(f(".879").pow(2)))),4)),0);
const tangentRows=[
 {l:"lo",r:"1",b:".172",q:".878955401",k:".063716016"},
 {l:"1",r:"1.1",b:".209",q:".828547105",k:".073303502"},
 {l:"1.1",r:"1.2",b:".252",q:".776312419",k:".085318707"},
 {l:"1.2",r:"1.3",b:".302",q:".724514843",k:".099625668"}];
function Flow(phi,q,k){return is(ia(ia(phi,f("-.01449").sub(k).add(g.add(q).div(2))),im(g,sinI(phi))),im(R,rootI(is(g.pow(2).add(q.pow(2)),im(g.mul(q).mul(2),cosI(phi))))));}
for(let i=0;i<tangentRows.length;i++){let z=tangentRows[i],q=f(z.q),k=f(z.k);
 lt("secondary tangent"+i+" slope",JD(z.b),q);lt("secondary tangent"+i+" intercept",is(J(z.b),im(z.b,JD(z.b))),k);
 lt("secondary tangent"+i+" slope<.879",q,".879");
 gt("secondary tangent"+i+" left",Flow(z.l==="lo"?lo:z.l,q,k),".8993");
 gt("secondary tangent"+i+" right",Flow(z.r,q,k),".8993");
}
function secData(phi){const s=sinI(phi),c=cosI(phi),Z=ia(".5",s),Y=rootI(is(Q,ip(Z,2))),U=ia(im(Z,s),im(Y,c)),V=is(im(Y,s),im(Z,c)),bb=is(V,".5"),ff=is(1,id(c,Y)),fp=id(ia(is(im(Q.sub("1.25"),s),id(ip(s,2),2)),"-.5"),ip(Y,3));return{s,c,Z,Y,U,V,b:bb,f:ff,fp};}
gt("later zero secondary source coordinate positive",secData("1.3").b,".39");
gt("later zero secondary f positive",secData("1.3").f,0);
gt("later zero secondary f' positive",secData("1.3").fp,0);
gt("later zero secondary f' numerator increasing",Q.sub("2.25"),0);
const secRows=[["1.3","1.4"],["1.4","1.5"],["1.5","1.55"],["1.55","1.56"],["1.56","quarter"]];
for(let i=0;i<secRows.length;i++){let[l,h]=secRows[i];l=l==="quarter"?hp:l;h=h==="quarter"?hp:h;const L=secData(l),H=secData(h),B=id(im(g,H.Y),L.U);
 for(const [j,z]of[[0,L],[1,H]])gt("zero secondary contact derivative row"+i+" endpoint"+j,is(B,JD(z.b)),".007");
}
function Dlow(phi){return ia(ia(phi,f("-.01449").add(g.div(2))),ia(ineg(J(d)),ia(im(g,im(is(".5",d),sinI(phi))),im(g,im(ia(".5",d),cosI(phi))))));}
gt("diagonal secondary convex second derivative at1.3",im(g,is(im(is(d,".5"),sinI("1.3")),im(ia(d,".5"),cosI("1.3")))),0);
lt("diagonal secondary endpoint derivative",is(1,im(g,ia(d,".5"))),0);
const aligned=is(ia(hp,im(g,is(1,d))),ia(".01449",J(d)));
gt("aligned common endpoint",aligned,".897798");
function Ksec(phi){return is(is(phi,".01449"),J(secData(phi).b));}
for(const [l,h]of[["1.3","1.35"],["1.35","1.4"]]){const L=secData(l),H=secData(h),speed=im(L.U,H.f);
 for(const [j,z]of[[0,L],[1,H]])lt("early zero-secondary derivative product "+l+" "+j,im(JD(z.b),speed),1);}
gt("zero-secondary at1.3",Ksec("1.3"),".9053");
lt("zero-secondary V upper",rootI(Q.sub("2.25")),"1.291");
gt("zero-secondary f' at1.4",secData("1.4").fp,".72");
gt("zero-secondary B'' lower",f("-1.291").add(f("1.5").mul(".72")),"-.22");
gt("zero-secondary B' lower",im("1.5",is(1,id(cosI("1.4"),rootI(Q.sub("2.25"))))),"1.3");
gt("zero-secondary J'' at1.4",JDD(secData("1.4").b),".161");
gt("zero-secondary cost concavity reserve",f(".161").mul(f("1.3").pow(2)).sub(f("1.176").mul(".22")),0);
gt("zero-secondary endpoint1.4",Ksec("1.4"),".914");
gt("zero-secondary quarter endpoint",Ksec(hp),".9025");
const B1=is(rootI(Q.sub("2.25")),".5");
lt("B1 below diagonal",B1,d[0]);
gt("B1>.79",B1,".79");gt("r(B1)>.85",rr(B1),".85");
gt("whole upper secondary coordinate derivative",is(im(rr(0),cosI(".11")),sinI(".11")),0);
gt("zero secondary at B1 sign",is(is(B1,".5"),id(sinI(".055"),im(2,cosI(".055")))),0);
gt("upper secondary contact at diagonal",is(".5",im(is(d,".5"),ia(cosI(".11"),sinI(".11")))),0);
gt("upper contact second derivative constant",f("3.78884").mul(".85").sub("2.99496"),0);
gt("upper contact second derivative radial term",is(kk.mul(".79"),id(g,cosI(".11"))),0);
gt("upper secondary diagonal derivative",f(1).sub(g.mul(".4")),0);
const denSec=is(im(rr(B1),cosI(".11")),sinI(".11"));
lt("upper zero secondary coordinate speed",id(".4",denSec),".54");
gt("upper zero secondary cost derivative",f(1).sub(f("1.176").mul(".54")),0);
gt("core projection monotonic upper",is(cosI(".11"),sinI(".11")),0);
gt("upper primary source side is sufficient",is(d,".5"),0);
const diagPriLoss=ia(im(g.mul(".4"),id(sinI(".11"),ip(cosI(".11"),2))),id(g.div(12),ip(cosI(".11"),2)));
lt("upper primary diagonal derivative loss",diagPriLoss,1);
const zeroPriSpeed=id(ia(id(sinI(".11"),2),"1/12"),rr(B1));
lt("upper primary zero coordinate speed",zeroPriSpeed,".17");
gt("upper primary zero cost derivative",f(1).sub(f("1.176").mul(".17")),0);
const q=f(".643398450"),k=f(".128316398");
lt("primary small target tangent slope",JD(".42"),q);
lt("primary small target tangent intercept",is(J(".42"),im(".42",JD(".42"))),k);
lt("primary target slope at.5",JD(".5"),q);
lt("primary target line at.65",J(".65"),k.add(q.mul(".65")));
gt("primary small target late direct",is(f("1.46").sub(".01449"),J(".65")),".8999");
gt("primary large target derivative at.65",is(im(g,rr(".65")),JD(".65")),".060");
gt("primary zero derivative at B1",is(im(g,rr(B1)),JD(B1)),".015");
gt("primary diagonal decreasing derivative",f("13/12").mul(g).sub(1).sub(g.pow(2).mul(f(".4").pow(2)).div(4)),0);
function priData(phi){const s=sinI(phi),c=cosI(phi),m=ia(id(s,2),im("13/12",c)),v=is(im("13/12",s),id(c,2)),U=ia(1,m),V=rootI(is(Q,ip(U,2)));return{s,c,m,v,U,V,b:is(V,".5")};}
lt("primary zero begins after1.466",priData("1.466").b,".65");
lt("primary zero U<1.62 atB=.65",rootI(Q.sub(f("1.15").pow(2))),"1.62");
gt("primary zero relative curvature",f("1.264").sub(Q.div(f("2.25").mul("1.15")).sub(f(".5").mul("1.15").div(f("1.62").mul("205/144")))),0);
gt("primary target curvature ratio at.65",id(JDD(".65"),JD(".65")),"1.264");
gt("primary target third derivative at.65",JDDD(".65"),"6.8");
gt("primary target derivative at.65",JD(".65"),".684");
lt("primary target second derivative at B1",JDD(B1),"2.003");
gt("primary target curvature ratio increasing",f("6.8").mul(".684").sub(f("2.003").pow(2)),0);
gt("primary zero low endpoint",is(f("1.466").sub(".01449"),J(".65")),".9059");
gt("primary zero quarter endpoint",is(is(hp,".01449"),J(B1)),".9025");
gt("core-corner late direct",is(f("1.16").sub(".01449").add(g.div(2)),J(d)),gamma);
gt("core-corner small target direct",is(ia(is(lo,".01449"),g.div(2)),J(".5")),gamma);
gt("core-corner side at diagonal impossible",ia(".5",im("13/12",cosI("1.16"))),d[1]);
function cornerEnd(phi,b,aa){const A=ia(".5",ia(im(is(".5",b),sinI(phi)),im(ia(".5",aa),cosI(phi)))),B=is(rootI(is(Q,ip(ia(A,".5"),2))),".5");return{A,B};}
const cornerLow=cornerEnd(lo,".5",ac),cornerHigh=cornerEnd("1.16",dc,dc);
gt("corner-contact B>.516",cornerLow.B,".516");
gt("corner-contact A>.84",cornerHigh.A,".84");lt("corner-contact B<.95",cornerHigh.B,".95");
gt("corner-contact target J'' positive",JDD(".516"),0);
gt("corner-contact cosine>.399",cosI("1.16"),".399");
gt("corner-contact convexity reserve",f(12).mul(".399").mul("1.3").div(4),1);
const cornerCuts=["lo",".89",".91",".93",".95",".97",".99","1.01","1.03","1.05","1.07","1.09","1.11","1.13","1.15","1.16"];
const cornerRows=[];
for(let i=0;i+1<cornerCuts.length;i++){
 const L=cornerCuts[i]==="lo"?lo:cornerCuts[i],H=cornerCuts[i+1];
 for(const [name,b,aa]of[["side",".5",ac],["diagonal",dc,dc]]){
  const value=is(ia(is(L,".01449"),im(g,b)),J(cornerEnd(H,b,aa).B));
  gt("corner fixed endpoint "+i+" "+name,value,gamma);
  cornerRows.push({interval:[cornerCuts[i],H],core_endpoint:name,lower:value[0].str()});
 }
}
const C10=trigpoly("cos",10),C8=trigpoly("cos",8),S11=trigpoly("sin",11);
const K=PI[0].div(2).sub(".01449").sub(k).add(g.add(q).div(2)).sub(gamma);
const A=add(add(mul(C10,[K,f(-1)]),[g]),scale(S11,g.mul("13/12")));
const P=add(mul(A,A),scale(add([g.pow(2)],scale(mul(C8,C8),q.pow(2))),Q.neg()));
let tail=f(0);for(let j=9;j<P.length;j++)if(P[j].lt(0))tail=tail.add(P[j].neg().mul(f(".7").pow(j)));
const allowance=f(".000267");lt("primary support discarded negative tail",tail,allowance);
const P8=P.slice(0,9);P8[0]=P8[0].sub(allowance);const bs=bern(P8,".11",".7");
const floors=[".0096312",".0320782",".0392637",".0362823",".0282149",".0194898",".0134423",".0122873",".0174390"];
for(let j=0;j<bs.length;j++)gt("primary support Bernstein"+j,bs[j],floors[j]);
gt("primary squared numerator factor positive",K.sub(".7"),0);
gt("primary scalar overcover reaches1.46",is(hp,".11"),"1.46");
tables.push({name:"lower_primary_B_le_.65",interval:[".11",".7"],degree:8,tail:tail.str(),allowance:allowance.str(),power_coefficients:P8.map(x=>x.str()),bernstein_coefficients:bs.map(x=>x.str()),printed_lower:floors});
for(const z of[".9019",".8993",".897798",".9053",".914",".9025",".8999",".9059"])gt("final "+z+" exceeds gamma",f(z),gamma);
return {status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge3 C+ to O+, whole quarter-one interval, all axes/core pieces; fixed contact and scalar support proof",comparisons:checks.length,checks,tangentRows,cornerRows,tables};

})();
process.stdout.write(JSON.stringify(result,null,2)+"\n");
if(result.status!=="PASS")process.exitCode=1;

