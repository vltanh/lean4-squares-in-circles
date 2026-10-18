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
const checks=[],tables=[];function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),g=f(".94831"),gamma=f(".89765"),kk=f(".1109"),ac=f("7/12");
const R=rootI(Q),d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7");
function a(b){return is(rootI(is(Q,ip(ia(b,".5"),2))),".5");}
function rr(b){return id(ia(b,".5"),ia(a(b),".5"));}
function rp(b){return id(Q,ip(ia(a(b),".5"),3));}
function T(b){return ia(".01670",ia(im("2.42322",b),ia(im("-.91744",ip(b,2)),im("-.95769",im(a(b),b)))));}
function TD(b){return is(is("2.42322",im("1.83488",b)),im(".95769",is(a(b),im(b,rr(b)))));}
function TDD(b){return ia("-1.83488",im(".95769",ia(im(2,rr(b)),im(b,rp(b)))));}
gt("outer diagonal>.899",d,".899");lt("outer diagonal<.9",d,".9");lt("outer axial<1.415",a0,"1.415");
lt("core norm<.8",im(2,ip(dc,2)),f(".8").pow(2));gt("radial derivative>.557",id(Q,ip(ia(a0,".5"),3)),".557");
lt("T''(.6)<-.048",TDD(".6"),"-.048");gt("T''(.6)>-.049",TDD(".6"),"-.049");gt("T''(.7)>0",TDD(".7"),0);
gt("T'(.6)>.610",TD(".6"),".610");gt("middle derivative>.605",f(".610").sub(f(".049").mul(".1")),".605");
lt("T'(.6)<.62",TD(".6"),".62");
const bstar=f(".53362"),H=is(T(bstar),im(".62",bstar)),HD=is(TD(bstar),".62");
lt("small arc tangent quadratic upper",ia(H,id(ip(HD,2),".096")),".110895");
lt("line small arc endpoint .6",is(T(".6"),im(".62",".6")),kk);
lt("line small arc endpoint .7",is(T(".7"),im(".62",".7")),kk);
lt("global line diagonal endpoint",is(T(d),im(".633",d)),kk);
gt("small line reserve",kk,".110895");
gt("r(.7)>.762",rr(".7"),".762");gt("r(.8)>.871",rr(".8"),".871");
lt("T'(.8)<.674",TD(".8"),".674");lt("T'(d)<.774",TD(d),".774");
lt("ratio on .7 to .8",f(".674").div(".762"),".89");lt("ratio on .8 to d",f(".774").div(".871"),".89");
gt("g sin1.4>.89",im(g,sinI("1.4")),".89");
function U2(x){return is(ia(ia(ia(hp,x),f("-.0497").sub(kk).add(f(".633").div(2))),im(g,dc)),ia(im(".633",im(is(a0,".5"),id(sinI(x),cosI(x)))),id(f(".633").div(12),cosI(x))));}
for(const x of[0,".7"])gt("axis2 upper endpoint "+x,U2(x),"1.14");
const margin=is(is(im(a(".6"),sinI("1.4")),im(".6",cosI("1.4"))),id(ia(1,ia(sinI("1.4"),cosI("1.4"))),2));
lt("lower axis3 phi<=1.4 implies b<.6",margin,0);
gt("all lower secondary supports concave",is(im(g,sinI(lo)),id(im(R,rootI(g.pow(2).add(f(".85").pow(2)))),4)),0);
function Flow(phi,q,k){return is(ia(ia(phi,f("-.0497").sub(k).add(g.add(q).div(2))),im(g,sinI(phi))),im(R,rootI(is(g.pow(2).add(q.pow(2)),im(g.mul(q).mul(2),cosI(phi))))));}
const tangentRows=[{"l":"lo","r":"0.95","b":"0.186","q":"0.849072101","k":"0.036194154"},{"l":"0.95","r":"1","b":"0.208","q":"0.827123134","k":"0.040516466"},{"l":"1","r":"1.05","b":"0.226","q":"0.809833767","k":"0.044267347"},{"l":"1.05","r":"1.1","b":"0.245","q":"0.792248783","k":"0.048407521"},{"l":"1.1","r":"1.16","b":"0.268","q":"0.771892909","k":"0.053626828"},{"l":"1.16","r":"1.23","b":"0.297","q":"0.747715180","k":"0.060452973"},{"l":"1.23","r":"1.31","b":"0.335","q":"0.718627475","k":"0.069635209"},{"l":"1.31","r":"1.4","b":"0.384","q":"0.685655525","k":"0.081467247"}];
for(let i=0;i<tangentRows.length;i++){const z=tangentRows[i],q=f(z.q),k=f(z.k),l=z.l==="lo"?lo:z.l;
 lt("tangent"+i+" slope upper",TD(z.b),q);lt("tangent"+i+" intercept upper",is(T(z.b),im(z.b,TD(z.b))),k);lt("tangent"+i+" slope<.85",q,".85");
 gt("tangent"+i+" left lower",Flow(l,q,k),".89790");gt("tangent"+i+" right lower",Flow(z.r,q,k),".89790");
}
for(const p of["1.4","quarter"])gt("later lower secondary endpoint "+p,Flow(p==="quarter"?hp:p,f(".62"),kk),".89800");
function Fup(x){const q=f(".633");return is(ia(ia(ia(hp,x),f("-.0497").sub(kk).add(g.add(q).div(2))),im(g,ia(sinI(x),cosI(x)))),im(R,rootI(ia(g.pow(2).add(q.pow(2)),im(g.mul(q).mul(2),sinI(x))))));}
gt("upper secondary support concavity",is(g,id(im(R,g.add(".633")),4)),0);
for(const x of[".02",".7"])gt("upper secondary endpoint "+x,Fup(x),".91100");
gt("lower primary core-corner barrier atleft",ia(".5",ia(im(ia(dc,".5"),cosI(lo)),sinI(lo))),"1.5");
function areq(phi){return ia(".5",ia(id(sinI(phi),2),im("13/12",cosI(phi))));}
function bz(phi){return is(rootI(is(Q,ip(ia(areq(phi),".5"),2))),".5");}
gt("lower primary requires phi>1.12",areq("1.12"),a0[1]);
lt("bzero(1.4)<.551",bz("1.4"),".551");lt("r(.551)<.65",rr(".551"),".65");lt("T''(.551)<0",TDD(".551"),0);
gt("sin1.12>.9",sinI("1.12"),".9");lt("cos1.12<.436",cosI("1.12"),".436");
gt("zero boundary contact-derivative increases",f(".557").mul(".757").div(".65").sub(f(".65").mul(".436").div(f(".9").pow(2))),0);
lt("zero boundary contact derivative at1.4",is(id(im(g,rr(bz("1.4"))),sinI("1.4")),TD(bz("1.4"))),"-.013");
const kap=is(a0,".5"),alpha2=f("205/144");
function NN(m){return is(is(im(Q,im(m,ia(im(2,m),1))),im(m,ip(ia(m,1),3))),Q.mul(alpha2));}
lt("zero-boundary second numerator upper",NN(kap),"-1.8");
gt("zero-boundary second speed magnitude",f("1.8").div(f("1.051").pow(3)),"1.55");
gt("zero-boundary cost curvature>.94",f(".610").mul("1.55"),".94");
const ph0=f("1.383036"),b0=bz(ph0),v0=is(im("13/12",sinI(ph0)),id(cosI(ph0),2)),bp0=id(v0,rr(b0));
const K0=is(is(ph0,".0497"),T(b0)),KD0=is(1,im(TD(b0),bp0));
gt("zero-boundary reference value",K0,".89777657");
lt("zero-boundary reference derivative upper",KD0,".000001");gt("zero-boundary reference derivative lower",KD0,"-.000001");
gt("whole zero-boundary quadratic lower",is(K0,id(ip(KD0,2),"1.88")),".89777656");
const eps=f(".02");
lt("upper strip axis4 core coordinate<.5",ia("-.5",ia(id(is(a0,".5"),cosI(eps)),id(sinI(eps),im(12,cosI(eps))))),".5");
gt("upper strip axis3 cost derivative",f(1).sub(g.mul(".4")),0);
const speed=ia(im(is(a0,".5"),id(sinI(eps),ip(cosI(eps),2))),id("1/12",ip(cosI(eps),2)));
lt("upper strip axis4 coordinate speed",speed,".105");gt("upper strip axis4 cost derivative",f(1).sub(g.mul(".105")),0);
gt("upper strip axis3 zero exit a>.992",is(1,im(".4",sinI(eps))),".992");
gt("upper strip axis4 zero exit a>.992",is(ia(".5",id(cosI(eps),2)),id(sinI(eps),12)),".992");
lt("a(.81)<.992",a(".81"),".992");
gt("upper strip zero-core exit cost",is(is(hp,".0497"),T(".81")),".906");
gt("lower primary later domain included",is(hp,".171"),"1.399");
lt("lower primary later overcover reaches1.4",is(hp,".171"),"1.4");
const C10=trigpoly("cos",10),C8=trigpoly("cos",8),S11=trigpoly("sin",11),S9=trigpoly("sin",9);
for(const [name,q,xlo,xhi,dir,coef,sp,allow,floors] of[
 ["lower",f(".62"),"0",".171",-1,g.mul("13/12"),S11,f(".000000001"),[".0136520",".0162755",".0174316",".0172488",".0158580",".0133907",".0099778",".0057480",".0008271"]],
 ["upper",f(".633"),".02",".7",1,g.div(-12),S9,f(".00001"),[".0617974",".4122007",".7506755","1.0578577","1.3123765","1.4933330","1.5837907","1.5742478","1.4631437"]]
]){
 const K=PI[0].div(2).sub(".0497").sub(kk).add(g.add(q).div(2)).sub(gamma);
 const A=add(add(mul(C10,[K,f(dir)]),[g]),scale(sp,coef)),P=add(mul(A,A),scale(add([g.pow(2)],scale(mul(C8,C8),q.pow(2))),Q.neg()));
 let tail=f(0);for(let j=9;j<P.length;j++)if(P[j].lt(0))tail=tail.add(P[j].neg().mul(f(xhi).pow(j)));
 lt(name+" primary negative tail",tail,allow);
 const P8=P.slice(0,9);P8[0]=P8[0].sub(allow);const bs=bern(P8,xlo,xhi);
 for(let j=0;j<bs.length;j++)gt(name+" primary Bernstein "+j,bs[j],floors[j]);
 gt(name+" squared numerator angle factor",K.sub(xhi),0);
 tables.push({name,interval:[xlo,xhi],degree:8,tail:tail.str(),allowance:allow.str(),power_coefficients:P8.map(t=>t.str()),bernstein_coefficients:bs.map(t=>t.str()),printed_lower:floors});
}
for(const z of["1.14",".89790",".89800",".91100",".89777656",".906",".89777"])gt("final "+z+" exceeds gamma",f(z),gamma);
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"0011011 edge3 O- to C+, whole quarter-one interval, all axes/core pieces; imports aligned mixed theorem only",comparisons:checks.length,checks,tangentRows,tables};

})();
process.stdout.write(JSON.stringify(result,null,2)+'\n');
if(result.status!=='PASS')process.exitCode=1;
