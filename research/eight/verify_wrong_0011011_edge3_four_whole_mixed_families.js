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
const checks=[];function gt(name,x,y=0){x=Array.isArray(x)?x:I(x);y=f(y);checks.push({name,pass:x[0].gt(y),lower:x[0].str(),upper:x[1].str(),threshold:y.str()});}
function lt(name,x,y=0){gt(name,ineg(x),f(y).neg());}
const Q=f("3.9156"),gamma=f(".89765"),ac=f("7/12"),d=is(rootI(Q.div(2)),".5"),dc=ia(".5",id(rootI(2),24)),a0=is(rootI(Q.sub(".25")),".5"),hp=id(PI,2),lo=is(hp,".7"),q=f(".704"),kap=is(a0,".5");
const E=f(".22042").sub(f(".34492").mul(ac)),G=f(".98439");
function a(B){return is(rootI(is(Q,ip(ia(B,".5"),2))),".5");}
function V(B){return ia(im("-.01025",a(B)),ia(im(".16031",B),im(".63457",im(a(B),B))));}
function M(B){return ia(im("-.02112",a(B)),ia(im(".29090",B),im(".44642",im(a(B),B))));}
gt("d>.899",d,".899");lt("d<.9",d,".9");gt("a0>1.4145",a0,"1.4145");lt("a0<1.415",a0,"1.415");
lt("core ac-dc<.025",is(ac,dc),".025");
lt("negative core corner affine-label loss",f(".34492").mul(".025").sub(f(".05334").div(4)),0);
gt("radial ratio>.261",id(".5",ia(a0,".5")),".261");
lt("radial derivative<1.5",f(4).div(f("1.399").pow(3)),"1.5");
lt("V second derivative negative",f("-1.26914").mul(".261").add(f(".01025").mul("1.5")),0);
lt("M second derivative negative",f("-.89284").mul(".261").add(f(".02112").mul("1.5")),0);
gt("V chord slope>.704",id(is(V(d),V(0)),d),q);
gt("M chord slope>.704",id(is(M(d),M(0)),d),q);
gt("V endpoint derivative positive",f(".17056"),0);
gt("M endpoint derivative positive",f(".31202"),0);
gt("positive outer to negative core direct",ia(is(lo,im(".01025",a0)),".16823"),"1.024");
const s=sinI(lo),c=cosI(lo);
lt("lower-half cos<.645",c,".645");gt("lower-half sin>.764",s,".764");
gt("normal secondary target coefficient positive",q.sub(G.mul(".645")),0);
gt("source coordinate lower bound",dc,".5");
const rows=[
 {name:"C-minus to O-minus",e:E,g:G,L0:im("-.02112",a0)},
 {name:"O-plus to C-plus by reversal",e:f(".04970"),g:f(".94831"),L0:im("-.01025",a0)}
];
for(const z of rows){
 const {e,g,L0}=z,base=ia(f(e).neg(),L0);
 function f1(phi){const W=id(ia(1,ia(sinI(phi),cosI(phi))),2);return ia(ia(phi,base),is(im(g,W),im(g,im(a0,sinI(phi)))));}
 gt(z.name+" secondary endpoint",f1(lo),".922");
 gt(z.name+" lower secondary derivative",is(1,ia(im(g.div(2),s),im(g,im(kap,c)))),0);
 gt(z.name+" secondary derivative increases",is(im(kap,s),id(c,2)),0);
 gt(z.name+" primary monotonicity kappa",im(g,kap),".645");lt(z.name+" g<1",g,1);
 const F2low=ia(ia(ia(lo,base),g.div(2)),im(g,id(is(c,kap),s)));
 gt(z.name+" lower primary endpoint",F2low,".945");
 const C0=ia(base,is(q.div(2),im(g,dc)));
 function U2(x){return ia(ia(ia(ia(hp,x),base),g.div(2)),ineg(ia(im(g,id(kap,cosI(x))),im(g.div(12),id(sinI(x),cosI(x))))));}
 for(const x of[0,".7"])gt(z.name+" upper primary endpoint"+x,U2(x),"1.11");
 const F3=ia(ia(lo,C0),ia(im(q.div(-12),s),im(q,im(ia(dc,".5"),c))));
 gt(z.name+" other secondary lower endpoint",F3,"1.058");
 const L=im(q,ia(d,".5"));lt(z.name+" L<1",L,1);gt(z.name+" L>0",L,0);
 const F4=ia(ia(im(L,hp),im(is(1,L),lo)),is(C0,id(q,im(12,s))));
 gt(z.name+" other primary lower whole bound",F4,"1.23");
 function U4(x){return ia(ia(ia(hp,x),C0),ineg(ia(id(q.div(12),cosI(x)),im(q,id(im(kap,sinI(x)),cosI(x))))));}
 for(const x of[0,".7"])gt(z.name+" other primary upper endpoint"+x,U4(x),"1.26");
}
gt("secondary lower whole derivative",is(1,im(q,ia(dc,f("7/12")))),0);
gt("secondary upper whole derivative",is(1,im(q,ia(dc,f("-5/12")))),0);
const plusbase=is(im("-.02112",a0),".01449");
gt("positive core to negative outer late direct",ia(".95",plusbase),".905");
const Z1=ia(ia(lo,plusbase),im(q,is(id(ia(1,ia(s,c)),2),im(a0,s))));
gt("positive core to negative outer early axis1",Z1,".912");
gt("positive core to negative outer early axis1 derivative",is(1,im(q,rootI(ia(".25",ip(kap,2))))),0);
const Z2=ia(ia(ia(lo,plusbase),q.div(2)),im(q,id(is(c,kap),s)));
gt("positive core to negative outer early axis2",Z2,".929");
gt("positive core target kappa product",im(q,kap),".64");
gt("positive core early axis2 derivative numerator",f(1).sub(q).sub(f(".645").mul(".005")),0);
const Z3=ia(ia(lo,plusbase),im(q,ia(".5",im(f("-1/12"),1))));
gt("positive core early axis3 simple bound",Z3,"1.119");
lt("positive core early axis4 impossible",is(ia(ac,im(d,sinI(".95"))),ia(1,im(d,cosI(".95")))),0);
for(const z of["1.024",".922",".945","1.11","1.058","1.23","1.26",".905",".912",".929","1.119"])gt("final "+z+" exceeds gamma",f(z),gamma);
return{status:checks.every(x=>x.pass)?"PASS":"FAIL",scope:"Four whole mixed edge3/edge5 families: C- O-, O+ C+, C+ O-, O+ C-; all core pieces and retained axes",comparisons:checks.length,checks};

})();
process.stdout.write(JSON.stringify(result,null,2)+'\n');
if(result.status!=='PASS')process.exitCode=1;
