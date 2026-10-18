"use strict";
// Exact fixed-comparison checker for ten mixed zero-quarter contact families.
// All arithmetic is rational BigInt. No numerical optimizer or adaptive box cover.
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){let t=a%b;a=b;b=t;}return a;}
class Rat{
  constructor(n,d=1n){n=BigInt(n);d=BigInt(d);if(d<0n){n=-n;d=-d;}if(!d)throw Error("zero denominator");let g=gcd(n,d);this.n=n/g;this.d=d/g;}
  add(b){b=rr(b);return new Rat(this.n*b.d+b.n*this.d,this.d*b.d);}
  neg(){return new Rat(-this.n,this.d);}
  sub(b){return this.add(rr(b).neg());}
  mul(b){b=rr(b);return new Rat(this.n*b.n,this.d*b.d);}
  div(b){b=rr(b);return new Rat(this.n*b.d,this.d*b.n);}
  pow(k){return new Rat(this.n**BigInt(k),this.d**BigInt(k));}
  cmp(b){b=rr(b);let v=this.n*b.d-b.n*this.d;return v<0n?-1:v>0n?1:0;}
  toString(){return this.d===1n?String(this.n):this.n+"/"+this.d;}
}
function rr(x){if(x instanceof Rat)return x;if(typeof x==="bigint")return new Rat(x);let s=String(x);if(s.includes("/")){let [n,d]=s.split("/");return new Rat(n,d);}if(s.includes(".")){let neg=s[0]==="-";if(neg)s=s.slice(1);let [a,b]=s.split(".");return new Rat((neg?-1n:1n)*BigInt(a+b),10n**BigInt(b.length));}return new Rat(s);}
function ii(x){return Array.isArray(x)?x:[rr(x),rr(x)];}
function ia(a,b){a=ii(a);b=ii(b);return[a[0].add(b[0]),a[1].add(b[1])];}
function ineg(a){a=ii(a);return[a[1].neg(),a[0].neg()];}
function isub(a,b){return ia(a,ineg(b));}
function im(a,b){a=ii(a);b=ii(b);let z=[a[0].mul(b[0]),a[0].mul(b[1]),a[1].mul(b[0]),a[1].mul(b[1])];z.sort((x,y)=>x.cmp(y));return[z[0],z[3]];}
function idiv(a,b){b=ii(b);if(b[0].cmp(0)<=0&&b[1].cmp(0)>=0)throw Error("division across zero");return im(a,[rr(1).div(b[1]),rr(1).div(b[0])]);}
function ipow(a,k){a=ii(a);if(k===0)return ii(1);if(k%2===0&&a[0].cmp(0)<0&&a[1].cmp(0)>0){let z=[a[0].pow(k),a[1].pow(k)].sort((x,y)=>x.cmp(y));return[rr(0),z[1]];}let z=[a[0].pow(k),a[1].pow(k)].sort((x,y)=>x.cmp(y));return z;}
function isqrt(n){if(n<0n)throw Error("negative root");if(n<2n)return n;let x=1n<<BigInt((n.toString(2).length+1)>>1);while(true){let y=(x+n/x)>>1n;if(y>=x)return x;x=y;}}
function root(a){a=ii(a);if(a[0].cmp(0)<0)throw Error("negative interval root");let scale=10n**14n;let lo=isqrt(a[0].n*scale*scale/a[0].d),hi=isqrt(a[1].n*scale*scale/a[1].d)+1n;return[new Rat(lo,scale),new Rat(hi,scale)];}
function trig(x,cosine){x=rr(x);if(x.cmp(0)<0||x.cmp(1)>0)throw Error("trig range");let term=cosine?rr(1):x,sum=term,lo;for(let j=1;j<=8;j++){let den=cosine?(2*j-1)*(2*j):(2*j)*(2*j+1);term=term.mul(x.pow(2)).div(den).neg();sum=sum.add(term);if(j===7)lo=sum;}return[lo,sum];}
function sin(x){return trig(x,false);}function cos(x){return trig(x,true);}
function dec(x,digits=9){x=rr(x);let sc=10n**BigInt(digits),n=x.n*sc/x.d;if(x.n<0n&&x.n*sc%x.d)n--;let neg=n<0n;if(neg)n=-n;let s=String(n).padStart(digits+1,"0");return(neg?"-":"")+s.slice(0,-digits)+"."+s.slice(-digits);}
function decup(x,digits=9){return dec(rr(x).neg(),digits).startsWith("-")?dec(rr(x).neg(),digits).slice(1):"-"+dec(rr(x).neg(),digits);}
const checks=[],tables=[];
function check(name,condition){if(!condition)throw Error("FAIL: "+name);checks.push(name);}
function gt(name,x,y){check(name,ii(x)[0].cmp(ii(y)[1])>0);}
function lt(name,x,y){check(name,ii(x)[1].cmp(ii(y)[0])<0);}
const Q=rr("9789/2500"),R=root(Q),d=isub(root(Q.div(2)),".5"),dc=ia(".5",idiv(root(2),24)),a0=isub(root(Q.sub(".25")),".5");
gt("d>.8992140",d,".8992140");lt("d<.8992141",d,".8992141");
gt("dc>.5589",dc,".5589");lt("dc<.559",dc,".559");gt("a0>1.414",a0,"1.414");lt("R<2",R,2);
const left=rr(".3024"),right=rr(".44152");
lt("negative-core feasibility excludes phi<=.3024",im(isub(d,".5"),ia(sin(left),cos(left))),".5");
lt("negative-angle feasibility excludes x>=.44152",ia(isub(d,".5"),isub(im(isub(dc,".5"),cos(right)),im(ia(dc,".5"),sin(right)))),0);
gt("cos(.44152)>.9",cos(right),".9");
const A=[
{name:"edge1 C- O-",cd:"-.11418",p:".09133",q:".88074",g:".62095",pieces:[[".3024",".6","1.48"],[".6",".7","2"]]},
{name:"edge3 C- O-",cd:".07943",p:".19335",q:".76744",g:".62750",pieces:[[".3024",".7","1.463"]]},
{name:"edge0 O+ C+ reversed",cd:"-.25648",p:"0",q:".94766",g:".62095",pieces:[[".3024",".6","1.443"],[".6",".7","2"]]},
{name:"edge3 O+ C+ reversed",cd:"-.94615",p:"-.51554",q:"1.19909",g:".58829",pieces:[[".4",".7","1.6"]]}
];
function full(t,l,row){let p=rr(row.p),q=rr(row.q),s=sin(t),c=cos(t),N=root(ia(p.pow(2).add(q.pow(2)).add(rr(l).pow(2)),im(rr(l).mul(2),isub(im(p,s),im(q,c)))));let F=isub(ia(rr(t).add(row.cd).add(rr(l).add(p).sub(q).div(2)),im(l,ia(s,c))),im(R,N));return{F,N};}
for(const row of A)for(const [lo,hi,l]of row.pieces){
 gt(row.name+" multiplier above core slope "+l,l,row.g);
 gt(row.name+" norm concavity "+l,rr(l).pow(2),rr(row.p).pow(2).add(rr(row.q).pow(2)));
 let vals=[];
 for(const t of [lo,hi]){let z=full(t,l,row);gt(row.name+" full support "+t+" lambda "+l,z.F,".898");vals.push({phi:t,N_upper:decup(z.N[1]),cost_lower:dec(z.F[0])});}
 tables.push({family:"A full circle",row:row.name,range:[lo,hi],lambda:l,values:vals});
}
const ad=A[3],ld=rr("1.19");
gt("D multiplier above core slope",ld,ad.g);gt("D nonnegative secondary coefficient",rr(ad.q).sub(ld),0);
gt("D axial envelope decreasing",ld.mul(".914").mul(".92"),1);
gt("cos(.4)>.92",cos(".4"),".92");
gt("D diagonal envelope increasing",rr(1).sub(ld.mul(".4")),0);
function diagonalA(t){return ia(rr(t).add(ad.cd),ia(im(rr(ad.q).sub(ad.p),d),im(ld,isub(".5",im(isub(d,".5"),ia(sin(t),cos(t)))))));}
function axialA(t){return ia(rr(t).add(ad.cd).add(ld.div(2)),ia(im(rr(ad.p).neg(),a0),ia(im(ld.div(2),cos(t)),im(ld.neg(),im(isub(a0,".5"),sin(t))))));}
let za=diagonalA(left),zb=axialA(".4");gt("D diagonal left endpoint",za,".898");gt("D axial right endpoint",zb,".898");
tables.push({family:"A endpoint support",row:ad.name,range:[".3024",".4"],lambda:"1.19",diagonal_lower:dec(za[0]),axial_lower:dec(zb[0])});
const B=[
{name:"edge0 O+ C-",cd:".14041",p:"0",q:".94766",g:".62095",method:"low"},
{name:"edge0 C+ O- reversed",cd:"-.21286",p:".13422",q:"1.03828",g:"1.08816",method:"high"},
{name:"edge1 O+ C-",cd:"-.05550",p:"0",q:".99940",g:"1.13855",method:"high"},
{name:"edge1 C+ O- reversed",cd:".28271",p:"-.09133",q:".88074",g:".62095",method:"contact"},
{name:"edge3 O+ C-",cd:"-.72700",p:".51554",q:"1.19909",g:"1.04073",method:"high endpoint"},
{name:"edge3 C+ O- reversed",cd:".27632",p:"-.19335",q:".76744",g:"1.04729",method:"high"}
];
for(const row of B.filter(z=>z.method.startsWith("high"))){
 let p=rr(row.p),q=rr(row.q),g=rr(row.g);
 gt(row.name+" core slope>1",g,1);
 if(row.method==="high"){
   gt(row.name+" source diagonal condition",g,q.sub(p.cmp(0)<0?p:0));
 }else{
   gt(row.name+" source endpoint comparison",im(p,a0),im(p.add(q).sub(g),d));
   lt(row.name+" positive endpoint secondary coefficient",g.div(".9"),q);
 }
 let z=ia(row.cd,ia(im(p.add(q),d),im(g,isub(1,d))));
 gt(row.name+" monotone endpoint",z,".898");tables.push({family:"B monotone",row:row.name,endpoint_lower:dec(z[0])});
}
gt("B high envelope derivative quotient>1",rr(".0589").sub(rr(".4").pow(2).div(4)),0);
const bl=B[0],ll=rr(bl.q);
gt("B low core diagonal condition",im(ll,cos(right)),bl.g);
gt("B low initial derivative",isub(im(ll,ia(".5",dc)),1),0);
function lowB(t){return ia(rr(t).neg().add(bl.cd).add(ll.div(2)),ia(im(bl.g,dc),ia(im(ll,im(isub(".5",dc),cos(t))),im(ll,im(ia(".5",dc),sin(t))))));}
for(const t of ["0",".44152"]){let z=lowB(t);gt("B low endpoint "+t,z,".898");tables.push({family:"B low",phi_minus_x:t,cost_lower:dec(z[0])});}
const bc=B[3],p=rr(bc.p),q=rr(bc.q),g=rr(bc.g);
gt("B contact derivative in target coordinate",im(q,cos(right)),g);
function curve(t){let b=ia(".5",ia(im(ia(".5",dc),sin(t)),im(isub(".5",dc),cos(t)))),bp=isub(im(ia(".5",dc),cos(t)),im(isub(".5",dc),sin(t))),bpp=isub(".5",b),Y=root(isub(Q,ipow(ia(b,".5"),2)));
let fp=isub(q,im(p,idiv(ia(b,".5"),Y))),fpp=idiv(p.neg().mul(Q),ipow(Y,3));
let F=ia(rr(t).neg().add(bc.cd),ia(im(p,isub(Y,".5")),ia(im(q,b),im(g,dc))));
let Fp=isub(im(fp,bp),1),Fpp=ia(im(fpp,ipow(bp,2)),im(fp,bpp));
return{b,bp,Y,F,Fp,Fpp};}
let end=curve(right);lt("B contact b endpoint<.8993",end.b,".8993");
gt("B contact radical lower from b bound",Q.sub(rr("1.3993").pow(2)),rr("1.399").pow(2));
gt("B contact bprime>.95",rr("1.0589").mul(".9"),".95");
let bracket=rr(".092").mul(3).mul(4).mul("1.4").div(rr("1.399").pow(5)).mul(rr("1.06").pow(2).add(rr(".059").pow(2))).add(rr(3).mul(".092").mul(4).div(rr("1.399").pow(3)).mul(".059")).sub(".88");
lt("B contact Fthird<-.5",bracket.mul(".95"),"-.5");
let mid=curve(".14");lt("B contact Fprime reference",mid.Fp,"-.0055");lt("B contact Fsecond upper",mid.Fpp,".005");gt("B contact Fsecond lower",mid.Fpp,"-.005");
lt("B contact strong-concavity derivative maximum",rr("-.0055").add(rr(".005").pow(2)),0);
gt("B contact terminal value",end.F,".898");
tables.push({family:"B core-diagonal contact",reference:".14",Fprime_upper:decup(mid.Fp[1]),Fsecond_lower:dec(mid.Fpp[0]),Fsecond_upper:decup(mid.Fpp[1]),right:".44152",terminal_lower:dec(end.F[0])});

/* All remaining mixed zero-quarter regimes. */
{
const Cs=B.map(z=>({...z,p:rr(z.p).neg().toString(),name:"C-source complementary "+z.name}));
const cap=rr(".32"),s32=sin(cap),c32=cos(cap);
lt("C-source negative-angle cap .32",ia(isub(dc,".5"),isub(im(isub(d,".5"),c32),im(ia(d,".5"),s32))),0);
gt("cos .32>.949",c32,".949");lt("sin .32<.315",s32,".315");
function cContact(x,z){
 let s=sin(x),c=cos(x),Z=ia(isub(".5",dc),c),Y=root(isub(Q,ipow(Z,2))),U=isub(im(c,Y),im(s,Z)),V=ia(im(s,Y),im(c,Z));
 let H=ia(rr(x).neg().add(z.cd),ia(im(z.g,dc),ia(im(rr(z.p).neg(),isub(U,".5")),im(z.q,isub(V,".5")))));
 let bcore=ia(".5",ia(im(ia(".5",d),s),im(isub(".5",d),c)));
 let G=ia(rr(x).neg().add(z.cd),ia(im(rr(z.q).sub(z.p),d),im(z.g,bcore)));
 return{Z,Y,U,V,H,G};
}
let geo0=cContact(0,Cs[0]),geo1=cContact(cap,Cs[0]);
gt("C-contact Y>1.74",geo0.Y,"1.74");lt("C-contact U0<1.75",geo0.U,"1.75");gt("C-contact V0>.94",geo0.V,".94");
gt("C-contact Uend>1.39",geo1.U,"1.39");lt("C-contact Vend<1.41",geo1.V,"1.41");
gt("C-contact f decreasing",rr(".949").mul(rr("1.74").pow(2)).sub(rr(".942").mul(rr(".315").pow(2))),0);
gt("C-contact M positive",rr(".767").mul("1.39").sub(rr(".516").mul("1.41")),0);
lt("C-contact M derivative negative",rr(".194").mul("1.75").sub(rr(".767").mul(".94")),0);
gt("C-contact e1 state monotonicity",rr(Cs[3].q).sub(rr(Cs[3].g).mul("1.32")),0);
lt("C-contact e3 state monotonicity1",rr(Cs[5].q).add(Cs[5].p),Cs[5].g);
lt("C-contact e3 state monotonicity2",Cs[5].q,im(Cs[5].g,c32));
gt("C outer-diagonal high-slope monotonicity",rr("1.04").mul("1.399"),1);
gt("C outer-diagonal trigonometric endpoint",ia(im(ia(".5",d),c32),im(isub(d,".5"),s32)),"1.399");
lt("C outer-diagonal low-slope monotonicity",rr(".621").pow(2).mul(rr("1.4").pow(2).add(rr(".4").pow(2))),1);
for(const z of Cs){
 let x0=cContact(0,z),x1=cContact(cap,z);
 gt(z.name+" H0",x0.H,".898");gt(z.name+" Hcap",x1.H,".898");
 let gl=rr(z.g).cmp(1)>0?x0.G:x1.G;gt(z.name+" G selected endpoint",gl,".898");
 tables.push({family:"all C-source negative phi",row:z.name,H0:dec(x0.H[0]),Hcap:dec(x1.H[0]),G_lower:dec(gl[0])});
}
function coFull(t,l,z){return ia(full(t,l,z).F,im(rr(z.g).sub(l),dc));}
function coDiag(t,l,z){return ia(rr(t).add(z.cd),ia(im(rr(z.g).sub(l),dc),ia(im(rr(z.q).sub(z.p),d),im(l,isub(".5",im(isub(d,".5"),ia(sin(t),cos(t))))))));}
function coAx(t,l,z){return ia(rr(t).add(z.cd).add(rr(l).div(2)),ia(im(rr(z.g).sub(l),dc),ia(im(rr(z.p).neg(),a0),ia(im(rr(l).div(2),cos(t)),im(rr(l).neg(),im(isub(a0,".5"),sin(t)))))));}
function coAxD(t,l){return isub(1,im(l,ia(im(".5",sin(t)),im(isub(a0,".5"),cos(t)))));}
const r0=idiv(".5",ia(a0,".5"));
function axialActivation(t,l,z){return ia(im(r0,ia(z.p,im(l,sin(t)))),isub(z.q,im(l,cos(t))));}
function diagActivation(t,l,z){gt(z.name+" diagonal y negative "+t,im(l,cos(t)),z.q);gt(z.name+" diagonal coefficient order "+t,im(l,isub(cos(t),sin(t))),rr(z.p).add(z.q));}
function normRow(z,lo,hi,l){
 gt(z.name+" positive norm multiplier core",l,rr(z.g).sub("1/1000000000000"));
 gt(z.name+" positive norm concavity",rr(l).pow(2),rr(z.p).pow(2).add(rr(z.q).pow(2)));
 for(const t of[lo,hi])gt(z.name+" positive full norm "+t,coFull(t,l,z),".898");
 tables.push({family:"C-source positive full-circle",row:z.name,range:[lo,hi],lambda:String(l),left:dec(coFull(lo,l,z)[0]),right:dec(coFull(hi,l,z)[0])});
}
for(const j of[1,2]){
 let z=Cs[j],l=z.g;diagActivation(".1",l,z);gt(z.name+" early diagonal monotone",rr(1).sub(rr(l).mul(".4")),0);gt(z.name+" diagonal0",coDiag(0,l,z),".898");
 normRow(z,".1",".4",l);gt(z.name+" axial activation .4",axialActivation(".4",l,z),0);gt(z.name+" axial primary sign .4",ia(z.p,im(l,sin(".4"))),0);
 lt(z.name+" axial derivative .4",coAxD(".4",l),0);lt(z.name+" axial derivative .7",coAxD(".7",l),0);gt(z.name+" axial value .7",coAx(".7",l,z),".898");
}
{let z=Cs[3],l=".93";normRow(z,"0",".1",l);gt(z.name+" axial activation .1",axialActivation(".1",l,z),0);lt(z.name+" axial derivative amplitude",rr(l).pow(2).mul(rr(".25").add(rr(".915").pow(2))),1);gt(z.name+" axial .1 value",coAx(".1",l,z),".898");}
{let z=Cs[5],l=z.g;diagActivation(".05",l,z);gt(z.name+" early diag derivative",rr(1).sub(rr(l).mul(".4")),0);gt(z.name+" diag0",coDiag(0,l,z),".898");normRow(z,".05",".7",l);}
{let z=Cs[0],l=z.q;gt(z.name+" multiplier core",l,z.g);lt(z.name+" axial amplitude",rr(l).pow(2).mul(rr(".25").add(rr(".915").pow(2))),1);gt(z.name+" axial0",coAx(0,l,z),".898");}
{let z=Cs[4],l=z.g;gt(z.name+" positive y",z.q,l);gt(z.name+" diagonal monotone",rr(1).sub(rr(l).mul(".4")),0);gt(z.name+" diagonal0",coDiag(0,l,z),".898");gt(z.name+" axial0>1.04",coAx(0,l,z),"1.04");lt(z.name+" axial derivative>-.09",rr(l).pow(2).mul(rr(".25").add(rr(".915").pow(2))),rr("1.09").pow(2));gt(z.name+" whole axial lower",rr("1.04").sub(rr(".7").mul(".09")),".898");}
for(const j of[0,3]){
 let z=B[j],l=rr(j===0?z.q:".93"),p=rr(z.p),q=rr(z.q),S=isub(rr(p.add(q).sub(l)).neg().div(2),im(R,root(p.pow(2).add(q.sub(l).pow(2)))));
 gt(z.name+" positive phi core coefficients",im(l,cos(".7")),z.g);gt(z.name+" positive phi derivative",rr(1).sub(l.div(12)),0);
 let F0=ia(rr(z.cd).add(l),ia(S,im(rr(z.g).sub(l),dc)));gt(z.name+" positive phi low endpoint",F0,".898");
}
gt("O-source positive phi high derivative",rr(1).sub(rr("1.14").mul(rr(".4").mul(".645").add(rr(1).div(12))).div(".58")),0);
lt("sin .7<.645",sin(".7"),".645");gt("cos² .7>.58",ipow(cos(".7"),2),".58");
const Js=[
{n:"O++ C e0",cd:"-.25648",p:"0",q:".94766",g:".62095"},
{n:"O++ C e1 reversed",cd:"-.11418",p:"-.09133",q:".88074",g:".62095"},
{n:"O++ C e3",cd:"-.94615",p:".51554",q:"1.19909",g:".58829"},
{n:"O++ C e3 reversed",cd:".07943",p:"-.19335",q:".76744",g:".62750"}];
lt("O++ C phi<=.4 impossible",ia(isub(d,".5"),isub(idiv(sin(".4"),12),im(".5",cos(".4")))),0);
lt("O++ C target corner impossible",rr(".4").add(rr(".645").div(12)).sub(".764"),0);
gt("O++ C source b>.828",rr(".5").add(rr(".764").div(2)).sub(rr(".645").div(12)),".828");
lt("O++ C source a<.97",Q.sub(rr("1.328").pow(2)),rr("1.47").pow(2));
gt("O++ C radial ratio>.9",rr("1.328").div("1.47"),".9");
lt("O++ C contact B<.1",rr(".9").sub(".828").div(".764"),".1");
for(const z of Js){
 let p=rr(z.p),q=rr(z.q),g=rr(z.g);
 if(p.cmp(0)<=0){
  gt(z.n+" source monotone",q.sub(g.div(".764")).sub(p.mul(".9")),0);
  gt(z.n+" lower at B0",rr(".4").add(z.cd).add(p.mul(".97")).add(q.mul(".828")),".898");
 }else{
  gt(z.n+" B0 endpoint lower",rr(".4").add(z.cd).add(p.mul(".899")).add(q.mul(".828")),".898");
  gt(z.n+" diagonal endpoint lower",rr(".4").add(z.cd).add(p.add(q).mul(".899")).sub(g.mul(".1")),".898");
 }
}
const Ks=[
{n:"C++ O e0",cd:"-.02953",p:"0",q:".99940",g:"1.08816"},
{n:"C++ O e1 reversed",cd:".12783",p:".13422",q:"1.03828",g:"1.13855"},
{n:"C++ O e3 reversed",cd:".46969",p:".33147",q:"1.13360",g:"1.04073"},
{n:"C++ O e3",cd:"-.02145",p:"0",q:".71553",g:"1.04729"}];
lt("C++ O phi<=.4 impossible",ia(isub(dc,".5"),isub(im(isub(a0,".5"),sin(".4")),im(".5",cos(".4")))),0);
lt("R<1.978788",R,"1.978788");gt("cos .7>.764",cos(".7"),".764");
for(let j=0;j<3;j++){
 let z=Ks[j],p=rr(z.p),q=rr(z.q),g=rr(z.g),N=root(ia(p.pow(2).add(q.pow(2)).add(g.pow(2)),im(g.mul(2),isub(im(p,sin(".4")),im(q,cos(".4"))))));
 let F=isub(ia(rr(".4").add(z.cd).add(g.add(p).add(q).div(2)),im(g,sin(".4"))),im(R,N));
 let speed=j===0?rr("1"):j===1?rr("1.047"):g;
 if(j<2)gt(z.n+" norm speed",speed.pow(2),p.pow(2).add(q.pow(2)));
 gt(z.n+" value .4",F,".98");
 gt(z.n+" derivative>-.27",rr(1).add(g.mul(".764")).sub(rr("1.978788").mul(speed)),"-.27");
}
gt("C++ O full interval lower",rr(".98").sub(rr(".3").mul(".27")),".898");
{let z=Ks[3],g=rr(z.g);gt(z.n+" positive target secondary",im(g,cos(".7")),z.q);let v=coAx(".4",g,z);gt(z.n+" axial .4>1.01",v,"1.01");lt(z.n+" axial derivative>-.1",g.pow(2).mul(rr(".25").add(rr(".915").pow(2))),rr("1.1").pow(2));gt(z.n+" axial whole lower",rr("1.01").sub(".03"),".898");}
const Ps=[
{n:"primary -- e1",cd:".12783",p:"-.13422",q:"1.03828",g:"1.13855",l:"1.95"},
{n:"primary -- e3",cd:".46969",p:"-.33147",q:"1.13360",g:"1.04073",l:"1.95"},
{n:"primary -- e0 reversed",cd:"-.02953",p:"0",q:".99940",g:"1.08816",l:"2.01"},
{n:"primary -- e3 reversed",cd:"-.02145",p:"0",q:".71553",g:"1.04729",l:"1.95"}];
lt("core-source primary impossible",rr(1).div(12).sub(rr("1.399").mul(".764")).add(rr(".4").mul(".645")),0);
lt("outer-source negative-target primary phi<=.4 impossible",ia(isub(a0,".5"),isub(im(isub(dc,".5"),sin(".4")),im(ia(dc,".5"),cos(".4")))),0);
lt("primary projection with unfavorable sign at 0",isub(isub(a0,".5"),ia(dc,".5")),0);
lt("primary projection with unfavorable sign at .7",isub(isub(a0,".5"),ia(im(ia(dc,".5"),cos(".7")),im(".5",sin(".7")))),0);
gt("primary core-corner endpoint ordering",rr("1.95").mul(rr(".389").add(rr(".414").mul(".764"))),"1.139");
gt("primary corner envelope concavity",rr("1.0589").mul(".764").sub(rr(".059").mul(".645")),0);
gt("sin .4>.389",sin(".4"),".389");gt("sqrt2-1>.414",isub(root(2),1),".414");
function primarySide(t,z){
 let s=sin(t),c=cos(t),g=rr(z.g),lam=idiv(g,s),X=isub(lam,z.p),N=root(ia(ipow(X,2),rr(z.q).pow(2))),Z=idiv(im(R,X),N);
 let H=isub(ia(rr(t).add(z.cd).add(rr(z.p).neg().add(z.q).add(g).div(2)),ia(lam,im(g.mul(13).div(12),idiv(c,s)))),im(R,N));
 return{H,Z};
}
for(const z of Ps){
 let l=rr(z.l),N=root(l.sub(z.p).pow(2).add(rr(z.q).pow(2))),C=rr(z.cd).add(l).add(rr(z.p).neg().add(z.q).div(2));
 for(const t of[".4",".7"]){
  let F=ia(rr(t).add(C),ia(im(z.g,dc),isub(ia(im(l,im(ia(".5",dc),cos(t))),im(l,im(isub(".5",dc),sin(t)))),im(R,N))));
  gt(z.n+" corner endpoint "+t,F,".898");
 }
 lt(z.n+" Z(.4)<1.913",primarySide(".4",z).Z,"1.913");lt(z.n+" Z(.6)<1.85",primarySide(".6",z).Z,"1.85");
 gt(z.n+" side terminal",primarySide(".7",z).H,".898");
}
lt("primary side derivative first interval",rr(1).sub(rr(".825").pow(2)).add(rr("1.04").mul(rr(".913").mul(".825").sub(rr(13).div(12)))),0);
lt("primary side derivative second interval",rr(1).sub(rr(".764").pow(2)).add(rr("1.04").mul(rr(".85").mul(".764").sub(rr(13).div(12)))),0);
gt("cos .6>.825",cos(".6"),".825");
gt("primary positive-sign convexity",rr(2).mul("1.0589").mul(".764").sub(rr(".915").mul(rr(1).add(rr(".764").pow(2)))),0);
for(const z of B){
 let t=rr(".55"),s=sin(t),c=cos(t),g=rr(z.g),A=ia(".5",dc),bb=isub(a0,".5");
 let F=ia(t.add(z.cd).add(g.div(2)),ia(im(z.p,a0),im(g,idiv(isub(im(A,c),bb),s))));
 let Fp=ia(1,im(g,idiv(isub(im(bb,c),A),ipow(s,2))));
 gt(z.name+" primary tangent value",F,".98");gt(z.name+" primary tangent derivative lower",Fp,"-.4");lt(z.name+" primary tangent derivative upper",Fp,".4");
}
gt("primary positive-sign tangent lower",rr(".98").sub(rr(".15").mul(".4")),".898");
}
const report={status:"PASS",fixed_comparisons:checks.length,scope:"Complete mixed C/O zero-quarter pair regimes of0010111, conditional on stated exterior geometry and exact role labels; all costs>.898>.89765.",Q:Q.toString(),tables,checks};
if(typeof console!=="undefined")console.log(JSON.stringify(report,null,2));

