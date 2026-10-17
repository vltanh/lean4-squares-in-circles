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
const report={status:"PASS",fixed_comparisons:checks.length,scope:"Ten complete named mixed zero-quarter regimes; all costs >449/500=.898>17953/20000.",Q:Q.toString(),tables,checks};
if(typeof console!=="undefined")console.log(JSON.stringify(report,null,2));

