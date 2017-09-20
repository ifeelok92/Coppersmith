# include <NTL/ZZX.h>
# include <NTL/ZZ.h>
# include <NTL/tools.h>
# include <NTL/mat_ZZ.h>
# include<NTL/LLL.h>
# include <NTL/ZZ_pX.h>
# include <fstream>

using namespace std;
using namespace NTL;

ZZ lbound;
vec_ZZ RL;



void xX(ZZX& f,ZZ X){
  long degree = deg(f);
  for(int i=1;i<=degree;i++){
    f.rep[i] *= power(X,i);
  }
}



void inverse_xX(vec_ZZ& f,ZZ X){

  for(int i=0;i<f.length();i++){
    f[i] /= power(X,i);
  }
}



ZZ norm2(const vec_ZZ& v){
  ZZ sqr_sum(0);
  for(int k=1;k<=v.length();k++){
    add(sqr_sum,sqr_sum,sqr(v(k)));
  }
  return sqr_sum;
}



//提前终止：算各系数绝对值之和
long SatNorm(const vec_ZZ& z)
{
   long n = z.length();
   long j;
   ZZ sum;
   sum = 0;

   for (j = 0; j < n; j++)
   {
      add(sum,sum,abs(z[j]));
   }

   if(sum<lbound)
   {
       RL = z;
       return 1;
   }
   else
       return 0;
}



//算多项式在a点的值f(a)
ZZ evaluation(ZZX &f, ZZ a)
{
    int n = deg(f);
    int i;
    ZZ sum;
    sum =0;
    for(i=0; i<=n; i++)
    {
        add(sum,sum, coeff(f,i)*power(a,i));
    }
    return sum;
}



//由gij(xX)生成格
mat_ZZ gen_lattice(const long h,ZZX& f,const ZZ N,const ZZ X){
  long delta=deg(f);
  long n=delta*h;

  ZZX g[h][delta];
  ZZX fi; set(fi);
  xX(f,X); //f(x)->f(xX)
  ZZ Nh;
  Nh=power(N,h-1);
  lbound=Nh;
  mat_ZZ B;
  B.SetDims(n,n);

  for(long i=0;i<h;i++){
   // cout<<"================="<<endl;
  //  cout<<"round "<<i<<endl;
    ZZX xx;
    SetCoeff(xx,0,1);
   // cout<<"xx="<<xx<<endl;
   //cout<<"fi is "<<fi<<endl;


    for(long j=0;j<delta;j++){
      //cout<<"\t j = "<<j<<endl;
      mul(g[i][j],Nh,fi); //N^(h-1-i)f(xX)^i
      mul(g[i][j],g[i][j],xx); //上式×(xX)
      //cout<<"g[i][j]="<<g[i][j]<<endl;
      LeftShift(xx,xx,1);
      mul(xx,xx,X);

      vec_ZZ u(g[i][j].rep);
      //cout<<"u="<<u<<endl;

      for(int k=0;k<=deg(g[i][j]);k++){
        B(i*delta+j+1)(k+1)=u[k];
      }
    }
    mul(fi,fi,f);
    Nh/=N;

  }
  ofstream fout("matrix_data.txt");
  fout<<B;
  fout.close();

  return B;

}



//l:RSA prime bit length
//delta:polynomial degree
//return X
ZZ* gen_param(long l,long delta,long& h,ZZ& N){
  ZZ p,q,X,Y;
  RR c;
  ZZ* pp;
  pp = new ZZ[2];

  p=GenPrime_ZZ(l);
  q=GenPrime_ZZ(l);
  N=p*q;
  cout<<"N = "<<N<<endl;


    cout<<"enter h"<<endl;
    cin>>h;

    if(h==0)
      h=2*l/delta;
    else{
      cout<<"asympltotic value of h is "<<h<<endl;
    }
  
  cout<<"h = "<<h<<endl;
  long m=h*delta;
  cout<<"dim = "<<m<<endl;
  cout<<"delta = "<<delta<<endl;
    //X = floor(2^{-0.5}*N^{(h-1)/(m-1)}*m^{-1/(m-1)};
    RoundToZZ(Y,pow(to_RR(N),to_RR(h-1)/to_RR(m-1))/pow(to_RR(m),1/to_RR(m-1))/pow(to_RR(2.0), to_RR(0.5)));
    cout<<"X = "<<Y<<endl;

    pp[0]= Y;


    RR k;
    RR temp1,temp2,temp3,temp4;
    RR RX;
    c=pow(to_RR(1.5),to_RR(m)); //c=1.5^n
    temp1=pow(to_RR(m),to_RR(1.5)); //m^1.5
    temp2=power((to_RR(3)*c-to_RR(2))/(to_RR(2)*c-to_RR(2)),m-1);
    temp3=to_RR(1)/c;

    k=temp1*temp2;
    k*=temp3;
    k+=to_RR(1);
    RX=pow(to_RR(N),to_RR(h-1)/to_RR(m-1))/pow(to_RR(m),1/to_RR(m-1))/pow(to_RR(2.0), to_RR(0.5));
    temp4=pow(k,to_RR(2)/to_RR(m-1));//k^(2/(n-1))
    RX/=temp4;
    RoundToZZ(X,RX);
    cout<<"rounding X = "<<X<<endl;
    pp[1]=X;

  return pp;
}



void gen_poly(ZZ_pX& f,long fd,const ZZ r){
  //ZZ r;
  //r = X-1;
  //f=x-r
  SetCoeff(f,0,to_ZZ_p(-r));
  SetCoeff(f,1,1);

  // g is a random polynomial with degree fd-1
  ZZ_pX g;
  while(1)
  {
    random(g,fd);
    if(deg(g)==fd-1)
      break;
  }

  //f=(x-r)*g
  mul(f,f,g);
    //make f monic
  MakeMonic(f);
  cout<<"poly = "<<f<<endl;
  cout<<"root = "<<r<<endl;

}








//使B变为/tilde{B}
void rounding(mat_ZZ& B,const ZZ X,long delta){
  RR c;
  RR t;
  long n=B.NumRows();

  cout<<"X^(n-delta) = "<<power(X,n-delta)<<endl;
  //c=1.5^n
  c=power(to_RR(1.5),n);
  cout<<"c = "<<c<<endl;
  RR k;
  k=c/to_RR(power(X,n-delta));
  cout<<"c/(X^(n-delta)) = "<<k<<endl;
  for(int i=1;i<=n;i++){
    for(int j=1;j<=i;j++){
      mul(t,k,to_RR(B(i,j)));
      RoundToZZ(B(i,j),t);
    }
  }
//  cout<<"after rounding\n";
//  cout<<B<<endl;
}


//进行格基约化，并计时,返回幺模变换阵
mat_ZZ reduce_lattice(mat_ZZ& B){
    double a,b;
    mat_ZZ U;
    a=GetTime();
    G_LLL_RR(B,U);
    b=GetTime();
    cout<<"reduction time: "<<b-a<<"(s)"<<endl;
    return U;
}



mat_ZZ reduce_lattice_earlier(mat_ZZ& B){
    double a,b;
    mat_ZZ U;
    a=GetTime();
    G_LLL_RR(B,U,0.99,0,SatNorm);
    b=GetTime();
    cout<<"early abort reduction time: "<<b-a<<"(s)"<<endl;
    return U;
}



//size-reduce lower-triangular matrix
void off_diag_reduce(mat_ZZ& B){
  ZZ q,r;
  ZZ a,b;
  for(long i=B.NumRows()-1;i>0;i--){
    b=B(i,i);
    //run through row(j)
    for(long j=i+1;j<=B.NumRows();j++){
      a=B(j,i);
      DivRem(q,r,a,b);
      vec_ZZ sc_vec;
      mul(sc_vec,q,B(i));
      //sc_vec=q*B(i);
      sub(B(j),B(j),sc_vec);
      //B(j)-=sc_vec;
     }
  }
}



void test_off_diag_reduce(){
  mat_ZZ B;
  ifstream fin("matrix_data.txt");
  fin>>B;
  cout<<"before off_diag reduce: "<<endl;
  cout<<B<<endl;
  fin.close();
  cout<<"after off_diag reduce: "<<endl;
  off_diag_reduce(B);
  cout<<B<<endl;
}


bool check_root(const ZZ X,const ZZ r,const vec_ZZ b1){
  ZZX v;
  vec_ZZ b(b1); //f(xX)对应的向量
  inverse_xX(b,X);//还原为f(x)对应的向量
  conv(v,b); //向量转换为多项式
  if(IsZero(evaluation(v,r))) return true;
  else return false;
}

//测试f(x)=[19 14 1]
//v(x) = [3 8 -24 -8 -1 2]
void test0(){
  ZZX f;
  ZZ X; X=2;
  ZZ N;N=35;
  SetCoeff(f,0,19); SetCoeff(f,1,14); SetCoeff(f,2,1);
  cout<<"f(x) = "<<f<<endl;
  long h=3;

  mat_ZZ p;
  p=gen_lattice(h,f,N,X);
  cout<<"before rounding:\n";
  cout<<p<<endl;
  rounding(p,X,2);
  cout<<"after rounding:\n";
  cout<<p<<endl;

}


void test1(bool use_round=false){
  long h,l;
  cout<<"please enter the RSA prime bit length: "<<endl;
  cin>>l;
  long delta=3;
  ZZ X,N,r;
  ZZ *pp;
  ZZX f;
  mat_ZZ B,Br;
  

  cout<<"***********step 0: generate parameters"<<endl;
  pp=gen_param(l,delta,h,N);
  X=pp[0];
  r=pp[1]-1;

  ofstream xr("Xr.txt");
  xr<<X<<"\n"<<r<<endl;
  xr.close();

  ZZ_p::init(N);
  ZZ_pX f_p;

  cout<<"***********step 1: generate polynomial"<<endl;
  gen_poly(f_p,delta,r);
  conv(f,f_p);
  ZZX fc(f);
  cout<<"fc = "<<fc<<endl;
  cout<<"***********step 2: generate lattice basis and reduce it"<<endl;
  B=gen_lattice(h,f,N,pp[0]);
  //cout<<B<<endl;

  mat_ZZ C(B);
cout<<"reduction"<<endl;
  reduce_lattice(B);
  //cout<<B<<endl;

  reduce_lattice_earlier(C);

  cout<<"***********step 3: check root"<<endl;
  if(check_root(X,r,B(1)))
    cout<<"Coppersmith method succeeds."<<endl;
  else cerr<<"fail!!!!"<<endl;

  if(check_root(X,r,RL))
    cout<<"Early abort succeeds."<<endl;
  else cerr<<"fail!!!!"<<endl;


 

  /////////////////////////////////////////////////
  if(use_round){

    mat_ZZ U;
    vec_ZZ v;
    cout<<endl;
    cout<<"==============with rounding=============="<<endl;

    Br=gen_lattice(h,fc,N,pp[1]);



    off_diag_reduce(Br);
    mat_ZZ reB(Br);
    rounding(Br,pp[1],delta);
    U=reduce_lattice(Br);
    mul(v,U(1),reB);
    if(v.length()<7){
      cout<<"v(x) = "<<v<<endl;
    }
    if(check_root(pp[1],r,v))
      cout<<"Coppersmith rounding succeeds."<<endl;
    else cerr<<"fail!!!!"<<endl;
  }
}
  
void  test_fplll_correctness(){
  ifstream fin("Xr.txt");
  ZZ X,r;
  fin>>X>>r;
  cout<<"X = "<<X<<endl;
  cout<<"r = "<<r<<endl;
  fin.close();
  fin.open("time.txt");
  mat_ZZ B;
  fin>>B;
  cout<<"B(1) = "<<B(1)<<endl;
  if(check_root(X,r,B(1)))
       cout<<"Coppersmith method succeeds."<<endl;
  else cerr<<"fail!!!!"<<endl;
}




int main()
{
  //test0();
  test1(true);
  //test_fplll_correctness();
   return 0;
}





/*
f(x) = [19 14 1]
before reduction:
[[1225 0 0 0 0 0]
[0 2450 0 0 0 0]
[665 980 140 0 0 0]
[0 1330 1960 280 0 0]
[361 1064 936 224 16 0]
[0 722 2128 1872 448 32]
]

after reduction
reduction time: 0
[[3 16 -96 -64 -16 64]
[49 100 0 160 0 64]
[-128 50 -20 80 160 32]
[-201 8 132 -32 -48 32]
[-83 -142 52 8 32 160]
[61 32 148 -128 48 128]
]
v(x) = [3 8 -24 -8 -1 2]
 */
