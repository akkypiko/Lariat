int d1 = 1;
int d2 = 0;
int d3 = 0;
int d4 = 0;
int d5 = 0;
int d6 = 0;
int d7 = 0;
int d8 = 0;
int Nd1, Nd2, Nd3, Nd4, Nd5, Nd6, Nd7, Nd8;
inline ckbloom(x,y,z,w) {
  if
    :: (x+y+z == 3) -> w = 0
    :: (x+y+z == 2) -> w = 1
    :: (x+y+z == 2) -> w = 0
    :: (x+y+z == 1) -> w = 1
    :: (x+y+z == 0) -> w = 0
  fi
}
active proctype flowers ()
{
  do
    ::true ->
       printf("%d%d%d%d%d%d%d%d\n",d1,d2,d3,d4,d5,d6,d7,d8);
       ckbloom(0, d1,d2,Nd1);
       ckbloom(d1,d2,d3,Nd2);
       ckbloom(d2,d3,d4,Nd3);
       ckbloom(d3,d4,d5,Nd4);
       ckbloom(d4,d5,d6,Nd5);
       ckbloom(d5,d6,d7,Nd6);
       ckbloom(d6,d7,d8,Nd7);
       ckbloom(d7,d8,0, Nd8);
       atomic {
	 d1 = Nd1;
	 d2 = Nd2;
	 d3 = Nd3;
	 d4 = Nd4;
	 d5 = Nd5;
	 d6 = Nd6;
	 d7 = Nd7;
	 d8 = Nd8;
       }
  od
}