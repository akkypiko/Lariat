
// System Alpha

init {
    a = 0;
    b = 0;
    sw = 0;
}

system {
    b = 1 -> a <- a;
    b = 0 -> a <- (a + 1) % 3;
}




/*
 systemAlpha.pml
*/
mtype = {on, off};
int a, b;
mtype sw;
int Na, Nb;
mtype Nsw;
active proctype alpha ()
{
  a = 0;
  b = 0;
  sw = off;
  do
    ::true ->

       if
	 ::(b == 1) -> Na = a
	 ::else ->
	    if
	      ::(a == 0) -> Na = 1
	      ::(a == 1) -> Na = 2
	      ::(a == 2) -> Na = 0
	    fi
       fi;

       if
	 ::(a == b) -> Nb = b
	 ::else ->
	    if
	      ::(b == 0) -> Nb = 1
	      ::(b == 1) -> Nb = 2
	      ::(b == 2) -> Nb = 0
	    fi
       fi;

       if
	 ::(a == 2 && b == 2) -> Nsw = on
	 ::(a == 1 && b == 1) -> Nsw = off
	 ::else -> Nsw = sw
       fi;

       atomic{
	 a = Na;
	 b = Nb;
	 sw = Nsw
       }
       od
}