int posA, posB, NposA, NposB;
active proctype stairs()
{
  posA = 0;
  posB = 0;
  printf("A:%d, B:%d\n", posA ,posB);
  do
    ::(posA < 10 && posB < 10) ->
       if
	 ::(posA - posB == 3) -> NposA = posB
	 ::(posA - posB <= 2) -> NposA = posA + 1
	 ::(posA - posB <= 2) -> NposA = posA + 2
       fi;
       if
	 ::(posB - posA == 3) -> NposB = posA
	 ::(posB - posA <= 2) -> NposB = posB + 1
	 ::(posB - posA <= 2) -> NposB = posB + 2
       fi;
       atomic {
	 posA = NposA;
	 posB = NposB;
	 printf("A:%d, B:%d\n", posA ,posB);
       }
    ::else -> skip
  od
}