int: n; % size of latin square
set of int: Num = 1..n;

int: m; % number of groups
set of int: Group = 1..m;
set of int: Group0 = 0..m;

array[Group] of int: s;
array[Num,Num] of Group0: a;

array[Num,Num] of var Num: x;

%%%%%%%

% add your constraints here
include "alldifferent.mzn";

constraint 
  forall(i in Num)(alldifferent([x[i,c] | c in Num]));

constraint 
  forall(i in Num)(alldifferent([x[r,i] | r in Num]));

constraint forall(i in Group)
              (s[i]=sum([ x[r,c]  |  r in Num, c in Num where a[r,c]==i]));

constraint forall(i in Group)
              (alldifferent([ x[r,c] |  r in Num, c in Num where  a[r,c]==i]));


%%%%%%%

solve satisfy;

output ["x = [|"] ++
       [ if j = 1 /\ 2 <= i /\ i <= n then "| " else "" endif ++
         show(x[i,j]) ++ 
         if j == n then "\n" else ", " endif  
       | i,j in Num ] 
       ++
       ["|];\n"]
;

