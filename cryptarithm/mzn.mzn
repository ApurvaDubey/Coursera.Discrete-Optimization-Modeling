var 0..9: M;
var 0..9: I;
var 0..9: N;
var 0..5: Z;
var 0..9: C;
var 0..9: R;
var 0..9: O;
var 0..9: K;

include "alldifferent.mzn";

constraint alldifferent([M,I,N,Z,C,R,O,K]);

constraint 
1*I + 10*N + 100*I + 1000*M +
1*C + 10*N + 100*I + 1000*Z =
1*Z + 10*K + 100*C + 1000*O + 10000*R;

solve satisfy;