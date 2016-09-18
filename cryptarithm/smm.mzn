var 0..9: S;
var 0..9: E;
var 0..9: N;
var 0..9: D;
var 0..9: M;
var 0..9: O;
var 0..9: R;
var 0..9: Y;

include "alldifferent.mzn";

constraint alldifferent([S,E,N,D,M,O,R,Y]);

constraint 
1*D + 10*N + 100*E + 1000*S +
1*E + 10*R + 100*O + 1000*M =
1*Y + 10*E + 100*N + 1000*O + 10000*M;

solve satisfy;