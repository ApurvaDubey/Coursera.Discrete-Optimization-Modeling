var 0..9: S;
var 0..9: E;
var 0..9: N;
var 0..9: D;
var 0..9: M;
var 0..9: O;
var 0..9: T;
var 0..9: Y;

include "alldifferent.mzn";

constraint alldifferent([S,E,N,D,M,O,T,Y]);

constraint 
1*D + 10*N + 100*E + 1000*S +
1*T + 10*S + 100*O + 1000*M =
1*Y + 10*E + 100*N + 1000*O + 10000*M;

solve maximize 1*Y + 10*E + 100*N + 1000*O + 10000*M;