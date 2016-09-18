% Author: Apurva Dubey
% Date: 03/Oct/2015

%------------------------------------------------------------------------
% parameters
int: nr; % number of reclaimers
         % number of rails = nr for stages A,B,C,D,E
         % number of rails = (nr + 1) div 2 for stage F
set of int: RECLAIMER = 1..nr;
bool: stageF; % is this stage F data

int: ns; % number of stockpiles
set of int: STOCKPILE = 1..ns;
array[STOCKPILE] of int: size; % size in 10000 tonnes
array[STOCKPILE] of SHIP: ship; % which ship carries stockpile

constraint forall(sh in SHIP)
                 (assert(exists(s in STOCKPILE)(ship[s] = sh),
                 "Ship " ++ show(sh) ++ " has no cargo!"));
 
int: maxtime; % time considered
set of int: TIME = 0..maxtime;

int: nsh; % number of ships
set of int: SHIP = 1..nsh;
array[SHIP] of TIME: arrival; % when ship arrives in port

int: len; % length of pad
set of int: POSITION = 0..len;

int: stack_time;
int: reclaim_time;
int: reclaim_speed;
%------------------------------------------------------------------------

%------------------------------------------------------------------------
% variables
array[STOCKPILE] of var POSITION: westend;
array[STOCKPILE] of var POSITION: eastend;
array[STOCKPILE] of var TIME: stack;
array[STOCKPILE] of var TIME: endstack;
array[STOCKPILE] of var TIME: reclaim;
array[STOCKPILE] of var TIME: finished;
array[STOCKPILE] of var RECLAIMER: which; %'which' reclaimer is used for each stockpile i.e. if which[i]==j then 'i' is stockpile and 'j' is reclaimer

array[SHIP] of var TIME: departure;
array[SHIP] of var TIME: wait;

array[RECLAIMER,TIME] of var POSITION: posReclaimer; % position of reclaimer 'r' at a given time 't' 

var int: obj;
%------------------------------------------------------------------------


%------------------------------------------------------------------------
% constraints


% constraint 1: STOCKPILE overlap in space -> STOCKPILE non-overlap in time
constraint forall(i in STOCKPILE, j in STOCKPILE where i < j)
  (
    % if there is overlap in space
     not(
        (eastend[i] <= westend[j]) \/ 
        (westend[i] >= eastend[j])
        )
      ->  % note that it's only one directional which makes sense i.e. if two stockpile dont overlap in time then can or cannot occupy the same space
    % then there cannot be overlap in time
     (
        (finished[i] <= stack[j]) \/ 
        (stack[i] >= finished[j])
      )
    );


% constraint 2: STOCKPILE overlap in time -> STOCKPILE non-overlap in space
constraint forall(i in STOCKPILE, j in STOCKPILE where i < j)
  (
    % if there is overlap in time
     not(
        (finished[i] <= stack[j]) \/ 
        (stack[i] >= finished[j])
      )
      ->  % note that it's only one directional which makes sense i.e. if two stockpiles are non-overlapping in space
          % then they can or cannot overlap in time
    % then there cannot be overlap in space
     (
        (eastend[i] <= westend[j]) \/ 
        (westend[i] >= eastend[j])
      )
    );

% constraint 3: STOCKPILE: east = west + size
constraint forall(i in STOCKPILE)
    (eastend[i] = westend[i] + size[i]);

% constraint 4: STOCKPILE: no spill over either eastend or westend
constraint forall(i in STOCKPILE)
    ((eastend[i] <= len) /\ (westend[i] >= 0));

% constraint 5: STOCKPILE: stacking time
constraint forall(i in STOCKPILE)
      (endstack[i] = stack[i] + stack_time*size[i]);

% constraint 6: STOCKPILE: reclaiming time
constraint forall(i in STOCKPILE)
      (finished[i] = reclaim[i] + reclaim_time*size[i]);

% constraint 7: STOCKPILE: reclaiming can start only after stacking
constraint forall(i in STOCKPILE)
      (reclaim[i] >= endstack[i]);

% constraint 8: 
% You should add constraints to your model to enforce that
% two stockpiles reclaimed by the same reclaimer do not overlap in time.
constraint forall(i in STOCKPILE, j in STOCKPILE where i < j) % loop through all pair of stockpiles
   ( (which[i] == which[j]) % if the same reclaimer picks two stockpiles
     -> % then it implies
     (
        (finished[i] <= reclaim[j]) \/ 
        (reclaim[i] >= finished[j])
      ) % those two stockpiles dont overlap in reclaim time
  );

% constraint 9:
% You should add constraints to your model so that no stockpile can be reclaimed onto a ship
% before the arrival time of the ship.
constraint forall(i in STOCKPILE)
(reclaim[i] >= arrival[ship[i]]);

% constraint 10:
% Also no two stockpiles can be reclaimed onto the same ship at
% the same time. Make sure these reclaims do not overlap in time.
constraint forall(i in STOCKPILE, j in STOCKPILE where i < j) % loop through all pair of stockpiles
   ( (ship[i] == ship[j]) % if the same reclaimer picks two stockpiles
     -> % then it implies
     (
        (finished[i] <= reclaim[j]) \/ 
        (reclaim[i] >= finished[j])
      ) % those two stockpiles dont overlap in reclaim time
  );


% constraint 11:
% at the time of reclaiming the reclaimer should be at the westend of the stockpile
constraint forall(i in STOCKPILE)
(posReclaimer[which[i],reclaim[i]] = westend[i]);


constraint forall(i in STOCKPILE)
(posReclaimer[which[i],finished[i]] = westend[i]); % should be at the westend up until reclaiming finishes


constraint forall(r in RECLAIMER,i in 0..maxtime-1)
(abs(posReclaimer[r,i+1] - posReclaimer[r,i])*reclaim_speed <= 1 );



% constraint 12:
% Add constraints to your model to ensure that if a reclaimer finishes reclaiming a stockpile
% with westend at x and then has to start reclaiming a stockpile with westend at y there is at least
% |y-x|*reclaim speed time between these two events.

constraint forall(i in STOCKPILE, j in STOCKPILE where i < j) % loop through all pair of stockpiles
   ( ((which[i] == which[j]) /\ (reclaim[i] >= finished[j])) % if the same reclaimer picks two stockpiles & reclaiming of 'i' will happen after 'j'
     -> % then it implies
     (
      (reclaim[i] - finished[j]) >= abs(posReclaimer[which[i],reclaim[i]] - posReclaimer[which[j],finished[j]])*reclaim_speed
      ) 
  );

constraint forall(i in STOCKPILE, j in STOCKPILE where i < j) % loop through all pair of stockpiles
   ( ((which[i] == which[j]) /\ (reclaim[j] >= finished[i])) % if the same reclaimer picks two stockpiles & reclaiming of 'i' will happen after 'j'
     -> % then it implies
     (
      (reclaim[j] - finished[i]) >= abs(posReclaimer[which[i],finished[i]] - posReclaimer[which[j],reclaim[j]])*reclaim_speed
      ) 
  );



% constraint 13:
%calculate departure time of each ship
constraint forall(i in SHIP)
(departure[i] = max([finished[j] | j in STOCKPILE where i==ship[j]])); % find the finish time corresponding to the last stockpile to finish for the ship

% constraint 14:
% calculate wait time of each ship
constraint forall(i in SHIP)
(wait[i] = departure[i] - arrival[i]);


% constraint 15: ==> for stage F
% multiple reclaimers on the same rail
constraint forall(i in 1..(nr div 2), j in TIME)
  (posReclaimer[2*i-1,j] <= posReclaimer[2*i,j]);


%------------------------------------------------------------------------



%------------------------------------------------------------------------
% objective function

constraint obj = sum(i in SHIP)(wait[i]);

solve 

:: 
seq_search([

int_search(finished, first_fail, indomain_random, complete),
int_search(which, first_fail, indomain_random, complete)
% int_search(westend, first_fail, indomain_random, complete)
% int_search(stack, first_fail, indomain_random, complete)

])

minimize obj;

%------------------------------------------------------------------------


%------------------------------------------------------------------------
%output for submission
output 
["westend  = ", show(westend), ";\n"] ++
["eastend  = ", show(eastend), ";\n"] ++
["stack    = ", show(stack), ";\n"] ++
["endstack = ", show(endstack), ";\n"] ++
["reclaim  = ", show(reclaim), ";\n"] ++
["finish   = ", show(finished) , ";\n"] ++
["which    = ", show(which), ";\n"]
;

% output for solution visualization
% warning: this is an experimental feature.  Feedback and suggestions are encouraged.

include "portschedule_viz.mzn";
output [portschedule_viz(westend,eastend,stack,endstack,reclaim,finished,which)];
