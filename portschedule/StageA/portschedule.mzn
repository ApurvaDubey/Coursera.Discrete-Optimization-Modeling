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
array[STOCKPILE] of var RECLAIMER: which = [1 | i in STOCKPILE];

array[SHIP] of var TIME: departure;
array[SHIP] of var TIME: wait;

array[TIME] of var POSITION: posReclaimer; % position of reclaimer at a given time 't' 

var int: obj;
%------------------------------------------------------------------------

% at the time of reclaiming the reclaimer should be at the westend of the stockpile
constraint forall(i in STOCKPILE)
(posReclaimer[reclaim[i]] = westend[i]);

constraint forall(i in 0..maxtime-1)
(abs(posReclaimer[i+1] - posReclaimer[i])*reclaim_speed <= 1 ) ;

% reclaiming can start only after a ship's arrival
constraint forall(i in STOCKPILE)
(reclaim[i] >= arrival[ship[i]]);

% calculate wait time of each ship
constraint forall(i in SHIP)
(wait[i] = departure[i] - arrival[i]);

%calculate departure time of each ship
constraint forall(i in SHIP)
(departure[i] = finished[i]);


% constraint 1: overlap in space -> non-overlap in time
constraint forall(i in STOCKPILE, j in STOCKPILE where i < j)
  (

    % if there is overlap in space
      (((eastend[i] >= westend[j]) /\  (eastend[i] <=  eastend[j]))
        \/
      ((westend[i] >= westend[j]) /\  (westend[i] <=  eastend[j])))
      ->  % note that it's only one directional which makes sense i.e. if two stockpile dont overlap in time then can or cannot occupy the same space
    % then there cannot be overlap in time
           ((finished[i] <= stack[j]) \/ (stack[i] >= finished[j]))

    );


% constraint 2: overlap in time -> non-overlap in space
constraint forall(i in STOCKPILE, j in STOCKPILE where i < j)
  (

    % if there is overlap in time
        (((stack[i] >= stack[j])  /\ (stack[i] <= finished[j]))
        \/
        ((finished[i] >= stack[j])  /\ (finished[i] <= finished[j])))

      ->  % note that it's only one directional which makes sense i.e. if two stockpiles are non-overlapping in space
          % then they can or cannot overlap in time
    % then there cannot be overlap in space
           ((eastend[i] <= westend[j]) \/ (westend[i] >= eastend[j]))

    );

% constraint 3: east = west + size
constraint forall(i in STOCKPILE)
    (eastend[i] = westend[i] + size[i]);

% constraint 4: no spill over either eastend or westend
constraint forall(i in STOCKPILE)
    ((eastend[i] <= len) /\ (westend[i] >= 0));

% constraint 5: stacking time
constraint forall(i in STOCKPILE)
      (endstack[i] = stack[i] + stack_time*size[i]);

% constraint 6: reclaiming time
constraint forall(i in STOCKPILE)
      (finished[i] = reclaim[i] + reclaim_time*size[i]);

% constraint 7: reclaiming can start only after stacking
constraint forall(i in STOCKPILE)
      (reclaim[i] >= endstack[i]);

% 

%------------------------------------------------------------------------
% intermediate variables


%------------------------------------------------------------------------



%------------------------------------------------------------------------
% constraints

% none of the stockpile should spill beyond the pad
% two stockpiles cannot over lap in time or space

% loop through all TIMEs
% loop through all paris of stock-piles
% there should not be any case where two stockpiles are occupying overlapping positions at the same time



%------------------------------------------------------------------------



%------------------------------------------------------------------------
% objective function

constraint obj = sum(i in SHIP)(wait[i]);

solve minimize obj;

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
% 
% include "portschedule_viz.mzn";
% output [portschedule_viz(westend,eastend,stack,endstack,reclaim,finished,which)];
