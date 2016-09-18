% Author: Apurva Dubey
% Date: 02/Oct/2015

% ------------------------------------------------------------------
% Input parameters

int: n;                 % number of gangs
set of int: Gang = 1..n; 
array[Gang] of int: m;  % size of each gang

set of int: Time = 1..t; % time slots
set of int: Student = 1..t; % students
int: r; % number of rivalries
set of int: Rival = 1..r; % number of rival gangs
array[Rival] of Gang: g1; % rival gangs - first side
array[Rival] of Gang: g2; % rival gangs - second side
array[Gang] of var Time: MaxSlot;
% ------------------------------------------------------------------

% ------------------------------------------------------------------
% variables
var 3..3*sum(m): obj; % upper bound is an approximation
array[Time] of var 0..(3 + 2*(max(m)-1)): ObjStu; % array containing confession points of each student

%     ObjStu = [if IsLeader[i] == 0 /\ timeslot[i] < timeslot[LeaderOfStu[i]] then 1
%                  elseif IsLeader[i] == 1 /\ timeslot[i] < t/2 then 3 else  0 endif | i in 1..t]
% ;

array[Time] of var Student: order; % person interviewed at time t
array[Student] of var Time: timeslot; % time slot for student s
array[Student] of var Time:  LeaderOfStu;  % leader correpondting to student s

array[Gang] of var 0..1: SadGang; % which gang leaders will be sad: Needed for Stage B


% ------------------------------------------------------------------

% ------------------------------------------------------------------
% intermediate variables
int: t = sum(i in Gang)(m[i]);
array[Gang] of Time: cumu = [sum(k in Gang where k<=j)(m[k]) | j in Gang];
array[Student] of Gang: GangOfStu = [ g | g in Gang, j in 1..m[g]]; % find the mapping of Student to Gang

array[Student] of 0..1: IsLeader = [1] ++ [ if GangOfStu[i] == GangOfStu[i-1]+1  then 1 else 0 endif | i in 2..t]; % flag the students that are leaders
array[Gang] of Student: LeaderOfGang = [1] ++ [ cumu[i] + 1 | i in 1..n-1]; % find leader of each gang

% find the last time slot for each gang
constraint forall(g in Gang)(MaxSlot[g] = max([ if GangOfStu[i] == g then timeslot[i] else -1 endif | i in Student]));

% find the leader of each student
constraint forall(s in 1..t)
(
if s == 1 then LeaderOfStu[s] = 1
elseif GangOfStu[s] == GangOfStu[s-1] then LeaderOfStu[s] = LeaderOfStu[s-1]
else LeaderOfStu[s] = s
endif
);

% CONSTRAINTS BELOW ARE APPLICABLE ONLY FOR STAGE B
% find sad gang leaders
constraint forall(r in Rival)(
((timeslot[LeaderOfGang[g1[r]]] > MaxSlot[g2[r]]) <-> SadGang[g1[r]] = 1));

constraint forall(r in Rival)(
((timeslot[LeaderOfGang[g2[r]]] > MaxSlot[g1[r]]) <-> SadGang[g2[r]] = 1));
% ------------------------------------------------------------------


% ------------------------------------------------------------------
% Constraints
include "alldifferent.mzn";
constraint alldifferent(order);
constraint alldifferent(timeslot);
constraint alldifferent(MaxSlot);

% bijection between order and timeslot
constraint forall(s in Student, t in Time)(order[t] = s <-> timeslot[s] = t);

% no two members of the same gang can be interviewed one after the other
constraint forall(i in 1..t-1)(GangOfStu[order[i]] != GangOfStu[order[i+1]]);

%% FOLLOWING CONSTRAINTS ARE APPLICABLE ONLY FOR STAGE 'B'
% no two members of gangs in a rivalry can be interviewed one after the other
constraint forall(i in 1..t-1) % loop through times
  (forall(j in Rival) % loop through rival gangs
        ( (GangOfStu[order[i]] == g1[j] -> GangOfStu[order[i+1]] != g2[j]) /\ (GangOfStu[order[i]] == g2[j] -> GangOfStu[order[i+1]] != g1[j])
        )
);

constraint forall(i in 1..t)(IsLeader[i]==1 -> (ObjStu[i] = 0 \/ ObjStu[i] >= 3)); % "=" applicable for only for Stage A

% constraint forall(i in 1..t)(IsLeader[i]==1 -> (ObjStu[i] != 1 /\ ObjStu[i] != 2));
constraint forall(i in 1..t)(IsLeader[i]==0 -> (ObjStu[i] == 0 \/ ObjStu[i] == 1));


% additional constraints for ObjStu array

constraint forall(i in 1..t)((ObjStu[i] =  3) -> (IsLeader[i]==1));
% constraint forall(i in 1..t)((ObjStu[i] >  3) -> (IsLeader[i]==1));
constraint forall(i in 1..t)((ObjStu[i] =  1) -> (IsLeader[i]==0));


constraint forall(i in 1..t, j in 1..t where i < j)(
    ((GangOfStu[i] == GangOfStu[j]) /\ (IsLeader[i] == 0 /\ IsLeader[j] == 0))
      -> (order[i] < order[j])
);

% constraint timeslot[LeaderOfGang[3]] < t/2;
% constraint timeslot[LeaderOfGang[5]] > t/2;

% ------------------------------------------------------------------


% ------------------------------------------------------------------
% Objective function

% STAGE A
% constraint forall(i in 1..t)(
%     ObjStu[i] = if IsLeader[i] == 0 /\ timeslot[i] < timeslot[LeaderOfStu[i]] then 1
%                  elseif IsLeader[i] == 1 /\ timeslot[i] < t/2 then 3 else  0 endif
% );

% STAGE B
  % Interviewing the leader of a gang (e.g. gang1) after all the members of another gang (e.g. gang2)
  % in a rivalry with gang1 makes the leader of gang1 feel that the principal is working against them
  % and the leader confesses 3+2l points where l is the number of other members of their own gang (i.e.
  % m1) not interviewed yet.

% Below is valid only for Stage B
constraint forall(i in 1..t)(
    ObjStu[i] = if IsLeader[i] == 1 /\ SadGang[GangOfStu[i]] == 1 
                    then 3 + 2 * sum([ if timeslot[j] > timeslot[i] then 1 else 0 endif | j in 1..t where GangOfStu[j] == GangOfStu[i] ])
                 elseif IsLeader[i] == 0 /\ timeslot[i] < timeslot[LeaderOfStu[i]] then 1
                 elseif IsLeader[i] == 1 /\ timeslot[i] < t/2 then 3 else  0 endif
);



% sum up confession points across all students
constraint obj = sum(s in Student)(ObjStu[s]);
% ------------------------------------------------------------------

% ------------------------------------------------------------------
% Solution search
solve 
:: 
seq_search([

int_search(SadGang, first_fail, indomain_max, complete),
% int_search(ObjStu, first_fail, indomain_max, complete),
% int_search(MaxSlot, first_fail, indomain_min, complete),
% int_search(order, first_fail, indomain_random, complete)
% % int_search(timeslot, first_fail, indomain_random, complete)

])
maximize obj;
% ------------------------------------------------------------------


% ------------------------------------------------------------------
output ["order = ",show(order),
	";\nobj = ", show(obj),
% 	";\ncumu = ", show(cumu),
% 	";\nxx = ", show(sum(m)),
% 	";\nSadGang = ", show(SadGang),
% 	";\nLeaderOfGang = ", show(LeaderOfGang),
% 	";\nMaxSlot = ", show(MaxSlot),
%   ";\norder       = ",show(order),
%   ";\ntimeslot    = ",show(timeslot),
%   ";\nObjStu      = ", show(ObjStu),
%   ";\nGangOfStu   = ", show(GangOfStu),
%   ";\nLeaderOfStu = ", show(LeaderOfStu),
%   ";\nIsLeader    = ", show(IsLeader), 
  ";\n" ];
% ------------------------------------------------------------------



