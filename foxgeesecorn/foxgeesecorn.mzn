% input parameters

int: f; % foxes
int: g; % geese
int: c; % corn
int: k; % capacity of boat
set of int: Cap = 0..k;
int: t; % maximum number of trips
set of int: Trips = 1..t;
int: pf; % profit per fox
int: pg; % profit per geese
int: pc; % profit per corn

array[Trips] of var Cap: fox;
array[Trips] of var Cap: geese;
array[Trips] of var Cap: corn;

int: trips = t;
var int: max = f*pf+g*pg+c*pc;

set of int: time = 0..t;

%%%%%%%%%%%%%%%%%%%%%%%%%% ADD constraints in here %%%%%%%%%%%%%

array[time] of var 0..f: LB_f;
array[time] of var 0..g: LB_g;
array[time] of var 0..c: LB_c;

array[time] of var 0..f: RB_f;
array[time] of var 0..g: RB_g;
array[time] of var 0..c: RB_c;

% Initial condition
constraint (LB_f[0]=f /\ LB_g[0]=g /\ LB_c[0]=c);
constraint (RB_f[0]=0 /\ RB_g[0]=0 /\ RB_c[0]=0);

% modeling of item count on Left Bank
constraint forall(i in 1..trips)
(

% trips West to East: view of LB
if (i mod 2) == 1 then
(
    let {
    var int : LB_f_i = 
    if (LB_f[i-1] - fox[i]) > 0 /\ (LB_c[i-1] - corn[i]) > 0 /\ (LB_g[i-1] - geese[i]) == 0 then (LB_f[i-1] - 1 - fox[i])                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    
    elseif ((LB_f[i-1] - fox[i]) > 0 /\ (LB_g[i-1] - geese[i]) > 0 ) 
            /\ (LB_f[i-1] - fox[i] > LB_g[i-1] - geese[i]) then  (LB_f[i-1] - 1 - fox[i])                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    
    else (LB_f[i-1] - fox[i])                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              

    endif
    } in LB_f[i] = LB_f_i
    
    /\
    
    let {
    var int : LB_g_i = 
    if ((LB_f[i-1] - fox[i]) > 0 /\ (LB_g[i-1] - geese[i])> 0) 
        /\ ((LB_f[i-1] - fox[i]) <= (LB_g[i-1] - geese[i])) then (LB_g[i-1] - (LB_f[i-1] - fox[i]) - geese[i])

    elseif ((LB_g[i-1] - geese[i]) > 0 /\ (LB_c[i-1] - corn[i]) > 0 /\ (LB_f[i-1] - fox[i]) == 0) 
        /\ (LB_g[i-1] - geese[i] > LB_c[i-1] - corn[i]) then LB_g[i-1] - 1 - geese[i]

    else LB_g[i-1] - geese[i]
    endif
    } in LB_g[i] = LB_g_i
    
    /\
    
    let {
    var int : LB_c_i = 
    if (LB_f[i-1] - fox[i]) > 0 /\  (LB_c[i-1] - corn[i]) > 0 /\ (LB_g[i-1] - geese[i]) == 0 then LB_c[i-1] - 1  - corn[i]

    elseif ((LB_g[i-1] - geese[i])> 0 /\ (LB_c[i-1] - corn[i])> 0 /\ (LB_f[i-1] - fox[i]) == 0) 
        /\ ((LB_g[i-1] - geese[i])> (LB_c[i-1] - corn[i])) then LB_c[i-1] - 1 - corn[i]

    elseif ((LB_g[i-1] - geese[i])> 0 /\ (LB_c[i-1] - corn[i])> 0 /\ (LB_f[i-1] - fox[i]) == 0) 
        /\ ((LB_g[i-1] - geese[i]) <= (LB_c[i-1] - corn[i])) then LB_c[i-1] - (LB_g[i-1] - geese[i]) - corn[i]

    else LB_c[i-1]  - corn[i]
    endif
    } in LB_c[i] = LB_c_i
    
)


else % % trips East to West: view of LB
(
    LB_f[i] = LB_f[i-1] + fox[i]
    
    /\
    
    LB_g[i] = LB_g[i-1] + geese[i]
    
    /\
    
    LB_c[i] = LB_c[i-1] + corn[i]
    
    )
endif
)
;


% Constraints for right bank
constraint forall(i in 1..trips)
(

% trips East to West: view of RB
if (i mod 2) == 0 then
(

    let {
    var int : RB_f_i = 
    if (RB_f[i-1] - fox[i]) > 0 /\ (RB_c[i-1] - corn[i]) > 0 /\ (RB_g[i-1] - geese[i]) == 0 then (RB_f[i-1] - 1 - fox[i])                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    
    elseif ((RB_f[i-1] - fox[i]) > 0 /\ (RB_g[i-1] - geese[i]) > 0 ) 
            /\ (RB_f[i-1] - fox[i] > RB_g[i-1] - geese[i]) then  (RB_f[i-1] - 1 - fox[i])                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              
    
    else (RB_f[i-1] - fox[i])                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              

    endif
    } in RB_f[i] = RB_f_i
    
    /\
    
    let {
    var int : RB_g_i = 
    if ((RB_f[i-1] - fox[i]) > 0 /\ (RB_g[i-1] - geese[i])> 0) 
        /\ ((RB_f[i-1] - fox[i]) <= (RB_g[i-1] - geese[i])) then (RB_g[i-1] - (RB_f[i-1] - fox[i]) - geese[i])

    elseif ((RB_g[i-1] - geese[i]) > 0 /\ (RB_c[i-1] - corn[i]) > 0 /\ (RB_f[i-1] - fox[i]) == 0) 
        /\ (RB_g[i-1] - geese[i] > RB_c[i-1] - corn[i]) then RB_g[i-1] - 1 - geese[i]

    else RB_g[i-1] - geese[i]
    endif
    } in RB_g[i] = RB_g_i
    
    /\
    
    let {
    var int : RB_c_i = 
    if (RB_f[i-1] - fox[i]) > 0 /\  (RB_c[i-1] - corn[i]) > 0 /\ (RB_g[i-1] - geese[i]) == 0 then RB_c[i-1] - 1  - corn[i]

    elseif ((RB_g[i-1] - geese[i])> 0 /\ (RB_c[i-1] - corn[i])> 0 /\ (RB_f[i-1] - fox[i]) == 0) 
        /\ ((RB_g[i-1] - geese[i])> (RB_c[i-1] - corn[i])) then RB_c[i-1] - 1 - corn[i]

    elseif ((RB_g[i-1] - geese[i])> 0 /\ (RB_c[i-1] - corn[i])> 0 /\ (RB_f[i-1] - fox[i]) == 0) 
        /\ ((RB_g[i-1] - geese[i]) <= (RB_c[i-1] - corn[i])) then RB_c[i-1] - (RB_g[i-1] - geese[i]) - corn[i]

    else RB_c[i-1]  - corn[i]
    endif
    } in RB_c[i] = RB_c_i
    
)


else % trips West to East: view of RB
(
    RB_f[i] = RB_f[i-1] + fox[i]
    
    /\
    
    RB_g[i] = RB_g[i-1] + geese[i]
    
    /\
    
    RB_c[i] = RB_c[i-1] + corn[i]
    
    )
endif
)
;

% Capacity constraint on boat
constraint forall(i in 1..trips)
 (fox[i] + geese[i] + corn[i] <= k);

% Constraint that there are enough items available for shipment
constraint forall(i in 1..trips)
(
if (i mod 2) == 1 then
  (
    fox[i] <= LB_f[i-1] /\
    geese[i] <= LB_g[i-1] /\
    corn[i] <= LB_c[i-1] 
   )
else
  (
    fox[i] <= RB_f[i-1] /\
    geese[i] <= RB_g[i-1] /\
    corn[i] <= RB_c[i-1] 
   )
endif

);

% Ensure that there is something shipped in the first trip
constraint fox[1] + geese[1] + corn[1] >= 1;

constraint obj >= pf /\ obj <= max;

var int: obj = RB_f[trips]*pf + RB_g[trips]*pg + RB_c[trips]*pc;

%%%%%%%%%%%%%%%%% you may want to modify the search strategy below

solve 
:: seq_search([int_search(fox, largest, indomain_max, complete), int_search(RB_f, largest, indomain_max, complete), int_search(geese, largest, indomain_max, complete),int_search(corn, smallest, indomain_min, complete)])
% :: int_search(fox, largest, indomain_max, complete)
maximize obj;

output ["  fox = ", show(fox),
     ";\ngeese = ", show(geese),
     ";\n corn = ", show(corn),
     ";\ntrips = ", show(trips), 
     ";\n  obj = ", show(obj),
%      ";\n LB_f = ", show(LB_f),
%      ";\n RB_f = ", show(RB_f),
%      ";\n LB_g = ", show(LB_g),
%      ";\n RB_g = ", show(RB_g),
%      ";\n LB_c = ", show(LB_c),
%      ";\n RB_c = ", show(RB_c),
       ";\n"];


