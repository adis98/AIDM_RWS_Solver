% RWS problem - basic form
include "globals.mzn";

% Set the parameters
int: groups; % The number of employees - groups of employees
int: numShifts; % Number of shifts (D, A, N)
int: w = 7; % Days in the week
int: pr = w*groups;
set of int: S = 1..numShifts;
set of int: Sp = 0..numShifts;
set of int: N = 1..groups;
set of int: W = 1..w;
array[S,W] of int: demand; % number of employees needed to be assigned per shift i per day j
array[S] of int: minShift;
array[S] of int: maxShift;
int: minOff;
int: maxOff;
int: minOn;
int: maxOn;
array[S] of set of int: forbidden;
array[int,int] of int: forbidden3;
int: forbidden3l = length(forbidden3) div 3;

% Define decision variables
array[1..pr] of var Sp: T; % the schedule of the first employee
var 0..w-1: o; % the offset 
array[1..(w-1)] of var bool: bools; % helper variables for the offset calculation

% Define objective function
solve satisfy;

% Define constraints
% Demand constraints
% Eq (1)
constraint
forall(d in W, s in S)(
  sum(i in 0..groups-1)(T[d + i*w] = s) == demand[s,(d+o) mod (w+1) + (d+o) div (w+1)]
);

constraint 
forall(d in W) (
  sum(i in 0..groups-1)(T[d+w*i] == 0) = groups - sum(s in S) (demand[s,(d+o) mod (w+1) + (d+o) div (w+1)])
);

% Symmetry breaking constraints
% Eq (3)
constraint symmetry_breaking_constraint(T[1] != 0);
% Eq (4)
constraint symmetry_breaking_constraint(T[pr] == 0);
constraint all_equal(T[pr-minOff..pr]);

% Lengths of shift blocks constraints
% Eq (5) for Shifts
constraint forall(i in 2..pr) (forall(s in S)
  (if (T[i] = s /\ T[(i-1)] != s) then
    all_equal(T[i..min(i+minShift[s]-1, pr)]) else true endif));
% Eq (5) for i=1
constraint (forall(s in S)
  (if T[1] = s then 
    all_equal(T[1..minShift[s]]) else true endif));
% Eq (5) for Days off
constraint forall(i in 2..(pr-minOff)) 
  (if (T[i] = 0 /\ T[(i-1)] != 0) then
    all_equal(T[i..i+minOff-1]) else true endif);

% Eq (6) for Shifts
constraint forall(i in 2..pr) (forall(s in S)
  (if (T[i] = s /\ T[((i - 1) mod (pr+1))] != s) then 
     (i + maxShift[s] > pr) \/ (sum(j in minShift[s]..maxShift[s]) (T[max(1,((i+j) mod (pr+1)))] != s)) > 0 else true endif));
% Eq (6) for i=1
constraint (forall(s in S)
  (if T[1] = s then 
     (1 + maxShift[s] > pr) \/ (sum(j in minShift[s]..maxShift[s]) (T[max(1,((1+j) mod (pr+1)))] != s)) > 0 else true endif));
% Eq (6) for Off days
constraint forall(i in 2..pr)
  (if (T[i] = 0 /\ T[((i - 1) mod (pr+1))] != 0) then 
     (i + maxOff > pr) \/ (sum(j in minOff..maxOff) (T[max(1,((i+j) mod (pr+1)))] != 0)) > 0 else true endif);  
     
% Eq (7) for Shifts
constraint forall(i in 2..pr)
  (if (T[i] != 0 /\ T[((i-1) mod (pr+1))] = 0) then 
    forall(j in 1..minOn-1) (T[max(1,((i+j) mod (pr+1)))] != 0) else true endif);
% Eq (7) for i=1
constraint (if T[1] != 0 then 
  forall(j in 1..minOn-1) (T[max(1,((1+j) mod (pr+1)))] != 0) else true endif);

% Eq (8) for Shifts
constraint forall(i in 2..pr)
  (if (T[i] != 0 /\ T[((i - 1))] = 0) then 
     ((sum(j in minOn..maxOn) (T[max(1,(i+j) mod (pr+1))] = 0)) > 0) else true endif);
constraint
((sum(j in minOn..maxOn) (T[max(1,((1+j) mod (pr+1)))] = 0)) > 0);      

% Forbidden shifts constraints
% Eq (9)
constraint forall(i in 1..pr) (forall(s in S)
   (T[i] != s \/ count_eq(forbidden[s], T[max(1,((i+1) mod (pr+1)))], 0)));

% Eq (10)
constraint
forall(i in 1..pr)(
 if(forbidden3l > 0) then(
     forall(j in 1..forbidden3l)(
       (forbidden3[j,1] != T[i]) \/ (forbidden3[j,2] != T[max(1,(i+1)mod(pr+1))]) \/ (forbidden3[j,3] != T[max(1,(i+2)mod(pr+1))])
     )
 )
 else true endif
);

% Offset constraints        
% Eq (11) 
constraint forall(d in 2..w) (bools[d-1] = (sum(s in S)(demand[s,d]) <= sum(s in S)(demand[s,d-1])));
constraint symmetry_breaking_constraint(if (sum(bools) == (w-1)) then (o = 0) else (o = arg_min(bools)) endif);

% Outputs
output ["result = \(T) \n"];
output ["o = \(o) \n"];