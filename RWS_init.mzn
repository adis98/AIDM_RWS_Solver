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

% Define objective function
solve satisfy;

% Define constraints
% Demand constraints
% Eq (1)
constraint forall(d in W) (forall(s in S) (sum(i in 0..groups-1) (T[d+w*i] = s) = demand[s, d+o]));
% Eq (2)
constraint forall(d in W) (sum(i in 0..groups-1) (T[d+w*i] = 0) = groups - sum(i in S) (demand[i,d+o]));

% Symmetry breaking constraints
% Eq (3)
constraint T[1] != 0;
% Eq (4)
constraint T[pr] = 0;

% Lengths of shift blocks constraints
% Eq (5) for Shifts
constraint forall(i in 2..pr) (forall(s in S)
  (if (T[i] = s /\ T[(i-1) mod (pr+1)] != s) then forall(j in 1..minShift[s]-1) (T[max(1,(i+j) mod (pr+1))] = s) else true endif));
% Eq (5) for i=1
constraint (forall(s in S)
  (if T[1] = s then forall(j in 1..minShift[s]-1) (T[max(1,(1+j) mod (pr+1))] = s) else true endif)); 
% Eq (5) for Off days
constraint forall(i in 2..pr) 
  (if (T[i] = 0 /\ T[(i-1) mod (pr+1)] != 0) then forall(j in 1..minOff-1) (T[max(1,(i+j) mod (pr+1))] = 0) else true endif);

% Eq (6) for Shifts
constraint forall(i in 2..pr) (forall(s in S)
  (if (T[i] = s /\ T[(i - 1) mod (pr+1)] != s) then 
     (i + maxShift[s] > pr) \/ sum(j in minShift[s]..maxShift[s]) (T[max(1,(i+j) mod (pr+1))] != s) > 0 else true endif));
% Eq (6) for i=1
constraint (forall(s in S)
  (if T[1] = s then 
     (1 + maxShift[s] > pr) \/ sum(j in minShift[s]..maxShift[s]) (T[max(1,(1+j) mod (pr+1))] != s) > 0 else true endif));
% Eq (6) for Off days
constraint forall(i in 2..pr)
  (if (T[i] = 0 /\ T[(i - 1) mod (pr+1)] != 0) then 
     (i + maxOff > pr) \/ sum(j in minOff..maxOff) (T[max(1,(i+j) mod (pr+1))] != 0) > 0 else true endif);  

% Eq (7) for Shifts
constraint forall(i in 2..pr)
  (if (T[i] != 0 /\ T[(i-1) mod (pr+1)] = 0) then forall(j in 1..minOn-1) (T[max(1,(i+j) mod (pr+1))] != 0) else true endif);
% Eq (7) for i=1
constraint (if T[1] != 0 then forall(j in 1..minOn-1) (T[max(1,(1+j) mod (pr+1))] != 0) else true endif);
% Eq (8) for Shifts
constraint forall(i in 2..pr)
  (if (T[i] != 0 /\ T[(i - 1) mod (pr)+1] = 0) then 
     (i + maxOn > pr) \/ sum(j in minOn..maxOn) (T[max(1,(i+j) mod (pr+1))] = 0) > 0 else true endif);
     
% Forbidden shifts constraints
% Eq (9)
constraint forall(i in 1..pr) (forall(s in S)
   (T[i] != s \/ count_eq(forbidden[s], T[max(1,(i+1) mod (pr+1))], 0)));
% Eq (10)
constraint forall(i in 1..pr) (forall(ii in 1..3)
   (if forbidden3l>0 then
   sum(jj in 1..forbidden3l) (forbidden3[jj ,ii] - T[max(1,(i+jj-1) mod (pr+1))] != 0) > 0
   else true endif));
   
array[1..(w-1)] of var bool: bools;

% constraint forall(d in 2..w) (bools[d-1] = (sum(s in S)(demand[s,d]) <= sum(s in S)(demand[s,d-1])));
% constraint o = max(arg_min(bools), 0);
% Eq (11)
% Symmetry breaking constraint for the offset
%  constraint o = max(min(forall(d in 2..w) (d -> (sum(s in S)(demand[s,d]) > sum(s in S)(demand[s,d-1])))) - 1,0);
%  constraint o = argmax(1, demand);
output ["\(T)"];
% array[1..3] of int: x = [1, 2, 3];
% output["\(bools)"];
% output["\(arg_min(bools))"];
% output["\(arg_max(forall(d in 2..w) ((sum(s in S)(demand[s,d]) > sum(s in S)(demand[s,d-1])))))"];
% constraint forall(j in 1..n) (sum (i in 1..n) (q[i,j]) == 1);