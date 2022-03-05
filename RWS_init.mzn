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

%%  Problem extensions
% Infeasible weekly fluctuation
% Eq (13)
constraint 
  forall(s in S) (
    forall(i in W) (
      forall(j in maxShift[s]+1..2*minShift[s]-1) (
        forall(k in j-minShift[s]..minShift[s]-1) (
         demand[s,(i+k) mod (w+1) + (i+k) div(w+1)] >= demand[s,i] - demand[s,(w+i-1) mod (w+1)] + demand[s, (i+j-1) mod (w+1) + (i+j-1) div(w+1)] - demand[s, (i+j) mod (w+1) + (i+j) div(w+1)]
        )
      )
    )
  );

% Bounding the number of blocks
int : demand_sum = sum(i in W)(sum(j in S)(demand[i,j]));
var 0..pr: low_w; %  helper variable for bounding blocks constraints
var 0..pr: up_w; %  helper variable for bounding blocks constraints
var 0..pr: low_o; %  helper variable for bounding blocks constraints
var 0..pr: up_o; %  helper variable for bounding blocks constraints
var 0..pr: low; %  helper variable for bounding blocks constraints
var 0..pr: up; %  helper variable for bounding blocks constraints

% Eq (14-19)
constraint low_w = demand_sum div maxOn + 1;
constraint up_w = demand_sum div minOn;
constraint low_o = (pr - demand_sum) div maxOff + 1;
constraint up_o = (pr - demand_sum) div minOff;
constraint low = max(low_o, low_w);
constraint up = min(up_o, up_w);

array[1..pr] of var 1..pr: c_w; % helper variables for bounding blocks constraints
array[1..pr] of var 1..pr: c_o; % helper variables for bounding blocks constraints
array[1..pr] of var 1..pr: c_b; % helper variables for bounding blocks constraints

% Eq (21-25)
constraint c_w[1] = 0;
constraint forall(i in 2..pr) (c_w[i] = c_w[i-1] + (T[i] == 0));
constraint c_o[1] = 0;
constraint forall(i in 2..pr) (c_o[i] = c_o[i-1] + (T[i] != 0));
constraint c_b[1] = 0;
constraint forall(i in 2..pr) (c_b[i] = c_b[i-1] + (T[i-1] == 0 /\ T[i] != 0));

constraint forall(i in 1..pr) (
  if c_b[i] < c_b[(i+1) mod (pr+1) + (i+1) div (pr+1)] then 
    (low - c_b[i])*minOff <= pr - demand_sum - c_o[i] /\ pr - demand_sum - c_o[i] <= (up - c_b[i])*maxOff
  else true
  endif);

constraint forall(i in 1..pr) (
  if c_b[i] < c_b[(i+1) mod (pr+1) + (i+1) div (pr+1)] then 
    (low - c_b[i])*minOn <= demand_sum - c_w[i] /\ demand_sum - c_w[i] <= (up - c_b[i])*maxOn
  else true
  endif);
  


% Outputs
output ["result = \(T) \n"];
output ["o = \(o) \n"];