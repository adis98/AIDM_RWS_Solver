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
array[1..w] of var 1..w+4: gt;
var 0..groups: free;
array[1..pr] of var Sp: T; % the schedule of the first employee
var 0..w-1: o; % the offset 

% Define objective function
solve maximize free;

% Define constraints
% Demand constraints
% Eq (1)
constraint
forall(d in W, s in S)(
  sum(i in 0..groups-1)(T[d + i*w] = s) == demand[s,max(1,(d+o) mod (w))]
);
%constraint forall(d in W,s in S) ((sum(i in 0..groups-1) (T[d+w*i] = s)) == demand[s, ((d+o) mod (pr)) + 1]);
% Eq (2)
constraint 
forall(d in W) (
  sum(i in 0..groups-1)(T[d+w*i] = 0) == groups - sum(i in S) (demand[i,max(1,(d+o) mod (w))])
);

% Symmetry breaking constraints
% Eq (3)
constraint symmetry_breaking_constraint(T[1] != 0);
% Eq (4)
constraint symmetry_breaking_constraint(T[pr] == 0);

% Lengths of shift blocks constraints
% Eq (5) for Shifts
constraint forall(i in 2..pr) (forall(s in S)
  (if (T[i] = s /\ T[(i-1)] != s) then forall(j in 1..minShift[s]-1) (T[max(1,((i+j) mod (pr)))] = s) else true endif));
% Eq (5) for i=1
constraint (forall(s in S)
  (if T[1] = s then forall(j in 1..minShift[s]-1) (T[max(1,((1+j) mod (pr)))] = s) else true endif)); 
% Eq (5) for Off days
constraint forall(i in 2..pr) 
  (if (T[i] = 0 /\ T[(i-1)] != 0) then forall(j in 1..minOff-1) (T[max(1,((i+j) mod (pr)))] = 0) else true endif);

% Eq (6) for Shifts
constraint forall(i in 2..pr) (forall(s in S)
  (if (T[i] = s /\ T[((i - 1) mod (pr+1))] != s) then 
     (sum(j in minShift[s]..maxShift[s]) (T[max(1,((i+j) mod (pr)))] != s)) > 0 else true endif));
% Eq (6) for i=1
constraint (forall(s in S)
  (if T[1] = s then 
     (sum(j in minShift[s]..maxShift[s]) (T[max(1,((1+j) mod (pr)))] != s)) > 0 else true endif));
% Eq (6) for Off days
constraint forall(i in 2..pr)
  (if (T[i] = 0 /\ T[((i - 1) mod (pr+1))] != 0) then 
     (sum(j in minOff..maxOff) (T[max(1,((i+j) mod (pr)))] != 0)) > 0 else true endif);  

% Eq (7) for Shifts
constraint forall(i in 2..pr)
  (if (T[i] != 0 /\ T[((i-1) mod (pr+1))] = 0) then forall(j in 1..minOn-1) (T[max(1,((i+j) mod (pr)))] != 0) else true endif);
% Eq (7) for i=1
constraint (if T[1] != 0 then forall(j in 1..minOn-1) (T[max(1,((1+j) mod (pr)))] != 0) else true endif);
% Eq (8) for Shifts
constraint forall(i in 2..pr)
  (if (T[i] != 0 /\ T[((i - 1))] = 0) then 
     ((sum(j in minOn..maxOn) (T[max(1,(i+j) mod (pr))] = 0)) > 0) else true endif);
constraint
((sum(j in minOn..maxOn) (T[max(1,((1+j) mod (pr)))] = 0)) > 0);      
% Forbidden shifts constraints
% Eq (9)
constraint forall(i in 1..pr) (forall(s in S)
   (T[i] != s \/ count_eq(forbidden[s], T[max(1,((i+1) mod (pr)))], 0)));
% Eq (10)
constraint forall(i in 1..pr) (forall(ii in 1..3)
   (if forbidden3l>0 then
   sum(jj in 1..forbidden3l) (forbidden3[jj ,ii] - T[max(1,((i+jj-1) mod (pr)))] != 0) > 0
   else true endif));
   
array[1..(w-1)] of var bool: bools;

constraint
free = sum(i in 1..groups)(T[max(1,(w*i-1))]=0 /\ T[max(1,(w*i))]=0);

%offset - aditya
constraint
forall(d in 2..w)(
  if(sum(s in S)(demand[s,d]) > sum(s in S)(demand[s,d-1])) then(
    gt[d] = d
  )
  else (
    gt[d] = w+4
  )
  endif
);

constraint
  if(sum(s in S)(demand[s,1]) > sum(s in S)(demand[s,w])) then(
    gt[1] = 1
  )
  else(
    gt[1] = w+4
  )
  endif;
 
constraint
symmetry_breaking_constraint(if(min(gt) == w + 4) then o == 0 else o = min(gt)-1 endif);

% constraint forall(d in 2..w) (bools[d-1] = (sum(s in S)(demand[s,d]) <= sum(s in S)(demand[s,d-1])));
%constraint o = max(arg_min(bools), 0);
% Eq (11)
% Symmetry breaking constraint for the offset
%  constraint o = max(min(forall(d in 2..w) (d -> (sum(s in S)(demand[s,d]) > sum(s in S)(demand[s,d-1])))) - 1,0);
%  constraint o = argmax(1, demand);
output ["\(T) \n"];
output ["free weekends \(free)\n"];
%output ["offset \(o)\n"];
% array[1..3] of int: x = [1, 2, 3];
% output["\(bools)"];
% output["\(arg_min(bools))"];
% output["\(arg_max(forall(d in 2..w) ((sum(s in S)(demand[s,d]) > sum(s in S)(demand[s,d-1])))))"];
% constraint forall(j in 1..n) (sum (i in 1..n) (q[i,j]) == 1);