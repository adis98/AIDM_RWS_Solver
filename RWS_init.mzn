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
% solve maximize f;
solve satisfy;

% Define important functions
function int: calc_mod(int: inp, int: divisor) = (divisor+inp-1) mod divisor + 1;

% Define constraints
% Demand constraints
% Eq (1)
constraint
forall(d in W, s in S)(
  sum(i in 0..groups-1)(bool2int(T[d+i*w] == s)) = demand[s,(d+o-1) mod w + 1]
);

constraint 
forall(d in W) (
  sum(i in 0..groups-1)(bool2int(T[d+w*i] == 0)) = groups - sum(s in S) (demand[s,(d+o-1) mod w + 1])
);

% Symmetry breaking constraints
% Eq (3)
constraint symmetry_breaking_constraint(T[1] != 0);
% Eq (4)
constraint symmetry_breaking_constraint(T[pr] == 0);

% Lengths of shift blocks constraints
% Eq (5) for Shifts
constraint forall(i in 1..pr)
  (if (T[i] == 0) /\ (T[calc_mod(i-1, pr)] != 0) then
      forall(j in 1..minOff-1)(T[calc_mod(i+j,pr)] == 0) else true endif /\
  forall(s in S)(
    (if (T[i] == s) /\ (T[calc_mod(i-1,pr)] != s) then
      forall(j in 1..minShift[s]-1)(T[calc_mod(i+j,pr)] == s) else true endif)
%       all_equal(T[i..min(i+minShift[s]-1, pr)]) else true endif)
  )); 

% constraint forall(i in 2..pr) (forall(s in S)
%   (if (T[i] = s /\ T[(i-1)] != s) then
%     all_equal(T[i..min(i+minShift[s]-1, pr)]) else true endif));
% % Eq (5) for i=1
% constraint (forall(s in S)
%   (if T[1] = s then 
%     all_equal(T[1..minShift[s]]) else true endif));
% % Eq (5) for Days off
% constraint forall(i in 2..(pr-minOff)) 
%   (if (T[i] = 0 /\ T[(i-1)] != 0) then
%     all_equal(T[i..i+minOff-1]) else true endif);

% Eq (6) for Shifts
constraint forall(i in 1..pr)(
  (if (T[i] == 0 /\ T[calc_mod(i-1,pr)] != 0) then 
     (i + maxOff > pr) \/ (sum(j in minOff..maxOff) (bool2int(T[calc_mod(i+j,pr)] != 0)) > 0) else true endif) /\
     forall(s in S)(
  (if (T[i] == s /\ T[calc_mod(i-1,pr)] != s) then 
     (i + maxShift[s] > pr) \/ (sum(j in minShift[s]..maxShift[s]) (bool2int(T[calc_mod(i+j,pr)] != s)) > 0) else true endif)));    

% constraint forall(i in 2..pr) (forall(s in S)
%   (if (T[i] = s /\ T[i-1] != s) then 
%      (i + maxShift[s] > pr) \/ (sum(j in minShift[s]..maxShift[s]) (T[calc_mod(i+j, pr+1)] != s)) > 0 else true endif));
% % Eq (6) for i=1
% constraint (forall(s in S)
%   (if T[1] = s then 
%      (1 + maxShift[s] > pr) \/ (sum(j in minShift[s]..maxShift[s]) (T[calc_mod(1+j, pr+1)] != s)) > 0 else true endif));
% % Eq (6) for Off days
% constraint forall(i in 2..pr)
%   (if (T[i] = 0 /\ T[i-1] != 0) then 
%      (i + maxOff > pr) \/ (sum(j in minOff..maxOff) (T[calc_mod(i+j, pr+1)] != 0)) > 0 else true endif);  
     
% Eq (7) for Shifts
constraint forall(i in 1..pr)(
  if (T[i] != 0 /\ T[calc_mod(i-1,pr)] == 0) then 
    sum(j in 1..minOn-1)(T[calc_mod(i+j,pr)] == 0) = 0
%     count_eq(T[i+1..i+minOn-1],0,0)
  else true
  endif);

% constraint forall(i in 2..pr)
%   (if (T[i] != 0 /\ T[i-1] = 0) then 
%     forall(j in 1..minOn-1) (T[calc_mod(i+j, pr+1)] != 0) else true endif);
% % Eq (7) for i=1
% constraint (if T[1] != 0 then 
%   forall(j in 1..minOn-1) (T[calc_mod(1+j, pr+1)] != 0) else true endif);

% Eq (8) for Shifts
constraint forall(i in 1..pr-maxOn)(
  if (T[i] != 0 /\ T[calc_mod(pr+i-1,pr)] == 0) then 
    (i + maxOn > pr) \/ (count(T[i+minOn..i+maxOn], 0) > 0)
%     sum(j in minOn..maxOn) (T[calc_mod(i+j, pr+1)] = 0) > 0
  else true
  endif);

% constraint forall(i in 2..pr)
%   (if (T[i] != 0 /\ T[((i - 1))] = 0) then 
%      ((sum(j in minOn..maxOn) (T[calc_mod(i+j, pr+1)] = 0)) > 0) else true endif);
% constraint
% ((sum(j in minOn..maxOn) (T[calc_mod(1+j, pr+1)] = 0)) > 0);      

% Forbidden shifts constraints
% Eq (9)
constraint forall(i in 1..pr) (forall(s in S)(
   (T[i] != s) \/ (count_eq(forbidden[s], T[calc_mod(i+1,pr)], 0))));
%    (T[i] != s \/ not member(forbidden[s], T[calc_mod(i+1, pr+1)])));

% Eq (10)
constraint
forall(i in 1..pr)(
 if(forbidden3l > 0) then(
     forall(j in 1..forbidden3l)(
       (forbidden3[j,1] != T[i]) \/ (forbidden3[j,2] != T[calc_mod(i+1,pr)]) \/ (forbidden3[j,3] != T[calc_mod(i+2,pr)])
     )
 )
 else true endif
);

% Offset constraints        
% Eq (11) 
constraint forall(d in 2..w) (bools[d-1] = (sum(s in S)(demand[s,d]) <= sum(s in S)(demand[s,d-1])));
constraint symmetry_breaking_constraint(if (sum(bools) == (w-1)) then (o = 0) else (o = arg_min((bools))) endif);

% Problem extensions
% Infeasible weekly fluctuation
% Eq (13)
constraint 
  forall(s in S) (
    forall(i in W) (
      forall(j in maxShift[s]+1..2*minShift[s]-1) (
        forall(k in j-minShift[s]..minShift[s]-1) (
         demand[s,calc_mod(i+k, w)] >= demand[s,i] - demand[s,calc_mod(i-1, w)] + demand[s,calc_mod(i+j-1, w)] - demand[s, calc_mod(i+j, w)]
        )
      )
    )
  );

% Bounding the number of blocks
% int: demand_sum = sum(demand);
% var 0..pr: low_w; %  helper variable for bounding blocks constraints
% var 0..pr: up_w; %  helper variable for bounding blocks constraints
% var 0..pr: low_o; %  helper variable for bounding blocks constraints
% var 0..pr: up_o; %  helper variable for bounding blocks constraints
% var 0..pr: low; %  helper variable for bounding blocks constraints
% var 0..pr: up; %  helper variable for bounding blocks constraints

% % Eq (14-19)
int: demand_sum = sum(demand);
int: low_w = ceil(demand_sum/maxOn);
int: up_w = floor(demand_sum/minOn);
int: low_o = ceil((pr - demand_sum)/maxOff);
int: up_o = floor((pr - demand_sum)/minOff);
int: low = max(low_o, low_w);
int: up = min(up_o, up_w);
% constraint low_w = ceil(demand_sum/maxOn);
% constraint up_w = floor(demand_sum/minOn);
% constraint low_o = ceil((pr - demand_sum)/maxOff);
% constraint up_o = floor((pr - demand_sum)/minOff);
% constraint low = max(low_o, low_w);
% constraint up = min(up_o, up_w);

array[1..pr] of var 0..pr: c_w; % helper variables for bounding blocks constraints
array[1..pr] of var 0..pr: c_o; % helper variables for bounding blocks constraints
array[1..pr] of var 0..pr: c_b; % helper variables for bounding blocks constraints

% % Eq (21-25)
constraint c_o[1] = 0;
constraint forall(i in 2..pr) (c_o[i] = c_o[i-1] + bool2int(T[i] == 0));
constraint c_w[1] = 1;
constraint forall(i in 2..pr) (c_w[i] = c_w[i-1] + bool2int(T[i] != 0));
constraint c_b[1] = 1;
constraint forall(i in 2..pr) (c_b[i] = c_b[i-1] + bool2int(T[i-1] == 0 /\ T[i] != 0));

constraint forall(i in 1..pr) (
  if c_b[i] < c_b[calc_mod(i+1, pr)] then 
    ((low - c_b[i])*minOff <= pr - demand_sum - c_o[i] /\ pr - demand_sum - c_o[i] <= (up - c_b[i])*maxOff) /\
    ((low - c_b[i])*minOn <= demand_sum - c_w[i] /\ demand_sum - c_w[i] <= (up - c_b[i])*maxOn)
  else true
  endif);
  
% Weekly rest times
int: g = 1440;
array[1..numShifts+1] of int: start = [g, 6*60, 14*60, 22*60];
array[1..numShifts+1] of int: end = [0, 14*60, 22*60, 30*60];
int: wr = 36*60;
int: wr_red = 24*60;
int: e = 1;
int: s_p = 4;

% Eq 26 (Rest time)
array[1..pr] of var 0..pr*g: rest;

constraint forall(i in 1..pr)(
  if T[calc_mod(i-1, pr)] == 0 then 
    rest[i] = rest[calc_mod(i-1, pr)] + start[T[i]+1]
  else 
    rest[i] = g - end[T[calc_mod(i-1, pr)]+1] + start[T[i]+1]
  endif);
  
% % Eq (27)-(32)
array[1..6,1..pr] of var bool: D;

constraint forall(i in 1..pr)(
  D[1,i] = (rest[i] >= wr) /\
  D[2,i] = (T[i] != 0) /\
  D[3,i] = (T[calc_mod(i-1, pr)] == 0) /\ 
  D[4,i] = (end[T[calc_mod(i-2, pr)]+1] <= g) /\
  D[5,i] = (rest[i] < 2*(g*((w+i+o-1) mod w) + start[T[i]+1])) /\
%   D[5,i] = (rest[i] < 2*(g*((w+i+o-1-1) mod w + 1) + start[T[i]+1])) /\
  D[6,i] = (rest[i] >= wr_red));

% % % Eq (33)
array[1..groups] of var 0..2*w: P;

% function var int: x_help(int: i, int: j, int: w, var int: o, int: pr) = (pr+(i-1)*w+j-o) mod (pr+1) + (pr+(i-1)*w+j-o) div (pr+1);
function var int: x_help(int: i, int: j, int: w, var int: o, int: pr) = (pr + (i-1)*w + j - o - 1) mod pr + 1;

array[1..groups,1..2*w] of var bool: P_help;

constraint forall(i in 1..groups)(
  forall(j in 1..2*w) (P_help[i,j] = 
   (D[1,x_help(i,j,w,o,pr)] /\
   D[2,x_help(i,j,w,o,pr)] /\
   D[3,x_help(i,j,w,o,pr)] /\
   D[4,x_help(i,j,w,o,pr)] /\  
   ((j <= w) == D[5,x_help(i,j,w,o,pr)])
   )));
             
% constraint forall(i in 1..groups)(
%       (P[i] = arg_max(P_help[i,W])));         
constraint forall(i in 1..groups)(
  if (sum(P_help[i,..]) != 0) then 
    P[i] = arg_max(bool2int(P_help[i,..]))
  else
    P[i] = 0
  endif);

% % Eq (34)
constraint forall(i in 1..groups)(
  sum(j in 0..(s_p-1))(P[calc_mod(i+j, groups)] == 0) <= e);
  
% % Eq (35)
array[1..groups] of var 0..2*w: P_red;

array[1..groups,1..2*w] of var bool: Pred_help;
  
constraint forall(i in 1..groups)(
  forall(j in 1..2*w) (Pred_help[i,j] = 
  (D[2,x_help(i,j,w,o,pr)] /\
   D[6,x_help(i,j,w,o,pr)] /\  
   ((j <= w) == D[5,x_help(i,j,w,o,pr)])
   )));

constraint forall(i in 1..groups)(
  if P[i] != 0 then 
    P_red[i] = P[i]
  else
    if (sum(Pred_help[i,..]) != 0) then 
      P_red[i] = arg_max(bool2int(Pred_help[i,..])) 
    else
      P_red[i] = 0
    endif
  endif);
  
output ["\(P_red)"];
% % Eq (36)
% constraint forall(i in 1..groups)(
%   P_red[i] != 0);
  
% % % % Eq (37)
% constraint forall(i in 1..groups)(
%   sum(j in 0..(s_p-1))(
%     rest[(pr + (i+j-1)*w + P_red[calc_mod(i+j, groups)] - o - 1) mod pr + 1]) >= wr*s_p);
    
% % % % Eq (38)
% var 0..groups: f;

% constraint f = sum(i in 1..groups)(T[(pr+w*i-o-1-1) mod pr + 1] == 0 /\ T[(pr+w*i-o-1) mod pr + 1] == 0);

% % % Eq (39), (40)
% array[1..groups] of var 0..groups: dist;
% array[1..groups] of var bool: free;
% array[1..groups,1..groups] of var bool: free_help;
% var int: dm;

% constraint forall(i in 1..groups)(
%   free[i] = (T[(pr+w*i-o-1-1) mod pr + 1] == 0 /\ T[(pr+w*i-o-1) mod pr + 1] == 0));

% constraint forall(i in 1..groups)(
%   forall(j in i+1..i+groups)(
%     free_help[i,j-i] = (free[i] /\ free[calc_mod(j,groups)])));
     
% constraint forall(i in 1..groups)(
%   if free[i] == true then 

%       dist[i] = arg_max(bool2int(free_help[i,N]))    
%   else
%       dist[i] = 0
%   endif);
  
% constraint 
%   if max(dist) == 0 then
%     dm = groups+1
%   else
%     dm = max(dist)
%   endif;
  
  
% Outputs
output ["result = \(T) \n"];
output ["o = \(o) \n"];
% output["f = \(f)"];