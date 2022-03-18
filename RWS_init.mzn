% RWS problem - basic form
include "globals.mzn";

% ==================================================================================================
% Model parameters
% ==================================================================================================
int: groups;                        % (N) The number of employees - groups of employees
int: numShifts;                     % (M) Number of shifts (D, A, N)
int: w = 7;                         % (W) Days in the week
int: pr = w*groups;                 % (NW) Number of days to be scheduled
% Set of ranges
set of int: S = 1..numShifts;       % set with all shifts
set of int: Sp = 0..numShifts;      % set with all shifts plus the days off
set of int: N = 1..groups;          % set with all number of groups (or schedule wrrks)
set of int: W = 1..w;               % set with all days indexes in a week
set of int: NW = 1..pr;             % set with all indices of the schedule

array[S,W] of int: demand;          % (R) Employees demand per shift i per day j
array[S] of int: minShift;          % (lw) Minimum consecutive occurances of shift s
array[S] of int: maxShift;          % (uw) Maximum consecutive occurances of shift s
int: minOff;                        % (lo) Minimum consecutive days off
int: maxOff;                        % (uo) Maximum consecutive days off
int: minOn;                         % (ls) Minimum consecutive shifts duration with no day off
int: maxOn;                         % (us) Maximum consecutive shifts duration with no day off
array[S] of set of int: forbidden;  % (Fs) Forbidden shifts after shift s
array[int,int] of int: forbidden3;  % (F) Forbidden sequences of shifts
int: forbidden3l = length(forbidden3) div 3; % number of forbidden sequences

% ==================================================================================================
% Decision variables
% ==================================================================================================
array[NW] of var Sp: T;          % the schedule of the first employee
% var 0..w-1: o;                      % the offset for the first day

% ==================================================================================================
% objective function
% ==================================================================================================
solve :: int_search(T, 
                    smallest, 
                    indomain_min) 
maximize f;
%       :: int_search([f], 
%                     smallest, 
%                     indomain_min) 
% maximize f;
% solve maximize f;
% solve :: int_search(T, 
%                     smallest, 
%                     indomain_min,
%                     complete) 
%          satisfy;
% % solve satisfy;

% ==================================================================================================
% function declarations
% ==================================================================================================
function int: calc_mod(int: inp, int: divisor) = inp - bool2int(inp>divisor)*divisor + bool2int(inp<1)*divisor;

% ==================================================================================================
% Constraints
% ==================================================================================================
% Eq (1) - Constraints the demand for each day for each shift 
constraint
forall(d in W, s in S)(
%   sum([bool2int(T[d+i*w] == s) | i in 0..groups-1]) = demand[s,d + o - bool2int((d+o)>w)*w]
  count(i in 0..groups-1)(T[d+i*w] == s) = demand[s,d + o - bool2int((d+o)>w)*w]
);

% Eq (2) - Constraints the number of day off assignments for each day (redundant)
constraint redundant_constraint(
forall(d in W) (
  sum([bool2int(T[d+i*w] == 0) | i in 0..groups-1]) = groups - sum([demand[s,d + o - bool2int((d+o)>w)*w] | s in S])
));

% Eq (3) - Constraints the first day of the schedule not to be a day off (symmetry breaking)
constraint symmetry_breaking_constraint(T[1] != 0);
% Eq (4) - Constraints the last day of the schedule to be a day off (symmetry breaking)
constraint symmetry_breaking_constraint(T[pr] == 0);

% Eq (5) - Constraints the minimum consecutive off days, and shifts for each shift
constraint forall(i in NW)(
  (T[i] == 0) /\ (T[calc_mod(i-1, pr)] != 0) ->
      forall(j in 1..minOff-1)(T[calc_mod(i+j,pr)] == 0));
      
% constraint forall(i in NW)(
%   forall(s in S)(
%     (if (T[i] == s) /\ (T[calc_mod(i-1,pr)] != s) then
%       forall(j in 1..minShift[s]-1)(T[calc_mod(i+j,pr)] == s) else true endif)
%   )); 

constraint forall(i in NW,s in S)(
    (T[i] == s) /\ (T[calc_mod(i-1,pr)] != s) ->
      forall(j in 1..minShift[s]-1)(T[calc_mod(i+j,pr)] == s)
    );

% Eq (6) - Constraints the maximum consecutive off days, and shifts for each shift
constraint forall(i in NW)(
  (T[i] == 0 /\ T[calc_mod(i-1,pr)] != 0) -> 
    (i + maxOff > pr) \/  exists(j in minOff..maxOff)(T[calc_mod(i+j, pr)] != 0) :: domain);
    
constraint forall(i in NW,s in S)(
  (T[i] == s /\ T[calc_mod(i-1,pr)] != s) ->
    (i + maxShift[s] > pr) \/ (exists(j in minShift[s]..maxShift[s]) (T[calc_mod(i+j,pr)] != s)) :: domain);
  
     
% Eq (7) - Constraints the minimum consecutive days without a day-off
constraint forall(i in NW)(
  (T[i] != 0 /\ T[calc_mod(i-1,pr)] == 0) ->
    forall(j in 1..minOn-1)(T[calc_mod(i+j,pr)] != 0));

% Eq (8) - Constraints the maximum consecutive days without a day-off
constraint forall(i in NW)(
  (T[i] != 0 /\ T[calc_mod(i-1,pr)] == 0) ->
    (i + maxOn > pr) \/  exists(j in minOn..maxOn)(T[calc_mod(i+j, pr)] == 0) :: domain);  

% Eq (9) - Applies the forbidden shifts constraints
constraint forall(i in NW,s in S)(
  (T[i] != s) \/ (T[calc_mod(i+1,pr)] in forbidden[s] == false));

% Eq (10) - Applies the forbidden sequences constraint
constraint
forall(i in NW)(
 (forbidden3l > 0) ->
     forall(j in 1..forbidden3l)(
         forbidden3[j,..] != [T[i],T[calc_mod(i+1,pr)],T[calc_mod(i+2,pr)]] :: domain
     )
);
       
% Eq (11),(12) - Constraints the offset
int: o_helper = min([w+1] ++ [d-1 | d in 2..w where sum(demand[..,d]) > sum(demand[..,d-1])]);
% constraint if o_helper <= w then o = o_helper else o = 0 endif;
int: o = if o_helper <= w then o_helper else 0 endif;
% ==================================================================================================
% Extended constraints
% ==================================================================================================
% Eq (13) - Infeasibility weekly fluctuation
constraint 
  forall(s in S, i in W, j in maxShift[s]+1..2*minShift[s]-1, k in j-minShift[s]..minShift[s]-1) (
    demand[s,calc_mod(i+k, w)] >= demand[s,i] - demand[s,calc_mod(i-1, w)] + demand[s,calc_mod(i+j-1, w)] - demand[s, calc_mod(i+j, w)]
  );

% % Eq (14)-(19) - Bounding the number of blocks
int: demand_sum = sum(demand);
int: low_w = ceil(demand_sum/maxOn);
int: up_w = floor(demand_sum/minOn);
int: low_o = ceil((pr - demand_sum)/maxOff);
int: up_o = floor((pr - demand_sum)/minOff);
int: low = max(low_o, low_w);
int: up = min(up_o, up_w);

% Eq (20)
% constraint 
%   global_cardinality_low_up([bool2int(T[i] != 0 /\ T[calc_mod(i-1,pr)] == 0) - bool2int(T[i] == 0 /\ T[calc_mod(i-1,pr)] != 0) | i in NW], [-1,1], [low,low], [up,up]);


% STOPPPPP

% array[NW] of var 0..pr: c_w; % helper variables for bounding blocks constraints
% array[NW] of var 0..pr: c_o; % helper variables for bounding blocks constraints
% array[NW] of var 0..pr: c_b; % helper variables for bounding blocks constraints

% % % Eq (21-25)
% constraint c_o[1] = 0;
% constraint forall(i in 2..pr) (c_o[i] = c_o[i-1] + bool2int(T[i] == 0));
% constraint c_w[1] = 1;
% constraint forall(i in 2..pr) (c_w[i] = c_w[i-1] + bool2int(T[i] != 0));
% constraint c_b[1] = 1;
% constraint forall(i in 2..pr) (c_b[i] = c_b[i-1] + bool2int(T[i-1] == 0 /\ T[i] != 0));

% constraint forall(i in NW) (
%   if c_b[i] < c_b[calc_mod(i+1, pr)] then 
%     ((low - c_b[i])*minOff <= pr - demand_sum - c_o[i] /\ pr - demand_sum - c_o[i] <= (up - c_b[i])*maxOff) /\
%     ((low - c_b[i])*minOn <= demand_sum - c_w[i] /\ demand_sum - c_w[i] <= (up - c_b[i])*maxOn)
%   else true
%   endif);
  
% % Weekly rest times
% int: g = 1440;
% array[1..numShifts+1] of int: start = [g, 6*60, 14*60, 22*60];
% array[1..numShifts+1] of int: end = [0, 14*60, 22*60, 30*60];
% int: wr = 36*60;
% int: wr_red = 24*60;
% int: e = 1;
% int: s_p = 4;

% % Eq 26 (Rest time)
% array[NW] of var 0..pr*g: rest;

% constraint forall(i in NW)(
%   if T[calc_mod(i-1, pr)] == 0 then 
%     rest[i] = rest[calc_mod(i-1, pr)] + start[T[i]+1]
%   else 
%     rest[i] = g - end[T[calc_mod(i-1, pr)]+1] + start[T[i]+1]
%   endif);
  
% % % Eq (27)-(32)
% array[1..6,NW] of var bool: D;

% constraint forall(i in NW)(
%   D[1,i] = (rest[i] >= wr) /\
%   D[2,i] = (T[i] != 0) /\
%   D[3,i] = (T[calc_mod(i-1, pr)] == 0) /\ 
%   D[4,i] = (end[T[calc_mod(i-2, pr)]+1] <= g) /\
%   D[5,i] = (rest[i] < 2*(g*((w+i+o-1) mod w) + start[T[i]+1])) /\
% %   D[5,i] = (rest[i] < 2*(g*((w+i+o-1-1) mod w + 1) + start[T[i]+1])) /\
%   D[6,i] = (rest[i] >= wr_red));

% % % % Eq (33)
% array[1..groups] of var 0..2*w: P;

% % function var int: x_help(int: i, int: j, int: w, var int: o, int: pr) = (pr+(i-1)*w+j-o) mod (pr+1) + (pr+(i-1)*w+j-o) div (pr+1);
% function var int: x_help(int: i, int: j, int: w, var int: o, int: pr) = (pr + (i-1)*w + j - o - 1) mod pr + 1;

% array[1..groups,1..2*w] of var bool: P_help;

% constraint forall(i in 1..groups)(
%   forall(j in 1..2*w) (P_help[i,j] = 
%    (D[1,x_help(i,j,w,o,pr)] /\
%    D[2,x_help(i,j,w,o,pr)] /\
%    D[3,x_help(i,j,w,o,pr)] /\
%    D[4,x_help(i,j,w,o,pr)] /\  
%    ((j <= w) == D[5,x_help(i,j,w,o,pr)])
%    )));
             
% % constraint forall(i in 1..groups)(
% %       (P[i] = arg_max(P_help[i,W])));         
% constraint forall(i in 1..groups)(
%   if (sum(P_help[i,..]) != 0) then 
%     P[i] = arg_max(bool2int(P_help[i,..]))
%   else
%     P[i] = 0
%   endif);

% % % Eq (34)
% constraint forall(i in 1..groups)(
%   sum(j in 0..(s_p-1))(P[calc_mod(i+j, groups)] == 0) <= e);
  
% % % Eq (35)
% array[1..groups] of var 0..2*w: P_red;

% array[1..groups,1..2*w] of var bool: Pred_help;
  
% constraint forall(i in 1..groups)(
%   forall(j in 1..2*w) (Pred_help[i,j] = 
%   (D[2,x_help(i,j,w,o,pr)] /\
%    D[6,x_help(i,j,w,o,pr)] /\  
%    ((j <= w) == D[5,x_help(i,j,w,o,pr)])
%    )));

% constraint forall(i in 1..groups)(
%   if P[i] != 0 then 
%     P_red[i] = P[i]
%   else
%     if (sum(Pred_help[i,..]) != 0) then 
%       P_red[i] = arg_max(bool2int(Pred_help[i,..])) 
%     else
%       P_red[i] = 0
%     endif
%   endif);
  
% % Eq (36)
% constraint forall(i in 1..groups)(
%   P_red[i] != 0);
  
% % % % Eq (37)
% constraint forall(i in 1..groups)(
%   sum(j in 0..(s_p-1))(
%     rest[(pr + (i+j-1)*w + P_red[calc_mod(i+j, groups)] - o - 1) mod pr + 1]) >= wr*s_p);
    
% Eq (38)
% var 0..groups: f;

% constraint f = sum(i in 1..groups)(T[calc_mod(w*i-o-1, pr)] == 0 /\ T[calc_mod(pr+w*i-o,pr)] == 0);

% % Eq (39), (40)
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
  
% ==================================================================================================
% Output results
% ==================================================================================================   
array[1..4] of string: shifts_str= ["-", "1", "2", "3"];
output ["["] ++ [shifts_str[fix(T[i])+1] ++ if i == pr then "]\n" else "," endif | i in NW];
output ["\(o)\n"];


output ["result = \(T) \n"];
output ["o = \(o) \n"];
output ["\(sum(i in 1..groups)(T[calc_mod(w*i-o-1, pr)] == 0 /\ T[calc_mod(pr+w*i-o,pr)] == 0))"];
% output["f = \(f)"];