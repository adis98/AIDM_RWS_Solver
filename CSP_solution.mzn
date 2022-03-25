include "globals.mzn";

% MODEL PARAMETERS
% (N) The number of employees - groups of employees
int: groups;                   
% (M) Number of shifts (D, A, N)
int: numShifts;                
% (W) Days in the week
int: w = 7;                    
% (NW) Number of days to be scheduled
int: pr = w*groups;            

% Set with all shifts
set of int: S = 1..numShifts; 
% Set with all shifts plus the days off 
set of int: Sp = 0..numShifts; 
% Set with all number of groups (or schedule wrrks)
set of int: N = 1..groups;  
% Set with all days indexes in a week   
set of int: W = 1..w;    
% Set with all indices of the schedule      
set of int: NW = 1..pr;        

% (R) Employees demand per shift i per day j
array[S,W] of int: demand;
% (lw) Minimum consecutive occurances of shift s     
array[S] of int: minShift; 
% (uw) Maximum consecutive occurances of shift s    
array[S] of int: maxShift;   
% (lo) Minimum consecutive days off  
int: minOff;     
% (uo) Maximum consecutive days off              
int: maxOff;     
% (ls) Minimum consecutive shifts duration with no day off              
int: minOn;   
% (us) Maximum consecutive shifts duration with no day off                 
int: maxOn;                    
% (Fs) Forbidden shifts after shift s
array[S] of set of int: forbidden; 
 % (F) Forbidden sequences of shifts
array[int,int] of int: forbidden3;
% Number of forbidden sequences
int: forbidden3l = length(forbidden3) div 3;

% DECISION VARIABLES
% The schedule of the first employee
array[NW] of var Sp: T;  
var 0..groups: f;

% OBJECTIVE FUNCTION
% Search by selecting the variables with the smallest minimum value 
% in their domain first.
% Then, using the 'indomain_min' value selection strategy, 
% we branch on this smallest values. 
solve :: int_search(T, 
                    smallest, 
                    indomain_min,
                    complete) 
         maximize f;

% FUNCTION DECLARATIONS
% Function that performs calculations with modulus without using the
% explicit "mod" function. 
function int: calc_mod(int: inp, int: divisor) = 
  inp - bool2int(inp>divisor)*divisor + bool2int(inp<1)*divisor;

% CONSTRAINTS
% Constraints the demand for each day for each shift 
constraint 
forall(d in W, s in S)(
  count(i in 0..groups-1)(T[d+i*w] == s) = 
    demand[s,d + o - bool2int((d+o)>w)*w]
);

% Constraints the number of day off assignments
constraint implied_constraint(
forall(d in W) (
  sum([bool2int(T[d+i*w] == 0) | i in 0..groups-1]) = 
    groups - sum([demand[s,d + o - 
                 bool2int((d+o)>w)*w] | s in S])
));

% Constraints the first day of the schedule
constraint symmetry_breaking_constraint(T[1] != 0);
% Constraints the last day of the schedule
constraint symmetry_breaking_constraint(T[pr] == 0);

% Constraints the minimum consecutive off days, and shifts
% For off days
constraint forall(i in NW)(
  (T[i] == 0) /\ (T[calc_mod(i-1, pr)] != 0) ->
      forall(j in 1..minOff-1)(T[calc_mod(i+j,pr)] == 0));
% For shifts
constraint forall(i in NW,s in S)(
    (T[i] == s) /\ (T[calc_mod(i-1,pr)] != s) ->
      forall(j in 1..minShift[s]-1)(T[calc_mod(i+j,pr)] == s)
    );

% Constraints the maximum consecutive off days, and shifts
% For off days
constraint forall(i in NW)(
  (T[i] == 0 /\ T[calc_mod(i-1,pr)] != 0) -> 
    (i + maxOff > pr) \/  
    exists(j in minOff..maxOff)(T[calc_mod(i+j, pr)] != 0)
);
% For shifts
constraint forall(i in NW,s in S)(
  (T[i] == s /\ T[calc_mod(i-1,pr)] != s) ->
    (i + maxShift[s] > pr) \/ 
    (exists(j in minShift[s]..maxShift[s])
      (T[calc_mod(i+j,pr)] != s))
);
  
     
% Constraints the minimum consecutive days without a day-off
constraint forall(i in NW)(
  (T[i] != 0 /\ T[calc_mod(i-1,pr)] == 0) ->
    forall(j in 1..minOn-1)(T[calc_mod(i+j,pr)] != 0));

% Constraints the maximum consecutive days without a day-off
constraint forall(i in NW)(
  (T[i] != 0 /\ T[calc_mod(i-1,pr)] == 0) ->
    (i + maxOn > pr) \/ 
    exists(j in minOn..maxOn)(T[calc_mod(i+j, pr)] == 0)
);  

% Applies the forbidden shifts constraints
constraint forall(i in NW,s in S)(
  (T[i] != s) \/ 
  (T[calc_mod(i+1,pr)] in forbidden[s] == false)
);

% Applies the forbidden sequences constraint
constraint
forall(i in NW)(
 (forbidden3l > 0) ->
     forall(j in 1..forbidden3l)(
         forbidden3[j,..] != 
           [T[i],T[calc_mod(i+1,pr)],T[calc_mod(i+2,pr)]]
     )
);
       
% Constraints the offset
int: o_helper = 
  min([w+1] ++ 
  [d-1 | d in 2..w where sum(demand[..,d]) > sum(demand[..,d-1])]
  );
% Calculates the offset 
int: o = if o_helper <= w then o_helper else 0 endif;

% Checks for infeasibile weekly fluctuation
constraint 
  forall(s in S, i in W, j in maxShift[s]+1..2*minShift[s]-1, 
    k in j-minShift[s]..minShift[s]-1) (
    demand[s,calc_mod(i+k, w)] >= 
    demand[s,i] - demand[s,calc_mod(i-1, w)] +
    demand[s,calc_mod(i+j-1, w)] - 
    demand[s, calc_mod(i+j, w)]
  );

% Constraints the objective function
% (i.e. the number of free weekends)
constraint f = sum(i in 1..groups)(T[calc_mod(w*i-o-1, pr)] == 0 /\
 T[calc_mod(pr+w*i-o,pr)] == 0);

% OUTPUT
array[1..4] of string: shifts_str= ["-", "1", "2", "3"];
output ["["] ++ [shifts_str[fix(T[calc_mod(i-o,pr)])+1] ++ 
  if i == pr then "]\n" 
  else "," 
  endif | i in NW];
output ["\(f)\n"];