include "globals.mzn";

% Set the parameters
int: groups; % The number of employees - groups of employees
int: numShifts; % Number of shifts (D, A, N)
int: w = 7; % Days in the week
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
int: pr = groups*w;
array[S] of set of int: forbidden;
array[int,int] of int: forbidden3;
int: forbidden3l = length(forbidden3) div 3;



%decision variables in new perspective
array[1..groups,1..w,0..numShifts] of var 0..1: T_new;
array[1..groups*w] of var Sp: T; 
var 0..groups: free;

%maximize the number of free weekends
solve satisfy;

%function to calculate modulus
function int: calc_mod(int: inp, int: divisor) = 
  inp - bool2int(inp>divisor)*divisor + bool2int(inp<1)*divisor;
  
%to have exactly one shift selected 
constraint
forall(worker in N,day in W)( 
    %(sum(x in 0..3)(T_new[worker,day,x])) == 1
    count_eq(T_new[worker,day,..],1,1)
);

%To convert to desired output format
constraint
forall(i in 1..groups, j in 1..w, k in 0..numShifts)(
  (T_new[i,j,k] == 1) ->(T[(i-1)*w + j] = k) 
);

%demand constraints
constraint
forall(s in S,d in W)(
  (sum(x in N)(T_new[x,d,s])) == demand[s,((d+o-1) mod w)+1]
);  

constraint implied_constraint(
forall(d in W)(
  (sum(x in N)(T_new[x,d,0])) == groups - (sum(s in S)(demand[s,((d+o-1) mod w)+1]))
));

%symmetry breaking constraints
constraint symmetry_breaking_constraint(T_new[1,1,0] != 1);
constraint symmetry_breaking_constraint(T_new[groups,w,0]== 1);

%shift constraints
%minShift maxShift
constraint
forall(s in S, n in 1..groups, d in 1..w)(
 if(d > 1) then(
    if(T_new[n,d,s] == 1 /\ T_new[n,d-1,s]==0) then( 
      forall(x in 0..minShift[s]-1)(
        T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, s] == 1
      )
      
      /\
      sum(x in minShift[s]..maxShift[s])(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, s]) < (maxShift[s] - minShift[s] + 1)
    )
    else true endif
  )
  
  elseif(d == 1 /\ n > 1) then(
    if(T_new[n,d,s] == 1 /\ T_new[n-1,w,s]==0) then( 
        forall(x in 0..minShift[s]-1)(
          T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, s] == 1
        )
        
        /\
        sum(x in minShift[s]..maxShift[s])(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, s]) < maxShift[s] - minShift[s] + 1 
    )
    else true endif
  )
  elseif(d == 1 /\ n == 1) then(
    if(T_new[n,d,s] == 1 /\ T_new[groups,w,s]==0) then( 
        forall(x in 0..minShift[s]-1)(
          T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, s] == 1
        )
        
        /\
        sum(x in minShift[s]..maxShift[s])(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, s]) < maxShift[s] - minShift[s] + 1
      )
      else true endif
  )
  else true
  endif
); 

%minOff and maxOff
constraint
forall(n in 1..groups, d in 1..w)(
 if(d > 1) then(
    if(T_new[n,d,0] == 1 /\ T_new[n,d-1,0]==0) then( 
      forall(x in 0..minOff-1)(
        T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0] == 1
      )
      
      /\
      sum(x in minOff..maxOff)(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0]) < maxOff - minOff + 1 
    )
    else true endif
  )
  
  elseif(d == 1 /\ n > 1) then(
    if(T_new[n,d,0] == 1 /\ T_new[n-1,w,0]==0) then( 
        forall(x in 0..minOff-1)(
          T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0] == 1
        )
        
        /\
        sum(x in minOff..maxOff)(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0]) < maxOff - minOff + 1
    )
    else true endif
  )
  elseif(d == 1 /\ n == 1) then(
    if(T_new[n,d,0] == 1 /\ T_new[groups,w,0]==0) then( 
        forall(x in 0..minOff-1)(
          T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0] == 1
        )
        
        /\
        sum(x in minOff..maxOff)(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0]) < maxOff - minOff + 1 
      )
      else true endif
  )
  else true
  endif
); 

%minOn and maxOn 
constraint
forall(n in 1..groups, d in 1..w)(
 if(d > 1) then(
    if(T_new[n,d,0] == 0 /\ T_new[n,d-1,0]==1) then( 
      forall(x in 0..minOn-1)(
        T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0] == 0
      )
      
      /\
      sum(x in minOn..maxOn)(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0]) > 0 
    )
    else true endif
  )
  
  elseif(d == 1 /\ n > 1) then(
    if(T_new[n,d,0] == 0 /\ T_new[n-1,w,0]==1) then( 
        forall(x in 0..minOn-1)(
          T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0] == 0
        )
        
        /\
        sum(x in minOn..maxOn)(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0]) > 0
    )
    else true endif
  )
  elseif(d == 1 /\ n == 1) then(
    if(T_new[n,d,0] == 0 /\ T_new[groups,w,0]==1) then( 
        forall(x in 0..minOn-1)(
          T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0] == 0
        )
        
        /\
        sum(x in minOn..maxOn)(T_new[((((n-1)*w + d-1 + x) div w) mod groups) + 1, (((n-1)*w + d-1 + x) mod w) + 1, 0]) > 0 
      )
      else true endif
  )
  else true
  endif
); 

%forbidden sequences
%length 2

constraint
forall(n in 1..groups, d in 1..w, s in S)(
  if(T_new[n,d,s] == 1 /\ length(forbidden[s]) > 0) then( 
    forall(x in forbidden[s], i in 1..length(forbidden[s]))(
      T_new[((((n-1)*w + d-1 + i) div w) mod groups) + 1, (((n-1)*w + d-1 + i) mod w) + 1, x] != 1  
    )
  )
  else true endif
);

%length 3 

constraint
forall(n in 1..groups, d in 1..w, s in S)(
  if(T_new[n,d,s] == 1 /\ forbidden3l > 0) then( 
    forall(x in 1..forbidden3l)(
      (T_new[((((n-1)*w + d-1 + 1-1) div w) mod groups) + 1, (((n-1)*w + d-1 + 1-1) mod w) + 1, forbidden3[x,1]] != 1) \/
      (T_new[((((n-1)*w + d-1 + 2-1) div w) mod groups) + 1, (((n-1)*w + d-1 + 2-1) mod w) + 1, forbidden3[x,2]] != 1) \/
      (T_new[((((n-1)*w + d-1 + 3-1) div w) mod groups) + 1, (((n-1)*w + d-1 + 3-1) mod w) + 1, forbidden3[x,3]] != 1)
    )
  )
  else true endif
);

%offset breaking

% Constraints the offset
int: o_helper = 
  min([w+1] ++ 
  [d-1 | d in 2..w where sum(demand[..,d]) > sum(demand[..,d-1])]
  );
% Calculates the offset 
int: o = if o_helper <= w then o_helper else 0 endif;

array[1..4] of string: shifts_str= ["-", "1", "2", "3"];
output ["["] ++ [shifts_str[fix(T[calc_mod(i+pr - o,pr)])+1] ++ 
  if i == pr then "]\n" 
  else "," 
  endif | i in 1..pr];
output ["Offset: \(o)\n"];


 



