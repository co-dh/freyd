/ B&dM p.207: the Gofer program for the 0/1 knapsack (section 8.4), in q.
/ Transcribed from AOP/A8_4_KnapsackProgram.lean (namespace Knap207): each `/` line is the book's definition, the line below it the q.
/ Renames forced by q: value, within are q primitives -> value_, within_; cons' -> consp (no ' in names).
/ An item is a (value;weight) pair; a packing x is held as (x;(value x;weight x)), as in the Lean Rep.
/ f'[x], not f'x: after a name ending in _ the lexer reads _' as an operator.

/ ---- Appendix prelude (p.265-266)
/ cons (a,x) = [a] ++ x
cons:{enlist[x 0],x 1}    / enlist: an item is a 2-list, a plain , would splice it into the packing
/ cpr (a,xs) = [(a,x) | x <- xs]
cpr:{(x 0;)'[x 1]}
/ dupl (a,(b,c)) = ((a,b),(a,c))
dupl:cpr    / the Appendix's dupl is cpr on the two-item list (b;c), not the diagonal
/ catalist (c,f) [] = c ; catalist (c,f) (a:x) = f (a, catalist (c,f) x)
catalist:{[c;f;xs] {x(z;y)}[f]/[c;reverse xs]}    / foldr as / over the reversed list: q has no right fold, recursion overflows

/ ---- the program
/ value = outl . outr
value_:{x[1;0]}
/ weight = outr . outr
weight:{x[1;1]}
/ r = geq . cross (value, value)
r:{(>=) . value_'[x]}
/ p = leq . cross (weight, weight)
p:{(<=) . weight'[x]}
/ q = meet . pair (p, r)
q:{p[x]&r x}
/ merge r ([],y) = y ; merge r (x,[]) = x
/ merge r (a:x,b:y) = if r (a,b) then a : merge r (x,b:y) else b : merge r (a:x,y)
merge:{x idesc value_'[x:raze x]}    / merge r: both lists are r-sorted, and the stable idesc keeps x before y on ties, as r = geq does
/ thinL q [] = [] ; thinL q [a] = [a]
/ thinL q (a:b:x) = if q (a,b) then thinL q (a:x) else if q (b,a) then thinL q (b:x) else a : thinL q (b:x)
/ thinL q on an r-sorted list: b replaces the held a iff weight b < weight a (the running minimum drops),
/ and a is emitted unless the next such b has a's value (then q (b,a) holds and a is dropped)
thinL:{k:where differ mins weight'[x]; x k where 1_differ value_'[x k],0N}
/ within w = (w >=) . weight
within_:{[w;x] w>=weight x}
/ addin f = plus . cross (f, id)
addin:{[f;x] f[x 0]+x 1}
/ augment (val,wt) = cross (addin val, addin wt) . dupl
augment:{[val;wt;x] (addin val;addin wt)@'dupl x}
/ cons' (val,wt) = cross (cons, augment (val,wt)) . dupl
consp:{[val;wt;x] (cons;augment[val;wt])@'dupl x}
/ start = [([],(0,0))]
start:enlist (();0 0)
/ step (val,wt) w = pair (filter (within w) . list (cons' (val,wt)), outr) . cpr
step:{[val;wt;w;x] ys:consp[val;wt]'[x:cpr x]; (ys where within_[w]'[ys];x[;1])}
/ knapsack (val,wt) w = outl . head . catalist (start, thinL q . merge r . step (val,wt) w)
knapsack:{[val;wt;w;xs] first catalist[start;{[val;wt;w;x] thinL merge step[val;wt;w] x}[val;wt;w];xs]}

/ ---- checks: the Lean #guard, then brute force over all subsets; exit 1 on any mismatch
fail:{-2 "FAIL: ",x; exit 1}
g:knapsack[first;last;10;(6 5;5 4;4 6;3 3)]
-1 "guard: ",.Q.s1 g;
if[not g~((6 5;5 4);11 9); fail "guard expected ((6 5;5 4);11 9), got ",.Q.s1 g]

/ best value among all subsets of items within capacity c, by enumerating the 2^n bitmasks
brute:{[its;c] m:(n#2) vs til prd (n:count its)#2; max (sum its[;0]*m) where c>=sum its[;1]*m}
check:{[n;c] its:flip (1+n?30;1+n?20); k:knapsack[first;last;c;its]; b:brute[its;c];
  -1 "n=",string[n]," c=",string[c]," knapsack=",string[k[1;0]]," brute=",string b;
  if[not (b=k[1;0])&(c>=k[1;1])&k[1]~sum (enlist 0 0),k 0; fail "brute-force mismatch on ",.Q.s1 (its;c;k)]}
\S 207
check ./: (15 40;15 60;14 25;16 80;15 1);

/ timing: 200 items, capacity 1000
big:flip (1+200?100;1+200?100)
-1 "200 items, capacity 1000: ",string[system "t knapsack[first;last;1000;big]"]," ms";
exit 0
