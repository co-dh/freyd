/ B&dM p.207: the Gofer program for the 0/1 knapsack (section 8.4), in q.
/ Transcribed from AOP/A8_4_KnapsackProgram.lean (namespace Knap207); one q function per book definition, same order.
/ Renames forced by q: cross, value, within are q primitives -> cross_, value_, within_; cons' -> consp (no ' in names).
/ An item is a (value;weight) pair; a packing x is held as (x;(value x;weight x)), as in the Lean Rep.

/ ---- Appendix prelude (p.265-266): dupl, pair, cross take and return pairs
/ cross_:{[fg;ab] ((fg 0) ab 0;(fg 1) ab 1)}    / now (f;g)@'ab at each call
dupl:{((x 0;x[1;0]);(x 0;x[1;1]))}    / ((a;b);(a;c)), the Appendix's dupl, not the diagonal
/ pair:{[fg;a] ((fg 0) a;(fg 1) a)}    / now (f;g)@\:a at each call
/ outl:{x 0}    / now x 0 at each call
/ outr:{x 1}    / now x 1 at each call
/ plus:{(+) . x}    / now (+) . at each call
/ geq:{(>=) . x}    / now (>=) . at each call
/ leq:{(<=) . x}    / now (<=) . at each call
/ meet:{(&) . x}    / now (&) . at each call
/ cons:{(enlist x 0),x 1}
cons:{enlist[x 0],x 1}    / enlist: an item is a 2-list, a plain , would splice it into the packing
/ cpr:{{(x;y)}[x 0] each x 1}
cpr:{(enlist x 0),/:enlist each x 1}    / enlist: a plain x,/:y would splice the item into each packing
/ foldr as a left fold over the reversed list: q has no right fold, and recursion would hit the stack on long input
catalist:{[s;f;xs] {[f;b;a] f (a;b)}[f]/[s;reverse xs]}
/ an index loop, not the book's recursion: q's stack is too shallow for lists of a thousand packings
merge:{[r;xy] xs:xy 0; ys:xy 1; i:j:0; z:();
  while[(i<count xs)&j<count ys; $[r (xs i;ys j); [z,:enlist xs i; i+:1]; [z,:enlist ys j; j+:1]]];
  z,(i _ xs),j _ ys}
/ a holds the head of the book's recursive call; z the elements already emitted
thinL:{[q;xs] if[2>count xs; :xs]; a:xs 0; z:(); i:1;
  while[i<count xs; b:xs i; $[q (a;b); (); q (b;a); a:b; [z,:enlist a; a:b]]; i+:1];
  z,enlist a}

/ ---- the program
/ value_:{outl outr x}
value_:{x[1;0]}
/ weight:{outr outr x}
weight:{x[1;1]}
/ r:{geq cross_[(value_;value_)] x}
r:{(>=) . (value_;value_)@'x}
/ p:{leq cross_[(weight;weight)] x}
p:{(<=) . (weight;weight)@'x}
/ q:{meet pair[(p;r)] x}
q:{(&) . (p;r)@\:x}
within_:{[w;x] w>=weight x}
/ addin:{[f;x] plus cross_[(f;{x})] x}
addin:{[f;x] (+) . (f;{x})@'x}

/ augment:{[val;wt;x] cross_[(addin[val];addin[wt])] dupl x}
augment:{[val;wt;x] (addin[val];addin[wt])@'dupl x}
/ consp:{[val;wt;x] cross_[(cons;augment[val;wt])] dupl x}
consp:{[val;wt;x] (cons;augment[val;wt])@'dupl x}

start:enlist (();0 0)
/ step:{[val;wt;w;x] pair[({[val;wt;w;ys] ys where within_[w] each ys:consp[val;wt] each ys}[val;wt;w];outr')] cpr x}
step:{[val;wt;w;x] ({[val;wt;w;ys] ys where within_[w] each ys:consp[val;wt] each ys}[val;wt;w];{x 1}')@\:cpr x}
knapsack:{[val;wt;w;xs] first catalist[start;{[val;wt;w;x] thinL[q] merge[r] step[val;wt;w] x}[val;wt;w];xs]}

/ ---- checks: the Lean #guard, then brute force over all subsets; exit 1 on any mismatch
fail:{-2 "FAIL: ",x; exit 1}
g:knapsack[first;last;10;(6 5;5 4;4 6;3 3)]
-1 "guard: ",.Q.s1 g;
if[not g~((6 5;5 4);11 9); fail "guard expected ((6 5;5 4);11 9), got ",.Q.s1 g]

/ best value among all subsets of items within capacity c, by enumerating the 2^n bitmasks
brute:{[its;c] m:(count[its]#2) vs til "j"$2 xexp count its; v:sum its[;0]*m; max v where c>=sum its[;1]*m}
check:{[n;c] its:flip (1+n?30;1+n?20); k:knapsack[first;last;c;its]; b:brute[its;c];
  ok:(b=k[1;0])&(c>=k[1;1])&(k[1]~sum each flip $[count k 0; k 0; enlist 0 0]);
  -1 "n=",string[n]," c=",string[c]," knapsack=",string[k[1;0]]," brute=",string b;
  if[not ok; fail "brute-force mismatch on ",.Q.s1 (its;c;k)]}
\S 207
check[15;40]; check[15;60]; check[14;25]; check[16;80]; check[15;1]

/ timing: 200 items, capacity 1000
big:flip (1+200?100;1+200?100)
-1 "200 items, capacity 1000: ",string[system "t knapsack[first;last;1000;big]"]," ms";
exit 0
