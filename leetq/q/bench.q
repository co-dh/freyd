/ The q side of leetq's Bench/Main.lean: the same MINSTD data, the same operators, the same checksums.
/ Run: QHOME=/home/dh/q q leetq/q/bench.q [-ns 100000 1000000] -q   (single-threaded: no -s)
/ Prints `op n ms checksum`, ms the mean of `\t:5`.

M:2147483647
/ `cnt` MINSTD values after `seed`: Lean's `gen`
gen:{[c;s] 1_ c {(48271*x) mod M}\ s}

/ time `e` (a string evaluated globally) five times; print the mean and the checksum `c`
out:{[op;n;e;c] -1 " " sv (op;string n;string (system "t:5 ",e)%5;string c);}

bgetAll:{[n] d::(gen[n;1] mod n)!gen[n;2] mod 1000000; ks::gen[n;3] mod 2*n;
  out["getAll";n;"d@ks";sum d@ks]}
bzipD:{[n] d::(gen[n;1] mod n)!gen[n;2] mod 1000000; e::(gen[n;4] mod n)!gen[n;5] mod 1000000;
  out["zipD";n;"d+e";{(sum key x)+sum value x} d+e]}
bselby:{[n] t::([] k:gen[n;6] mod 1000; v:gen[n;7] mod 1000000);
  out["selby";n;"select sum v by k from t";exec sum k+v from 0!select sum v by k from t]}
bij:{[n] m:1|n div 10; kt::`k xkey ([] k:gen[m;9] mod m; w:gen[m;10] mod 1000000);
  t::([] k:gen[n;8] mod m; v:gen[n;11] mod 1000000);
  out["ij";n;"t ij kt";exec sum v+w from t ij kt]}
baj:{[n] tr::([] s:gen[n;12] mod 100; tm:gen[n;13] mod 1000000);
  / q's fast aj path: grouped by `s` (`p#`), time ascending within it; the stable sort keeps tie order
  qr::update `p#s from `s`tm xasc ([] s:gen[n;14] mod 100; tm:gen[n;15] mod 1000000; p:gen[n;16] mod 1000000);
  out["aj";n;"aj[`s`tm;tr;qr]";exec sum p from aj[`s`tm;tr;qr]]}
bwj:{[n] w::-100 0+\:tr`tm; out["wj";n;"wj[w;`s`tm;tr;(qr;(sum;`p))]";exec sum p from wj[w;`s`tm;tr;(qr;(sum;`p))]]}
/ Every needle's run of a sorted key column: `binr` the first index, `bin` the last.
look:{[k;v;xs] lo:k binr xs; v raze lo+til each 0|1+(k bin xs)-lo}
blookup:{[op;n] k0:gen[n;17] mod n; v0:gen[n;18] mod 1000000; ix:iasc k0; k::k0 ix; v::v0 ix;
  xs::gen[n;19] mod n; out[op;n;"look[k;v;xs]";sum look[k;v;xs]]}

/ Compute on compressed columns (LeetQ.Compressed): `sum v`, `sum v where b`, `select sum v by k from t`
/ on the columns Bench/Main.lean builds for them (columns 21, 23, 22). `/h` is the same with v and k cast to
/ short, the width Lean's dense column has. Few repetitions of a fast op are noise, so `tm` reruns with 20x
/ more until the total passes 100 ms (5 -> 100 -> 2000 ...).
tm:{[e] r:5; t:(system "t:",string[r]," ",e)%r; while[(100>t*r)&50000>r; r*:20; t:(system "t:",string[r]," ",e)%r]; t}
out2:{[op;n;e;c] -1 " " sv (op;string n;string tm e;string c);}
/ chk: `sum` of the keys and the sums, order free; v is the sum column of the grouped table
bcomp:{[sfx;f;n] v::f gen[n;21] mod 1000; k::f gen[n;22] mod 1000; b::1=gen[n;23] mod 2; t::([] k:k; v:v);
  out2["sumDense",sfx;n;"sum v";sum v];
  out2["sumWhereDense",sfx;n;"sum v where b";sum v where b];
  out2["selbySumDense",sfx;n;"select sum v by k from t";(sum "j"$exec k from r)+sum "j"$exec v from r:0!select sum v by k from t]}

ns:$[`ns in key a:.Q.opt .z.x; "J"$a`ns; 100000 1000000 10000000]
$[`comp in key a; {bcomp["";"j"$;x]; bcomp["/h";"h"$;x]} each ns;
  {bgetAll x; bzipD x; bselby x; bij x; baj x; bwj x; blookup["lookupDense";x]; blookup["lookupFoR";x]} each ns];
\\
