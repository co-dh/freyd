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
/ Every needle's run of a sorted key column: `binr` the first index, `bin` the last.
look:{[k;v;xs] lo:k binr xs; v raze lo+til each 0|1+(k bin xs)-lo}
blookup:{[op;n] k0:gen[n;17] mod n; v0:gen[n;18] mod 1000000; ix:iasc k0; k::k0 ix; v::v0 ix;
  xs::gen[n;19] mod n; out[op;n;"look[k;v;xs]";sum look[k;v;xs]]}

/ Compute on compressed columns (LeetQ.Compressed), added once that module is merged, as `sum v`,
/ `sum v where b`, `select sum v by k from t` on the columns Bench/Main.lean builds for them.

ns:$[`ns in key a:.Q.opt .z.x; "J"$a`ns; 1000 10000 100000]
{bgetAll x; bzipD x; bselby x; bij x; baj x; blookup["lookupDense";x]; blookup["lookupFoR";x]} each ns;
\\
