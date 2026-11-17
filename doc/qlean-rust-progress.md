# qlean C → Rust: progress (2026-11-15)

Integration branch `rust-port-0` at `a878f71` (/data/tmp/qrs/wt0); C baseline `8665576`.

## Merged on rust-port-0

| measure                                  | lines  |
|------------------------------------------|--------|
| Rust in `rust/src/*.rs`                  | 1,220  |
| of which FFI/unsafe scaffold (`ffi c lib pod rt simd`) | 493 |
| of which ported logic (safe modules)     | 727    |
| C deleted (`own.c` −107, `zip.c` −41)    | 148    |
| C added (calls into Rust, `sort.c` +10, `own.c` +10, `zip.c` +1) | 21 |
| exported `qrs_*` functions               | 22     |

The 22 exports: coc_lanes coc_std exc_ok group_fill group_ids group_ids_win ids_firsts ids_map ids_max ids_pack
key_range key_range_win own_check own_head own_write_head res_unpack res_unpack_add res_unpack_scalar u8_sum zq
ztable ztrailer. Several are stubs of the task-S scaffold that C does not call yet (B5–B11 fill them).

## Finished, not merged yet

| task | branch / worktree            | change                                    | state                                       |
|------|------------------------------|-------------------------------------------|---------------------------------------------|
| B4   | `rust-rel-B4` @ `2ce5081`    | `group::fill` replaces `ids_run` in `dedup` | committed, all gates green except qipc      |
| B1   | /data/tmp/qrs/wtB1 (uncommitted) | `ids.h` −44, `ids.rs` +87             | agent ended mid-run; reach ok (120 hits), not committed |

## Against the targets

| scope                                   | C lines | ported so far |
|-----------------------------------------|---------|---------------|
| Rel native ABI, column (b)              | 817     | B3 key range; B1, B4 pending merge |
| everything `LeetQ.Run` reaches, column (a) | 5,924 | —             |
| all of `qlean/c`                        | 21,170  | 148 deleted (≈0.7%) |
