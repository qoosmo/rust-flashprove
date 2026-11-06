# Port notes: C++ semantics already ported

Pinned upstream `9e2bdd8ff5bf9c62f18263d7dac189b0400b260c`. One section per ported header. Each
section records what a later port step needs, so later sessions read this file instead of the C++.
Values are exact field elements; when the order of products differs from the C++, the values do not.

## `blocks/iop/tensor.h` → `flashprove-iop/src/tensor.rs` (verifier side)

- Index: bit $t$ of $j$ is variable $t$. A table with $2^k$ rows of length $l$ is indexed by
  $b + 2^k c$ (row $b$, place $c$): the low variables give the row.
- `Tensor`: $v[j] = s \prod_t (j_t ? h_t : l_t) \cdot B[\text{first} + d(j)]$. A pair $(1,0)$ or $(0,1)$ is
  a choice variable (`pick_mask`, `pick_value`). A dense variable has the pair $(1,1)$, and bit $i$
  of $d(j)$ is bit `dense_vars[i]` of $j$.
- `eq(z, s)`: pairs $(1-z_t, z_t)$. `product(f, s)`: pairs $(1, f_t)$.
- `insert_choice(at, count, value)`: new variables at `at..at+count` with fixed bits; dense
  variables $\ge$ `at` shift up.
- `fix_low(g, count)`: entry $j$ becomes $\sum_i \mathrm{eq}(i,g)\,v[i + 2^{\text{count}} j]$. The
  dense slice folds from the top dense bit down: $x_0 + (x_1 - x_0) g$.
- `rotate(by)`: variable $t$ goes to $(t + n - \text{by}) \bmod n$. The caller fixes `dense_vars`.
- `Form`: tensors + entries (an index may repeat) + `FrozenPart`s. A frozen part is
  $s \cdot f$ restricted to `(j & mask) == value`, with $f$ read at `without_bits(j, mask)`.
- `Form::fix_low(g, count, times)`: frozen parts are thawed unless every fixed variable is a
  choice of every part; entries move to `index >> count` with weight $\prod_t \mathrm{eq}$; the
  merge sorts by index and sums duplicates.
- Not ported (prover only): `held`, `EngineTerm`, `Held` hints, `with_table`, `set_held`.

## `blocks/iop/relation.h` (+ `VectorLay` of foldeq.h:126) → `flashprove-iop/src/relation.rs`

- `Row` = terms (Tensor on a table) + units (one entry) + runs (`first + step*j`; own E
  coefficients or a shared F stretch) + main forms; public `target`. `coefficient(o, part, idx)`
  sums all four.
- `add_scaled(other, x)`: concatenates scaled terms, units and forms; adds runs that cover the same
  entries (`lies_as`) into one; target $+= x\,t'$.
- Table bits of oracle $o$: `row_bits` $= \lceil\log_2 \text{rows}\rceil$, `place_bits` = `log_ell` of its
  code (base for MAIN, mask for MASK).
- `GroupLayout` (`Statement::layout`): members sorted by id (= sending order, `join` inserts by
  `upper_bound`). Blocks are aligned with $2^{\text{row\_bits}}$ rows, placed by decreasing size, ties
  in member order (stable sort). Kept members get no main block. $h = \lceil\log_2 \text{mask rows used}\rceil$,
  $k = \max(\lceil\log_2 \text{main used}\rceil, h, 1)$.
- `group_index(idx, a, first, gb)` $= (\text{first} + (idx \bmod 2^a)) + ((idx \gg a) \ll gb)$.
- `add_to_group_row(S, L, row, x, acc, aside)`: `acc.d` gets $2^{h + \text{log\_ell\_zk}}$ zeros.
  A term with scalar ·x gets `insert_choice(a, bits - a, first >> a)` and goes to `c` (MAIN) or is
  written into `d` (MASK). MAIN parts of kept members go to `kept` (sorted by oracle id, own
  indices). With `aside`, runs and units are summed into `aside.sums` and carried at the end with
  x = 1.
- `begin_run`: PLAIN rows as added → each member's sample rows in member order → GENERATOR rows.
- `add_row` faults (fail closed, `Err`): wrong group, missing table, term vars ≠ table bits, entry
  out of range, empty run, form does not fit, nonzero coefficient on a sample pad.
- `Statement::sampled` here stands in for send.h's pass-key; S3 (SEND) builds the sample rows and
  the pad.
- `VectorLay`: `index(j)` = j (rows low) or $(j \gg p) \mid ((j \bmod 2^p) \ll a)$ (rows high);
  `on_table` pads with zero choices, then rotates by $p$ when rows are high.
- Not ported: `MaskLedger`/`MaskSlot` (prover side), `sampled_elsewhere` (second chain).

## `blocks/iop/bat.h` → `flashprove-iop/src/bat.rs`

- `combine(S, g, in, x)`: row $i$ is added with weight $x^i$ through `add_to_group_row`, with
  runs and units set aside and carried once at the end with weight 1. `combine_rows` does the
  same sum on oracle messages (`Row::add_scaled`).
- `run`: `begin_run` first, then the BAT round's draw x (round 9 for test_u, 27 for test_omega).

## `fold.h`, `fold_rounds.h`, `fold_algebra.h` → `flashprove-iop/src/fold.rs`

- Messages: the FOLD ε round's message ends with the hiding sum $\sigma$ (before it, the fresh
  mask's root if the mask was not sent ahead: round 28 is 32 + 24 bytes, round 10 is 24). Its draw
  is ε. Then $k$ = the **stage's** k (`iopp_fold_shape` overrides the layout's k, h) FOLD rounds,
  each sending $(c_0, c_2)$, then drawing $g_j$.
- Running claim: $\sigma + \varepsilon t$; per round $c_1 = \text{claim} - 2c_0 - c_2$,
  $\text{claim} \leftarrow c_0 + c_1 g + c_2 g^2$. The output target is the final claim (notes 8, 27).
- `fold_output`: $c$ ← `c.fix_low(γ, k, ε)` then `freeze(log ell)`; each kept form scaled by
  $\varepsilon\prod(1-g_j)$; $d_0$ = `fold_mask_form` (d folded at $g_1..g_h$, times
  $\varepsilon\prod_{t\ge h} g_t$); $d_1$ = `fold_mask_weights(k, h, ell_mask, γ)`.
- `fold_shape_check`, `fold_row_check`: ported as `Result`.
- Not yet driven: the `GroupRow` that `fold_output` consumes needs every claim's coefficients,
  and the sample rows come from SEND (S3, send.h).

## Next: SEND sample rows (send.h, S3), then CS (cs.h:721)
