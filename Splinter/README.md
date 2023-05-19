# Splinter Verification 

TODO fill this in

### Commands

`$verus -Zunpretty=expanded bundle.rs` to get expanded macro representation of a verus file.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs`
To verify just a single module.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 1`

To disable "Recommends" checks (since `verus` will sometimes incorrectly warn about recommends clauses
not being satisfied when they are provably satisfied).
```
--no-auto-recommends-check
```

If you find yourself buried in error output, use this command to only get the top (and also get it in color):
```
$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 2 --color=always 2>&1 | head -n 50
```

### Verus

We use it. "Documentation" here: https://github.com/verus-lang/verus/tree/main/source/pervasive
