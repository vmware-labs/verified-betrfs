# Splinter Verification 

TODO fill this in

### Commands

`$verus -Zunpretty=expanded bundle.rs` to get expanded macro representation of a verus file.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs`
To verify just a single module.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 1`


### Verus

We use it. "Documentation" here: https://github.com/verus-lang/verus/tree/main/source/pervasive